"""Independent rational dual / finite-cover checker; no optimizer imported.

--regenerate additionally rebuilds every elementary interval enclosure.
This is not a formal verification of the analytic lemmas or imported tables.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,gzip,math,time,hashlib
from cover_v4 import roots,cell,check_first_cover
from config_v4 import ETA,FINAL,T,BETA,SMOOTH_DELTA
if not __debug__:raise RuntimeError('Do not run a proof checker with python -O')
S=10**16;TS=10**6;DS=10**12

def ceildiv(n,d):
    assert d>0;return -((-n)//d)

def check_record(rec,c,L,regenerate=False):
    inp=rec['input'];assert inp['case']==c and inp['L']==L
    assert inp['S']==S and inp['tau_scale']==TS and inp['dual_scale']==DS
    l2=Q(inp['ordinary_lower']);assert l2>=Q(c['source_l2'])
    sec=inp['second'];n=2 if c['kind']=='complex' else 1
    assert inp['n']==n
    if sec:
        assert Q(sec['lo'])==l2<Q(sec['hi'])<=2 and sec['n'] in (1,2)
    if regenerate:
        from input_bounds import make_input
        regenerated=make_input(c,L,l2,{'hi':sec['hi'],'n':sec['n']} if sec else None,inp['lambda_den'])
        assert regenerated==inp,'interval input mismatch'
    rows=inp['rows'];assert rows and Q(rows[0][0])==l2
    end_lambda=max(Q(2),l2)
    for j,row in enumerate(rows[:-1]):
        assert Q(row[0])<Q(row[1])==Q(rows[j+1][0]);assert row[2]>0 and row[3]>=0
    assert rows[-1][0]==str(end_lambda) and rows[-1][1]=='infinity' and rows[-1][2]==S
    assert set(inp['first_bounds'])==({'inside'} if c['kind']=='rr' else {'inside','outside'})
    assert inp['first']==max(inp['first_bounds'].values())+(sec['contribution'] if sec else 0)
    assert inp['final']==ceildiv(FINAL.numerator*S,FINAL.denominator)
    d,D,Df,vf=inp['d'],inp['D'],inp['Df'],inp['v_first'];assert min(d,D,Df)>0
    k=math.isqrt(d*TS*TS//S);end=k if k*k*S>=d*TS*TS else k+1
    F=inp['far_budget'];pos=total=excluded=checks=0;maximum=-1;binding=None
    for br in rec['certificate']['branches']:
        a,b=br['a'],br['b'];assert a==pos and a<b<=end;pos=b;total+=1
        shift=b*(S//TS);df=max(vf-shift,0);n2=sec['n'] if sec else 0
        df2=max(sec['v']-shift,0) if sec else 0
        # Independent single-common-denominator formula, not builder helper.
        denominator=TS*TS*d*Df*S
        numerator=(D*denominator-D*a*a*Df*S*S
                   -n*D*df*df*TS*TS*d-n2*df2*df2*TS*TS*d*Df)
        B=ceildiv(numerator,denominator)
        if br.get('excluded'):
            assert B<0 and br['budget']==B;excluded+=1;continue
        if br.get('excluded_far'):
            assert F<0 and br['budget']==F;excluded+=1;continue
        assert min(F,B)>=0
        Y,Z=br['Y'],br['Z'];assert isinstance(Y,int) and isinstance(Z,int) and min(Y,Z)>=0
        for row in rows:
            C=max(0,row[4]-shift)**2//S
            assert Y*row[2]+Z*C>=row[3]*DS,('invalid dual',c,sec,a,b)
        checks+=len(rows)
        value=ceildiv(Y*F+Z*B,DS)+inp['first']+inp['final']
        assert value==br['upper'] and value<S,('unproved exponent',c,sec,a,b,value)
        if value>maximum:
            maximum=value;binding={'case':c,'second':sec,'ordinary_lower':str(l2),
                'gamma':inp['gamma'],'shift':inp['shift'],'branch':br,'first':inp['first'],
                'first_bounds':inp['first_bounds'],'far_budget':F,'near_budget':B,'final':inp['final']}
    assert pos==end and maximum==rec['certificate']['maximum']
    return {'maximum':maximum,'branches':total,'excluded':excluded,'checks':checks,'binding':binding}

def check_leaf(leaf,L,regenerate=False):
    c=leaf['case'];assert c==cell(c['parent'],c['lo'],c['hi'])
    records=leaf['records'];assert records
    if leaf['mode']=='unreserved':
        assert len(records)==1 and records[0]['input']['second'] is None
        assert Q(records[0]['input']['ordinary_lower'])==Q(c['source_l2'])
    else:
        assert leaf['mode']=='reserved';end=Q(leaf['tail_start']);assert end>=Q(c['source_l2'])
        assert records[-1]['input']['second'] is None
        assert Q(records[-1]['input']['ordinary_lower'])==end
        assert (len(records)-1)%2==0
        pos=Q(c['source_l2'])
        for j in range(0,len(records)-1,2):
            a,b=records[j]['input'],records[j+1]['input'];sa,sb=a['second'],b['second']
            assert sa is not None and sb is not None and sa['n']==1 and sb['n']==2
            assert sa['lo']==sb['lo'] and sa['hi']==sb['hi']
            assert Q(sa['lo'])==pos<Q(sa['hi']);pos=Q(sa['hi'])
        assert pos==end
    return [check_record(rec,c,L,regenerate) for rec in records]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--L',default='4.60')
    ap.add_argument('--regenerate',action='store_true');a=ap.parse_args();expected=roots()
    t=time.time();cs=[];records=branches=excluded=checks=0;mx=-1;binding=None;stats={};root_count=0
    with gzip.open(a.certificate,'rt') as f:
        for idx,line in enumerate(f):
            assert idx<len(expected);root=json.loads(line);assert root['root']==expected[idx]
            pos=Q(root['root']['lo']);root_count+=1
            for leaf in root['leaves']:
                c=leaf['case'];assert c['parent']==root['root']['parent'] and Q(c['lo'])==pos
                pos=Q(c['hi']);assert pos<=Q(root['root']['hi']);cs.append(c)
                results=check_leaf(leaf,a.L,a.regenerate)
                for r in results:
                    records+=1;branches+=r['branches'];excluded+=r['excluded'];checks+=r['checks']
                    if r['maximum']>mx:mx=r['maximum'];binding=r['binding']
                    kind=c['kind'];stats[kind]=max(stats.get(kind,-1),r['maximum'])
            assert pos==Q(root['root']['hi'])
            if root_count%25==0:print(root_count,'roots',len(cs),'cells',records,'records',round(time.time()-t,2),'seconds',flush=True)
    assert root_count==len(expected),'incomplete root cover';check_first_cover(cs)
    from enclosures import RigorousWeights,I,upper,lower
    w=RigorousWeights(a.L)
    large=upper((1+I(ETA))*w.V*w.G(Q('1.5'))*w.winv(Q('1.5'))+I(FINAL))
    assert large<S
    support=lower(w.A-3);tail_support=lower(w.A-2*w.x);assert min(support,tail_support)>0
    assert all(0<=b<=1 for b in BETA) and list(BETA)==sorted(BETA) and T<Q('.5')
    assert lower(w.H0)>3*S//100 and upper(w.V)<1000*S and upper(w.winv(Q(0)))<10*S
    smooth=I(10000*SMOOTH_DELTA)*((1+I(ETA))*w.V*w.winv(Q(0))+12)
    assert upper(smooth)<ETA*S
    report={'L':a.L,'status':'PASS: exact finite dual inequalities and full case cover',
      'regenerated_interval_inputs':a.regenerate,'roots':root_count,'first_zero_cells':len(cs),
      'density_cases':records,'threshold_branches':branches,'excluded_branches':excluded,
      'exact_dual_column_checks':checks,'maximum_numerator':mx,'scale':S,
      'maximum_decimal':str(Q(mx,S)),'minimum_margin_numerator':S-mx,
      'maxima_by_kind':stats,'binding':binding,'large_lambda1_bound':large,
      'support_margin_A_minus_3':support,'support_margin_A_minus_2x':tail_support,
      'smooth_kernel_error_upper':upper(smooth),'smooth_delta':str(SMOOTH_DELTA),
      'certificate_sha256':hashlib.sha256(a.certificate.read_bytes()).hexdigest(),
      'seconds':time.time()-t,
      'scope':'Verifies the numerical reduction and elementary enclosures. It is not a formalization of the analytic lemmas, height extension, or source zero-location tables.'}
    out=a.certificate.parent/('verification_'+a.L.replace('.','_')+'.json')
    out.write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
