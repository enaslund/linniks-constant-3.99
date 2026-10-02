"""Independent finite cover + exact dual verifier for the two-zero extension.
--regenerate recomputes every elementary enclosure, including height tails.
No optimizer is used. Analytic implications still require mathematical review.
"""
from pathlib import Path
from fractions import Fraction as Q
import argparse,json,gzip,math,time,hashlib
from cover_v5 import roots,cell,check_first_cover
from verify_v4 import check_record,S
from config_v4 import ETA,FINAL,T,BETA
if not __debug__:raise RuntimeError('Do not run with python -O')

def check_density(pr,c,L,regenerate):
    gap=pr['gap'];method=pr['method'];assert method in ('single','paired')
    if gap is not None:
        assert c['kind']=='complex' and Q(gap['lo'])>=Q(c['lp'])
        assert gap['hi']=='infinity' or Q(gap['hi'])>Q(gap['lo'])
    if method=='paired':
        assert c['kind'] in ('rc','complex')
        if c['kind']=='complex':assert gap is not None and gap['hi']!='infinity'
    records=pr['records'];assert records
    if pr['mode']=='unreserved':
        assert len(records)==1 and records[0]['input']['second'] is None
        assert Q(records[0]['input']['ordinary_lower'])==Q(c['source_l2'])
    else:
        assert pr['mode']=='reserved';end=Q(pr['tail_start']);assert end>=Q(c['source_l2'])
        assert records[-1]['input']['second'] is None and Q(records[-1]['input']['ordinary_lower'])==end
        assert (len(records)-1)%2==0;pos=Q(c['source_l2'])
        for j in range(0,len(records)-1,2):
            sa,sb=records[j]['input']['second'],records[j+1]['input']['second']
            assert sa and sb and sa['n']==1 and sb['n']==2
            assert sa['lo']==sb['lo'] and sa['hi']==sb['hi'] and Q(sa['lo'])==pos<Q(sa['hi'])
            pos=Q(sa['hi'])
        assert pos==end
    ans=[]
    for rec in records:
        inp=rec['input'];assert inp['gap']==gap and inp['method']==method
        if regenerate:
            from input_bounds_v5 import make_input5
            sec=inp['second']
            gen=make_input5(c,L,Q(inp['ordinary_lower']),{'hi':sec['hi'],'n':sec['n']} if sec else None,inp['lambda_den'],gap,method)
            assert gen==inp,'regenerated input mismatch'
        r=check_record(rec,c,L,False)
        if r['binding'] is not None:r['binding'].update({'gap':gap,'method':method})
        r['method']=method;ans.append(r)
    return ans

def check_leaf(leaf,L,regenerate):
    c=leaf['case'];assert c==cell(c['parent'],c['lo'],c['hi']);prs=leaf['proofs'];assert prs
    if leaf['gap_mode']=='none':assert len(prs)==1 and prs[0]['gap'] is None
    else:
        assert leaf['gap_mode']=='partition' and c['kind']=='complex'
        pos=Q(c['lp'])
        for i,pr in enumerate(prs):
            gap=pr['gap'];assert gap is not None and Q(gap['lo'])==pos
            if i==len(prs)-1:assert gap['hi']=='infinity'
            else:assert gap['hi']!='infinity' and Q(gap['hi'])>pos;pos=Q(gap['hi'])
    return [r for pr in prs for r in check_density(pr,c,L,regenerate)]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--L',default='4.57');ap.add_argument('--regenerate',action='store_true');a=ap.parse_args()
    expected=roots();t=time.time();cs=[];records=branches=excluded=checks=paired=0;mx=-1;binding=None;stats={};rootcount=0;gap_cases=0
    with gzip.open(a.certificate,'rt') as f:
        for idx,line in enumerate(f):
            assert idx<len(expected);root=json.loads(line);assert root['root']==expected[idx];rootcount+=1
            pos=Q(root['root']['lo'])
            for leaf in root['leaves']:
                c=leaf['case'];assert c['parent']==root['root']['parent'] and Q(c['lo'])==pos;pos=Q(c['hi']);assert pos<=Q(root['root']['hi']);cs.append(c)
                gap_cases+=len(leaf['proofs'])
                for r in check_leaf(leaf,a.L,a.regenerate):
                    records+=1;branches+=r['branches'];excluded+=r['excluded'];checks+=r['checks'];paired+=r['method']=='paired'
                    if r['maximum']>mx:mx=r['maximum'];binding=r['binding']
                    stats[c['kind']]=max(stats.get(c['kind'],-1),r['maximum'])
            assert pos==Q(root['root']['hi'])
            if rootcount%25==0:print(rootcount,'roots',len(cs),'cells',records,'records',round(time.time()-t,2),'seconds',flush=True)
    assert rootcount==len(expected);check_first_cover(cs)
    from enclosures import RigorousWeights,I,upper,lower
    w=RigorousWeights(a.L);large=upper((1+I(ETA))*w.V*w.G(Q('1.5'))*w.winv(Q('1.5'))+I(FINAL));assert large<S
    support=lower(w.A-3);tail_support=lower(w.A-2*w.x);assert min(support,tail_support)>0
    report={'L':a.L,'status':'PASS: full finite cover, exact duals, paired-height enclosures','regenerated_interval_inputs':a.regenerate,
      'roots':rootcount,'first_zero_cells':len(cs),'gap_cases':gap_cases,'density_cases':records,'paired_density_cases':paired,
      'threshold_branches':branches,'excluded_branches':excluded,'exact_dual_column_checks':checks,
      'maximum_numerator':mx,'scale':S,'maximum_decimal':str(Q(mx,S)),'minimum_margin_numerator':S-mx,
      'maxima_by_kind':stats,'binding':binding,'large_lambda1_bound':large,'support_margin_A_minus_3':support,
      'support_margin_A_minus_2x':tail_support,'certificate_sha256':hashlib.sha256(a.certificate.read_bytes()).hexdigest(),
      'seconds':time.time()-t,'scope':'Finite numerical reduction and elementary interval enclosures; not a formalization of the new analytic paired-zero lemma or inherited analytic inputs.'}
    out=a.certificate.parent/('verification_v5_'+a.L.replace('.','_')+'.json');out.write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
