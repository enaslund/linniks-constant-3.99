"""Optimizer-independent verifier. Reconstructs source coverage and EVERY scalar input.
The analytic lemmas are mathematical premises; this program is not a formalization.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1');os.environ.setdefault('OMP_NUM_THREADS','1')
from endgame import *
import gzip,time,hashlib,argparse
from concurrent.futures import ProcessPoolExecutor
from config_v4 import TAU_SCALE as TS, DUAL_SCALE as DS
if not __debug__:raise RuntimeError('Python assertions must be enabled')

def ceildiv(a,b):
    assert isinstance(a,int) and isinstance(b,int) and b>0
    return -((-a)//b)

def scenario(rec):
    inp=rec['input'];rows=inp['rows'];d,D,Df=inp['d'],inp['D'],inp['Df'];ss=inp['second'];n=inp['n'];n2=ss['n'] if ss else 0
    assert min(d,D,Df)>0 and inp['S']==S and inp['dual_scale']==DS and inp['tau_scale']==TS
    assert len(rows)==len(inp['count_cost']) and all(x in (0,S) for x in inp['count_cost'])
    assert inp['count_budget']==2*S and inp['final']==5*10**10
    assert rows[-1][1]=='infinity' and rows[-1][2]==S and rows[-1][4]==-S and inp['count_cost'][-1]==0
    pos=Q(rows[0][0])
    for r in rows[:-1]:
        assert len(r)==5 and Q(r[0])==pos<Q(r[1]);pos=Q(r[1])
        assert all(isinstance(x,int) for x in r[2:]) and r[2]>0 and r[3]>=0
    assert pos==max(Q(3),Q(inp['ordinary_lower']))==Q(rows[-1][0])
    end=math.isqrt(d*TS*TS//S);end+=int(end*end*S<d*TS*TS)
    pos=0;maximum=-1;checks=excluded=branches=0;binding=None;F=inp['far_budget'];active_count=0
    for br in rec['certificate']['branches']:
        a,b=br['a'],br['b'];assert type(a)==type(b)==int and a==pos<b<=end;pos=b;branches+=1
        sh=b*(S//TS);f1=max(inp['v_first']-sh,0);f2=max(ss['v']-sh,0) if ss else 0
        de=TS*TS*d*Df*S
        nu=D*de-D*a*a*Df*S*S-n*D*f1*f1*TS*TS*d-n2*f2*f2*TS*TS*d*Df
        B=ceildiv(nu,de)
        if br.get('excluded'):
            assert B<0 and br['budget']==B;excluded+=1;continue
        if br.get('excluded_far'):
            assert F<0 and br['budget']==F;excluded+=1;continue
        assert min(F,B)>=0
        Y,Z,U=br['Y'],br['Z'],br['U'];assert all(type(x)==int and x>=0 for x in (Y,Z,U))
        active_count+=int(U>0)
        for row,count in zip(rows,inp['count_cost']):
            cost=max(row[4]-sh,0)**2//S
            assert Y*row[2]+Z*cost+U*count>=DS*row[3],('invalid column',a,b,row)
        checks+=len(rows)
        value=ceildiv(Y*F+Z*B+U*2*S,DS)+inp['first']+inp['final']
        assert value==br['upper'] and value<S,('invalid objective',value)
        if value>maximum:
            maximum=value;binding={k:inp[k] for k in ('case','height','L','ordinary_lower','second','gap','extension','third_lower','third_certificate','first','first_bounds','shifted_first_proof','far_budget','final','location_update')}
            binding.update(near_budget=B,branch=br)
    assert pos==end and maximum==rec['certificate']['maximum']
    return dict(maximum=maximum,branches=branches,excluded=excluded,checks=checks,binding=binding,count_dual_active=active_count)

def verify_tree(sp,node,L,path=''):
    if 'split' in node:
        assert set(node)=={'split','mid','children'} and len(node['children'])==2
        aa,bb=split_new(sp,node['split'],node['mid'])
        return verify_tree(aa,node['children'][0],L,path+'0')+verify_tree(bb,node['children'][1],L,path+'1')
    if 'positivity' in node:
        assert set(node)=={'positivity'};assert positivity_proof(sp,Q(node['positivity']['g']))==node['positivity']
        return [dict(maximum=-1,branches=0,excluded=0,checks=0,binding=None,count_dual_active=0,kind=sp['case']['kind'],height=sp['height'],variant='positivity')]
    if 'second_exclusion' in node:
        assert set(node)=={'second_exclusion'}
        red,proof=reduced_spec(sp);assert red is None and proof==node['second_exclusion']
        return [dict(maximum=-1,branches=0,excluded=0,checks=0,binding=None,count_dual_active=0,kind=sp['case']['kind'],height=sp['height'],variant='new_second_exclusion')]
    assert set(node)=={'record'};rec=node['record']
    if 'input' not in rec:
        from compact_records import regenerate_record
        rec=regenerate_record(sp,rec,L);inp=rec['input'];par=parse_params(inp)
    else:
        assert set(rec)=={'input','certificate'};inp=rec['input'];par=parse_params(inp)
        assert inp['L']==L and type(inp['lambda_den'])==int and 50<=inp['lambda_den']<=10000
        gen=make_endgame(sp,L,par,inp['lambda_den']);assert gen==inp,('regenerated input mismatch',sp,par)
    result=scenario(rec);result.update(kind=sp['case']['kind'],height=sp['height'],variant=par['method'])
    if result['binding']:result['binding']['path']=path
    return [result]

def task(args):
    line,L=args;rt=json.loads(line);idx=rt['id'];assert type(idx)==int and 0<=idx<len(specs());sp=specs()[idx];assert rt['L']==L
    if 'format' in rt:
        from compact_records import FORMAT
        assert rt.pop('format')==FORMAT
    keys={'id','L','seconds','inside'}
    if sp['case']['kind']!='rr':keys.add('outside')
    assert set(rt)==keys
    ans=[]
    for ht in ('inside','outside'):
        if ht=='outside' and sp['case']['kind']=='rr':continue
        ans+=verify_tree(with_height(sp,ht),rt[ht],L)
    best=max(ans,key=lambda x:x['maximum']);out=dict(id=idx,leaves=len(ans),maximum=best['maximum'],binding=best['binding'],branches=sum(x['branches'] for x in ans),excluded=sum(x['excluded'] for x in ans),checks=sum(x['checks'] for x in ans),count_dual_active=sum(x['count_dual_active'] for x in ans),kinds={},heights={},variants={})
    if out['binding']:out['binding']['spec_id']=idx
    for a in ans:
        out['variants'][a['variant']]=out['variants'].get(a['variant'],0)+1
        for field,kind in [('kinds','kind'),('heights','height')]:out[field][a[kind]]=max(out[field].get(a[kind],-1),a['maximum'])
    return out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('certificate',type=Path);ap.add_argument('--L',required=True);ap.add_argument('--workers',type=int,default=4);a=ap.parse_args();tt=time.time();_,base_counts=validate_source_cover();mx=-1;binding=None;tot={k:0 for k in ('leaves','branches','excluded','checks','count_dual_active')};maps={k:{} for k in ('kinds','heights','variants')}
    from poly_rows import verify_polynomial_table
    from alias_check import check as check_alias
    polynomial_proofs=verify_polynomial_table();alias_proof=check_alias()
    location=location_proof();ids=[]
    with gzip.open(a.certificate,'rt') as f,ProcessPoolExecutor(max_workers=a.workers) as pool:
        for j,out in enumerate(pool.map(task,((line,a.L) for line in f),chunksize=1)):
            assert j==out['id'];ids.append(j)
            for k in tot:tot[k]+=out[k]
            for k in maps:
                for key,value in out[k].items():maps[k][key]=(maps[k].get(key,0)+value if k=='variants' else max(maps[k].get(key,-1),value))
            if out['maximum']>mx:mx=out['maximum'];binding=out['binding']
            if j%100==0:print('VERIFIED',j,'max',mx/S,'leaves',tot['leaves'],'seconds',round(time.time()-tt,1),flush=True)
    assert ids==list(range(2768))
    from verify_published_single import scenario as check_large
    large=json.loads((ROOT/'results'/f'large_{a.L}.json').read_text());large_result=check_large(large,None,a.L,True)
    from small_exception import check
    small=check(a.L)
    from small_exception_399 import check as check_small399
    small399=check_small399()
    large399=json.loads((ROOT/'results/large_branch_3.99.json').read_text())
    large399_result=check_large(large399,None,'3.99',True)
    w=wgt(a.L);support=lower(w.A-3);decay=lower(w.A-2*w.x);assert support>0 and decay>0
    report=dict(L=a.L,status='PASS: exact numerical implication from stated analytic/source premises; NOT a formally verified theorem',regenerated_every_input=True,**base_counts,**tot,maximum_numerator=mx,scale=S,margin_numerator=S-mx,maxima_by_kind=maps['kinds'],maxima_by_height=maps['heights'],variants=maps['variants'],binding=binding,large_case=large_result,small_exception=small,new_second_zero_proof=location,new_complex_polynomials=polynomial_proofs,polynomial_table_sha256=hashlib.sha256((ROOT/'results/polynomial_table.json').read_bytes()).hexdigest(),source_alias_enclosure=alias_proof,small_exception_at_3_99=small399,large_case_at_3_99=large399_result,support_margin=support,decay_margin=decay,capacity_blocks_used=0,certificate_sha256=hashlib.sha256(a.certificate.read_bytes()).hexdigest(),seconds=time.time()-tt,scope='Source lemmas and new weighted-near, shifted-envelope and family-transfer deductions are mathematical premises. All elementary interval inputs and dual inequalities are regenerated. Published single-zero height-one far density only.')
    (ROOT/'results'/f'verification_{a.L}.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
