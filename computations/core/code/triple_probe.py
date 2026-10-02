import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from triple_inputs import *
from compact_records import expand_root
import numpy as np
from scipy.optimize import linprog,minimize_scalar
from dual_fast import hull_dual
from concurrent.futures import ProcessPoolExecutor
import gzip,time,argparse

def sample(inp,ngrid=51,count=False):
    d,D,Df=inp['d']/S,inp['D']/S,inp['Df']/S;vf=inp['v_first']/S;n=inp['n'];sec=inp['second'];n2=sec['n'] if sec else 0;v2=sec['v']/S if sec else 0
    W=np.array([r[2]/S for r in inp['rows']]);G=np.array([r[3]/S for r in inp['rows']]);v=np.array([r[4]/S for r in inp['rows']]);F=inp['far_budget']/S;C0=np.array(inp.get('count_cost',[0]*len(v)))/S
    count=count and np.any(C0)
    def fun(t):
        B=D*(1-t*t/d)-n*D/Df*max(vf-t,0)**2-n2*max(v2-t,0)**2
        if B<0:return (-1,t,0,0,0)
        C=np.maximum(v-t,0)**2
        y,z=hull_dual(W,C,G,F,B)
        if count:
            # Only solve 3-row LP when its extra constraint excludes the unconstrained witness.
            sol=linprog([F,B,2.],A_ub=-np.stack([W,C,C0],axis=1),b_ub=-G,bounds=(0,None),method='highs')
            if not sol.success:raise RuntimeError(sol.message)
            y,z,u=sol.x
        else:u=0
        return (inp['first']/S+y*F+z*B+2*u+inp['final']/S,t,y,z,u)
    grid=np.linspace(0,math.sqrt(d),ngrid);vals=[fun(t) for t in grid];j=max(range(len(vals)),key=lambda j:vals[j][0]);mx=vals[j]
    if 0<j<len(grid)-1:
        res=minimize_scalar(lambda t:-fun(t)[0],bounds=(grid[j-1],grid[j+1]),method='bounded',options={'xatol':1e-7});mx=max(mx,fun(res.x))
    return mx

def job(args):
    line,L,ngrid,use_count=args;rec=expand_root(json.loads(line));out=[]
    for ht in ('inside','outside'):
        if ht not in rec:continue
        for path,inp in leaves(rec[ht]):
            new=input_with_third(inp,L);v=sample(new,ngrid,use_count)
            out.append(dict(id=rec['id'],height=ht,path=path,case=inp['case'],gap=inp.get('gap'),second=inp['second'],extension=inp['extension'],third_lower=new['third_lower'],value=v,den=inp['lambda_den']))
    return out
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--workers',type=int,default=4);ap.add_argument('--grid',type=int,default=41);ap.add_argument('--count',action='store_true');ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=2768);a=ap.parse_args()
    fn=ROOT/'results/certificate_4.33.jsonl.gz'
    with gzip.open(fn,'rt') as f:lines=[line for i,line in enumerate(f) if a.start<=i<a.stop]
    result=[];tt=time.time()
    p=ROOT/'results'/f'probe_{a.L}_{a.start}_{a.stop}_{int(a.count)}.jsonl'
    with p.open('w') as f,ProcessPoolExecutor(max_workers=a.workers) as pool:
        for j,out in enumerate(pool.map(job,[(l,a.L,a.grid,a.count) for l in lines],chunksize=1)):
            result+=out
            for r in out:f.write(json.dumps(r)+'\n')
            if j%100==0:print('PROBE',j,'max',max([r['value'][0] for r in result],default=-1),'fail',sum(r['value'][0]>=1 for r in result),'sec',round(time.time()-tt,1),flush=True)
    summary=dict(L=a.L,leaves=len(result),failed=int(sum(r['value'][0]>=1 for r in result)),maximum=max(result,key=lambda r:r['value'][0]),seconds=time.time()-tt,status='EXPLORATORY ONLY; not interval-certified; count constraint used='+str(a.count))
    p.with_suffix('.summary.json').write_text(json.dumps(summary,indent=2));print(json.dumps(summary,indent=2))
