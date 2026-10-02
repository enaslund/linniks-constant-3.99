import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from endgame import *
import numpy as np,gzip,time,argparse,traceback
from scipy.optimize import linprog
from concurrent.futures import ProcessPoolExecutor
from optimize_near import hull_n,optimize
from config_v4 import TAU_SCALE as TS,DUAL_SCALE as DS

def ceildiv(a,b):return -((-a)//b)

def near(inp,a,b):
    sh=b*(S//TS);C=[max(r[4]-sh,0)**2//S for r in inp['rows']]
    d,D,Df=inp['d'],inp['D'],inp['Df'];df=max(inp['v_first']-sh,0);ss=inp['second'];n2=ss['n'] if ss else 0;df2=max(ss['v']-sh,0) if ss else 0
    de=TS*TS*d*Df*S
    nu=D*de-D*a*a*Df*S*S-inp['n']*D*df*df*TS*TS*d-n2*df2*df2*TS*TS*d*Df
    return C,ceildiv(nu,de)

class CannotCertify(Exception):pass

def solve(inp,target=Q('.9998'),accept=Q('.999995'),min_width=1,use_count=True):
    d=inp['d'];end=math.isqrt(d*TS*TS//S);end+=int(end*end*S<d*TS*TS)
    rr=inp['rows'];W=[r[2] for r in rr];G=[r[3] for r in rr];F=inp['far_budget'];Icost=inp['count_cost'];count=use_count and any(Icost)
    wa=np.array(W)/S;ga=np.array(G)/S;ic=np.array(Icost)/S
    pending=[(a,min(a+5000,end)) for a in range(0,end,5000)];pending.sort(key=lambda x:abs((x[0]+x[1])/2-.92*end),reverse=True)
    leaves=[]
    while pending:
        a,b=pending.pop();C,B=near(inp,a,b)
        if B<0:leaves.append({'a':a,'b':b,'excluded':True,'budget':B});continue
        if F<0:leaves.append({'a':a,'b':b,'excluded_far':True,'budget':F});continue
        ca=np.array(C)/S;y,z=hull_n(wa,ca,ga,F/S,B/S);u=0.
        # The extra constraint may be inactive. Nonnegative zero is always a valid choice.
        if count and inp['first']/S+y*F/S+z*B/S>float(target)-.00001:
            sol=linprog([F/S,B/S,2.],A_ub=-np.stack([wa,ca,ic],axis=1),b_ub=-ga,bounds=(0,None),method='highs')
            if not sol.success:raise RuntimeError(sol.message)
            y,z,u=sol.x
        Y=max(0,math.ceil(y*DS)+1);Z=max(0,math.ceil(z*DS)+1);U=max(0,math.ceil(u*DS))
        Y+=max(0,max(ceildiv(g*DS-Y*w-Z*c-U*ic,w) for w,c,ic,g in zip(W,C,Icost,G)))
        assert all(Y*w+Z*c+U*ic>=g*DS for w,c,ic,g in zip(W,C,Icost,G))
        upperval=ceildiv(Y*F+Z*B+U*2*S,DS)+inp['first']+inp['final']
        if upperval>=target*S:
            if b-a>min_width:
                m=(a+b)//2;pending.extend([(a,m),(m,b)]);continue
            if upperval>=accept*S:raise CannotCertify((upperval/S,a,b))
        leaves.append(dict(a=a,b=b,Y=Y,Z=Z,U=U,upper=upperval))
    leaves.sort(key=lambda r:r['a']);return dict(branches=leaves,maximum=max((r['upper'] for r in leaves if 'upper' in r),default=-1))

def improve_leaf(sp,par,L,depth=0,allow_opt=True):
    red,up=reduced_spec(sp)
    if red is None:return {'second_exclusion':up}
    err=None;inp=None
    for den in ([200,500,2000] if depth==0 else [500,2000]):
        try:
            inp=make_endgame(sp,L,par,den);cert=solve(inp)
            return {'record':{'input':inp,'certificate':cert}}
        except CannotCertify as ex:err=ex.args[0]
        except AssertionError as ex:
            if par['method']!='pair':raise
            par=dict(method='mixture',gg='1.6',gz='1.08',mix='.18',zeta='3');inp=make_endgame(sp,L,par,den)
            try:return {'record':{'input':inp,'certificate':solve(inp)}}
            except CannotCertify as ex:err=ex.args[0]
    # Try a separately proposed rational near witness once, before increasing the case count.
    if (allow_opt or depth in (8,12)) and inp is not None and par['method']!='pair' and err[0]<1.045:
        ans=optimize(inp,L,False,160)
        if ans['optimized']<err[0]-.00003:
            gg,gz,mix=ans['parameters'];p2=dict(method='mixture',gg=f'{gg:.4f}',gz=f'{gz:.4f}',mix=f'{mix:.4f}',zeta='3')
            try:
                ii=make_endgame(sp,L,p2,500);ce=solve(ii);return {'record':{'input':ii,'certificate':ce}}
            except (CannotCertify,AssertionError):par=p2
    c=sp['case'];a,b=Q(c['lo']),Q(c['hi']);gap=sp.get('gap');sec=sp['second']
    if depth>=13:raise RuntimeError(('unresolved',sp,par,err))
    # Subdivide the quantitatively widest remaining uncertainty, never omit it.
    options=[]
    if sec and Q(sec['hi'])-Q(sp['ordinary_lower'])>Q('.00008'):
        width=Q(sec['hi'])-Q(sp['ordinary_lower']);options.append((float(width)*.7,'second',(Q(sec['hi'])+Q(sp['ordinary_lower']))/2))
    if b-a>Q('.0000125'):options.append((float(b-a)*2.,'first',(a+b)/2))
    if par['method']=='pair' and gap and gap['hi']!='infinity' and Q(gap['hi'])-Q(gap['lo'])>Q('.001'):
        options.append((float(Q(gap['hi'])-Q(gap['lo']))*.3,'gap',(Q(gap['hi'])+Q(gap['lo']))/2))
    if not options:raise RuntimeError(('unresolved widths',sp,par,err))
    _,axis,mid=max(options);aa,bb=split_new(sp,axis,mid)
    return {'split':axis,'mid':str(mid),'children':[improve_leaf(aa,par,L,depth+1,False),improve_leaf(bb,par,L,depth+1,False)]}

def from_plan(sp,node,L):
    if 'split' in node:
        aa,bb=split_new(sp,node['split'],node['mid'])
        return {'split':node['split'],'mid':node['mid'],'children':[from_plan(aa,node['children'][0],L),from_plan(bb,node['children'][1],L)]}
    p=node['leaf']
    if p['method']=='positivity':return {'positivity':positivity_proof(sp,Q(p['g']))}
    return improve_leaf(sp,p,L)

def task(args):
    plan,L,dest=args;idx=plan['id'];tt=time.time();out={'id':idx,'L':L};sp=specs()[idx]
    try:
        for ht in ('inside','outside'):
            if ht=='outside' and sp['case']['kind']=='rr':continue
            out[ht]=from_plan(with_height(sp,ht),plan[ht],L)
        out['seconds']=time.time()-tt
        with gzip.open(Path(dest)/f'{idx:04d}.json.gz','wt') as f:json.dump(out,f,separators=(',',':'))
        return dict(id=idx,ok=True,seconds=out['seconds'])
    except Exception as ex:
        report=dict(id=idx,ok=False,error=repr(ex),trace=traceback.format_exc(),seconds=time.time()-tt)
        (Path(dest)/f'{idx:04d}.fail.json').write_text(json.dumps(report,indent=2));return report
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.34');ap.add_argument('--workers',type=int,default=4);ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=2768);ap.add_argument('--ids',default='');a=ap.parse_args()
    from poly_rows import verify_polynomial_table
    print(verify_polynomial_table(),flush=True)
    with gzip.open(ROOT/'results/search_plan_4_35.jsonl.gz','rt') as f:plans=[json.loads(l) for l in f]
    ids=set(map(int,a.ids.split(','))) if a.ids else set(range(a.start,a.stop))
    dest=ROOT/'results'/('records_'+a.L);dest.mkdir(exist_ok=True)
    jobs=[(p,a.L,str(dest)) for p in plans if p['id'] in ids and not(dest/f"{p['id']:04d}.json.gz").exists()]
    tt=time.time();bad=0
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        for j,r in enumerate(pool.map(task,jobs,chunksize=1)):
            bad+=not r['ok']
            if j%20==0 or not r['ok']:print('BUILD',j,'id',r['id'],'ok',r['ok'],'bad',bad,'sec',round(time.time()-tt,1),'details',r.get('error',''),flush=True)
    print('DONE',len(jobs),'failed',bad,'seconds',time.time()-tt,flush=True)
