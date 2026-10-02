"""Build a complete adaptive rational certificate. Optimizer output is repaired
and checked in integer arithmetic before any branch can be accepted.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1');os.environ.setdefault('OMP_NUM_THREADS','1')
from pathlib import Path
from fractions import Fraction as Q
import math,json,gzip,time,argparse
import numpy as np
from scipy.optimize import linprog
from input_bounds import *
from cover_v4 import roots,cell
ROOT=Path(__file__).resolve().parents[1]

class CannotCertify(Exception):pass

def near_data(inp,ta,tb):
    bb=tb*(S//TAU_SCALE)
    costs=[max(r[4]-bb,0)**2//S for r in inp['rows']]
    d,D,Df=inp['d'],inp['D'],inp['Df']
    budget=Q(D)*(1-Q(ta*ta*S,TAU_SCALE**2*d))
    budget-=Q(inp['n']*D*max(inp['v_first']-bb,0)**2,Df*S)
    second=inp['second']
    if second:budget-=Q(second['n']*max(second['v']-bb,0)**2,S)
    return costs,ceil_fraction(budget)

def dual_bound(inp,ta,tb):
    C,B=near_data(inp,ta,tb)
    if B<0:return {'a':ta,'b':tb,'excluded':True,'budget':B}
    W=[r[2] for r in inp['rows']];G=[r[3] for r in inp['rows']];F=inp['far_budget']
    if F<0:return {'a':ta,'b':tb,'excluded_far':True,'budget':F}
    active=[i for i,c in enumerate(C) if c>0];zero=[i for i,c in enumerate(C) if c==0]
    assert zero
    zmax=zero[0]
    for j in zero[1:]:
        if G[j]*W[zmax]>G[zmax]*W[j]:zmax=j
    active.append(zmax)
    sol=linprog(-np.array([G[i]/S for i in active]),
        A_ub=np.array([[W[i]/S for i in active],[C[i]/S for i in active]]),
        b_ub=[F/S,B/S],bounds=(0,None),method='highs')
    if not sol.success:raise RuntimeError('LP proposal failure: '+sol.message)
    yy=np.maximum(-sol.ineqlin.marginals,0)
    Y=max(0,math.ceil(float(yy[0])*DUAL_SCALE)+1);Z=max(0,math.ceil(float(yy[1])*DUAL_SCALE)+1)
    repair=max(0,max(ceil_fraction(Q(g*DUAL_SCALE-Y*w-Z*c,w)) for w,c,g in zip(W,C,G)));Y+=repair
    assert all(Y*w+Z*c>=g*DUAL_SCALE for w,c,g in zip(W,C,G))
    U=ceil_fraction(Q(Y*F+Z*B,DUAL_SCALE))+inp['first']+inp['final']
    return {'a':ta,'b':tb,'Y':Y,'Z':Z,'upper':U}

def tau_end(inp):
    k=math.isqrt(inp['d']*TAU_SCALE**2//S)
    return k if k*k*S>=inp['d']*TAU_SCALE**2 else k+1

def solve_input(inp,target=Q('.9995'),min_width=20,accept=Q('.9999')):
    end=tau_end(inp);leaves=[]
    pending=[(a,min(a+5000,end)) for a in range(0,end,5000)]
    # Likely binding branches first. This only saves unsuccessful search work.
    mid=end*.92
    pending.sort(key=lambda x:abs((x[0]+x[1])/2-mid),reverse=True)
    while pending:
        a,b=pending.pop();r=dual_bound(inp,a,b)
        if not (r.get('excluded') or r.get('excluded_far')) and r['upper']>=target*S:
            if b-a>min_width:
                m=(a+b)//2;pending.extend([(a,m),(m,b)]);continue
            if r['upper']>=accept*S:
                raise CannotCertify((r['upper']/S,a,b))
        leaves.append(r)
    leaves.sort(key=lambda r:r['a'])
    valid=[r for r in leaves if 'upper' in r]
    mx=max((r['upper'] for r in valid),default=-1)
    return {'branches':leaves,'maximum':mx}

def proposal(c,L,l2lo=None,second=None,den=500):
    inp=make_input(c,L,l2lo,second,den)
    cert=solve_input(inp)
    return {'input':inp,'certificate':cert}

def prove_cell(c,L,depth=0):
    """All returned branches are individually certified. Failures cause case
    refinement, never deletion. The independent verifier checks the cover."""
    lo,hi=Q(c['lo']),Q(c['hi']);r=Q(c['source_l2']);records=[]
    try:
        rec=proposal(c,L);return [{'case':c,'mode':'unreserved','records':[rec]}]
    except CannotCertify as err:
        if err.args and err.args[0][0]<1.013:
            try:
                rec=proposal(c,L,den=2000);return [{'case':c,'mode':'unreserved','records':[rec]}]
            except CannotCertify:pass
    if hi-lo>Q('.0025') and Q(c['lp'])-lo<Q('.03'):
        mid=(lo+hi)/2
        return prove_cell(cell(c['parent'],lo,mid),L,depth+1)+prove_cell(cell(c['parent'],mid,hi),L,depth+1)
    # Reserve a second character family on bounded intervals, with both types.
    # From 1.6 onward an unreserved tail case is used.
    end=max(r,min(Q(c['lp']),Q('1.6')))
    try:
        try:tail=proposal(c,L,end)
        except CannotCertify:
            try:tail=proposal(c,L,end,den=2000)
            except CannotCertify:
                end=max(r,Q('1.6'));tail=proposal(c,L,end)
        pending=[(r,end)] if r<end else []
        while pending:
            a,b=pending.pop();pair=[];success=True
            for n in (1,2):
                try:pair.append(proposal(c,L,a,{'hi':str(b),'n':n}))
                except CannotCertify:success=False;break
            if success:records.extend(pair);continue
            if b-a>Q('.002'):
                m=(a+b)/2;pending.extend([(m,b),(a,m)]);continue
            # Refine the lambda mesh before refining the first-zero cell.
            pair=[];success=True
            for n in (1,2):
                try:pair.append(proposal(c,L,a,{'hi':str(b),'n':n},den=2000))
                except CannotCertify:success=False;break
            if success:records.extend(pair);continue
            raise CannotCertify(('second interval',str(a),str(b)))
        records.sort(key=lambda z:(Q(z['input']['ordinary_lower']),z['input']['second']['n']))
        records.append(tail)
        return [{'case':c,'mode':'reserved','records':records,'tail_start':str(end)}]
    except CannotCertify as error:
        if depth>=7:raise RuntimeError(f'Unproved case at {L}: {c}: {error}')
        mid=(lo+hi)/2
        return prove_cell(cell(c['parent'],lo,mid),L,depth+1)+prove_cell(cell(c['parent'],mid,hi),L,depth+1)

def work(arg):
    c,L=arg;t=time.time();ans=prove_cell(c,L)
    return {'root':c,'leaves':ans,'seconds':time.time()-t}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.58');ap.add_argument('--workers',type=int,default=6)
    ap.add_argument('--start',type=int,default=0);ap.add_argument('--stop',type=int,default=10000)
    a=ap.parse_args();cs=roots()[a.start:a.stop];tag=a.L.replace('.','_')
    dest=ROOT/'results'/f'certificate_{tag}_{a.start}_{a.stop}.jsonl.gz';t=time.time();mx=-1;count=0
    from concurrent.futures import ProcessPoolExecutor
    with gzip.open(dest,'wt') as f,ProcessPoolExecutor(max_workers=a.workers) as pool:
        for rec in pool.map(work,[(c,a.L) for c in cs],chunksize=1):
            f.write(json.dumps(rec,separators=(',',':'))+'\n');f.flush();count+=1
            maximum=max(z['certificate']['maximum'] for leaf in rec['leaves'] for z in leaf['records'])
            mx=max(mx,maximum)
            print(count,rec['root']['kind'],rec['root']['lo'],'leaves',len(rec['leaves']),
                'records',sum(len(x['records']) for x in rec['leaves']), 'W',maximum/S,
                'MAX',mx/S,'seconds',round(time.time()-t,1),flush=True)
    meta={'L':a.L,'roots':count,'maximum':mx,'scale':S,'seconds':time.time()-t}
    (Path(str(dest)+'.meta.json')).write_text(json.dumps(meta,indent=2));print(meta,flush=True)
if __name__=='__main__':main()
