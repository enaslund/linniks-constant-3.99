"""Identity-preserving hidden-global-family resource model.
Only a numerical implication from the analytic premises. No global theorem claim.
"""
from setup_local import *
from shadow_certificate import regenerate, shadow_plan,ceildiv,near_shadow
from config_v4 import TAU_SCALE as TS, DUAL_SCALE as DS
from fractions import Fraction
from numba import njit
from scipy.optimize import linprog

@njit(cache=True)
def dual3(W,C,G,F,B,n,finite):
    # Eliminate the hidden-count dual u, and then z. Convex search in y.
    lo=0.;hi=0.
    for j in range(len(W)):
        if C[j]==0.:lo=max(lo,G[j]/W[j])
        hi=max(hi,G[j]/W[j])
    def val(y):
        z=0.;u=0.
        for i in range(len(W)):
            deficit=G[i]-y*W[i]
            if C[i]>0.:z=max(z,deficit/C[i])
            if finite[i]:u=max(u,deficit)
        return y*F+z*B+n*u,z,u
    ratio=(5.**.5-1)/2
    x1=hi-ratio*(hi-lo);x2=lo+ratio*(hi-lo)
    f1,z1,u1=val(x1);f2,z2,u2=val(x2)
    for it in range(64):
        if f1<f2:
            hi=x2;x2=x1;f2=f1;z2=z1;u2=u1
            x1=hi-ratio*(hi-lo);f1,z1,u1=val(x1)
        else:
            lo=x1;x1=x2;f1=f2;z1=z2;u1=u2
            x2=lo+ratio*(hi-lo);f2,z2,u2=val(x2)
    if f1<f2:return x1,z1,u1
    return x2,z2,u2

def scenarios(base,step=Q('.01')):
    """Exhaustive identities of global family relative to the reserved local family."""
    ans=[]
    for br in shadow_plan(base,step):
        if br['ng']==0:
            ans.append(dict(br,identity='unhidden'))
        else:
            ans.append(dict(br,identity='distinct'))
            sec=base.get('second')
            if sec and sec['n']==br['ng']:
                ans.append(dict(br,identity='same_reserved'))
    return ans

def input_for(base,L,br,par,den=500):
    # regenerate has independently bounded features and model diagonals.
    inp=regenerate(base,L,{k:br[k] for k in ('lo','hi','ng','real')},par,den)
    inp['identity']=br['identity']
    if br['identity']=='same_reserved':
        assert inp['second'] is not None and inp['second']['n']==br['ng']
    if br['identity']=='unhidden':assert br['ng']==0
    return inp

def quadratic_terms(inp):
    """Upper Diagonal constants and lower features: rational B(tau) upper bound."""
    D=Q(inp['D'],S);d=Q(inp['d'],S);Df=Q(inp['Df'],S)
    terms=[(Q(inp['n'])*D/Df,Q(inp['v_first'],S))]
    if inp.get('second') and inp['identity']!='same_reserved':
        terms.append((Q(inp['second']['n']),Q(inp['second']['v'],S)))
    sh=inp['shadow']
    if sh['ng']:
        terms.append((Q(sh['ng'])*D/Q(sh['diagonal'],S),Q(sh['v_global'],S)))
    return D,d,terms

def near_exact(inp,a,b):
    """Exactly maximize the concave piecewise quadratic budget on [a/TS,b/TS]."""
    ta,tb=Q(a,TS),Q(b,TS);D,d,terms=quadratic_terms(inp)
    breaks=sorted(set([ta,tb]+[v for _,v in terms if ta<v<tb]))
    def f(t):return D*(1-t*t/d)-sum(k*max(v-t,0)**2 for k,v in terms)
    best=max(f(ta),f(tb))
    for l,r in zip(breaks,breaks[1:]):
        mid=(l+r)/2;active=[(k,v)for k,v in terms if v>mid]
        star=sum((k*v for k,v in active),Q(0))/(D/d+sum((k for k,v in active),Q(0)))
        t=min(r,max(l,star));best=max(best,f(t))
    B=ceildiv(best.numerator*S,best.denominator)
    sh=b*(S//TS);C=[max(row[4]-sh,0)**2//S for row in inp['rows']]
    return C,B

def propose(inp,a,b):
    C,B=near_exact(inp,a,b)
    if B<0:return {'a':a,'b':b,'excluded':True,'budget':B}
    W=[r[2] for r in inp['rows']];G=[r[3] for r in inp['rows']]
    finite=[r[1]!='infinity' for r in inp['rows']]
    ng=inp['shadow']['ng'] if inp['identity']=='distinct' else 0
    F=inp['far_budget']
    if ng:
        y,z,u=dual3(np.array(W)/S,np.array(C)/S,np.array(G)/S,F/S,B/S,ng,np.array(finite))
    else:
        from optimize_near import hull_n
        y,z=hull_n(np.array(W)/S,np.array(C)/S,np.array(G)/S,F/S,B/S);u=0.
    Y=max(0,math.ceil(y*DS)+1);Z=max(0,math.ceil(z*DS)+1);U=max(0,math.ceil(u*DS)+1)if ng else 0
    Y+=max(0,max(ceildiv(DS*g-Y*w-Z*c,w)for g,w,c in zip(G,W,C)))
    if ng:
        U+=max(0,max(DS*g-Y*w-U*S for g,w,fin in zip(G,W,finite)if fin)//S+1)
    assert all(Y*w+Z*c>=DS*g for g,w,c in zip(G,W,C))
    if ng:assert all(Y*w+U*S>=DS*g for g,w,fin in zip(G,W,finite)if fin)
    upper=inp['first']+inp['final']+ceildiv(Y*F+Z*B+U*ng*S,DS)
    return dict(a=a,b=b,Y=Y,Z=Z,U=U,upper=upper)

def threshold_end(inp):
    e=math.isqrt(inp['d']*TS*TS//S)
    return e+int(e*e*S<inp['d']*TS*TS)

def certify(inp,target=Q('.999'),min_width=1):
    end=threshold_end(inp);stack=[(i,min(end,i+5000))for i in range(0,end,5000)];ans=[]
    # Work at largest thresholds first, often the binding range.
    while stack:
        a,b=stack.pop();r=propose(inp,a,b)
        if not r.get('excluded') and r['upper']>=target*S:
            if b-a>min_width:
                mid=(a+b)//2;stack.extend([(a,mid),(mid,b)]);continue
            if r['upper']>=S:raise RuntimeError(('no certificate',r['upper']/S,a,b,inp['identity']))
        ans.append(r)
    return sorted(ans,key=lambda t:t['a'])

def check_one(inp,rows):
    end=threshold_end(inp);last=0;mx=-1;binding=None;ex=checks=0
    W=[r[2]for r in inp['rows']];G=[r[3]for r in inp['rows']];finite=[r[1]!='infinity'for r in inp['rows']]
    ng=inp['shadow']['ng']if inp['identity']=='distinct'else 0
    for row in rows:
        a,b=row['a'],row['b'];assert a==last and a<b<=end;last=b
        C,B=near_exact(inp,a,b)
        if row.get('excluded'):
            assert B<0 and row['budget']==B;ex+=1;continue
        Y,Z,U=[row[k] for k in ('Y','Z','U')]
        assert all(type(x)is int and x>=0 for x in (Y,Z,U))
        if not ng:assert U==0
        for w,c,g in zip(W,C,G):assert Y*w+Z*c>=DS*g;checks+=1
        if ng:
            for w,g,fin in zip(W,G,finite):
                if fin:assert Y*w+U*S>=DS*g;checks+=1
        ub=inp['first']+inp['final']+ceildiv(Y*inp['far_budget']+Z*B+U*ng*S,DS)
        assert ub==row['upper']and ub<S
        if ub>mx:mx=ub;binding=dict(row=row,near_budget=B)
    assert last==end
    return dict(maximum=mx,excluded=ex,checks=checks,branches=len(rows),binding=binding)

if __name__=='__main__':
    import argparse,time
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.20');ap.add_argument('--step',default='.01');ap.add_argument('--den',type=int,default=500);ap.add_argument('--verify',action='store_true');aa=ap.parse_args()
    base=load_data('selected_inputs.json')['2063'][0][1]
    par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')
    plan=scenarios(base,Q(aa.step));fn=PROJECT/'results'/f'identity_local_{aa.L}.jsonl.gz';t0=time.time()
    reports=[];maximum=-1;binding=None
    if aa.verify:
        with gzip.open(fn,'rt')as f:records=[json.loads(l)for l in f]
        assert len(records)==len(plan)
    else:records=[];out=gzip.open(fn,'wt')
    for i,br in enumerate(plan):
        inp=input_for(base,aa.L,br,par,aa.den)
        if aa.verify:
            rec=records[i];check_input(inp,rec['input']);assert rec['branch']==br;cc=rec['certificate']
        else:
            cc=certify(inp);rec=dict(branch=br,input=inp,certificate=cc);records.append(rec);out.write(json.dumps(rec,separators=(',',':'))+'\n');out.flush()
        rr=check_one(inp,cc);reports.append(rr)
        if rr['maximum']>maximum:maximum=rr['maximum'];binding=dict(branch=br,input=input_summary(inp),bound=rr)
        print('CASE',i,br,'max',rr['maximum']/S,'branches',rr['branches'],'sec',round(time.time()-t0,2),flush=True)
    if not aa.verify:out.close()
    report=dict(L=aa.L,status='PASS numerical implication for ONE LOCAL scenario, not a global exponent',regenerated_inputs=True,cases=len(plan),branches=sum(r['branches']for r in reports),checks=sum(r['checks']for r in reports),excluded=sum(r['excluded']for r in reports),maximum=maximum,scale=S,maximum_decimal=str(Q(maximum,S)),binding=binding,seconds=time.time()-t0)
    (PROJECT/'results'/f'identity_local_{aa.L}_report.json').write_text(json.dumps(report,indent=2));print('DONE',maximum/S,report['seconds'])
