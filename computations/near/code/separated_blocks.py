"""Near Gram blocks with truly separated heights, retaining ONE far representative.
Global hidden centers have actual |height|>1; any contributing local center is
inside fixed R0 and has height O(1/log q). This program checks only the numerical
consequence of the separately proved uniform near-block argument.
"""
from identity_model import *
from extension_enclosures import mixfeature
from optimize_near import hull_n
from numba import njit

@njit(cache=True)
def dual_block(W,C,G,WH,CH,GH,NH,F,B,n):
    # A three-variable LP is used only to propose the certificate below.
    # Kept out of verification; this function is not actually called.
    return 0.,0.,0.

def make_block_input(base,L,br,par,den=200):
    inp=input_for(base,L,br,par,den)
    if br['identity']=='unhidden':
        inp['hidden_rows']=[];return inp
    sec=inp['second'];w=wgt(L);r=Q(base['ordinary_lower']);ng=br['ng'];real=br['real']
    # This local implementation reuses the ordinary grid for the hidden family.
    # Reject cases where a third-family restriction removed its initial bins.
    assert inp['rows'] and Q(inp['rows'][0][0])==r, 'hidden-family grid must start at its height-one anchor'
    # Same family: its old local objective/far subtraction is replaced, not counted twice.
    if br['identity']=='same_reserved':
        inp['first']-=sec['contribution']
        inp['far_budget']+=sec['n']*lower(w.w(Q(sec['hi'])))
        inp['same_family_adjustment']=dict(removed_objective=sec['contribution'],restored_far=sec['n']*lower(w.w(Q(sec['hi']))))
    K=int((1+ETA)*S);D=inp['D'];m=2 if real else 1
    assert K>0 and (m+1)*D-m*K>0
    # A model block is K I+(D-K)11^t. Its global-only cost equals the inherited
    # singleton/averaged-real cost. The local residual cost is a Schur-complement bound.
    inp['separated_block']=dict(K=K,D=D,global_centers=m,characters=ng,anchor=str(r),matrix_minimum=(m+1)*D-m*K)
    gG,gZ,t=Q(par['gg']),Q(par['gz']),Q(par['mix']);s=Q(inp['shift']);Ba=w.B(r,real)
    hidden=[]
    for row in inp['rows']:
        a=Q(row[0]);end=row[1]
        if end=='infinity':
            hidden.append([str(a),'infinity',S,upper(iv.exp(-w.A*I(a))*Ba*w.winv(a)), -S, lower(w.winv(a))])
        else:
            h=Q(end);v=mixfeature(gG,gZ,s,t,h,real)
            hidden.append([str(a),end,row[2],upper(iv.exp(-w.A*I(a))*Ba),v,S])
    inp['hidden_rows']=hidden
    return inp

def near_block(inp,a,b):
    C,B=near_exact(inp,a,b)
    if inp['identity']=='unhidden':return C,[],B
    sh=inp['shadow'];bb=inp['separated_block'];D,K,m=bb['D'],bb['K'],bb['global_centers']
    denom=K+m*(D-K);assert denom>0
    # kappa=m(D-K)/(K+m(D-K)); monotonicity in tau is exact: kappa<1.
    kappa=Q(m*(D-K),denom)
    tau=Q(b,TS);ug=max(Q(sh['v_global'],S)-tau,0)
    CH=[]
    for row in inp['hidden_rows']:
        if row[1]=='infinity':CH.append(0);continue
        residual=max(Q(row[4],S)-tau-kappa*ug,0)
        # Using global optimum without reoptimizing its coefficients gives
        # D*(Phi_full-Phi_global) >= residual^2. No inverse or conditioning issue.
        val=residual*residual
        CH.append(val.numerator*S//val.denominator)
    return C,CH,B

def proposal_block(inp,a,b):
    C,CH,B=near_block(inp,a,b)
    if B<0:return dict(a=a,b=b,excluded=True,budget=B)
    rr=inp['rows'];W=[r[2]for r in rr];G=[r[3]for r in rr];F=inp['far_budget']
    hh=inp['hidden_rows'];WH=[r[2]for r in hh];GH=[r[3]for r in hh];NH=[r[5]for r in hh];ng=inp['shadow']['ng']
    if not hh:
        y,z=hull_n(np.array(W)/S,np.array(C)/S,np.array(G)/S,F/S,B/S);u=0.
    else:
        A=np.vstack([np.array([W,C,[0]*len(W)]).T,np.array([WH,CH,NH]).T])/S
        g=np.array(G+GH)/S
        sol=linprog([F/S,B/S,float(ng)],A_ub=-A,b_ub=-g,bounds=(0,None),method='highs')
        if not sol.success:raise RuntimeError(sol.message)
        y,z,u=sol.x
    Y=max(0,math.ceil(y*DS)+1);Z=max(0,math.ceil(z*DS)+1);U=max(0,math.ceil(u*DS)+1)if hh else 0
    Y+=max(0,max(ceildiv(DS*g-Y*w-Z*c,w)for g,w,c in zip(G,W,C)))
    if hh:
        U+=max(0,max(ceildiv(DS*g-Y*w-Z*c-U*n,n)for g,w,c,n in zip(GH,WH,CH,NH)))
    assert all(Y*w+Z*c>=DS*g for g,w,c in zip(G,W,C))
    assert all(Y*w+Z*c+U*n>=DS*g for g,w,c,n in zip(GH,WH,CH,NH))
    val=inp['first']+inp['final']+ceildiv(Y*F+Z*B+U*ng*S,DS)
    return dict(a=a,b=b,Y=Y,Z=Z,U=U,upper=val)

def cert_block(inp,target=Q('.998'),width=1):
    end=threshold_end(inp);stack=[(j,min(j+5000,end))for j in range(0,end,5000)];rows=[]
    while stack:
        a,b=stack.pop();row=proposal_block(inp,a,b)
        if not row.get('excluded') and row['upper']>=target*S:
            if b-a>width:
                mid=(a+b)//2;stack.extend([(a,mid),(mid,b)]);continue
            if row['upper']>=S:raise RuntimeError(('no certificate',row['upper']/S,a,b,inp['identity']))
        rows.append(row)
    return sorted(rows,key=lambda r:r['a'])

def verify_block(inp,rows):
    W=[r[2]for r in inp['rows']];G=[r[3]for r in inp['rows']];F=inp['far_budget'];hh=inp['hidden_rows']
    WH=[r[2]for r in hh];GH=[r[3]for r in hh];NH=[r[5]for r in hh];ng=inp['shadow']['ng']
    last=0;end=threshold_end(inp);mx=-1;binding=None;checks=ex=0
    for row in rows:
        a,b=row['a'],row['b'];assert a==last and a<b<=end;last=b
        C,CH,B=near_block(inp,a,b)
        if row.get('excluded'):
            assert B==row['budget'] and B<0;ex+=1;continue
        Y,Z,U=[row[k]for k in ('Y','Z','U')];assert all(type(j)is int and j>=0 for j in (Y,Z,U))
        if not hh:assert U==0
        for w,c,g in zip(W,C,G):assert Y*w+Z*c>=DS*g;checks+=1
        for w,c,g,n in zip(WH,CH,GH,NH):assert Y*w+Z*c+U*n>=DS*g;checks+=1
        v=inp['first']+inp['final']+ceildiv(Y*F+Z*B+U*ng*S,DS)
        assert v==row['upper']and v<S
        if v>mx:mx=v;binding=dict(branch=row,near_budget=B)
    assert last==end
    return dict(maximum=mx,branches=len(rows),checks=checks,excluded=ex,binding=binding)

if __name__=='__main__':
    import argparse,time
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.15');ap.add_argument('--step',default='.01');ap.add_argument('--den',type=int,default=200);ap.add_argument('--verify',action='store_true');ap.add_argument('--only',type=int,default=-1);aa=ap.parse_args()
    base=load_data('selected_inputs.json')['2063'][0][1]
    par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3');plan=scenarios(base,Q(aa.step));t0=time.time()
    fn=PROJECT/'results'/f'separated_local_{aa.L}.jsonl.gz';mx=-1;reports=[];binding=None
    if aa.verify:
        with gzip.open(fn,'rt')as f:records=[json.loads(l)for l in f]
        assert len(records)==len(plan)
    else:out=gzip.open(fn,'wt')
    for i,br in enumerate(plan):
        if aa.only>=0 and i!=aa.only:continue
        inp=make_block_input(base,aa.L,br,par,aa.den)
        if aa.verify:
            rec=records[i];assert rec['branch']==br;check_input(inp,rec['input']);cc=rec['certificate']
        else:
            cc=cert_block(inp);rec=dict(branch=br,input=inp,certificate=cc);out.write(json.dumps(rec,separators=(',',':'))+'\n');out.flush()
        rr=verify_block(inp,cc);reports.append(rr)
        if rr['maximum']>mx:mx=rr['maximum'];binding=dict(case=br,input=input_summary(inp),report=rr)
        print('CASE',i,br,'max',rr['maximum']/S,'branches',rr['branches'],'sec',round(time.time()-t0,2),flush=True)
    if not aa.verify:out.close()
    rep=dict(L=aa.L,status='PASS only for specified local scenario; analytic block premise not formally verified',regenerated_inputs=True,complete_global_second_cover=(aa.only<0),cases=len(reports),branches=sum(r['branches']for r in reports),excluded=sum(r['excluded']for r in reports),checks=sum(r['checks']for r in reports),maximum_numerator=mx,scale=S,margin_numerator=S-mx,binding=binding,seconds=time.time()-t0)
    (PROJECT/'results'/f'separated_local_{aa.L}_report.json').write_text(json.dumps(rep,indent=2));print('DONE',mx/S,time.time()-t0)
