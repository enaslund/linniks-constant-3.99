"""Numerical realization of separated first-family near blocks. Local scope."""
from separated_blocks import *
from refine_probe import spec_from_input
from build_progress import near as old_near

def first_out_input(base,L,branch,par,den=200):
    assert base['height']=='outside' and base['case']['kind']!='rr'
    inp=make_endgame(spec_from_input(base),L,par,den)
    w=wgt(L);a=Q(inp['case']['lo']);b=Q(inp['case']['hi']);p=max(a,Q(inp['case']['lp']))
    if inp.get('gap'):p=max(p,Q(inp['gap']['lo']))
    K=int((1+ETA)*S);D=inp['D'];Df=inp['Df'];n=inp['n'];real=(inp['case']['kind']=='rc');m=2 if real else 1
    inp['outside_subcase']=branch
    if branch=='height_one':
        inp['far_budget']-=n*lower(w.w(b));inp['hidden_rows']=[]
        return inp
    assert branch=='outside_buffer' and (m+1)*Df-m*K>0
    removed=inp['first_bounds']['outside'];inp['first']-=removed
    inp['first_block']=dict(K=K,Df=Df,D=D,global_centers=m,characters=n,anchor=str(p),removed_objective=removed)
    gg,gz,t=Q(par['gg']),Q(par['gz']),Q(par['mix']);s=Q(inp['shift']);B=w.B(p,real)
    grid=[p];edge=math.floor(p*den)+1;end=max(Q(3),p)
    while Q(edge,den)<end:grid.append(Q(edge,den));edge+=1
    if grid[-1]!=end:grid.append(end)
    hh=[]
    for l,r in zip(grid,grid[1:]):
        hh.append([str(l),str(r),lower(w.w(r)),upper(iv.exp(-w.A*I(l))*B),mixfeature(gg,gz,s,t,r,real),S])
    hh.append([str(end),'infinity',S,upper(iv.exp(-w.A*I(end))*B*w.winv(end)),-S,lower(w.winv(end))])
    inp['hidden_rows']=hh
    return inp

def max_budget(D,d,terms,a,b):
    ta,tb=Q(a,TS),Q(b,TS);breaks=sorted(set([ta,tb]+[v for _,v in terms if ta<v<tb]))
    def f(t):return D*(1-t*t/d)-sum(k*max(v-t,0)**2 for k,v in terms)
    best=max(f(ta),f(tb))
    for l,r in zip(breaks,breaks[1:]):
        mid=(l+r)/2;act=[(k,v)for k,v in terms if v>mid]
        star=sum((k*v for k,v in act),Q(0))/(D/d+sum((k for k,v in act),Q(0)))
        best=max(best,f(min(r,max(l,star))))
    return ceildiv(best.numerator*S,best.denominator)

def first_near(inp,a,b):
    D,d,Df=Q(inp['D'],S),Q(inp['d'],S),Q(inp['Df'],S);sec=inp['second'];vf=Q(inp['v_first'],S)
    if inp['outside_subcase']=='outside_buffer':
        block=inp['first_block'];K=Q(block['K'],S);m=block['global_centers'];beta=Df-K;denom=K+m*beta
        terms=[(inp['n']*D*m/denom,vf)]
    else:terms=[(inp['n']*D/Df,vf)]
    if sec:terms.append((Q(sec['n']),Q(sec['v'],S)))
    B=max_budget(D,d,terms,a,b);tau=Q(b,TS)
    C=[max(row[4]-b*(S//TS),0)**2//S for row in inp['rows']]
    CH=[]
    if inp['hidden_rows']:
        kappa=m*beta/denom;ug=max(vf-tau,0)
        for row in inp['hidden_rows']:
            if row[1]=='infinity':CH.append(0);continue
            val=D/Df*max(Q(row[4],S)-tau-kappa*ug,0)**2
            CH.append(val.numerator*S//val.denominator)
    return C,CH,B

def first_propose(inp,a,b):
    C,CH,B=first_near(inp,a,b)
    if B<0:return dict(a=a,b=b,excluded=True,budget=B)
    rr=inp['rows'];W=[r[2]for r in rr];G=[r[3]for r in rr];F=inp['far_budget'];hh=inp['hidden_rows'];ng=inp['n']if hh else 0
    WH=[r[2]for r in hh];GH=[r[3]for r in hh];NH=[r[5]for r in hh]
    if not hh:y,z=hull_n(np.array(W)/S,np.array(C)/S,np.array(G)/S,F/S,B/S);u=0.
    else:
        A=np.vstack([np.array([W,C,[0]*len(W)]).T,np.array([WH,CH,NH]).T])/S
        sol=linprog([F/S,B/S,float(ng)],A_ub=-A,b_ub=-np.array(G+GH)/S,bounds=(0,None),method='highs')
        if not sol.success:raise RuntimeError(sol.message)
        y,z,u=sol.x
    Y=max(0,math.ceil(y*DS)+1);Z=max(0,math.ceil(z*DS)+1);U=max(0,math.ceil(u*DS)+1)if hh else 0
    Y+=max(0,max(ceildiv(DS*g-Y*w-Z*c,w)for g,w,c in zip(G,W,C)))
    if hh:U+=max(0,max(ceildiv(DS*g-Y*w-Z*c-U*n,n)for g,w,c,n in zip(GH,WH,CH,NH)))
    val=inp['first']+inp['final']+ceildiv(Y*F+Z*B+U*ng*S,DS)
    return dict(a=a,b=b,Y=Y,Z=Z,U=U,upper=val)

def first_cert(inp,target=Q('.998'),minwidth=1):
    end=threshold_end(inp);stack=[(i,min(end,i+5000))for i in range(0,end,5000)];ans=[]
    while stack:
        a,b=stack.pop();row=first_propose(inp,a,b)
        if not row.get('excluded')and row['upper']>=target*S:
            if b-a>minwidth:mid=(a+b)//2;stack.extend([(a,mid),(mid,b)]);continue
            if row['upper']>=S:raise RuntimeError(('no first certificate',row['upper']/S,a,b))
        ans.append(row)
    return sorted(ans,key=lambda r:r['a'])

def first_verify(inp,rows):
    rr=inp['rows'];hh=inp['hidden_rows'];F=inp['far_budget'];ng=inp['n']if hh else 0;last=0;end=threshold_end(inp);mx=-1;binding=None;checks=exc=0
    for row in rows:
        a,b=row['a'],row['b'];assert a==last and a<b<=end;last=b;C,CH,B=first_near(inp,a,b)
        if row.get('excluded'):assert B==row['budget']and B<0;exc+=1;continue
        Y,Z,U=[row[k]for k in ('Y','Z','U')];assert all(type(k)is int and k>=0 for k in(Y,Z,U))
        if not hh:assert U==0
        for row0,c in zip(rr,C):assert Y*row0[2]+Z*c>=DS*row0[3];checks+=1
        for row0,c in zip(hh,CH):assert Y*row0[2]+Z*c+U*row0[5]>=DS*row0[3];checks+=1
        val=inp['first']+inp['final']+ceildiv(Y*F+Z*B+U*ng*S,DS);assert val==row['upper']and val<S
        if val>mx:mx=val;binding=dict(branch=row,near_budget=B)
    assert last==end
    return dict(maximum=mx,branches=len(rows),excluded=exc,checks=checks,binding=binding)

if __name__=='__main__':
 import argparse,time
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.25');ap.add_argument('--id',type=int,default=2559);ap.add_argument('--verify',action='store_true');ap.add_argument('--legacy-split',action='store_true');aa=ap.parse_args()
 data=load_data('selected_global_scan_inputs.json');base=next(x['input']for x in data if x['id']==aa.id);par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3');path=PROJECT/'results'/f'outside_first_{aa.id}_{aa.L}.jsonl.gz';t0=time.time();reps=[];mx=-1;bind=None
 branches=('height_one','outside_buffer')if aa.legacy_split else('outside_buffer',)
 if aa.verify:
  with gzip.open(path,'rt')as f:records=[json.loads(l)for l in f]
  assert len(records)==len(branches)
 else:out=gzip.open(path,'wt')
 for j,branch in enumerate(branches):
  inp=first_out_input(base,aa.L,branch,par)
  if aa.verify:
   rec=records[j];check_input(inp,rec['input']);cc=rec['certificate']
  else:
   cc=first_cert(inp);out.write(json.dumps(dict(input=inp,certificate=cc),separators=(',',':'))+'\n');out.flush()
  rr=first_verify(inp,cc);reps.append(rr);print(branch,rr['maximum']/S,time.time()-t0,flush=True)
  if rr['maximum']>mx:mx=rr['maximum'];bind=dict(input=input_summary(inp),report=rr)
 if not aa.verify:out.close()
 rep=dict(L=aa.L,source_id=aa.id,scope='One first-family-outside BUFFERED rectangle configuration, not a global exponent',maximum=mx,scale=S,branches=sum(r['branches']for r in reps),checks=sum(r['checks']for r in reps),excluded=sum(r['excluded']for r in reps),binding=bind,regenerated_inputs=True,seconds=time.time()-t0)
 (PROJECT/'results'/f'outside_first_{aa.id}_{aa.L}_report.json').write_text(json.dumps(rep,indent=2));print('DONE',mx/S,flush=True)
