"""Exploratory two-ordering/hidden-global-zero refinement; not a proof certificate."""
from start import *
from optimize_near import negative_bound,shape,hull_n,fast_fun,XN,XW
from scipy.optimize import minimize_scalar
from numba import njit

@njit(cache=True)
def ev(tau,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vglob,vcap,ng,fac=1.):
 B=D*(1-tau*tau/d)-n*D/Df*max(vf-tau,0)**2-n2*max(v2-tau,0)**2
 if ng: B-=ng*max(0.,fac*max(vglob-tau,0.)**2-max(vcap-tau,0.)**2)
 if B<0:return -1.
 C=np.maximum(v-tau,0.)**2
 y,z=hull_n(W,C,G,F,B)
 return first+y*F+z*B+.000005

@njit(cache=True)
def model(gg,gz,mix,a,b,s,kind,h2,n2,heights,W,G,F,first,globalhi,rlocal,ng,realG,nt=121):
 N,RG=norm0(gg,gz,s,mix,0.,0.);d0=1/(6*RG);cg=negative_bound(gg,s-a)/RG
 d=1.000001*(d0+.000001);D=1.000001*(1-d0+(1 if kind==0 else 2)*cg);Df=1.000001*(1-d0+(cg if kind==2 else 0))
 vf=(trans(gz,b-s)+mix*trans(gg,b-s)-(.75 if kind!=2 else 1)*(1+mix)/6)/N-.000001
 if kind==1: vf-=(negative_bound(gz,s-a)+mix*negative_bound(gg,s-a))/N
 n=2 if kind==2 else 1
 v2=(trans(gz,h2-s)+mix*trans(gg,h2-s)-(.75 if n2==1 else 1)*(1+mix)/6)/N-.000001 if n2 else 0.
 v=np.empty(len(heights))
 for i in range(len(v)):v[i]=(trans(gz,heights[i]-s)+mix*trans(gg,heights[i]-s)-(1+mix)/6)/N-.000001
 v[-1]=-1
 phifactor=.75 if realG else 1.
 vg=(trans(gz,globalhi-s)+mix*trans(gg,globalhi-s)-phifactor*(1+mix)/6)/N-.000001
 vr=(trans(gz,rlocal-s)+mix*trans(gg,rlocal-s)-phifactor*(1+mix)/6)/N-.000001
 fac=D/(D-.5*1.000001) if realG and ng else 1.
 end=math.sqrt(d);mx=-1.;mt=0
 for j in range(nt):
  tau=end*j/(nt-1);z=ev(tau,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vg,vr,ng,fac)
  if z>mx:mx=z;mt=j
 lo=end*max(0,mt-1)/(nt-1);hi=end*min(nt-1,mt+1)/(nt-1);ra=(math.sqrt(5)-1)/2
 x1=hi-ra*(hi-lo);x2=lo+ra*(hi-lo)
 f1=ev(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vg,vr,ng,fac);f2=ev(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vg,vr,ng,fac)
 for j in range(28):
  if f1>f2:
   hi=x2;x2=x1;f2=f1;x1=hi-ra*(hi-lo);f1=ev(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vg,vr,ng,fac)
  else:
   lo=x1;x1=x2;f1=f2;x2=lo+ra*(hi-lo);f2=ev(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first,vg,vr,ng,fac)
 return max(mx,f1,f2)


def probe(inp,L,step=.02,params=None):
 from triple_inputs import input_with_third,use_shifted
 new=use_shifted(input_with_third(inp,L),L)
 a,b=map(float,(Q(new['case']['lo']),Q(new['case']['hi'])));s0=float(Q(new['shift']));p=float(Q(new['gap']['lo'])) if new.get('gap') else float(Q(new['case']['lp']))
 r=float(Q(new['ordinary_lower']));sec=new['second'];h2=float(Q(sec['hi'])) if sec else 0.;n2=sec['n'] if sec else 0;kind={'rr':0,'rc':1,'complex':2}[new['case']['kind']]
 e=new['extension'];params=params or [float(Q(e['gG'])),float(Q(e['gZ'])),float(Q(e['mix'])) if e['variant']=='mixture' else 0.]
 heights=np.array([float(Q(row[1])) if row[1]!='infinity' else 30. for row in new['rows']]);W=np.array([row[2]/S for row in new['rows']]);G=np.array([row[3]/S for row in new['rows']]);F=new['far_budget']/S;first=new['first']/S
 tailargs=(kind,h2,n2,heights,W,G,F,first)
 baseline=model(*params,a,b,s0,*tailargs,r,r,0,False)
 vals=[]
 # Source-global lower can exceed current s because p is the limiting factor.
 source_lo=max(float(Q(new['case']['source_l2'])),a)
 if source_lo<r:
  nintervals=max(1,math.ceil((r-source_lo)/step));grid=np.linspace(source_lo,r,nintervals+1)
  for aa,bb in zip(grid,grid[1:]):
   for ng,real in ((1,True),(2,False)):
    s=min(1.9,p,aa);v=model(*params,a,b,s,*tailargs,bb,r,ng,real)
    vals.append(dict(global_lo=float(aa),global_hi=float(bb),ng=ng,value=v,shift=s))
 s=min(1.9,p,max(source_lo,r));v=model(*params,a,b,s,*tailargs,r,r,0,False);vals.append(dict(global_lo=max(source_lo,r),global_hi='infinity',ng=0,value=v,shift=s))
 return dict(L=L,baseline=float(baseline),improved=max(x['value']for x in vals),cases=vals,params=params,scope='floating exploration; finite global-lambda2 intervals but not interval-enclosed tau maximum')

if __name__=='__main__':
 data=load_data('selected_inputs.json');out=[]
 for id in ['2063','428','2421','1850']:
  if not data[id]:continue
  inp=data[id][0][1]
  for L in ['4.33','4.25','4.00']:
   ans=probe(inp,L,.02);ans['id']=id;out.append(ans);print(json.dumps({k:v for k,v in ans.items()if k!='cases'}),flush=True)
 (PACKAGE/'results/hidden_global_height_probe.json').write_text(json.dumps(out,indent=2))
