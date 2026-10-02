"""Exploratory alternative autocorrelation shape; not a rigorous certificate."""
from optimize_near import *
from endgame import make_endgame
@njit(cache=True)
def sh(u,r):
 if u<0 or u>1:return 0.
 q0=2-4*r/3+2*r*r/5
 return (q0+(-2*r*r+4*r-2)*u+(8*r*r/3-8*r)*u*u+16*r*u**3/3-16*r*r*u**5/15)/q0
@njit(cache=True)
def tf(g,z,r):
 v=0.
 for j in range(len(XN)):v+=XW[j]*sh(XN[j],r)*math.exp(-z*2*g*XN[j])
 return 2*g*v
@njit(cache=True)
def neg(g,delta,r):
 if delta<=0:return 0.
 mx=0.
 for i in range(1,501):
  y=i*.05;v=0.
  for j in range(len(XN)):
   t=2*g*XN[j];v+=XW[j]*sh(XN[j],r)*math.exp(delta*t)*math.cos(y*t)
  mx=max(mx,-2*g*v)
 return mx
@njit(cache=True)
def ff(par,a,b,s,kind,h2,n2,heights,W,G,F,first):
 gg,gz,mix,rG,rZ=par
 if gg<=gz:return 1e5+100*(gz-gg)
 R=tf(gg,-s,rG);rb=0.
 for j in range(len(XN)):
  t=2*gz*XN[j];f=sh(XN[j],rZ);g=sh(t/(2*gg),rG)
  rb+=XW[j]*f*f/g*math.exp(s*t)
 rb*=2*gz;rb+=2*mix*tf(gz,-s,rZ)+mix*mix*R
 N=math.sqrt(R*rb);d0=1/(6*R);c=neg(gg,s-a,rG)/R;d=1.000001*(d0+.000001)
 D=1.000001*(1-d0+(1 if kind==0 else 2)*c);Df=1.000001*(1-d0+(c if kind==2 else 0));n=2 if kind==2 else 1
 vf=(tf(gz,b-s,rZ)+mix*tf(gg,b-s,rG)-(.75 if kind!=2 else 1)*(1+mix)/6)/N-.000001
 if kind==1:vf-=(neg(gz,s-a,rZ)+mix*neg(gg,s-a,rG))/N
 v2=(tf(gz,h2-s,rZ)+mix*tf(gg,h2-s,rG)-(.75 if n2==1 else 1)*(1+mix)/6)/N-.000001 if n2 else 0.
 v=np.empty(len(heights))
 for j in range(len(v)):v[j]=(tf(gz,heights[j]-s,rZ)+mix*tf(gg,heights[j]-s,rG)-(1+mix)/6)/N-.000001
 v[-1]=-1.
 end=math.sqrt(d);nt=61;mx=-1.;mt=0
 for j in range(nt):
  tau=end*j/(nt-1);z=profile_val(tau,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
  if z>mx:mx=z;mt=j
 lo=end*max(0,mt-1)/(nt-1);hi=end*min(nt-1,mt+1)/(nt-1);ra=(math.sqrt(5)-1)/2
 x1=hi-ra*(hi-lo);x2=lo+ra*(hi-lo);f1=profile_val(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first);f2=profile_val(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
 for it in range(25):
  if f1>f2:hi=x2;x2=x1;f2=f1;x1=hi-ra*(hi-lo);f1=profile_val(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
  else:lo=x1;x1=x2;f1=f2;x2=lo+ra*(hi-lo);f2=profile_val(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
 return max(mx,f1,f2)
if __name__=='__main__':
 binding=json.loads((ROOT/'results/verification_4.33.json').read_text())['binding']
 with gzip.open(ROOT/'results/certificate_4.33.jsonl.gz','rt') as f:
  rec=expand_root(next(json.loads(line) for i,line in enumerate(f) if i==binding['spec_id']))
 inp=next(inp for path,inp in leaves(rec[binding['height']]) if path==binding['path'])
 assert inp['second'] and inp['case']['kind']=='complex'
 a,b=map(float,(Q(inp['case']['lo']),Q(inp['case']['hi'])));s=float(Q(inp['shift']));sec=inp['second'];rows=inp['rows'];args=(a,b,s,2,float(Q(sec['hi'])),sec['n'],np.array([float(Q(r[1])) if r[1]!='infinity' else 20. for r in rows]),np.array([r[2]/S for r in rows]),np.array([r[3]/S for r in rows]),inp['far_budget']/S,inp['first']/S)
 ini=[1.6,1.08,.18,1.,1.];print('INITIAL',ff(np.array(ini),*args),flush=True)
 op=minimize(lambda x:ff(x,*args),[1.6,1.08,.18,.9,.9],method='Nelder-Mead',bounds=[(1,2.8),(.5,1.7),(0,1.5),(0,1),(0,1)],options={'maxiter':220,'fatol':1e-7,'xatol':1e-5})
 out=dict(initial=ff(np.array(ini),*args),value=op.fun,parameters=op.x.tolist(),success=bool(op.success),evaluations=op.nfev,scope='floating exploration only')
 print(json.dumps(out),flush=True);(ROOT/'results/shape_probe.json').write_text(json.dumps(out,indent=2))
