"""Floating search, never used as a certificate."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from triple_probe import *
from refine_probe import spec_from_input,par_from_input,refined_second_input
from scipy.optimize import minimize, differential_evolution
from numpy.polynomial.legendre import leggauss
from numba import njit
XN,XW=leggauss(64);XN=(XN+1)/2;XW=XW/2

@njit(cache=True)
def shape(u):
 if u<0 or u>1:return 0.
 return (1-u)**3*(1+3*u+u*u)

@njit(cache=True)
def trans(ga,z,damp=0.):
 s=0.
 for j in range(len(XN)):
  t=2*ga*XN[j];s+=XW[j]*shape(XN[j])*math.exp(-(z+damp)*t)
 return 2*ga*s

@njit(cache=True)
def negative_bound(ga,delta,damp=0.):
 if delta<=damp:return 0.
 # Approximate supremum used ONLY to propose parameters; strict routines accept later.
 mx=0.
 for i in range(1,501):
  y=i*.05;v=0.
  for j in range(len(XN)):
   t=2*ga*XN[j];v+=XW[j]*shape(XN[j])*math.exp((delta-damp)*t)*math.cos(y*t)
  mx=max(mx,-2*ga*v)
 return mx

@njit(cache=True)
def norm0(gg,gz,s,mix,dg,dz):
 # Integrate fz^2/g accurately on the shorter support, plus cross and g terms.
 R=trans(gg,-s,dg);rb=0.
 for j in range(len(XN)):
  t=2*gz*XN[j];fg=shape(t/(2*gg))*math.exp(-dg*t);fz=shape(XN[j])*math.exp(-dz*t)
  rb+=XW[j]*fz*fz/fg*math.exp(s*t)
 rb*=2*gz
 rb+=2*mix*trans(gz,-s,dz)+mix*mix*R
 return math.sqrt(R*rb),R

@njit(cache=True)
def hull_n(W,C,G,F,B):
 xx=C/W;yy=G/W
 idx=np.argsort(xx);hx=np.empty(len(xx));hy=np.empty(len(xx));nn=0
 for j in idx:
  x,y=xx[j],yy[j]
  if nn and x==hx[nn-1]:
   if y<=hy[nn-1]:continue
   nn-=1
  while nn>=2:
   x0,y0=hx[nn-2],hy[nn-2];x1,y1=hx[nn-1],hy[nn-1]
   if (y1-y0)*(x-x1)<=(y-y1)*(x1-x0):nn-=1
   else:break
  hx[nn]=x;hy[nn]=y;nn+=1
 peak=0
 for j in range(nn):
  if hy[j]>hy[peak]:peak=j
 r=B/F
 if r>=hx[peak]:return hy[peak],0.
 for j in range(peak):
  if hx[j]<=r<=hx[j+1]:
   z=(hy[j+1]-hy[j])/(hx[j+1]-hx[j]);return max(0.,hy[j]-z*hx[j]),max(0.,z)
 return np.max(yy),0.

@njit(cache=True)
def profile_val(tau,d,D,Df,vf,n,v2,n2,v,W,G,F,first):
 B=D*(1-tau*tau/d)-n*D/Df*max(vf-tau,0)**2-n2*max(v2-tau,0)**2
 if B<0:return -1.
 C=np.maximum(v-tau,0)**2
 y,z=hull_n(W,C,G,F,B)
 return first+y*F+z*B+.000005

@njit(cache=True)
def fast_fun(par,a,b,s,kind,h2,n2,heights,W,G,F,first,nt=61):
 gg,gz,mix,dg,dz=par
 if gg<=gz or gz<=0 or mix<0 or dg<0 or dz<0:return 1e5+100*max(gz-gg,0)
 N,R=norm0(gg,gz,s,mix,dg,dz)
 d0=1/(6*R);c=negative_bound(gg,s-a,dg)/R
 d=1.000001*(d0+.000001);D=1.000001*(1-d0+(1 if kind==0 else 2)*c);Df=1.000001*(1-d0+(c if kind==2 else 0))
 vf=(trans(gz,b-s,dz)+mix*trans(gg,b-s,dg)-(.75 if kind!=2 else 1)*(1+mix)/6)/N-.000001
 if kind==1:vf-=(negative_bound(gz,s-a,dz)+mix*negative_bound(gg,s-a,dg))/N
 n=2 if kind==2 else 1
 v2=(trans(gz,h2-s,dz)+mix*trans(gg,h2-s,dg)-(.75 if n2==1 else 1)*(1+mix)/6)/N-.000001 if n2 else 0.
 v=np.empty(len(heights))
 for j in range(len(v)):
  v[j]=(trans(gz,heights[j]-s,dz)+mix*trans(gg,heights[j]-s,dg)-(1+mix)/6)/N-.000001
 v[-1]=-1.
 end=math.sqrt(d);mx=-1.;mt=0
 for j in range(nt):
  tau=end*j/(nt-1);z=profile_val(tau,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
  if z>mx:mx=z;mt=j
 # Local golden search; the full later acceptance covers every threshold regardless.
 lo=end*max(0,mt-1)/(nt-1);hi=end*min(nt-1,mt+1)/(nt-1)
 ra=(math.sqrt(5)-1)/2
 x1=hi-ra*(hi-lo);x2=lo+ra*(hi-lo)
 f1=profile_val(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first);f2=profile_val(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
 for it in range(26):
  if f1>f2:
   hi=x2;x2=x1;f2=f1;x1=hi-ra*(hi-lo);f1=profile_val(x1,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
  else:
   lo=x1;x1=x2;f1=f2;x2=lo+ra*(hi-lo);f2=profile_val(x2,d,D,Df,vf,n,v2,n2,v,W,G,F,first)
 return max(mx,f1,f2)

def optimize(inp,L='4.30',exponential=False,maxiter=120):
 new=use_shifted(input_with_third(inp,L),L)
 # Only use the inherited paired input as baseline. Search single/mixture alternatives.
 a,b=map(float,(Q(new['case']['lo']),Q(new['case']['hi'])));s=float(Q(new['shift']));kind={'rr':0,'rc':1,'complex':2}[new['case']['kind']]
 sec=new['second'];h2=float(Q(sec['hi'])) if sec else 0.;n2=sec['n'] if sec else 0
 hi=np.array([float(Q(r[1])) if r[1]!='infinity' else 20. for r in new['rows']]);W=np.array([r[2]/S for r in new['rows']]);G=np.array([r[3]/S for r in new['rows']]);F=new['far_budget']/S;first=new['first']/S
 args=(a,b,s,kind,h2,n2,hi,W,G,F,first)
 e=inp['extension'];ini=[float(Q(e['gG'])),float(Q(e['gZ'])),float(Q(e['mix'])) if e['variant']=='mixture' else .18]
 def fun(x):return fast_fun(np.array(list(x[:3])+ (list(x[3:]) if len(x)>3 else [0.,0.])),*args)
 if exponential:ini += [.04,.04]
 bds=[(.9,2.8),(.55,1.7),(0.,1.5)]+([(0.,1.),(0.,1.)] if exponential else [])
 ref=fun(ini);op=minimize(fun,ini,method='Nelder-Mead',bounds=bds,options={'maxiter':maxiter,'xatol':1e-4,'fatol':2e-6})
 return dict(initial=ref,optimized=op.fun,parameters=op.x.tolist(),success=bool(op.success),evaluations=op.nfev)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.30');ap.add_argument('--ids',default='428,2421,1301');ap.add_argument('--exp',action='store_true');ap.add_argument('--n',type=int,default=120);a=ap.parse_args();ids=set(map(int,a.ids.split(',')));res=[]
 with gzip.open(ROOT/'results/certificate_4.33.jsonl.gz','rt') as f:
  for i,line in enumerate(f):
   if i not in ids:continue
   rec=expand_root(json.loads(line))
   ls=list(leaves(rec['inside']));path,inp=ls[-1] if i==1301 else ls[0]
   opt=optimize(inp,a.L,a.exp,a.n);r=dict(id=i,path=path,L=a.L,exponential=a.exp,case=inp['case'],second=inp['second'],result=opt);res.append(r);print(json.dumps(r),flush=True)
 (ROOT/'results'/f'opt_{a.L}_{int(a.exp)}.json').write_text(json.dumps(res,indent=2))
