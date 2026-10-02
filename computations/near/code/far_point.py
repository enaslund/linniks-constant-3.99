"""Point-mass variational far-density experiment, not a global Linnik bound."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import numpy as np, json
from scipy.optimize import minimize
from numpy.polynomial.legendre import leggauss
from pathlib import Path
X,W=leggauss(40);X=(X+1)/2;W=W/2
ALPHA=np.array([.0788827218,.0849386148,.0895629779,.0938231516,.0979710491,.1021284916,.1063732939,.1107651869,.1153565492,.1201979632])
M=10

def val(par,lam,grad=False):
 c1,c2=par[:2];alpha=par[2:]
 if c1<=0 or c2<=0:return 1e20
 u=1/3+2*c1;x=2/3+3*c1+c2;h=c2/M
 # First cell sqrt substitution, rest Gauss.
 starts=u+np.arange(M)*h
 nodes=np.concatenate([u+h*X**2]+[u+j*h+h*X for j in range(1,M)]+[u+c2+(x-u-c2)*X])
 ww=np.concatenate([2*h*X*W]+[h*W]*(M-1)+[(x-u-c2)*W])
 Q=np.minimum(np.maximum(nodes[:,None]-starts,0),h)@(alpha*alpha)
 integ=np.dot(ww,np.exp(lam*nodes)*np.sqrt(Q))
 return M*M/(c1*c2*c2)*integ**2

if __name__=='__main__':
 out=[]
 for lam in [.74,1.14,1.5,1.77,2.,2.5]:
  p=np.r_[.09035,.235968,ALPHA]
  ini=val(p,lam)
  op=minimize(lambda z:val(z,lam),p,method='SLSQP',bounds=[(.005,.5),(.015,1.)]+[(.0001,1)]*10,constraints={'type':'eq','fun':lambda z:sum(z[2:])-1},options={'maxiter':200,'ftol':1e-10})
  res=dict(lam=lam,initial=ini,optimized=float(op.fun),parameters=op.x.tolist(),success=bool(op.success));out.append(res);print(json.dumps(res),flush=True)
 Path(str(Path(__file__).resolve().parents[1]/'results/far_point.json')).write_text(json.dumps(out,indent=2))
