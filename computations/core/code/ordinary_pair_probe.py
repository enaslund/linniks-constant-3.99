"""Exploratory joint ordinary-character gap / NEAR-pair / prime-envelope model.
Uses no two-zero FAR detector. Floating samples are not certificates.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
from optimize_near import *
from scipy.optimize import minimize_scalar
from config_v4 import T,BETA

@njit(cache=True)
def expint(r,lo,hi):
 if abs(r)<1e-10:return hi-lo
 return math.exp(-r*lo)*(-math.expm1(-r*(hi-lo)))/r

@njit(cache=True)
def env_values(l,p,A,bet,kt):
 H0=(kt*np.sum(bet))**2;tail=0.;C=0.;BB=0.;lam=0.;cros=0.
 for j in range(len(bet)-1,-1,-1):
  b=bet[j];lo=j*kt;hi=(j+1)*kt
  C+=2*b*(b/l*expint(2*p,lo,hi)+(tail-b/l*math.exp(-l*hi))*expint(2*p-l,lo,hi))
  tail+=b*expint(l,lo,hi)
  # B(p) uses inner unweighted tail at t; integrate (hi-t) exp(-2p t).
  e=math.exp(-2*p*lo);a=-math.expm1(-2*p*kt)/(2*p);moment=(1-(1+2*p*kt)*math.exp(-2*p*kt))/(4*p*p)
  BB+=2*b*(b*(kt*a-moment)+cros*a)*e+b*b*expint(2*p,lo,hi)/3
  cros+=b*kt
 h=tail*tail/H0;B=BB/H0;C/=H0
 return math.exp(-A*l)*h+math.exp(-A*p)*(B-C)

@njit(cache=True)
def ordinary_max(v,factor,W,G,d,D,Df,vf,n,v2,n2,F,first,nt=121):
 end=math.sqrt(d);best=-1.;besttau=0.;besty=0.;bestz=0.
 for j in range(nt):
  t=end*j/(nt-1);B=D*(1-t*t/d)-n*D/Df*max(vf-t,0)**2-n2*max(v2-t,0)**2
  if B<0:continue
  C=factor*np.maximum(v-t,0)**2;y,z=hull_n(W,C,G,F,B);val=first+y*F+z*B+.000005
  if val>best:best=val;besttau=t;besty=y;bestz=z
 lo=max(0.,besttau-end/(nt-1));hi=min(end,besttau+end/(nt-1));ra=(math.sqrt(5)-1)/2
 for _ in range(26):
  t1=hi-ra*(hi-lo);t2=lo+ra*(hi-lo)
  B1=D*(1-t1*t1/d)-n*D/Df*max(vf-t1,0)**2-n2*max(v2-t1,0)**2
  B2=D*(1-t2*t2/d)-n*D/Df*max(vf-t2,0)**2-n2*max(v2-t2,0)**2
  val1=-1.;val2=-1.
  if B1>=0:
   C1=factor*np.maximum(v-t1,0)**2;y1,z1=hull_n(W,C1,G,F,B1);val1=first+y1*F+z1*B1+.000005
   if val1>best:best=val1;besttau=t1;besty=y1;bestz=z1
  if B2>=0:
   C2=factor*np.maximum(v-t2,0)**2;y2,z2=hull_n(W,C2,G,F,B2);val2=first+y2*F+z2*B2+.000005
   if val2>best:best=val2;besttau=t2;besty=y2;bestz=z2
  if val1>val2:hi=t2
  else:lo=t1
 return best,besttau,besty,bestz

@lru_cache(None)
def fcomplex_grid(ga,lo,hi,dy=.05,Y=35):
 # Exact smooth normalized test evaluated by Gauss reference quadrature.
 gg=float(ga);t=2*gg*XN;cos=np.cos(np.outer(t,np.arange(0,Y+dy/2,dy)))
 sig=np.array(list(lo)) # pass tuple of real parts
 weights=2*gg*XW*np.array([shape(x) for x in XN])
 return (np.exp(-np.outer(sig,t))*weights)@cos

def pair_model(inp,L='4.25',gapstep=.05,cut=.3,zeta=3.,lamden=100,shifted=True):
 inp=input_with_third(inp,L);inp=use_shifted(inp,L) if shifted else inp
 e=inp['extension'];gg,gz=map(float,(Q(e['gG']),Q(e['gZ'])));s=float(Q(inp['shift']));mix=float(Q(e['mix'])) if e['variant']=='mixture' else 0.
 N,RG=norm0(gg,gz,s,mix,0.,0.);d0=1/(6*RG);D=inp['D']/S;d=inp['d']/S;graph=D/1.000001-1+d0
 r=max(Q(inp['ordinary_lower']),Q(inp['third_lower']) if inp['second'] else Q(0))
 pts=[r]+[Q(j,lamden) for j in range(int(r*lamden)+1,3*lamden+1)];pts=[float(x) for x in pts]
 deltas=np.arange(0,.5000001,gapstep);H=np.arange(0,35.00001,.05)
 realparts=sorted(set([round(x-s+u,10) for x in pts for u in deltas]))
 FC=fcomplex_grid(gz,tuple(realparts),0)+mix*fcomplex_grid(gg,tuple(realparts),0)
 indx={v:j for j,v in enumerate(realparts)};FG=fcomplex_grid(gg,(-s,),0)[0]/RG
 vg=[];fg=[];WG=[];GG=[];labels=[];bet=np.array([float(b) for b in BETA]);kt=float(T)/len(bet);A=float(Q(L)-2*T);ww=wgt(L)
 mints=1e3
 for l,h in zip(pts,pts[1:]):
  wi=lower(ww.w(Q(str(h))))/S
  for u,v in zip(deltas,deltas[1:]):
   # Each box chosen left objective and smaller right-endpoint detector values.
   vv=(trans(gz,h-s)+mix*trans(gg,h-s)-(1+mix)/6)/N-.000001
   diag=D
   if u<cut:
    maxB=0.
    for aa in (l,h):
     for bb in (u,v):
      P=FC[indx[round(aa-s,10)]];Q2=FC[indx[round(aa-s+bb,10)]]
      maxB=max(maxB,np.max(FG-zeta*(P+Q2)/(2*N)))
    # Small exploratory buffer, NOT a proved cell enclosure.
    maxB+=.001
    diag=1.000001*((1+maxB)/2-d0+graph)
    m=(trans(gz,h-s)+mix*trans(gg,h-s)+trans(gz,h+v-s)+mix*trans(gg,h+v-s))/(2*N)-(1+mix)/(6*N)-.000001
    if diag>0 and 2*diag>=1.000001*zeta/2*max(m,0):vv=m
    else:diag=D
   vg.append(vv);fg.append(D/diag);WG.append(wi);GG.append(env_values(l,l+u,A,bet,kt));labels.append([l,h,u,v,diag])
  vg.append((trans(gz,h-s)+mix*trans(gg,h-s)-(1+mix)/6)/N-.000001);fg.append(1.);WG.append(wi);GG.append(env_values(l,l+.5,A,bet,kt));labels.append([l,h,.5,'infinity',D])
 vg.append(-1.);fg.append(1.);WG.append(1.);GG.append(upper(ww.G(Q(3))*ww.winv(Q(3)))/S);labels.append([3,'infinity',0,'infinity',D])
 sec=inp['second'];result=ordinary_max(np.array(vg),np.array(fg),np.array(WG),np.array(GG),d,D,inp['Df']/S,inp['v_first']/S,inp['n'],sec['v']/S if sec else 0.,sec['n'] if sec else 0,inp['far_budget']/S,inp['first']/S)
 return dict(value=result,columns=len(vg),zeta=zeta,cut=cut,gapstep=gapstep,model='exploratory sampled near-pair coupling; NOT certified',first=inp['first']/S)

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.25');ap.add_argument('--ids',default='428,1301,2421');ap.add_argument('--cut',type=float,default=.3);ap.add_argument('--zeta',type=float,default=3.);ap.add_argument('--step',type=float,default=.05);a=ap.parse_args();ids=set(map(int,a.ids.split(',')));res=[]
 with gzip.open(ROOT/'results/certificate_4.33.jsonl.gz','rt') as f:
  for j,line in enumerate(f):
   if j not in ids:continue
   rec=expand_root(json.loads(line));ls=list(leaves(rec['inside']));path,inp=ls[-1] if j==1301 else ls[0]
   ans=pair_model(inp,a.L,a.step,a.cut,a.zeta);r=dict(id=j,path=path,L=a.L,result=ans);res.append(r);print(json.dumps(r),flush=True)
 (ROOT/'results'/f'ordinary_pair_{a.L}_{a.cut}_{a.zeta}.json').write_text(json.dumps(res,indent=2))
