"""Outward numerical inputs for detector mixtures and correlated first pairs.
The explicit-formula arguments are mathematical premises, not formalized here.
No optimizer is imported. Nonfinite interval values are rejected.
"""
from published_single_inputs import *
from math import factorial
from pair_bounds import real_tail
from base_enclosures import ceil_fraction


def _finite(a):
 assert np.all(np.isfinite(a[0])) and np.all(np.isfinite(a[1]))
 assert np.all(np.asarray(a[0])<=np.asarray(a[1]))
 return a

@lru_cache(None)
def vector_transform(gamma,sigma,Y=30,den=200):
 """Enclose Re F(sigma+i*j/den), j=0..Y*den."""
 g=Q(gamma);sig=Q(sigma);jj=np.arange(Y*den+1)
 ti=vi.rational(jj,den);re=fq(sig);z=(re,ti)
 small=(float(sig)**2+(jj/den)**2)<=.249
 outlo=np.empty(len(jj));outhi=np.empty(len(jj))
 for mask,is_small in [(small,True),(~small,False)]:
  if not np.any(mask):continue
  zz=(re,(ti[0][mask],ti[1][mask]))
  if is_small:
   assert sig*sig+Q(int(jj[mask][-1]),den)**2<=Q(1,4)
   ww=vi.cscale(zz,float(-2*g)) if (2*g).denominator==1 else vi.cmul(zz,vi.fromreal(fq(-2*g)))
   def ck(k):return fq(Q(30,(k+1)*(k+3)*(k+4)*(k+6)*factorial(k)))
   acc=vi.fromreal(ck(41))
   for k in range(40,-1,-1):acc=vi.cadd(vi.cmul(acc,ww),vi.fromreal(ck(k)))
   real=vi.mul(fq(Q(16,15)*g**5*2*g),acc[0])
   a=I(g);ff=I(Q(16,15)*g**5*2*g*Q(5,12))
   er=upper(ff*iv.exp(a)*a**42/factorial(42),10**40)
   ee=float(np.nextafter(float(Q(er,10**40)),np.inf));real=vi.add(real,(-ee,ee))
  else:
   e=vi.cexp(vi.cmul(zz,vi.fromreal(fq(-2*g))))
   one=vi.fromreal(vi.exact(1));z2=vi.cmul(zz,zz);z3=vi.cmul(z2,zz);z4=vi.cmul(z2,z2);z6=vi.cmul(z3,z3)
   t1=vi.cdiv(vi.fromreal(fq(Q(16,15)*g**5)),zz)
   t2=vi.cdiv(vi.fromreal(fq(Q(8,3)*g**3)),z3)
   t3=vi.cdiv(vi.cmul(vi.fromreal(fq(4*g*g)),vi.cadd(one,e)),z4)
   num=vi.cadd(vi.csub(e,one),vi.cmul(vi.fromreal(fq(2*g)),vi.cmul(zz,e)))
   t4=vi.cdiv(vi.cscale(num,4),z6)
   real=vi.cadd(vi.csub(t1,t2),vi.cadd(t3,t4))[0]
  _finite(real);outlo[mask]=real[0];outhi[mask]=real[1]
 return _finite((outlo,outhi))

@lru_cache(None)
def correlation_bound(gG,gZ,s,a,b,p,h,zeta=Q(3),den=200,Y=30):
 gG,gZ,s,a,b,p,h,zeta=map(Q,(gG,gZ,s,a,b,p,h,zeta))
 assert a<=b and p<=h and zeta>0
 G=test(gG);Z=test(gZ);RG=G.F(-s);N=norm(gG,gZ,s)
 gri=vi.bounds_iv(1/RG);fac=vi.bounds_iv(I(zeta)/(2*N))
 P=vi.mul(vector_transform(gG,-s,Y,den),gri)
 fx={q:vector_transform(gZ,q-s,Y,den) for q in set([a,b,p,h])}
 max_upper=-np.inf
 for aa in (a,b):
  for pp in (p,h):
   vals=_finite(vi.sub(P,vi.mul(fac,vi.add(fx[aa],fx[pp]))))
   max_upper=max(max_upper,float(np.max(vals[1])))
 # Sequential interpolation: no mixed derivative assumption is made.
 zM1=Z.exponential_moment(2,max(Q(0),s-a));zM2=Z.exponential_moment(2,max(Q(0),s-p))
 M2=G.exponential_moment(2,max(Q(0),s))/RG+I(zeta)*(zM1+zM2)/(2*N)
 height_err=upper(M2*I(Q(1,8*den*den)))
 param_err=upper(I(zeta)/(2*N)*(I((b-a)**2)*zM1/8+I((h-p)**2)*zM2/8))
 tail=real_tail(G,-s,Q(Y))/RG
 # Uniform tail over real-part intervals.
 def tailbox(f,lo,hi):
  yi=I(Y);g=f.gi;ee=iv.exp(-2*g*I(lo));abs_sig=max(abs(lo),abs(hi))
  return f.f0*I(abs_sig)/yi**2+8*g**3/(3*yi**3)+4*g*g*(1+ee)/yi**4+4*(1+ee)/yi**6+8*g*ee/yi**5
 tail+=I(zeta)/(2*N)*(tailbox(Z,a-s,b-s)+tailbox(Z,p-s,h-s))
 tail_int=upper(tail)
 sample_int=ceil_fraction(Q.from_float(max_upper)*S)
 bound=max(0,sample_int+height_err+param_err,tail_int)
 return bound,dict(bound=bound,sample_upper=sample_int,height_error=height_err,parameter_error=param_err,tail=tail_int,height_end=Y,height_den=den,corner_evaluations=4*(Y*den+1))

@lru_cache(None)
def paired_first(gG,gZ,s,a,b,p,h,kind,zeta=Q(3)):
 gG,gZ,s,a,b,p,h,zeta=map(Q,(gG,gZ,s,a,b,p,h,zeta));assert kind in ('complex','rc')
 G,Z=test(gG),test(gZ);RG=G.F(-s);N=norm(gG,gZ,s)
 CG,_=cb(gG,s-a);CZ,_=cb(gZ,s-a)
 graph=I(Q(CG,S))/RG if kind=='complex' else I(0)
 eraw=I(Q(CZ,S))/N/(2 if kind=='complex' else 1)
 e_int=upper(eraw);ee=I(Q(e_int,S))
 B,pf=correlation_bound(gG,gZ,s,a,b,p,h,zeta)
 d0=G.f0/(6*RG)
 D=(1+I(ETA))*((1+I(Q(B,S)))/2-d0+graph-I(zeta)*ee/2)
 mf=(Z.F(b-s)+Z.F(h-s))/(2*N)-(I(Q(3,4)) if kind=='rc' else 1)*Z.f0/(6*N)-I(ETA)-ee
 di,fi=upper(D),lower(mf);kap=(1+ETA)*zeta/2
 assert di>0 and 2*Q(di,S)>=kap*max(Q(fi,S),Q(0)),('pair comparison',di,fi)
 pf={**pf,'e':e_int,'diagonal':di,'feature':fi,'monotonicity_margin':str(2*Q(di,S)-kap*max(Q(fi,S),Q(0)))}
 return fi,di,pf

@lru_cache(None)
def mixnorm(gG,gZ,s,t):
 gG,gZ,s,t=map(Q,(gG,gZ,s,t));assert t>=0
 G,Z=test(gG),test(gZ);RG=G.F(-s);lo,hi,sc=norm_bounds(gG,gZ,s)
 rb=iv.mpf([I(Q(lo,sc)).a,I(Q(hi,sc)).b]);epsilon=t*(gZ/gG)**5
 return iv.sqrt(RG*(rb+2*I(epsilon)*Z.F(-s)+I(epsilon)**2*RG))

@lru_cache(None)
def mixfeature(gG,gZ,s,t,l,real=False,exception=False,a=None):
 gG,gZ,s,t,l=map(Q,(gG,gZ,s,t,l));G,Z=test(gG),test(gZ);epsilon=t*(gZ/gG)**5;N=mixnorm(gG,gZ,s,t)
 val=Z.F(l-s)+I(epsilon)*G.F(l-s)-(I(Q(3,4)) if real else 1)*(Z.f0+I(epsilon)*G.f0)/6
 if exception:
  cz,_=cb(gZ,s-Q(a));cg,_=cb(gG,s-Q(a));val-=I(Q(cz,S)+epsilon*Q(cg,S))
 return lower(val/N-I(ETA))

@lru_cache(None)
def mixrows(r,gG,gZ,s,t,L,den):
 rows0=single_rows(r,gG,gZ,s,L,den)
 return [row[:4]+[mixfeature(gG,gZ,s,t,Q(row[1]))] for row in rows0[:-1]]+[rows0[-1]]

def make_extended(spec,L,par,den=200):
 gg,gz=Q(par['gg']),Q(par['gz']);height=spec['height'];inp=make_single(spec,L,gg,gz,den,height)
 variant=par['method'];inp['extension']=dict(variant=variant,gG=str(gg),gZ=str(gz),mix=str(Q(par.get('mix','0'))),zeta=str(Q(par.get('zeta','3'))))
 c=spec['case'];a,b=Q(c['lo']),Q(c['hi']);s=Q(inp['shift'])
 if variant=='pair':
  if c['kind']=='rc':pa,ph=a,b
  else:
   assert spec.get('gap') and spec['gap']['hi']!='infinity'
   pa,ph=Q(spec['gap']['lo']),Q(spec['gap']['hi'])
  fi,di,pf=paired_first(gg,gz,s,a,b,pa,ph,c['kind'],Q(inp['extension']['zeta']))
  inp['v_first']=fi;inp['Df']=di;inp['pair_proof']=pf
 elif variant=='mixture':
  tt=Q(inp['extension']['mix'])
  inp['v_first']=mixfeature(gg,gz,s,tt,b,c['kind']!='complex',c['kind']=='rc',a)
  if inp['second']:
   inp['second']['v']=mixfeature(gg,gz,s,tt,Q(inp['second']['hi']),inp['second']['n']==1)
  inp['rows']=mixrows(inp['ordinary_lower'],gg,gz,s,tt,L,den)
  inp['mixture_norm']=[lower(mixnorm(gg,gz,s,tt),10**22),upper(mixnorm(gg,gz,s,tt),10**22),10**22]
 else:assert variant=='single'
 return inp

def positivity_proof(spec,g):
 assert spec['case']['kind']=='rr' and spec['second'] and spec['second']['n']==1
 aa=Q(spec['case']['lo']);bb=Q(spec['case']['hi']);hh=Q(spec['second']['hi']);g=Q(g)
 f=test(g);raw=f.F(bb-aa)+f.F(hh-aa)-f.F(-aa)-I(Q(3,8))*f.f0
 margin=lower(raw/f.f0)
 assert margin>S//50000
 return dict(g=str(g),shift=str(aa),normalized_margin_lower=margin,scope='two distinct real characters; first zero real; source explicit-formula errors chosen below margin')
