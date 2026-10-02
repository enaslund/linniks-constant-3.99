"""Outward elementary inputs for the two-test-function endgame.
No optimizer in this module. Analytic extensions are not formalized here.
"""
import sys,json,math
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
BASE=Path(__file__).resolve().parents[1]
OLD=BASE/'code'
from enclosures import I,iv,upper,lower,S,RigorousWeights,RigorousTest
from config_v4 import ETA,FINAL,TAU_SCALE,DUAL_SCALE
import vector_intervals as vi
iv.dps=50

fq=lambda q:vi.rational(Q(q).numerator,Q(q).denominator)
def vsum(a):
 lo,hi=np.asarray(a[0]),np.asarray(a[1]);assert len(lo)==len(hi)
 while len(lo)>1:
  if len(lo)%2:lo=np.r_[lo,0.];hi=np.r_[hi,0.]
  lo,hi=vi.add((lo[::2],hi[::2]),(lo[1::2],hi[1::2]))
 return float(lo[0]),float(hi[0])

def f_poly(g,t,order=0):
 uu=vi.div(t,fq(2*g));u2=vi.sq(uu);u3=vi.mul(u2,uu)
 f0=fq(Q(16,15)*g**5)
 if order==0:
  om=vi.sub(vi.exact(1),uu)
  return vi.mul(f0,vi.mul(vi.mul(vi.sq(om),om),vi.add(vi.add(vi.exact(1),vi.scale(uu,3)),u2)))
 if order==1:
  pol=vi.sub(vi.sub(vi.scale(u2,15),vi.scale(vi.sq(u2),5)),vi.scale(uu,10))
  return vi.mul(vi.div(f0,fq(2*g)),pol)
 pol=vi.scale(vi.sub(vi.sub(vi.scale(uu,3),vi.scale(u3,2)),vi.exact(1)),10)
 return vi.mul(vi.div(f0,fq(4*g*g)),pol)

@lru_cache(None)
def norm_bounds(gG,gZ,s,N=1024):
 gG,gZ,s=map(Q,(gG,gZ,s));assert gG>gZ>0 and N>=16
 jj=np.arange(N);left=vi.mul(fq(2*gZ),vi.rational(jj,N));right=vi.mul(fq(2*gZ),vi.rational(jj+1,N))
 ti=(left[0],right[1]);mid=vi.mul(fq(2*gZ),vi.rational(2*jj+1,2*N));h=fq(2*gZ/N)
 f=f_poly(gZ,ti);fp=f_poly(gZ,ti,1);fpp=f_poly(gZ,ti,2)
 q=f_poly(gG,ti);qp=f_poly(gG,ti,1);qpp=f_poly(gG,ti,2)
 assert np.all(q[0]>0),'denominator positivity'
 P=vi.sq(f);Pp=vi.scale(vi.mul(f,fp),2);Ppp=vi.scale(vi.add(vi.sq(fp),vi.mul(f,fpp)),2)
 # (P exp(s*t)/q)'' = exp(s*t) times the following expression.
 one=vi.div(vi.add(vi.add(Ppp,vi.mul(fq(2*s),Pp)),vi.mul(fq(s*s),P)),q)
 two=vi.div(vi.mul(vi.add(vi.scale(Pp,2),vi.mul(fq(2*s),P)),qp),vi.sq(q))
 three=vi.div(vi.mul(P,qpp),vi.sq(q))
 four=vi.div(vi.scale(vi.mul(P,vi.sq(qp)),2),vi.mul(vi.sq(q),q))
 d2=vi.mul(vi.exp(vi.mul(fq(s),ti)),vi.add(vi.sub(vi.sub(one,two),three),four))
 bound=np.maximum(abs(d2[0]),abs(d2[1]));assert np.all(np.isfinite(bound))
 fm=f_poly(gZ,mid);qm=f_poly(gG,mid)
 val=vi.div(vi.mul(vi.sq(fm),vi.exp(vi.mul(fq(s),mid))),qm)
 err=vi.mul(vi.mul(vi.exact(bound),vi.sq(h)),fq(Q(1,24)))
 integrals=vi.mul(h,vi.add(val,(-err[1],err[1])))
 lo,hi=vsum(integrals);assert math.isfinite(lo) and 0<lo<=hi
 scale=10**22
 l=(Q.from_float(lo)*scale).__floor__();u=-((-Q.from_float(hi)*scale).__floor__())
 return l,u,scale

@lru_cache(None)
def test(g):return RigorousTest(Q(g))
@lru_cache(None)
def cb(g,delta):return test(g).C_upper(max(Q(0),Q(delta)),Q(1,10**8))
@lru_cache(None)
def wgt(L):return RigorousWeights(L)
@lru_cache(None)
def norm(gG,gZ,s):
 lo,hi,sc=norm_bounds(gG,gZ,s)
 rb=iv.mpf([I(Q(lo,sc)).a,I(Q(hi,sc)).b]);rg=test(gG).F(-Q(s))
 return iv.sqrt(rb*rg)

@lru_cache(None)
def feat(gG,gZ,s,l,real=False,exception=False,a=None):
 gG,gZ,s,l=map(Q,(gG,gZ,s,l));fz=test(gZ);N=norm(gG,gZ,s)
 val=fz.F(l-s)-(I(Q(3,4)) if real else 1)*fz.f0/6
 if exception:
  C,_=cb(gZ,s-Q(a));val-=I(Q(C,S))
 return lower(val/N-I(ETA))

@lru_cache(None)
def constants(a,gG,gZ,s,kind):
 a,gG,gZ,s=map(Q,(a,gG,gZ,s));fg=test(gG);RG=fg.F(-s);d0=fg.f0/(6*RG)
 C,proof=cb(gG,s-a);cg=I(Q(C,S))/RG
 return (upper((1+I(ETA))*(d0+I(ETA))),
         upper((1+I(ETA))*(1-d0+(1 if kind=='rr' else 2)*cg)),
         upper((1+I(ETA))*(1-d0+(cg if kind=='complex' else 0))),proof)

if __name__=='__main__':
 import mpmath as mp
 mp.mp.dps=65
 for gg,gz,s in [('1.6','1.18','.702'),('1.36','1.13','.704'),('1.56','1.18','.702'),('2','1.4','1.9')]:
  lo,hi,sc=norm_bounds(Q(gg),Q(gz),Q(s));G,Z,ss=map(mp.mpf,(gg,gz,s))
  def ff(g,t):u=t/(2*g);return 16*g**5/15*(1-u)**3*(1+3*u+u*u)
  ref=mp.quad(lambda t:ff(Z,t)**2/ff(G,t)*mp.exp(ss*t),[0,2*Z])
  assert mp.mpf(lo)/sc<=ref<=mp.mpf(hi)/sc
  print(gg,gz,s,'reference',ref,'bounds',lo/sc,hi/sc,'width',(hi-lo)/sc)
