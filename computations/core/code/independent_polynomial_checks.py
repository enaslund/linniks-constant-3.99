"""Independent diagnostics: direct quadrature and finite-group alias algebra.
No imported transform implementation is used for the reference values.
This is a diagnostic, not a second exhaustive interval proof.
"""
import json,sys,math
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
import mpmath as mp
ROOT=Path(__file__).resolve().parents[1];mp.mp.dps=65

def mm(q):q=Q(q);return mp.mpf(q.numerator)/q.denominator

def F(g,z):
 g=mm(g)
 def fn(t):
  u=t/(2*g);return (16*g**5/15)*(1-u)**3*(1+3*u+u*u)*mp.exp(-z*t)
 return mp.quad(fn,[0,g,2*g])

def aliases():
 checked=hasalias=0
 for m in range(2,10):
  for n in range(1,9):
   chars=list(product(range(m),range(n)));zero=(0,0)
   def add(x,y):return ((x[0]+y[0])%m,(x[1]+y[1])%n)
   def mul(k,x):return (k*x[0]%m,k*x[1]%n)
   for x in chars:
    if mul(2,x)==zero:continue
    for y in chars:
     if y in (zero,x,mul(-1,x)):continue
     real=mul(2,y)==zero
     S=list(product(range(-2,3),range(-1,2) if real else range(-2,3)))
     principal=[w for w in S if w!=(0,0) and add(mul(w[0],x),mul(w[1],y))==zero]
     used=set()
     for w in principal:
      assert max(map(abs,w))==2 and w[0]*w[1]!=0
      i=0 if abs(w[0])==2 else 1;sg=1 if w[i]>0 else -1
      v=list(w);v[i]-=sg;v=tuple(v)
      assert v not in used and v not in ((1,0),(-1,0),(0,1),(0,-1));used.add(v)
      assert add(mul(v[0],x),mul(v[1],y))==mul(-sg,(x,y)[i])!=zero
      # v - (-sign)*unit_i == principal index w: exact frequency alignment.
      freq=list(v);freq[i]+=sg;assert tuple(freq)==w
     checked+=1;hasalias+=bool(principal)
 return dict(character_pairs_checked=checked,pairs_with_principal_aliases=hasalias,status='PASS: exact finite-group matching diagnostics')

def refs():
 tab=json.loads((ROOT/'results/polynomial_table.json').read_text());ans=[]
 # Include both the displayed rows and a spread of regenerated table rows.
 chosen=tab['rows'][::7]
 for row in chosen:
  p=row['proof'];a,b,g,t=map(mm,(p['a'],p['b'],p['gamma'],p['t']));c1=2*t/(t*t+mp.mpf('.5'));c2=mp.mpf('.5')/(t*t+mp.mpf('.5'));f0=16*g**5/15
  if row['type']=='second':
   h=mm(p['h']);exact=(c1*(F(p['gamma'],b-a)+F(p['gamma'],h-a))-F(p['gamma'],-a))/f0-((1+c1+c2)**2-1)/6
   assert exact>=mp.mpf(p['generic_normalized_margin'])/10**16
   B=p['alias']['bound'];fac=4*t
   for lam in (a,(a+h)/2,h):
    for y in (mp.mpf('0'),mp.mpf('.73'),mp.mpf('3.14'),mp.mpf('11.07'),mp.mpf('40.25')):
     v=mp.re(F(p['gamma'],-a+1j*y)-fac*F(p['gamma'],lam-a+1j*y));assert v<=mp.mpf(B)/10**16
  else:
   h=mm(p['new_lower']);old=mm(p['old_lower']);P1=c1*c1/2;P2=c2*c2/2;Q1=c1*(1+c2/2);Q2=c1*c2/2
   mass=(1+c1+c2)**2-1-P1-P2
   for x0 in (mp.mpf('0'),(b-a)/2,b-a):
    for y in (mp.mpf('0'),mp.mpf('.47'),mp.mpf('2.01'),mp.mpf('7.13'),mp.mpf('35.6')):
     y0=(old+h)/2-a
     v=mp.re(P1*F(p['gamma'],-a+1j*y)+P2*F(p['gamma'],-a+2j*y)-Q1*(F(p['gamma'],x0+1j*y)+F(p['gamma'],y0+1j*y))-Q2*(F(p['gamma'],x0+2j*y)+F(p['gamma'],y0+2j*y)))
     assert v<=mp.mpf(p['correlation']['bound'])/10**16
   exact=(c1*(F(p['gamma'],b-a)+F(p['gamma'],h-a))-F(p['gamma'],-a)-mp.mpf(p['correlation']['bound'])/10**16)/f0-mass/6
   assert exact>=mp.mpf(p['normalized_margin'])/10**16
  ans.append(dict(row_id=row['id'],type=row['type'],reference_margin=mp.nstr(exact,45)))
 return ans

if __name__=='__main__':
 out=dict(status='PASS: independent direct-quadrature and exact finite-group diagnostics',group=aliases(),reference_rows=refs(),precision=65,scope='Diagnostic checks only, not a second complete interval proof or formalization of the analytic source lemmas.')
 (ROOT/'results/independent_polynomial_checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
