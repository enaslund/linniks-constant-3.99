"""Independent high-precision diagnostics plus fail-closed checker probes.
Direct-quadrature references do not substitute for outward enclosures.
"""
import os
os.environ.setdefault('OPENBLAS_NUM_THREADS','1')
import sys,json,math,gzip,copy,argparse
from pathlib import Path
from fractions import Fraction as Q
import mpmath as mp
mp.mp.dps=65
ROOT=Path(__file__).resolve().parents[1]
B=[mp.mpf(x) for x in '.02318741 .07159337 .12265085 .17627704 .23237155 .29081583 .35147264 .41418551 .47877833 .54505502 .61279917 .68177389 .75172165 .82236428 .89340300 .96451862'.split()]
T=mp.mpf('.416829');k=T/16;H0=(k*sum(B))**2

def cv(x):
 q=Q(str(x));return mp.mpf(q.numerator)/q.denominator

def psi_transform(z):
 if not z:return k*sum(B)
 return mp.fsum(B[j]*mp.quad(lambda t:mp.exp(-z*t),[j*k,(j+1)*k]) for j in range(16))

def fp(p,t):
 """Integrate over the actual overlaps of shifted step intervals."""
 if t<0 or t>=T:return mp.mpf(0)
 ans=mp.mpf(0);step=int(mp.floor(t/k))
 for i in range(16):
  for j in (i+step,i+step+1):
   if not 0<=j<16:continue
   lo=max(i*k,j*k-t,mp.mpf(0));hi=min((i+1)*k,(j+1)*k-t,T-t)
   if hi>lo:ans+=B[i]*B[j]*(mp.exp(-2*p*lo)-mp.exp(-2*p*hi))/(2*p)
 return 2*mp.exp(-p*t)*ans

def cross_direct(p,a,mu=0):
 return mp.fsum(mp.quad(lambda t:fp(p,t)*mp.exp(-(a-p+1j*mu)*t),[j*k,(j+1)*k]) for j in range(16))/H0

def F_ref(g,z):
 f0=16*g**5/15
 return mp.quad(lambda t:f0*(1-t/(2*g))**3*(1+3*t/(2*g)+(t/(2*g))**2)*mp.exp(-z*t),[0,2*g])

def leaf_records(t):
 if 'record' in t:yield t['record']
 for c in t.get('children',[]):yield from leaf_records(c)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.33');args=ap.parse_args();L=args.L;A=cv(L)-2*T
 # References are evaluated before importing any supplied scalar-enclosure routines.
 checks=[]
 for p,a in [('1.16','.695'),('.96','.685'),('1.63','.73'),('2.293','.1'),('.96','.96')]:
  checks.append(dict(p=p,a=a,cross_real=str(mp.re(cross_direct(cv(p),cv(a))))))
 phase=[]
 for p,a,mu in [('1.16','.695',3),('.96','.685',12),('1.63','.73',30),('2.293','.1',70)]:
  pp,aa=cv(p),cv(a);C0=cross_direct(pp,aa);C1=cross_direct(pp,aa,mu)
  at_zero=mp.exp(-A*aa)*abs(psi_transform(aa))**2/H0-mp.exp(-A*pp)*mp.re(C0)
  at_height=mp.exp(-A*aa)*abs(psi_transform(aa+1j*mu))**2/H0-mp.exp(-A*pp)*mp.re(C1)
  assert at_zero>=at_height
  phase.append(dict(p=p,a=a,mu=mu,difference=str(at_zero-at_height)))
 sys.path.insert(0,str(ROOT/'code'))
 from endgame import cross_envelope,lower,upper,S,third_bound
 for z in checks:
  interval=cross_envelope(z['p'],z['a'],L);lo,hi=lower(interval),upper(interval);ref=mp.mpf(z['cross_real'])
  assert mp.mpf(lo)/S<=ref<=mp.mpf(hi)/S
  z.update(enclosure_lower=lo,enclosure_upper=hi,scale=S)
 assert abs(mp.mpf(checks[-1]['cross_real'])-psi_transform(cv('.96'))**2/H0)<mp.mpf('1e-55')
 third=[]
 for a,b,h in [('.695','.6975','.896'),('.685','.6875','.72'),('.755','.7575','.89'),('.7','.7025','.745')]:
  r,proof=third_bound(a,b,'complex',h);q=[p for p in proof if p['kind']=='X_4_28']
  if q:
   f0=16*cv('1.25')**5/15;tt=cv(r);m=(F_ref(cv('1.25'),tt-cv(b))+F_ref(cv('1.25'),min(tt,cv(h))-cv(a))-F_ref(cv('1.25'),-cv(b))+F_ref(cv('1.25'),0)-mp.mpf(7)*f0/6)/f0
   assert m>=mp.mpf(q[-1]['normalized_margin_lower'])/S>mp.mpf('0.00001')
   third.append(dict(a=a,b=b,second_upper=h,third_lower=r,margin=str(m)))
 from verify_progress import scenario,task
 path=ROOT/'results'/f'certificate_{L}.jsonl.gz'
 with gzip.open(path,'rt') as f:
  from compact_records import expand_root
  root=expand_root(next(json.loads(line) for line in f if '"outside"' in line and '"record"' in line))
 rec=next(leaf_records(root['inside']));scenario(rec);negative=[]
 def reject(name,func):
  try:func()
  except (AssertionError,ValueError,TypeError,KeyError):negative.append(name);return
  raise AssertionError('corruption accepted: '+name)
 r=copy.deepcopy(rec)
 for branch in r['certificate']['branches']:
  if 'Y' in branch:branch['Y']=branch['Z']=branch['U']=0;break
 reject('zero dual coefficients',lambda:scenario(r))
 r=copy.deepcopy(rec);r['certificate']['branches'][0]['a']=1
 reject('missing threshold beginning',lambda:scenario(r))
 r=copy.deepcopy(rec);r['input']['rows'][0][2]=float('nan')
 reject('nonfinite scalar',lambda:scenario(r))
 r=copy.deepcopy(root);del r['outside']
 reject('missing outside-height alternative',lambda:task((json.dumps(r),L)))
 r=copy.deepcopy(root);rr=next(leaf_records(r['inside']));rr['input']['third_lower']='5'
 reject('forged third-family lower bound',lambda:task((json.dumps(r),L)))
 r=copy.deepcopy(root);rr=next(leaf_records(r['inside']));rr['input']['first']-=100000000000
 reject('forged first-family contribution',lambda:task((json.dumps(r),L)))
 report=dict(L=L,status='PASS: independent diagnostics and six negative tests',cross_direct_checks=checks,phase_coupling_checks=phase,source_4_28_margin_checks=third,rejected_corruptions=negative,precision_decimal_digits=65,scope='Direct quadrature is a diagnostic reference, not interval certification or independent proof of Dirichlet analytic premises.')
 (ROOT/'results'/f'independent_checks_{L}.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
if __name__=='__main__':main()
