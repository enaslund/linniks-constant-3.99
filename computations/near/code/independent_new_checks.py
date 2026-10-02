"""Independent diagnostics. Exact rational algebra + high-precision direct integrals.
Input restoration uses shared generation and hashes; the algebra and direct
integral formulas below are independent of the interval formulas. These checks
are not a formal Dirichlet L-function proof.
"""
import itertools,json,gzip,random,math,time
from fractions import Fraction as Q
from pathlib import Path
import mpmath as mp
mp.mp.dps=65  # Set precision before constructing exact-decimal kernel constants.
ROOT=Path(__file__).resolve().parents[1]
S=10**16

def solve(A,b):
 n=len(b);m=[list(A[i])+[b[i]]for i in range(n)]
 for j in range(n):
  p=next(i for i in range(j,n)if m[i][j]);m[j],m[p]=m[p],m[j];c=m[j][j];m[j]=[x/c for x in m[j]]
  for i in range(n):
   if i!=j:
    c=m[i][j];m[i]=[m[i][k]-c*m[j][k]for k in range(n+1)]
 return [m[i][-1]for i in range(n)]

def capacity(A,v):
 n=len(v)
 for mask in range(1<<n):
  active=[i for i in range(n)if mask>>i&1];a=[Q(0)]*n
  if active:
   z=solve([[A[i][j]for j in active]for i in active],[v[i]for i in active])
   if any(t<0 for t in z):continue
   for i,t in zip(active,z):a[i]=t
  residual=[v[i]-sum(A[i][j]*a[j]for j in range(n))for i in range(n)]
  if any(residual[i]>0 for i in range(n)if i not in active):continue
  assert all(residual[i]==0 for i in active)
  return sum(v[i]*a[i]for i in range(n)),a
 raise AssertionError('SPD nonnegative QP has no KKT solution')

def algebra_checks():
 rng=random.Random(49371);rank_count=resid_count=0
 for trial in range(140):
  sizes=[rng.randint(1,3),rng.randint(1,2)];blocks=[];vs=[]
  for n in sizes:
   R=[[Q(rng.randint(-3,3),4)for j in range(n)]for i in range(n)]
   A=[[sum(R[k][i]*R[k][j]for k in range(n))+int(i==j)for j in range(n)]for i in range(n)]
   blocks.append(A);vs.append([Q(rng.randint(-5,10),7)for j in range(n)])
  d=Q(rng.randint(1,7),9);n=sum(sizes);full=[[d for j in range(n)]for i in range(n)];offset=0
  for A in blocks:
   for i in range(len(A)):
    for j in range(len(A)):full[offset+i][offset+j]+=A[i][j]
   offset+=len(A)
  v=sum(vs,[]);C,a=capacity(full,v);tau=d*sum(a);J=tau*tau/d
  for A,vv in zip(blocks,vs):J+=capacity(A,[x-tau for x in vv])[0]
  assert J==C;rank_count+=1
 for trial in range(800):
  m=rng.choice([1,2,3]);K=Q(rng.randint(10,20),10)
  beta=K*Q(rng.randint(-9,15),10*(m+1));D=K+beta;den=K+m*beta
  assert K+(m+1)*beta>0
  A=[[K/m+beta,beta],[beta,D]];vg=Q(rng.randint(-10,40),30);vl=Q(rng.randint(-10,40),30)
  old=None
  for tau in (Q(0),Q(1,10),Q(1,3),Q(4,5)):
   u=vg-tau;v=vl-tau;globalcost=m*max(u,0)**2/den
   full,_=capacity(A,[u,v]);kappa=m*beta/den
   residual=max(v-kappa*max(u,0),0)**2/D
   assert full>=globalcost+residual
   extra=full-globalcost
   if old is not None:assert extra<=old
   old=extra;resid_count+=1
 return dict(exact_rank_one_identity_instances=rank_count,exact_residual_and_monotonicity_instances=resid_count)

def M(q):
 q=Q(q);return mp.mpf(q.numerator)/q.denominator

def f(t,g):
 if t<0 or t>=2*g:return mp.mpf(0)
 u=t/(2*g);return 16*g**5/15*(1-u)**3*(1+3*u+u*u)

def transform(g,z):return mp.quad(lambda t:f(t,g)*mp.exp(-z*t),[0,g,2*g])

def feature(inp,lam,real):
 e=inp['extension'];gg,gz,t=M(e['gG']),M(e['gZ']),M(e['mix']);s=M(inp['shift']);eps=t*(gz/gg)**5
 RG=transform(gg,-s);RB=mp.quad(lambda x:f(x,gz)**2/f(x,gg)*mp.exp(s*x),[0,gz,2*gz])+2*eps*transform(gz,-s)+eps**2*RG
 N=mp.sqrt(RG*RB);phi=mp.mpf(1)/4 if real else mp.mpf(1)/3
 val=(transform(gz,M(lam)-s)+eps*transform(gg,M(lam)-s)-phi*(f(mp.mpf(0),gz)+eps*f(mp.mpf(0),gg))/2)/N-mp.mpf('0.000001')
 return val,N

BETA=[M(x)for x in '.02318741 .07159337 .12265085 .17627704 .23237155 .29081583 .35147264 .41418551 .47877833 .54505502 .61279917 .68177389 .75172165 .82236428 .89340300 .96451862'.split()]

def envelope(anchor,real):
 T=mp.mpf('.416829');dt=T/16;H0=(dt*sum(BETA))**2;p=M(anchor);term=mp.mpf(0);energy=mp.mpf(0)
 for i,b in enumerate(BETA):
  l,r=i*dt,(i+1)*dt;tail=dt*sum(BETA[i+1:]);term+=2*b*mp.quad(lambda x:mp.exp(-2*p*x)*(b*(r-x)+tail),[l,r]);energy+=b*b*mp.quad(lambda x:mp.exp(-2*p*x),[l,r])
 phi=mp.mpf(1)/4 if real else mp.mpf(1)/3
 return (term+phi*energy)/H0

def farweight(lam):
 c1,c2,theta=map(mp.mpf,['.09035','.235968','1.28683']);u=mp.mpf(1)/3+2*c1;v=u+c2;x=mp.mpf(2)/3+3*c1+c2;eps=mp.mpf('1e-7');la=M(lam)
 def r(t):return mp.exp(-theta*t)*mp.sqrt(min(t-u+eps,c2+eps))
 return 1/mp.quad(lambda t:r(t)*mp.exp(2*la*t),[u,u+mp.mpf('1e-4'),v,x])

def get_leaf(tree):
 if 'record'in tree:return [tree]
 return sum((get_leaf(t)for t in tree['children']),[])

def integral_checks():
 mp.mp.dps=65;inputs=[];seen=set()
 for j in range(8):
  with gzip.open(ROOT/'results'/f'local_split_4.20_8_{j}.json.gz','rt')as z:rt=json.load(z)
  from adaptive_local_blocks import make_block_input,PAR
  from certificate_io import check_input
  for tr in rt['trees']:
   for leaf in get_leaf(tr):
    br=leaf['branch'];key=(br['identity'],br['ng'],j//4)
    if key not in seen and br['ng']:
     inp=make_block_input(rt['base'],'4.20',br,PAR,400)
     inputs.append(check_input(inp,leaf['record']['input']));seen.add(key)
  if len(inputs)>=8:break
 from first_outside_blocks import first_out_input
 from certificate_io import load_data,check_input,parameters_of
 with gzip.open(ROOT/'results/outside_first_2559_4.28.jsonl.gz','rt')as z:old=json.loads(next(z))['input']
 base=next(r['input']for r in load_data('selected_global_scan_inputs.json')if r['id']==2559)
 inputs.append(check_input(first_out_input(base,'4.28','outside_buffer',parameters_of(old),old['lambda_den']),old))
 checks=0;details=[]
 for inp in inputs:
  if 'shadow'in inp:
   glob=inp['shadow'];vg,N=feature(inp,glob['hi'],glob['real']);assert M(Q(glob['v_global'],S))<=vg;checks+=1
   real=glob['real'];anchor=inp['separated_block']['anchor']
  else:
   real=inp['case']['kind']=='rc';anchor=inp['first_block']['anchor'];vg,N=feature(inp,inp['case']['hi'],real)
   assert M(Q(inp['v_first'],S))<=vg;checks+=1
  B=envelope(anchor,real);A=M(inp['L'])-2*mp.mpf('.416829');rows=inp['hidden_rows']
  for row in [rows[0],rows[len(rows)//2],rows[-1]]:
   if row[1]=='infinity':
    val=mp.exp(-A*M(row[0]))*B/farweight(row[0]);assert val<=M(Q(row[3],S));assert M(Q(row[5],S))<=1/farweight(row[0]);checks+=2
   else:
    val=mp.exp(-A*M(row[0]))*B;vv,_=feature(inp,row[1],real);assert val<=M(Q(row[3],S));assert M(Q(row[2],S))<=farweight(row[1]);assert M(Q(row[4],S))<=vv;checks+=3
  details.append(dict(L=inp['L'],anchor=anchor,real=real,global_feature=mp.nstr(vg,40),normalization=mp.nstr(N,40),B=mp.nstr(B,40)))
 return dict(direct_quadrature_precision=65,independent_integral_comparisons=checks,cases=details)

if __name__=='__main__':
 t=time.time();report=dict(status='PASS exact finite algebra and independent numerical diagnostics; not a formal analytic proof',algebra=algebra_checks(),integrals=integral_checks(),seconds=time.time()-t)
 (ROOT/'results/independent_new_checks.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
