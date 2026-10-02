"""Propose local polynomial rows, then require exact interval acceptance."""
from poly_rows import *
from optimize_near import trans
from scipy.optimize import brentq
from concurrent.futures import ProcessPoolExecutor
import time

def celltask(cell):
 a,b,p,r=map(Q,cell);af,bf,pf,rf=map(float,(a,b,p,r));ans=[]
 # Only proposals use direct floating integrals; every accepted row is fully enclosed.
 best=(rf,None)
 for ti in range(80,101,5):
  t=ti/100;c1=2*t/(t*t+.5);c2=.5/(t*t+.5);cost=((1+c1+c2)**2-1)/6
  for gi in range(100,141,5):
   g=gi/100
   def fun(h):return c1*(trans(g,bf-af)+trans(g,h-af))-trans(g,-af)-cost-.0008
   if fun(rf)<=0:continue
   hh=brentq(fun,rf,1.6)
   if hh>best[0]:best=(hh,(Q(gi,100),Q(ti,100)))
 if best[1] is not None:
  h=Q(math.floor(best[0]*1000),1000);g,t=best[1]
  # Choose a real-second polynomial at the same proposed endpoint.
  br=(-1,None)
  for ti in range(70,111,5):
   tr=Q(ti,100);u1,u2=coefficients(tr)
   for gi in range(85,141,5):
    gr=Q(gi,100);f=test(gr)
    ma=lower((I(u1)*f.F(b-a)+f.F(h-a)-f.F(-a))/f.f0-I(Q(1,8)+(u1+u2)/3))
    if ma>br[0]:br=(ma,(gr,tr))
  if br[1]:
   try:ans.append(dict(type='second',proof=complex_second_row(a,b,h,g,t,*br[1])))
   except AssertionError:pass
 best=(pf,None)
 for ti in range(80,111,5):
  t=ti/100;c1=2*t/(t*t+.5);c2=.5/(t*t+.5);cost=((1+c1+c2)**2-1-(c1*c1+c2*c2)/2)/6
  for gi in range(95,141,5):
   g=gi/100
   def fun(h):return c1*(trans(g,bf-af)+trans(g,h-af))-trans(g,-af)-cost-.0025
   if fun(pf)<=0 or fun(1.349)>=0:continue
   hh=brentq(fun,pf,1.349)
   if hh>best[0]:best=(hh,(Q(gi,100),Q(ti,100)))
 if best[1]:
  h=Q(math.floor(best[0]*1000),1000);g,t=best[1]
  for j in range(5):
   if h<=p:break
   try:
    ans.append(dict(type='additional',proof=additional_row(a,b,p,h,g,t)));break
   except AssertionError:h-=Q(1,1000)
 return ans

if __name__=='__main__':
 import argparse
 ap=argparse.ArgumentParser();ap.add_argument('--workers',type=int,default=4);arg=ap.parse_args()
 cells=sorted(set((s['case']['lo'],s['case']['hi'],s['case']['lp'],s['case']['source_l2']) for s in specs() if s['case']['kind']=='complex' and Q('.62')<=Q(s['case']['lo'])<=Q(s['case']['hi'])<=Q('.86')),key=lambda x:Q(x[0]))
 tt=time.time();rows=[]
 with ProcessPoolExecutor(max_workers=arg.workers) as pool:
  for i,rs in enumerate(pool.map(celltask,cells,chunksize=1)):
   rows.extend(rs)
   if i%10==0:print('POLY',i,len(rows),round(time.time()-tt,1),flush=True)
 for i,row in enumerate(rows):row['id']=i
 out=dict(status='PASS: each proposed row independently interval-enclosed',rows=rows,cells_considered=len(cells),row_count=len(rows),scale=S,seconds=time.time()-tt)
 (ROOT/'results/polynomial_table.json').write_text(json.dumps(out,indent=2));print('DONE',len(rows),time.time()-tt)
