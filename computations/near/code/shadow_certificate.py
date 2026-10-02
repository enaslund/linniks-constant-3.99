"""Outward scalar input + rational certificate for ONE first/local-second cell.
This is NOT a complete global Linnik certificate. The new height-shadow lemma
is a separately stated mathematical premise, not established by this program.
"""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
from start import *
from refine_probe import spec_from_input
from build_progress import near,solve,ceildiv,CannotCertify
from extension_enclosures import mixfeature,mixnorm
from optimize_near import hull_n
from config_v4 import TAU_SCALE as TS,DUAL_SCALE as DS
import time, math, gzip, argparse


def shadow_plan(base,step=Q('.01')):
 r=Q(base['ordinary_lower']);lo=max(Q(base['case']['source_l2']),Q(base['case']['lo']))
 n=max(0,math.ceil((r-lo)/step));ans=[]
 for j in range(n):
  a=lo+(r-lo)*j/n;b=lo+(r-lo)*(j+1)/n
  for ng in (1,2):ans.append(dict(lo=str(a),hi=str(b),ng=ng,real=(ng==1)))
 ans.append(dict(lo=str(max(lo,r)),hi='infinity',ng=0,real=False))
 return ans


def regenerate(base,L,branch,par,den=200):
 sp=spec_from_input(base)
 sp['case']=dict(sp['case']);sp['case']['source_l2']=str(max(Q(sp['case']['source_l2']),Q(branch['lo'])))
 inp=make_endgame(sp,L,par,den)
 if inp is None:raise ValueError('unexpected analytic exclusion')
 inp['shadow']=dict(branch)
 if branch['ng']:
  r=Q(base['ordinary_lower']);h=Q(branch['hi']);assert h<=r
  gG,gZ=Q(par['gg']),Q(par['gz']);s=Q(inp['shift']);t=Q(par['mix']);G,Z=test(gG),test(gZ);eps=t*(gZ/gG)**5;N=mixnorm(gG,gZ,s,t)
  glob=mixfeature(gG,gZ,s,t,h,branch['real'])
  phi=Q(1,4) if branch['real'] else Q(1,3)
  cap=upper((Z.F(r-s)+I(eps)*G.F(r-s)-I(phi)*(Z.f0+I(eps)*G.f0)/2)/N-I(ETA))
  Dh=inp['D']-int((1+ETA)*S/2) if branch['real'] else inp['D']
  assert 0<Dh<=inp['D']
  inp['shadow'].update(v_global=glob,v_existing_cap=cap,diagonal=Dh,local_minimum=str(r),principle='global xi<local minimum implies actual height>1; real hidden family can average conjugate centers')
 return inp


def near_shadow(inp,a,b):
 C,B=near(inp,a,b);sh=inp['shadow'];ng=sh['ng'];bonus=0
 if ng:
  xb=b*(S//TS);xa=a*(S//TS)
  new=max(sh['v_global']-xb,0);old=max(sh['v_existing_cap']-xa,0)
  newcost=(inp['D']*new*new)//(sh['diagonal']*S)
  oldcost=ceildiv(old*old,S)
  bonus=ng*max(0,newcost-oldcost)
 return C,B-bonus,bonus


def certify(inp,target=Q('.999'),minimum_width=1):
 end=math.isqrt(inp['d']*TS*TS//S);end+=int(end*end*S<inp['d']*TS*TS)
 W=[r[2]for r in inp['rows']];G=[r[3]for r in inp['rows']];F=inp['far_budget']
 wa=np.array(W)/S;ga=np.array(G)/S
 stack=[(j,min(j+5000,end))for j in range(0,end,5000)];out=[]
 while stack:
  a,b=stack.pop();C,B,bonus=near_shadow(inp,a,b)
  if B<0:out.append(dict(a=a,b=b,excluded=True,budget=B,bonus=bonus));continue
  y,z=hull_n(wa,np.array(C)/S,ga,F/S,B/S)
  Y=max(0,math.ceil(y*DS)+1);Z=max(0,math.ceil(z*DS)+1)
  Y+=max(0,max(ceildiv(g*DS-Y*w-Z*c,w)for g,w,c in zip(G,W,C)))
  assert all(Y*w+Z*c>=DS*g for g,w,c in zip(G,W,C))
  val=inp['first']+inp['final']+ceildiv(Y*F+Z*B,DS)
  if val>=target*S and b-a>minimum_width:
   m=(a+b)//2;stack.extend([(a,m),(m,b)]);continue
  if val>=S:raise CannotCertify((val/S,a,b))
  out.append(dict(a=a,b=b,Y=Y,Z=Z,upper=val,bonus=bonus))
 return sorted(out,key=lambda x:x['a'])


def verify_records(records,base,L,par,regenerate_inputs=True):
 plan=shadow_plan(base);assert len(records)==len(plan)
 maxv=-1;checks=0;branches=0;excluded=0;binding=None
 for j,(rec,branch)in enumerate(zip(records,plan)):
  inp=regenerate(base,L,branch,par,rec['input']['lambda_den']) if regenerate_inputs else rec['input']
  check_input(inp,rec['input'])
  W=[r[2]for r in inp['rows']];G=[r[3]for r in inp['rows']]
  end=math.isqrt(inp['d']*TS*TS//S);end+=int(end*end*S<inp['d']*TS*TS);last=0
  for row in rec['certificate']:
   a,b=row['a'],row['b'];assert a==last and a<b<=end;last=b;branches+=1
   C,B,bonus=near_shadow(inp,a,b);assert bonus==row['bonus']
   if row.get('excluded'):
    assert B==row['budget'] and B<0;excluded+=1;continue
   Y,Z=row['Y'],row['Z'];assert isinstance(Y,int)and isinstance(Z,int)and Y>=0 and Z>=0
   for w,c,g in zip(W,C,G):assert Y*w+Z*c>=DS*g;checks+=1
   v=inp['first']+inp['final']+ceildiv(Y*inp['far_budget']+Z*B,DS);assert v==row['upper']and v<S
   if v>maxv:maxv=v;binding=dict(global_branch=branch,tau=row,first=inp['first'],far_budget=inp['far_budget'],near_budget=B)
  assert last==end
 return dict(L=L,scope='One fixed first-zero/local-second cell, ALL global-second alternatives and unknown thresholds. NOT a global exponent.',status='PASS: exact rational numerical implication',regenerated_inputs=regenerate_inputs,global_cases=len(records),branches=branches,excluded=excluded,column_checks=checks,maximum_numerator=maxv,scale=S,maximum=float(Q(maxv,S)),margin=float(1-Q(maxv,S)),binding=binding)


if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.25');ap.add_argument('--verify',action='store_true');args=ap.parse_args()
 outdir=(PACKAGE/'results');base=load_data('selected_inputs.json')['2063'][0][1]
 par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')
 path=outdir/f'shadow_local_{args.L}.jsonl.gz';tt=time.time()
 if args.verify:
  with gzip.open(path,'rt')as f:records=[json.loads(l)for l in f]
 else:
  records=[]
  with gzip.open(path,'wt')as f:
   for i,branch in enumerate(shadow_plan(base)):
    inp=regenerate(base,args.L,branch,par);c=certify(inp);rec=dict(input=inp,certificate=c);records.append(rec);f.write(json.dumps(rec,separators=(',',':'))+'\n');f.flush()
    print('CASE',i,branch,'max',max((r['upper']/S for r in c if 'upper'in r),default=-1),'branches',len(c),'seconds',time.time()-tt,flush=True)
 report=verify_records(records,base,args.L,par,True);report['seconds']=time.time()-tt
 (outdir/f'shadow_local_{args.L}_verification.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2),flush=True)
