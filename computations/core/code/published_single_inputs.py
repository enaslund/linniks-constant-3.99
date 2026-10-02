"""Two-test reduction using ONLY the published height-one single-zero far bound.
No two-zero capacity table and no high-height far extension are used.
"""
from two_test_enclosures import *

@lru_cache(None)
def single_rows(r,gG,gZ,s,L,den):
 r,gG,gZ,s=map(Q,(r,gG,gZ,s));end=max(Q(3),r);w=wgt(L)
 pts=[r]+[Q(j,den) for j in range((r*den).__floor__()+1,(end*den).__floor__()+1)]
 if pts[-1]!=end:pts.append(end)
 out=[]
 for l,h in zip(pts,pts[1:]):out.append([str(l),str(h),lower(w.w(h)),upper(w.G(l)),feat(gG,gZ,s,h)])
 out.append([str(end),'infinity',S,upper(w.G(end)*w.winv(end)),-S]);return out

def make_single(spec,L,gG,gZ,den,height):
 c=spec['case'];a,b,p=map(Q,(c['lo'],c['hi'],c['lp']));gap=spec.get('gap');r=Q(spec['ordinary_lower']);kind=c['kind'];n=2 if kind=='complex' else 1
 if gap:p=Q(gap['lo'])
 assert height in ('inside','outside') and (kind!='rr' or height=='inside')
 # The local second-family lower bound is NOT a global zero-free bound.
 s=min(Q('1.9'),p,Q(c['source_l2']))
 d,D,Df,proof=constants(a,gG,gZ,s,kind);vf=feat(gG,gZ,s,b,kind!='complex',kind=='rc',a)
 w=wgt(L);far=upper((1+I(ETA))*w.V)
 if height=='inside':far-=n*lower(w.w(b))
 cc=dict(c);cc['lp']=str(p);firsts={height:upper(w.first(cc,height=='inside'))};first=firsts[height]
 sec=spec['second'];reserved=None
 if sec:
  hi=Q(sec['hi']);n2=sec['n'];vv=feat(gG,gZ,s,hi,n2==1);con=n2*upper(w.G(r,n2==1));first+=con;far-=n2*lower(w.w(hi))
  reserved={'lo':str(r),'hi':str(hi),'n':n2,'v':vv,'contribution':con}
 return dict(case=c,L=L,ordinary_lower=str(r),second=reserved,gamma=str(Q(gZ)),gamma_gram=str(Q(gG)),shift=str(s),lambda_den=den,S=S,tau_scale=TAU_SCALE,dual_scale=DUAL_SCALE,d=d,D=D,Df=Df,v_first=vf,n=n,C_certificate=proof,norm_certificate=list(norm_bounds(gG,gZ,s)),rows=single_rows(r,gG,gZ,s,L,den),far_budget=far,first_bounds=firsts,first=first,final=int(FINAL*S),gap=gap,method='single',height=height,column_model='two-test-published-single-far',representative='height-one',shift_rule='source-global-lambda2')

def make_large(L,gG=Q('1.5'),gZ=Q(1),den=100):
 a=s=Q('1.5');d,D,Df,proof=constants(a,gG,gZ,s,'complex');w=wgt(L)
 return dict(case=None,L=L,ordinary_lower=str(a),second=None,gamma=str(Q(gZ)),gamma_gram=str(Q(gG)),shift=str(s),lambda_den=den,S=S,tau_scale=TAU_SCALE,dual_scale=DUAL_SCALE,d=d,D=D,Df=Df,v_first=0,n=0,C_certificate=proof,norm_certificate=list(norm_bounds(gG,gZ,s)),rows=single_rows(a,gG,gZ,s,L,den),far_budget=upper((1+I(ETA))*w.V),first_bounds={},first=0,final=int(FINAL*S),gap=None,method='single',height='all',column_model='two-test-published-single-far',representative='height-one',shift_rule='large-zero-free')
