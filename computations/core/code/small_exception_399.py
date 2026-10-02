"""Uniform compact exceptional-zero endgame at L=3.99 from published inputs.
The source inputs are H Lemmas 8.4,8.8,13.3 and X (5.18), plus H's effective
sufficiently-small-exceptional-zero reduction. No near-profile or far-block
extension is used. This certifies the elementary bounds, not the source lemmas.
"""
from endgame import I,iv,Q,S,lower,upper,ROOT
import json

def check():
 L=Q(399,100);K=Q(1821,10000);c1=Q(57,1000);c2=Q(777,5000);alpha=Q(109,100);u=Q(1,10)
 A=L-2*K;aa=Q(4,3)+6*c1+2*c2;bb=Q(2,3)+4*c1;V=(Q(2,3)+2*c1+c2)/(4*c1*c2)
 assert A>3 and alpha*(A-aa)>1 and aa>bb>0
 m=I(alpha)*iv.ln(10);ki=I(K);ui=I(u);ai=I(A)
 e=iv.exp(-2*ki*m)
 B=I(Q(1,3))*(1-e)/(2*m)+(2*ki*m-1+e)/(2*m*m)
 principal=ki*ki+ki/4
 H=iv.exp(-ai*ui)*((1-iv.exp(-ki*ui))/ui)**2
 main=(ki*ki-H)/ui
 other=I(V)*B*(iv.exp(-I(A-aa)*m)-iv.exp(-I(A-bb)*m))/(m*ui)
 first=principal*iv.exp(-ai*m)/ui
 margin=main-other-first
 assert lower(margin)>0
 return dict(status='PASS: elementary uniform exceptional-zero endgame at L=3.99',L=str(L),K=str(K),c1=str(c1),c2=str(c2),alpha=str(alpha),A=str(A),density_exp_hi=str(aa),density_exp_lo=str(bb),density_constant=str(V),scale=S,
   min_gap_lower=lower(m),ordinary_envelope_upper=upper(B),first_envelope=str(K*K+K/4),main_linear_lower=lower(main),ordinary_linear_upper=upper(other),first_remainder_linear_upper=upper(first),remaining_linear_lower=lower(margin),safe_pre_error_linear_margin='8/10000',support_margin=str(A-3),monotonicity_margin=str(A-aa-1/alpha),
   scope='For a real exceptional zero with u0<=lambda1<=.1, fixed u0>0. For lambda1<=u0 use the published effective exponent 3+epsilon with epsilon=.5. This is a restricted branch, NOT a general Linnik exponent of 3.99. No cube-free assumption, no far block, no new near-density inequality.')

if __name__=='__main__':
 r=check();(ROOT/'results/small_exception_3.99.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
