"""Regenerate the elementary alias condition X (4.29), gamma=5/4.
This checks the continuous numerical inequality; the source character algebra remains a lemma.
"""
from endgame import *
from extension_enclosures import vector_transform,_finite
from two_test_enclosures import vi

def check():
 g=Q(5,4);f=test(g);Y=30;den=100
 zero=vector_transform(g,Q(0),Y,den);mx=-math.inf
 for j in range(44,86):
  vals=_finite(vi.sub(vector_transform(g,-Q(j,100),Y,den),vi.scale(zero,2)))
  mx=max(mx,float(np.max(vals[1])))
 assert math.isfinite(mx)
 scaled=(Q.from_float(mx)*S).__ceil__()
 M=f.exponential_moment(2,Q(85,100));M0=f.exponential_moment(2,Q(0))
 err_l=upper(M*I(Q(1,8*100**2)))
 err_y=upper((M+2*M0)*I(Q(1,8*den**2)))
 yy=I(Y);gi=I(g);ee=iv.exp(2*gi*I(Q(85,100)))
 # -2 Re F(i*t) is nonpositive; discard it in the height tail.
 tail=f.f0*I(Q(85,100))/yy**2+8*gi**3/(3*yy**3)+4*gi**2*(1+ee)/yy**4+4*(1+ee)/yy**6+8*gi*ee/yy**5
 bd=max(scaled+err_l+err_y,upper(tail));margin=lower(f.f0/6-I(Q(bd,S)))
 assert margin>0
 return dict(status='PASS: elementary uniform source alias condition',gamma=str(g),lambda_interval=['11/25','17/20'],lambda_step='1/100',height_end=Y,height_step='1/100',sample_evaluations=42*(Y*den+1),sample_upper=scaled,lambda_interpolation_error=err_l,height_interpolation_error=err_y,tail_upper=upper(tail),supremum_upper=bd,permitted_upper_lower=lower(f.f0/6),margin_lower=margin,scale=S,scope='Verifies X (4.29) for the fixed test and all real heights. It does not formalize the character-product argument deriving (4.28).')
if __name__=='__main__':
 r=check();(ROOT/'results/alias_condition.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
