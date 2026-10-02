"""Outward arithmetic for the compact small-real-exceptional-zero branch.

Heath-Brown's logarithmic repulsion and effective sufficiently-small-zero
reduction are mathematical inputs, not proved by this script.
"""
from fractions import Fraction as Q
from pathlib import Path
import argparse,json
from enclosures import I,lower,upper,S,iv

def check(L):
    L=Q(L); A=L-Q(1,2); alpha=Q(109,100); p=alpha*(A-Q(73,30))
    assert L>4 and p>1
    K=I(Q(1,4)); z=I(Q(71,50))
    B=(1-iv.exp(-2*K*z))/(6*z)+(2*K*z-1+iv.exp(-2*K*z))/(2*z*z)
    m_min=I(alpha)*iv.ln(10)
    coefficient=I(Q(11,100)*Q(67,6)/Q(5,2))+I(Q(15,1000))*iv.exp(-I(Q(73,30)*Q(5,2)))
    power=iv.exp(I(p-1)*iv.ln(I(Q(1,10))))
    main=(A-A*A/20)/16
    tail=I(Q(492,1000))*power
    residual=I(main)-tail
    assert upper(B)<Q(11,100)*S
    assert lower(m_min)>Q(5,2)*S
    assert upper(coefficient)<Q(492,1000)*S
    assert lower(residual)>0
    safe=Q(lower(residual)//(S//1000),1000)
    report={'L':str(L),'L_decimal':str(float(L)),'A':str(A),'alpha':str(alpha),'p':str(p),'scale':S,
      'ordinary_B_upper':upper(B),'min_gap_lower':lower(m_min),
      'tail_coefficient_upper':upper(coefficient),'power_at_point1_upper':upper(power),
      'main_linear_coefficient':str(main),'tail_linear_coefficient_upper':upper(tail),
      'remaining_linear_coefficient_lower':lower(residual),'safe_pre_error_margin_coefficient':str(safe),
      'status':'PASS: elementary inequalities in the analytic exceptional-zero reduction',
      'scope':'Uniform on u0<=u<=0.1 for fixed u0>0. For smaller u, use the effective q^(3+epsilon) implication stated in Heath-Brown (1992), introduction. No numerical u0 or q0 is computed.'}
    return report
if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--L',default='4.60');args=ap.parse_args()
    r=check(args.L);dest=Path(__file__).resolve().parents[1]/('results/small_exception_'+args.L.replace('.','_')+'.json')
    dest.write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
