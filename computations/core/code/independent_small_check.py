"""High-precision reference for the 3.99 exceptional branch.
No enclosure-library functions are imported. This is a diagnostic, not a second
interval proof. The monotonicity and source hypotheses are in ARGUMENT_4_33.md.
"""
from pathlib import Path
from fractions import Fraction
import json
import mpmath as mp
mp.mp.dps=80
root=Path(__file__).resolve().parents[1]
rep=json.loads((root/'results/verification_4.33.json').read_text())['small_exception_at_3_99']
def m(s):
 q=Fraction(str(s));return mp.mpf(q.numerator)/q.denominator
L=m('3.99');K=m('.1821');c1=m('.057');c2=m('.1554');al=m('1.09');u=m('.1')
A=L-2*K;a=m('4/3')+6*c1+2*c2;b=m('2/3')+4*c1
V=(m('2/3')+2*c1+c2)/(4*c1*c2);gap=al*mp.log(10)
B=(1-mp.exp(-2*K*gap))/(6*gap)+(2*K*gap-1+mp.exp(-2*K*gap))/(2*gap**2)
H=mp.exp(-A*u)*mp.quad(lambda t:mp.exp(-u*t),[0,K])**2
main=(K*K-H)/u
other=V*B*mp.quad(lambda t:mp.exp(-t*gap),[A-a,A-b])/u
first=(K*K+K/4)*mp.exp(-A*gap)/u
S=mp.mpf(rep['scale'])
assert main>=rep['main_linear_lower']/S
assert other<=rep['ordinary_linear_upper']/S
assert first<=rep['first_remainder_linear_upper']/S
assert main-other-first>=rep['remaining_linear_lower']/S
out={'status':'PASS: independent high-precision exceptional-branch diagnostic',
 'digits':80,'main':str(main),'other':str(other),'first':str(first),'surplus':str(main-other-first),
 'scope':'Direct high-precision numerical reference only; the interval proof and analytic premises are separate.'}
(root/'results/independent_small_3.99.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
