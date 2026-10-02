"""Enclose the supremum in Xylouris's side condition (4.34), p. 59, for the test f_gamma, gamma=1.04.

Xylouris proves (4.31) for real chi_1 and rho_1 with lambda_1 in [0.44, 0.80] and lambda_2 in
[0.44, 1.176] by showing that

    sup_t Re{ F(-lambda_2 + i t) - F(lambda_1 - lambda_2 + i t) - F(i t) }  <=  (5/48) f(0),

and he states (p. 59) that the supremum is below 0.10.  This script bounds the supremum from above
over the whole box (including lambda_2 < lambda_1) and all real t, in the style of alias_check.py:

* the expression is even in t, so t >= 0 suffices;
* the three transforms are enclosed by vector_transform on the grid t in (1/den)Z, 0 <= t <= Y, for
  lambda_1, lambda_2 on the grid (1/100)Z covering the box;
* between grid points, sequential linear interpolation in lambda_1, lambda_2 and t, with the
  second-derivative bounds |d^2/dx^2 Re F(x+it)|, |d^2/dt^2 Re F(x+it)| <= int u^2 f(u) e^{-xu} du;
* for t >= Y, the closed-form tail bound of vector_transform's large-|z| formula, and
  -Re F(it) <= 0 (Condition 2).

The script writes nothing unless run as a program.
"""
from endgame import *
from extension_enclosures import vector_transform,_finite
from two_test_enclosures import vi


def tailbox(f,lo,hi,Y):
 """|Re F(sigma+it)| for sigma in [lo,hi] and |t| >= Y (as in correlation_bound)."""
 yi=I(Y);g=f.gi;ee=iv.exp(-2*g*I(lo));abs_sig=max(abs(lo),abs(hi))
 return f.f0*I(abs_sig)/yi**2+8*g**3/(3*yi**3)+4*g*g*(1+ee)/yi**4+4*(1+ee)/yi**6+8*g*ee/yi**5


def check(Y=30,den=100):
 g=Q(104,100);f=test(g)
 l1=[Q(j,100) for j in range(44,81)]            # lambda_1 grid covering [0.44, 0.80]
 l2=[Q(j,100) for j in range(44,119)]           # lambda_2 grid covering [0.44, 1.18] > [0.44, 1.176]
 A={b:vector_transform(g,-b,Y,den) for b in l2}                         # Re F(-lambda_2 + it)
 xs=sorted(set(a-b for a in l1 for b in l2))
 B={x:vector_transform(g,x,Y,den) for x in xs}                          # Re F(lambda_1-lambda_2 + it)
 C=vector_transform(g,Q(0),Y,den)                                       # Re F(it)
 mx=-math.inf
 for a in l1:
  for b in l2:
   vals=_finite(vi.sub(vi.sub(A[b],B[a-b]),C))
   mx=max(mx,float(np.max(vals[1])))
 assert math.isfinite(mx)
 sample=(Q.from_float(mx)*S).__ceil__()
 # Second-derivative bounds: x = -lambda_2 >= -1.18, x = lambda_1 - lambda_2 >= -0.74, x = 0.
 M_a=f.exponential_moment(2,Q(118,100));M_b=f.exponential_moment(2,Q(74,100));M_0=f.exponential_moment(2,Q(0))
 h=Q(1,100)
 err_l1=upper(M_b*I(h*h/8))                     # only the middle term depends on lambda_1
 err_l2=upper((M_a+M_b)*I(h*h/8))
 err_t=upper((M_a+M_b+M_0)*I(Q(1,8*den*den)))
 tail=upper(tailbox(f,Q(-118,100),Q(-44,100),Q(Y))+tailbox(f,Q(-74,100),Q(36,100),Q(Y)))
 bound=max(sample+err_l1+err_l2+err_t,tail)
 permitted=lower(I(Q(5,48))*f.f0)
 margin=permitted-bound
 assert margin>0
 return dict(status='PASS: X (4.34) side condition',gamma=str(g),
             lambda1_interval=['11/25','4/5'],lambda2_interval=['11/25','147/125'],
             grid_lambda='1/100 (lambda_2 grid runs to 1.18)',height_end=Y,height_step=f'1/{den}',
             sample_upper=sample,lambda1_interpolation_error=err_l1,lambda2_interpolation_error=err_l2,
             height_interpolation_error=err_t,tail_upper=tail,supremum_upper=bound,
             permitted_lower=permitted,margin_lower=margin,scale=S,
             scope='Bounds sup over the box and all real t of Re{F(-l2+it)-F(l1-l2+it)-F(it)} for '
                   'f=f_gamma, gamma=1.04 (Xylouris (4.34), p. 59). It does not formalize the '
                   'derivation of (4.31) from (4.32)-(4.34).')


if __name__=='__main__':
 r=check();(ROOT/'results/x434_condition.json').write_text(json.dumps(r,indent=2));print(json.dumps(r,indent=2))
