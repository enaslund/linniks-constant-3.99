"""Rigorous new positivity exclusion for a real first and nonreal second character.
The source explicit-formula lemmas are mathematical inputs. This program
only certifies the elementary transform inequalities. No optimizer is used.
"""
import sys,json,math
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
BASE=Path(__file__).resolve().parents[1]
from extension_enclosures import I,iv,S,upper,lower,test,vector_transform,fq,vi,_finite
from base_enclosures import ceil_fraction
from pair_bounds import real_tail


def check(a=Q('0.7'),b=Q('.7025'),r=Q('.745'),h=Q('.75'),g=Q('1.1'),Y=30,den=200):
    a,b,r,h,g=map(Q,(a,b,r,h,g))
    assert 0<a<=b and a<=r<=h and g>0
    c1,c2=Q(112,81),Q(32,81)
    f=test(g);f0=f.f0
    # Generic case: chi_2^2 != chi_1.
    lhs=f.F(b-a)+I(c1)*f.F(h-a)-f.F(-a)
    generic=lower((lhs-I(Q(1,8)+(c1+c2)/3)*f0)/f0)
    # Order-four alias chi_2^2=chi_1. Bound the full correlation on all heights.
    P=vector_transform(g,-a,Y,den)
    corners=[]
    for ll in (a,b):
        for rr in (r,h):
            R=vi.sub(vi.mul(fq(c2),vi.sub(P,vector_transform(g,ll-a,Y,den))),
                     vi.mul(fq(c1),vector_transform(g,rr-a,Y,den)))
            _finite(R);corners.append(float(np.max(R[1])))
    sample=max(corners)
    sample_int=ceil_fraction(Q.from_float(sample)*S)
    moment=f.exponential_moment(2,Q(0))
    M2=I(c2)*f.exponential_moment(2,a)+I(c2+c1)*moment
    height_error=upper(M2*I(Q(1,8*den*den)))
    parameter_error=upper((I(c2*(b-a)**2+c1*(h-r)**2)*moment)/8)
    # Uniform real-part strips for the two nonnegative sigmas.
    def tailbox(lo,hi):
        yi=I(Y);gi=I(g);ee=iv.exp(-2*gi*I(lo));abs_sig=max(abs(lo),abs(hi))
        return f0*I(abs_sig)/yi**2+8*gi**3/(3*yi**3)+4*gi**2*(1+ee)/yi**4+4*(1+ee)/yi**6+8*gi*ee/yi**5
    tail=upper(I(c2)*(real_tail(f,-a,Q(Y))+tailbox(Q(0),b-a))+I(c1)*tailbox(r-a,h-a))
    sup=max(0,tail,sample_int+height_error+parameter_error)
    special=lower((lhs-I((1+c2)/8+c1/3)*f0-I(Q(sup,S)))/f0)
    assert generic>0 and special>0,(generic,special)
    return {'status':'PASS: uniform elementary exclusion for both character-alias cases',
      'a':str(a),'b':str(b),'second_lo':str(r),'second_hi':str(h),'gamma':str(g),
      'polynomial':'(7/8 + cos(theta))^2 / (81/64)',
      'c1':str(c1),'c2':str(c2),'scale':S,
      'generic_normalized_margin_lower':generic,'order4_normalized_margin_lower':special,
      'uniform_margin_lower':min(generic,special),
      'correlation':{'sample_upper':sample_int,'height_interpolation_error':height_error,
          'parameter_interpolation_error':parameter_error,'infinite_tail_upper':tail,'sup_upper':sup,
          'height_end':Y,'height_denominator':den,'corner_evaluations':4*(Y*den+1)},
      'scope':'Two distinct nonprincipal characters; first real with real first zero, second nonreal. Source explicit-formula, zero ordering, and conductor bounds remain analytic inputs. No Linnik exponent is certified by this local exclusion.'}

def lambda2_row():
    """Cover both real and nonreal second characters, with exact endpoints."""
    ans=check(a=Q('0.700'),b=Q('0.7025'),r=Q('0.700'),h=Q('0.762'),g=Q('1.09'))
    f=test(Q('.82'));a=Q('.700');b=Q('.7025');h=Q('.762')
    margin=lower((f.F(b-a)+f.F(h-a)-f.F(-a)-I(Q(3,8))*f.f0)/f.f0)
    assert margin>0, 'real second character not excluded'
    ans.update(real_second_normalized_margin_lower=margin,real_second_gamma='41/50',
        conclusion='Real character and real first zero, .700<=lambda_1<=.7025 imply lambda_2>.762, using the source conventions and sufficiently small fixed errors.')
    return ans

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument('--lambda2-row',action='store_true',help='Regenerate the complete new lambda2>.762 row, including real second characters.')
    args=ap.parse_args()
    ans=lambda2_row() if args.lambda2_row else check()
    dest=Path(__file__).resolve().parents[1]/'results'/('new_lambda2_bound.json' if args.lambda2_row else 'new_positivity.json')
    dest.parent.mkdir(parents=True,exist_ok=True)
    dest.write_text(json.dumps(ans,indent=2));print(json.dumps(ans,indent=2))
