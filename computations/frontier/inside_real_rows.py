"""Extend the retained real-first degree-two positivity row over first-zero cells.

All elementary enclosures use the same degree-two proof and order-four alias
case as research/arguments/real-first-row.md, with a variable positive t. The optional 1/108 saving uses the separate proof
in research/arguments/real-conductor-rows.md.
"""
from inside_model import *
import argparse
from optimize_near import trans
from scipy.optimize import brentq, minimize
from new_positivity import vector_transform, fq, vi, _finite
from base_enclosures import ceil_fraction
from pair_bounds import real_tail


def certify_row(a,b,h,g,t,Y=30,den=200,saving=Q(0)):
    a,b,h,g,t=map(Q,(a,b,h,g,t));assert 0<a<=b<=h and g>0 and t>0
    saving=Q(saving);assert saving in (Q(0),Q(1,108))
    r=a;c1=2*t/(t*t+Q(1,2));c2=Q(1,2)/(t*t+Q(1,2));f=test(g);f0=f.f0
    if saving:assert c1+c2>=Q(1,9), 'conductor tradeoff maximum must occur at theta=1/9'
    lhs=f.F(b-a)+I(c1)*f.F(h-a)-f.F(-a)
    generic=lower(lhs/f0-I(Q(1,8)+(c1+c2)/3)+I(saving))
    P=vector_transform(g,-a,Y,den);corners=[]
    for ll in(a,b):
        for rr in(r,h):
            R=vi.sub(vi.mul(fq(c2),vi.sub(P,vector_transform(g,ll-a,Y,den))),vi.mul(fq(c1),vector_transform(g,rr-a,Y,den)))
            _finite(R);corners.append(float(np.max(R[1])))
    sample=ceil_fraction(Q.from_float(max(corners))*S);moment=f.exponential_moment(2,Q(0))
    he=upper((I(c2)*f.exponential_moment(2,a)+I(c2+c1)*moment)*I(Q(1,8*den*den)))
    pe=upper(I(c2*(b-a)**2+c1*(h-r)**2)*moment/8)
    def tailbox(lo,hi):
        yi=I(Y);gi=I(g);ee=iv.exp(-2*gi*I(lo));sig=max(abs(lo),abs(hi))
        return f0*I(sig)/yi**2+8*gi**3/(3*yi**3)+4*gi**2*(1+ee)/yi**4+4*(1+ee)/yi**6+8*gi*ee/yi**5
    tail=upper(I(c2)*(real_tail(f,-a,Q(Y))+tailbox(0,b-a))+I(c1)*tailbox(r-a,h-a))
    bound=max(0,tail,sample+he+pe)
    alias=lower((lhs-I((1+c2)/8+c1/3)*f0-I(Q(bound,S)))/f0)
    # The source real-second inequality also covers nonreal selected zeros of a real character.
    real_gamma=Q('0.82');fr=test(real_gamma)
    real_margin=lower((fr.F(b-a)+fr.F(h-a)-fr.F(-a))/fr.f0-I(Q(3,8)))
    assert min(generic,alias,real_margin)>10**10,(generic,alias,real_margin)
    record=dict(a=str(a),b=str(b),lower=str(h),gamma=str(g),t=str(t),c1=str(c1),c2=str(c2),
        generic_margin=generic,order4_margin=alias,real_second_margin=real_margin,real_gamma=str(real_gamma),scale=S,
        correlation=dict(sample=sample,height_error=he,parameter_error=pe,tail=tail,bound=bound,Y=Y,den=den))
    if saving:record.update(generic_saving=str(saving),analytic_status='Conductor interpolation deduction under the retained source explicit-formula premises')
    return record


def propose(a,b,saving=Q(0)):
    aa,bb=float(a),float(b)
    def h_for(par):
        g,t=par;c1=2*t/(t*t+.5);c2=.5/(t*t+.5)
        def margin(h):return trans(g,bb-aa)+c1*trans(g,h-aa)-trans(g,-aa)-(1/8+(c1+c2)/3)+float(saving)
        if margin(bb)<=0:return bb-(abs(margin(bb)))
        return brentq(margin,bb,3.)
    op=minimize(lambda x:-h_for(x),[1.09,.875],method='Nelder-Mead',bounds=[(.6,1.8),(.5,1.5)],options=dict(maxiter=180,xatol=1e-8,fatol=1e-9))
    g,t=map(lambda x:Q(f'{x:.6f}'),op.x);h=Q(math.floor((-op.fun-.00005)*10000),10000)
    while True:
        try:return certify_row(a,b,h,g,t,saving=saving)
        except AssertionError:
            h-=Q('.0001')
            if h<=b:raise

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--start',default='.700');ap.add_argument('--stop',default='.725');ap.add_argument('--step',default='.0025');aa=ap.parse_args()
    a=Q(aa.start);out=[]
    while a<Q(aa.stop):
        b=min(a+Q(aa.step),Q(aa.stop));r=propose(a,b);out.append(r);print(json.dumps(r),flush=True);a=b
    dest=Path(__file__).resolve().parent/f'inside_real_rows_{aa.start}_{aa.stop}.json'
    dest.write_text(json.dumps(dict(scope='New local real-first lambda2 rows; no global Linnik exponent',rows=out),indent=2)+'\n')
