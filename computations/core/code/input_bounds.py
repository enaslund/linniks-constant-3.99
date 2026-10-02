"""Rigorous finite inputs, with height-uniform far budgets and reserved family.

No optimizer is imported. All scalar values are outward-rounded integers.
"""
from fractions import Fraction as Q
from functools import lru_cache
from enclosures import *
from config_v4 import *

@lru_cache(maxsize=None)
def weights(L):return RigorousWeights(L)
@lru_cache(maxsize=None)
def test(g):return RigorousTest(g)
@lru_cache(maxsize=None)
def C_bound(g,delta):return test(g).C_upper(delta,tolerance=Q(1,10**7))
@lru_cache(maxsize=None)
def profile_constants(a,s,g,kind):
    f=test(g);R=f.F(-s);d0=f.f0/(6*R)
    C,cc=C_bound(g,max(Q(0),s-a));cr=I(Q(C,S))/R
    d=upper((1+I(ETA))*(d0+I(ETA)))
    Do=upper((1+I(ETA))*(1-d0+(1 if kind=='rr' else 2)*cr))
    Df=upper((1+I(ETA))*(1-d0+(cr if kind=='complex' else 0)))
    return d,Do,Df,cc
@lru_cache(maxsize=None)
def feat(s,g,r,real=False,exception=False,a=None):
    f=test(g);R=f.F(-s);d0=f.f0/(6*R)
    ret=f.F(r-s)/R-(I(Q(3,4)) if real else 1)*d0-I(ETA)
    if exception:
        C,cc=C_bound(g,max(Q(0),s-a));ret-=I(Q(C,S))/R
    return lower(ret)
@lru_cache(maxsize=None)
def rows_for(l2,s,g,L,den):
    w=weights(L);end=max(Q(2),l2)
    if den>=10000:
        coarse=2000
        ep=[l2]+[Q(j,coarse) for j in range((l2*coarse).__floor__()+1,(end*coarse).__floor__()+1)]
        ep=sorted(set(ep+[Q(j,den) for j in range(int(Q('1.43')*den),int(Q('1.57')*den)+1) if l2<Q(j,den)<end]))
    else:
        ep=[l2]+[Q(j,den) for j in range((l2*den).__floor__()+1,(end*den).__floor__()+1)]
    if ep[-1]!=end:ep.append(end)
    assert ep[-1]==end and all(a<b for a,b in zip(ep,ep[1:]))
    rows=[]
    for l,r in zip(ep,ep[1:]):
        rows.append([str(l),str(r),lower(w.w(r)),upper(w.G(l)),feat(s,g,r) if r<=2 else -S])
    rows.append([str(end),'infinity',S,upper(w.G(end)*w.winv(end)),-S])
    return rows

def make_input(c,L,l2lo=None,second=None,den=500,gamma=None):
    a,b,p,r=map(Q,(c['lo'],c['hi'],c['lp'],c['source_l2']))
    l2=r if l2lo is None else Q(l2lo);assert l2>=r
    s=min(Q('1.9'),p,l2);g=gamma_for(a,s) if gamma is None else Q(gamma)
    d,Do,Df,cc=profile_constants(a,s,g,c['kind'])
    vf=feat(s,g,b,c['kind']!='complex',c['kind']=='rc',a)
    n=2 if c['kind']=='complex' else 1;w=weights(L)
    F=upper((1+I(ETA))*w.V)-n*lower(w.w(b))
    firsts={'inside':upper(w.first(c,True))}
    if c['kind']!='rr':firsts['outside']=upper(w.first(c,False))
    first=max(firsts.values());reserved=None
    if second is not None:
        hi,n2=Q(second['hi']),int(second['n']);assert hi>l2 and n2 in (1,2) and hi<=2
        vf2=feat(s,g,hi,n2==1)
        F-=n2*lower(w.w(hi));contribution=n2*upper(w.G(l2,n2==1));first+=contribution
        reserved={'lo':str(l2),'hi':str(hi),'n':n2,'v':vf2,'contribution':contribution}
    return {'case':c,'L':L,'ordinary_lower':str(l2),'second':reserved,
            'gamma':str(g),'shift':str(s),'lambda_den':den,
            'S':S,'tau_scale':TAU_SCALE,'dual_scale':DUAL_SCALE,
            'd':d,'D':Do,'Df':Df,'v_first':vf,'n':n,'C_certificate':cc,
            'rows':rows_for(l2,s,g,L,den),'far_budget':F,
            'first_bounds':firsts,'first':first,'final':ceil_fraction(FINAL*S)}
