"""Outward bounds for the averaged two-zero character vector.

No optimizer or sampled acceptance occurs here. Interpolation and the
infinite height tail both have explicit remainder bounds.
"""
from base_enclosures import *
from config_v4 import ETA
from functools import lru_cache
Q=Fraction

def real_tail(f,sigma,Y):
    si=I(sigma);g=f.gi;y=I(Y);ee=iv.exp(-2*g*si)
    return (f.f0*abs(si)/y**2+8*g**3/(3*y**3)
       +4*g*g*(1+ee)/y**4+4*(1+ee)/y**6+8*g*ee/y**5)

@lru_cache(maxsize=None)
def combo_sup(gamma,s,a,b,p,h,tol=Q(1,10**6)):
    gamma,s,a,b,p,h=map(Q,(gamma,s,a,b,p,h));f=RigorousTest(gamma)
    m1=(a+b)/2;m2=(p+h)/2
    sigmas=(-s,m1-s,m2-s);coefs=(1,-1,-1)
    Y=Q(30);err=I((b-a)/2)*f.exponential_moment(1,max(Q(0),s-a))
    err+=I((h-p)/2)*f.exponential_moment(1,max(Q(0),s-p))
    M2=upper(sum(f.exponential_moment(2,max(Q(0),-q)) for q in sigmas))
    tail=upper(sum(real_tail(f,q,Y) for q in sigmas))
    vals={}
    def at(t):
        if t not in vals:
            v=sum(c*f.F(iv.mpc(I(q),I(t))).real for c,q in zip(coefs,sigmas))
            vals[t]=(lower(v),upper(v))
        return vals[t]
    def seg(l,r):
        up=max(at(l)[1],at(r)[1])+ceil_fraction(Q(M2,8)*(r-l)**2)
        return (-up,l,r)
    heap=[seg(Q(i,10),Q(i+1,10)) for i in range(300)];heapq.heapify(heap)
    best=max(0,max(v[0] for v in vals.values()));target=ceil_fraction(tol*S)
    while -heap[0][0]>max(best,tail)+target:
        neg,l,r=heapq.heappop(heap);mid=(l+r)/2
        v=at(mid);best=max(best,v[0]);heapq.heappush(heap,seg(l,mid));heapq.heappush(heap,seg(mid,r))
        if len(vals)>100000:raise RuntimeError('pair supremum cover did not converge')
    total=max(0,tail,-heap[0][0])+upper(err)
    return total,{'sup_int':total,'tail_int':tail,'parameter_error_int':upper(err),
                  'second_derivative_int':M2,'evaluations':len(vals),'height_end':str(Y),'tolerance':str(tol)}

@lru_cache(maxsize=None)
def paired_constants(gamma,s,a,b,p,h,kind,C_int):
    gamma,s,a,b,p,h=map(Q,(gamma,s,a,b,p,h));f=RigorousTest(gamma);R=f.F(-s)
    d0=f.f0/(6*R);c=I(Q(C_int,S))/R
    sup,proof=combo_sup(gamma,s,a,b,p,h)
    B=I(Q(sup,S))/R
    e=c if kind=='rc' else c/2
    graph=c if kind=='complex' else I(0)
    v=(f.F(b-s)+f.F(h-s))/(2*R)-(I(Q(3,4)) if kind!='complex' else 1)*d0-I(ETA)-e
    D=(1+I(ETA))*((1+B)/2-d0+graph)
    # Enlarging D is safe. Prove the scalar cost comparison for all tau>=0.
    vv=lower(v);DD=upper(D)
    assert DD>0 and 2*Q(DD,S)>=(1+ETA)*max(Q(vv,S),Q(0))
    proof.update({'B_int':upper(B),'feature_int':vv,'diagonal_int':DD,
                  'monotonicity_margin':str(2*Q(DD,S)-(1+ETA)*max(Q(vv,S),Q(0)))})
    return vv,DD,proof
