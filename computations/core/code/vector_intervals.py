"""Directed binary64 interval arrays for elementary complex exponential.

Only IEEE-754 basic operations are used in the proofs. exp/sin/cos are
bounded Taylor polynomials after range reduction, not platform libm calls.
Use the default round-to-nearest mode; nextafter expands every operation.
"""
import numpy as np
import mpmath as mp
from math import factorial

NINF=-np.inf; PINF=np.inf

def dn(x): return np.nextafter(x,NINF)
def up(x): return np.nextafter(x,PINF)
def exact(x):
    x=np.asarray(x,dtype=float);return x,x

def enc(x):
    x=np.asarray(x,dtype=float);return dn(x),up(x)

def bounds_iv(x):
    # Float conversion rounds midpoint-ish endpoints; one ulp outward covers it.
    return float(dn(float(x.a))),float(up(float(x.b)))

mp.iv.dps=60
LN2=bounds_iv(mp.iv.ln(2)); PI=bounds_iv(mp.iv.pi)

def add(a,b):return dn(a[0]+b[0]),up(a[1]+b[1])
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
    z=np.stack(np.broadcast_arrays(a[0]*b[0],a[0]*b[1],a[1]*b[0],a[1]*b[1]))
    return dn(z.min(axis=0)),up(z.max(axis=0))
def sq(a):
    lo=np.where((a[0]<=0)&(a[1]>=0),0,np.minimum(a[0]*a[0],a[1]*a[1]));hi=np.maximum(a[0]*a[0],a[1]*a[1])
    return np.maximum(0,dn(lo)),up(hi)
def div(a,b):
    if np.any((b[0]<=0)&(b[1]>=0)):raise ArithmeticError('interval division by zero')
    return mul(a,(dn(1/b[1]),up(1/b[0])))
def scale(a,x):return mul(a,exact(x))
def rational(p,q=1):
    # Integers outside binary64's exact range must themselves be enclosed.
    pp=np.asarray(p,dtype=float);qq=np.asarray(q,dtype=float)
    pi=enc(pp) if np.any(abs(pp)>2**53) else exact(pp)
    qi=enc(qq) if np.any(abs(qq)>2**53) else exact(qq)
    return div(pi,qi)

def cadd(a,b):return add(a[0],b[0]),add(a[1],b[1])
def cneg(a):return neg(a[0]),neg(a[1])
def csub(a,b):return cadd(a,cneg(b))
def cmul(a,b):return sub(mul(a[0],b[0]),mul(a[1],b[1])),add(mul(a[0],b[1]),mul(a[1],b[0]))
def cscale(a,x):return scale(a[0],x),scale(a[1],x)
def cdiv(a,b):
    d=add(sq(b[0]),sq(b[1]));num=cmul(a,(b[0],neg(b[1])))
    return div(num[0],d),div(num[1],d)
def creal(a):return a[0]
def cabs2(a):return add(sq(a[0]),sq(a[1]))
def fromreal(a):return a,exact(0)

def exp(a):
    k=np.rint((a[0]+a[1])/(2*sum(LN2)/2)).astype(int)
    r=sub(a,mul(exact(k),LN2));
    if np.max(np.maximum(abs(r[0]),abs(r[1])))>.36:raise ArithmeticError('bad exponential reduction')
    # degree 24, remainder < exp(.36)*.36**25/25! < 10^-34.
    acc=rational(1,factorial(24))
    for j in range(23,-1,-1):acc=add(mul(acc,r),rational(1,factorial(j)))
    acc=add(acc,(-1e-34,1e-34));return dn(np.ldexp(acc[0],k)),up(np.ldexp(acc[1],k))

def sincos(a):
    twopi=scale(PI,2); k=np.rint((a[0]+a[1])/(sum(twopi))).astype(int)
    r=sub(a,mul(exact(k),twopi));
    if np.max(np.maximum(abs(r[0]),abs(r[1])))>3.142:raise ArithmeticError('bad trigonometric reduction')
    r2=sq(r)
    ca=rational((-1)**22,factorial(44));sa=rational((-1)**22,factorial(45))
    for j in range(21,-1,-1):
        ca=add(mul(ca,r2),rational((-1)**j,factorial(2*j)))
        sa=add(mul(sa,r2),rational((-1)**j,factorial(2*j+1)))
    # <= 3.142^46/46! for cos and 3.142^47/47! for sin, both < 10^-33.
    return add(mul(sa,r),(-1e-33,1e-33)),add(ca,(-1e-33,1e-33))

def cexp(a):
    ee=exp(a[0]);ss,cc=sincos(a[1]);return mul(ee,cc),mul(ee,ss)

if __name__=='__main__':
    rng=np.random.default_rng(109);x=rng.uniform(-8,8,1000);y=rng.uniform(-100,100,1000)
    z=cexp((enc(x),enc(y)));mp.mp.dps=65
    for j in range(1000):
        v=mp.exp(mp.mpc(float(x[j]),float(y[j])))
        assert mp.mpf(float(z[0][0][j]))<=v.real<=mp.mpf(float(z[0][1][j]))
        assert mp.mpf(float(z[1][0][j]))<=v.imag<=mp.mpf(float(z[1][1][j]))
    print('PASS complex exponential enclosures against 1000 high-precision evaluations')
