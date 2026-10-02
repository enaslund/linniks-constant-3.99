"""Outward-enclosed elementary inputs. No scipy quadrature is used here.

All transcendentals use mpmath.iv with 50 decimal working digits. Taylor
remainders and the supremum interpolation/tail bounds are explicit. Scalar
exports are exact integer lower/upper bounds on a fixed 10**16 grid.
"""
from fractions import Fraction
from functools import lru_cache
import math,heapq
from mpmath import iv
iv.dps=50
S=10**16

def I(x):
    if isinstance(x,Fraction):return iv.mpf(x.numerator)/x.denominator
    if isinstance(x,float):return iv.mpf(str(x))
    return iv.mpf(x)

def _scaled_int(t,scale,up):
    sign,man,exp,bc=t
    if bc<0:raise ValueError('Nonfinite interval')
    n=(-1 if sign else 1)*man*scale
    if exp>=0:return n*(1<<exp)
    den=1<<(-exp)
    return -((-n)//den) if up else n//den

def lower(x,scale=S):return _scaled_int(x._mpi_[0],scale,False)
def upper(x,scale=S):return _scaled_int(x._mpi_[1],scale,True)
def cap(x):return I(Fraction(upper(x),S))
def floor_fraction(x):return x.numerator//x.denominator
def ceil_fraction(x):return -((-x.numerator)//x.denominator)
@lru_cache(maxsize=None)
def taylor_coefficients(N):
    return tuple(I(Fraction(30,(k+1)*(k+3)*(k+4)*(k+6)*math.factorial(k))) for k in range(N))

class RigorousTest:
    def __init__(self,gamma):
        self.g=Fraction(gamma);self.gi=I(self.g);self.T=2*self.gi
        self.f0=16*self.gi**5/15
    def F(self,z):
        # z is a real exact rational or an interval complex scalar.
        if isinstance(z,(int,str,Fraction,float)):z=I(z)
        if upper(abs(z),10**6)<500000:
            N=42;w=-z*self.T
            # Same 42-term Taylor polynomial, evaluated by interval Horner.
            # Exact rational coefficients are enclosed once and cached.
            co=taylor_coefficients(N);s=co[-1]
            for ck in reversed(co[:-1]):s=s*w+ck
            approx=self.f0*self.T*s
            # Integral of f times the absolute exponential remainder.
            a=abs(z)*self.T
            err=(self.f0*self.T*I(Fraction(5,12)))*iv.exp(a)*a**N/math.factorial(N)
            # Use a rectangular complex enclosure when needed.
            er=I(Fraction(upper(err,10**45),10**45))
            delta=iv.mpf([-er.b,er.b])
            if hasattr(z,'imag') and upper(abs(z.imag),10**30)>0:
                return approx+iv.mpc(delta,delta)
            return approx+delta
        g=self.gi;e=iv.exp(-2*g*z)
        return (16*g**5/(15*z)-8*g**3/(3*z**3)
                +4*g*g*(1+e)/z**4+4*(-1+e+2*g*z*e)/z**6)
    def exponential_moment(self,k,d):
        # int t^k f(t) exp(d*t) dt, d>=0.
        d=I(d);N=70;term=I(1);s=I(0);a=d*self.T
        for j in range(N):
            r=k+j
            s+=term*30/((r+1)*(r+3)*(r+4)*(r+6))
            term*=a/(j+1)
        base=self.f0*self.T**(k+1)
        m0=base*30/((k+1)*(k+3)*(k+4)*(k+6))
        err=m0*iv.exp(a)*a**N/math.factorial(N)
        # Series coefficients are positive. Only an upper remainder is needed.
        return base*s+iv.mpf([0,I(Fraction(upper(err,10**45),10**45)).b])
    def C_upper(self,d,tolerance=Fraction(1,10**6)):
        """Bound -Re F(z) throughout Re z >= -d, with Re F>=0 at Re z>=0.

        Minimum principle reduces to the line Re z=-d. The line is covered
        by adaptive linear interpolation, with |g''|<=int t^2*f*exp(d*t),
        and a proved rational-decay tail from |Im z|>=20.
        """
        d=Fraction(d)
        if d<=0:return 0,{'evaluations':0,'C_int':0,'method':'right-half-plane positivity'}
        M2=upper(self.exponential_moment(2,d));T=Fraction(20)
        di=I(d);g=self.gi;e=iv.exp(2*g*di);Ti=I(T)
        tail=(self.f0*di/Ti**2+8*g**3/(3*Ti**3)
              +4*g*g*(1+e)/Ti**4+4*(1+e)/Ti**6+8*g*e/Ti**5)
        tail_u=upper(tail)
        vals={}
        def at(t):
            if t not in vals:
                z=iv.mpc(-I(d),I(t));x=-self.F(z).real
                vals[t]=(lower(x),upper(x))
            return vals[t]
        def interval(a,b):
            u=max(at(a)[1],at(b)[1])+ceil_fraction(Fraction(M2,8)*(b-a)**2)
            return (-u,a,b)
        heap=[]
        for j in range(200):heap.append(interval(Fraction(j,10),Fraction(j+1,10)))
        heapq.heapify(heap)
        best=max(0,max(v[0] for v in vals.values()))
        tol=ceil_fraction(tolerance*S)
        while -heap[0][0]>max(best,tail_u)+tol:
            neg,a,b=heapq.heappop(heap);m=(a+b)/2
            at(m);best=max(best,at(m)[0]);heapq.heappush(heap,interval(a,m));heapq.heappush(heap,interval(m,b))
            if len(vals)>100000:raise RuntimeError('Supremum refinement failed')
        C=max(0,tail_u,-heap[0][0])
        return C,{'evaluations':len(vals),'C_int':C,'tail_int':tail_u,'M2_int':M2,
                  'tolerance':str(tolerance),'method':'minimum principle + second derivative + tail'}

class RigorousWeights:
    def __init__(self,L='4.7'):
        self.L=I(L);self.K=I('0.13');self.b1=I('0.65');self.b2=I('0.33')
        self.c1=I('0.1');self.c2=I('0.26');self.theta=I('1.05');self.eps=I('0.0000001');self.M=10
        self.u=I(Fraction(1,3))+2*self.c1;self.v=self.u+self.c2
        self.x=I(Fraction(2,3))+3*self.c1+self.c2
        self.A=self.L-6*self.K;self.H0=self.K**2*(1+self.b1+self.b2)**2
        # Rational published coefficients, rather than a numerical minimizer.
        xr=Fraction(2,3)+Fraction(3,10)+Fraction(26,100)
        ur=Fraction(1,3)+Fraction(2,10);c2r=Fraction(26,100)
        zz=[1/(Fraction(1,2)+10*(xr-ur)/c2r-i) for i in range(1,11)]
        self.alpha=[z/sum(zz) for z in zz]
        self.J=[self.J_i(i) for i in range(10)]
        self.V=100/(self.c1*self.c2**2)*sum(I(a)**2*j for a,j in zip(self.alpha,self.J))
    @staticmethod
    def r_integral(n,a,lo,hi):
        # int_lo^hi r^n exp(a*r^2) dr, all endpoints nonnegative.
        N=64;term=I(1);s=I(0)
        lp=lo**(n+1);hp=hi**(n+1);ll=lo**2;hh=hi**2
        for j in range(N):
            s+=term*(hp-lp)/(2*j+n+1)
            term*=a/(j+1);lp*=ll;hp*=hh
        rad=abs(a)*hi**2
        measure=(hi**(n+1)-lo**(n+1))/(n+1)
        er=measure*iv.exp(rad)*rad**N/math.factorial(N)
        e=I(Fraction(upper(er,10**45),10**45))
        return s+iv.mpf([-e.b,e.b])
    @staticmethod
    def exp_integral(a,lo,hi):
        if upper(abs(a),10**20)<=1:
            # Stable and rigorous when a straddles zero: enclose integrand
            # over the entire integration interval, whose endpoints are positive.
            return (hi-lo)*iv.exp(a*iv.mpf([lo.a,hi.b]))
        return (iv.exp(a*hi)-iv.exp(a*lo))/a
    def J_i(self,i):
        h=self.c2/10;eps=self.eps;theta=self.theta
        ra=iv.sqrt(i*h+eps);rb=iv.sqrt((i+1)*h+eps);rv=iv.sqrt(self.c2+eps)
        first=(self.r_integral(2,theta,ra,rb)-(i*h+eps)*self.r_integral(0,theta,ra,rb)
               +h*self.r_integral(0,theta,rb,rv))
        return 2*iv.exp(theta*(self.u-eps))*first+h/rv*self.exp_integral(theta,self.v,self.x)
    @lru_cache(maxsize=None)
    def winv(self,l):
        l=I(l);a=2*l-self.theta
        ra=iv.sqrt(self.eps);rv=iv.sqrt(self.c2+self.eps)
        return (2*iv.exp(a*(self.u-self.eps))*self.r_integral(2,a,ra,rv)
                +rv*self.exp_integral(a,self.v,self.x))
    @lru_cache(maxsize=None)
    def w(self,l):return 1/self.winv(l)
    def B(self,l):
        l=I(l);k=self.K;b1=self.b1;b2=self.b2;e=iv.exp(-2*k*l)
        if upper(abs(l),10**30)==0:
            T=2*k;Q=k*k
        else:
            T=(1-e)/l;Q=k/l-T/(2*l)
        return ((e**2+b1*b1*e+b2*b2)*(Q+T/6)+k*T*(b1*e+b2+b1*b2))/self.H0
    def h(self,l):
        l=I(l);k=self.K
        if upper(abs(l),10**30)==0:return I(1)
        return ((iv.exp(-2*k*l)+self.b1*iv.exp(-k*l)+self.b2)*(1-iv.exp(-k*l))/l)**2/self.H0
    @lru_cache(maxsize=None)
    def G(self,l):return iv.exp(-self.A*I(l))*self.B(l)
    def first(self,c,inside):
        a=I(c['lo']);p=I(c['lp']);n=2 if c['kind']=='complex' else 1
        if not inside:return n*iv.exp(-self.A*p)*self.B(c['lo'])
        alpha=2 if c['kind']=='rc' else 1
        B=self.B(c['lo']);h=alpha*self.h(c['lo'])
        # Exact monotone formula, plus positive-part interval enclosure.
        diff=I(Fraction(max(0,upper(B-h)),S))
        return n*(iv.exp(-self.A*p)*diff+iv.exp(-self.A*a)*h)

if __name__=='__main__':
    w=RigorousWeights('4.68')
    print('V enclosure:',w.V)
    print('far weight at lambda=.525:',w.w(Fraction(21,40)))
