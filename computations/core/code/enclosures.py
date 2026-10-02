"""Outward elementary arithmetic for the v4 step-kernel proof.

base_enclosures supplies explicitly bounded Taylor series, integration
remainders, and the minimum-principle supremum enclosure from v3.
"""
from base_enclosures import *
from config_v4 import T,BETA,C1,C2,THETA,EPS0,ALPHA
class RigorousWeights:
    r_integral=staticmethod(__import__('base_enclosures').RigorousWeights.r_integral)
    exp_integral=staticmethod(__import__('base_enclosures').RigorousWeights.exp_integral)
    J_i=__import__('base_enclosures').RigorousWeights.J_i
    winv=__import__('base_enclosures').RigorousWeights.winv
    w=__import__('base_enclosures').RigorousWeights.w
    def __init__(self,L='4.58'):
        self.L=I(L);self.T=I(T);self.m=len(BETA);self.k=self.T/self.m
        self.beta=list(map(I,BETA));self.A=self.L-2*self.T
        self.H0=(self.k*sum(self.beta))**2
        self.cross=[self.beta[i]*sum(self.beta[i+1:]) for i in range(self.m)]
        self.c1=I(C1);self.c2=I(C2);self.theta=I(THETA);self.eps=I(EPS0);self.M=10
        self.u=I(Fraction(1,3))+2*self.c1;self.v=self.u+self.c2
        self.x=I(Fraction(2,3))+3*self.c1+self.c2
        xr=Fraction(2,3)+3*C1+C2;ur=Fraction(1,3)+2*C1
        zz=[1/(Fraction(1,2)+10*(xr-ur)/C2-i) for i in range(1,11)]
        self.alpha=list(ALPHA)
        self.J=[self.J_i(i) for i in range(10)]
        self.V=100/(self.c1*self.c2**2)*sum(I(a)**2*j for a,j in zip(self.alpha,self.J))
    @lru_cache(maxsize=None)
    def B(self,l,real=False):
        l=I(l);k=self.k;e=iv.exp(-2*k*l)
        if upper(abs(l),10**30)==0:U=2*k;Q0=k*k
        else:U=(1-e)/l;Q0=k/l-U/(2*l)
        out=I(0);power=I(1);den=8 if real else 6
        for b,c in zip(self.beta,self.cross):
            out+=power*(b*b*(Q0+U/den)+k*U*c);power*=e
        return out/self.H0
    @lru_cache(maxsize=None)
    def h(self,l):
        l=I(l);k=self.k
        if upper(abs(l),10**30)==0:return I(1)
        e=iv.exp(-k*l);power=I(1);s=I(0)
        for b in self.beta:s+=b*power;power*=e
        return ((1-e)*s/l)**2/self.H0
    @lru_cache(maxsize=None)
    def G(self,l,real=False):return iv.exp(-self.A*I(l))*self.B(l,real)
    def first(self,c,inside):
        a=I(c['lo']);p=I(c['lp']);n=2 if c['kind']=='complex' else 1
        B=self.B(c['lo'],c['kind']!='complex')
        if not inside:return n*iv.exp(-self.A*p)*B
        alpha=2 if c['kind']=='rc' else 1;h=alpha*self.h(c['lo'])
        diff=I(Fraction(max(0,upper(B-h)),S))
        return n*(iv.exp(-self.A*p)*diff+iv.exp(-self.A*a)*h)
