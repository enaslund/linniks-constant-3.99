"""Fast *proposal* for two-resource LPs; all acceptance remains exact.

An upper hull produces a floating candidate dual. Every original rational
column is then checked and any deficit repaired in integer arithmetic.
"""
from fractions import Fraction as Q
import math,numpy as np
from config_v4 import DUAL_SCALE
from base_enclosures import S,ceil_fraction
from certify_v4 import near_data

def hull_dual(W,C,G,F,B):
    # Normalize by far cost; the zero-near-cost tail guarantees a baseline.
    ww=np.asarray(W,dtype=float);xx=np.asarray(C,dtype=float)/ww;yy=np.asarray(G,dtype=float)/ww
    order=np.lexsort((-yy,xx));h=[]
    for j in order:
        x,y=xx[j],yy[j]
        if h and x==h[-1][0]:continue
        while len(h)>=2:
            a,b=h[-2],h[-1]
            if (b[1]-a[1])*(x-b[0])<=(y-b[1])*(b[0]-a[0]):h.pop()
            else:break
        h.append((x,y))
    peak=max(range(len(h)),key=lambda j:h[j][1]);r=B/F
    if r>=h[peak][0]:return h[peak][1],0.
    for j in range(peak):
        a,b=h[j],h[j+1]
        if a[0]<=r<=b[0]:
            z=(b[1]-a[1])/(b[0]-a[0]);return max(0.,a[1]-z*a[0]),max(0.,z)
    # A conservative proposal always exists: use only the far constraint.
    return max(yy),0.

def dual_bound(inp,ta,tb):
    C,B=near_data(inp,ta,tb)
    if B<0:return {'a':ta,'b':tb,'excluded':True,'budget':B}
    W=[r[2] for r in inp['rows']];G=[r[3] for r in inp['rows']];F=inp['far_budget']
    if F<0:return {'a':ta,'b':tb,'excluded_far':True,'budget':F}
    if F==0:Y=max(ceil_fraction(Q(g*DUAL_SCALE,w)) for g,w in zip(G,W));Z=0
    else:
        y,z=hull_dual(W,C,G,F,B)
        Y=max(0,math.ceil(y*DUAL_SCALE)+1);Z=max(0,math.ceil(z*DUAL_SCALE)+1)
    repair=max(0,max(ceil_fraction(Q(g*DUAL_SCALE-Y*w-Z*c,w)) for w,c,g in zip(W,C,G)));Y+=repair
    assert all(Y*w+Z*c>=g*DUAL_SCALE for w,c,g in zip(W,C,G))
    U=ceil_fraction(Q(Y*F+Z*B,DUAL_SCALE))+inp['first']+inp['final']
    return {'a':ta,'b':tb,'Y':Y,'Z':Z,'upper':U}
