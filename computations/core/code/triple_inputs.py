"""Third-family restrictions from the permitted source, with outward arithmetic.
A source inequality and its analytic hypotheses remain imported mathematical inputs.
"""
import sys,json,copy,math
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
ROOT=Path(__file__).resolve().parents[1]
from extension_enclosures import *

@lru_cache(None)
def third_bound(a,b,kind,h=None):
    a,b=Q(a),Q(b);h=None if h is None else Q(h)
    # H Lemma 10.3 / X p.55: lambda_3 >= 6/7-epsilon.
    r=Q('0.857'); evidence=[{'kind':'published_universal','lower':str(r)}]
    if kind=='rr':
        for aa,bb,z in [('.44','.60','1.176'),('.60','.70','1.055'),('.70','.80','.952')]:
            if Q(aa)<=a<=b<=Q(bb) and Q(z)>r:
                r=Q(z);evidence.append({'kind':'X_table_10','row':[aa,bb,z]})
    if kind!='rr':
        for bb,z in [('.52','1.320'),('.54','1.243'),('.56','1.160'),('.58','1.079'),('.60','1.001'),('.62','.933')]:
            if b<=Q(bb) and Q(z)>r:
                r=Q(z);evidence.append({'kind':'X_table_8','row':[bb,z]});break
    if kind=='complex' and Q('.44')<=a<=b<=Q('.85'):
        f=test(Q('1.25'));F0=f.F(0);base=f.F(-b)-F0+I(Q(7,6))*f.f0
        # If lambda_3 <= t, global lambda_2 <= min(t, local second upper h).
        # Eq. (4.28) has RHS <= the expression below on the WHOLE first interval.
        # q sufficiently large makes the epsilon smaller than the chosen fixed margin.
        def margin(t):
            upper2=min(t,h) if h is not None else t
            return lower((f.F(t-b)+f.F(upper2-a)-base)/f.f0)
        lo=int(r*10000);hi=15000
        if lo<=hi and margin(Q(lo,10000))>10**11:
            while lo<hi:
                mid=(lo+hi+1)//2
                if margin(Q(mid,10000))>10**11:lo=mid
                else:hi=mid-1
            t=Q(lo,10000)
            if t>r:
                r=t;evidence.append({'kind':'X_4_28','gamma':'5/4','a':str(a),'b':str(b),'local_second_upper':None if h is None else str(h),'lower':str(t),'normalized_margin_lower':margin(t),'scale':S})
    return str(r),evidence

def input_with_third(inp,L):
    """Keep the near model fixed, update the objective exponent, and add family info.
    Reserved local second => every remaining family is at least global lambda3.
    Unreserved => at most two ordinary CHARACTERS below global lambda3.
    """
    out=copy.deepcopy(inp);c=inp['case'];sec=inp['second'];old=Q(inp['L']);new=Q(L);w=wgt(L)
    r3,proof=third_bound(c['lo'],c['hi'],c['kind'],sec['hi'] if sec else None);r3=Q(r3)
    rows=[];counts=[]
    for row in inp['rows']:
        l=Q(row[0]);right=Q(row[1]) if row[1]!='infinity' else None
        if sec and right is not None and right<=r3:continue
        gg=upper(w.G(l)*(w.winv(l) if right is None else 1))
        rows.append(row[:3]+[gg,row[4]])
        counts.append(S if sec is None and right is not None and right<=r3 else 0)
    cc=dict(c);cc['lp']=str(Q(inp['gap']['lo']) if inp.get('gap') else Q(c['lp']))
    height=inp['height'];first=upper(w.first(cc,height=='inside'))
    out['first_bounds']={height:first}
    if sec:
        sec=copy.deepcopy(sec);sec['contribution']=sec['n']*upper(w.G(Q(sec['lo']),sec['n']==1));out['second']=sec
        first+=sec['contribution']
    out.update(L=L,first=first,rows=rows,third_lower=str(r3),third_certificate=proof,count_cost=counts,count_budget=2*S,third_rule='remove reserved local family; otherwise at most two characters')
    return out

def leaves(tree,path=''):
    if 'record' in tree:yield path,tree['record']['input']
    elif 'children' in tree:
        for j,t in enumerate(tree['children']):yield from leaves(t,path+str(j))

@lru_cache(None)
def cross_envelope(p,a,L):
    """C(p,a)=Re F_p(a-p)/H0, exact step integrals, real a,p.
    No zero-height maximization is used in this scalar evaluation.
    """
    p,a=Q(p),Q(a);ww=wgt(L);assert p>0 and a>0
    kk=ww.k;pi=I(p);ai=I(a);beta=ww.beta
    tails=[I(0)]*len(beta);tail=I(0)
    for j in reversed(range(len(beta))):
        tails[j]=tail
        tail+=beta[j]*(iv.exp(-ai*j*kk)-iv.exp(-ai*(j+1)*kk))/ai
    def int_exp(rate,j):
        rr=I(rate)
        if rate==0:return kk
        return (iv.exp(-rr*j*kk)-iv.exp(-rr*(j+1)*kk))/rr
    ans=I(0)
    for j,beta_j in enumerate(beta):
        ans+=beta_j*(beta_j/ai*int_exp(2*p,j)+(tails[j]-beta_j/ai*iv.exp(-ai*(j+1)*kk))*int_exp(2*p-a,j))
    return 2*ans/ww.H0

def shifted_first(inp,L):
    c=inp['case'];a,b=Q(c['lo']),Q(c['hi']);p=Q(inp['gap']['lo']) if inp.get('gap') else Q(c['lp']);n=inp['n'];kind=c['kind'];real=kind!='complex';alpha=2 if kind=='rc' else 1;w=wgt(L)
    if inp['height']=='outside':
        val=n*iv.exp(-w.A*I(p))*w.B(p,real)
        return upper(val),dict(anchor=str(p),rule='outside_only_distinguished_low_zeros',old_first=inp['first_bounds']['outside'])
    if p<b:
        return inp['first_bounds']['inside'],dict(rule='old_bound_retained',reason='lower second-zero anchor below top of first-zero interval')
    C=cross_envelope(str(p),str(a),L)
    val=n*(alpha*iv.exp(-w.A*I(a))*w.h(a)+iv.exp(-w.A*I(p))*(w.B(p,real)-alpha*C))
    return upper(val),dict(rule='shifted_autocorrelation_coupled_height',anchor=str(p),a=str(a),alpha=alpha,cross_lower=lower(C),cross_upper=upper(C),old_first=inp['first_bounds']['inside'])

def use_shifted(inp,L):
    out=copy.deepcopy(inp);new,proof=shifted_first(inp,L);old=next(iter(inp['first_bounds'].values()));new=min(new,old)
    out['first']+=new-old;out['first_bounds']={inp['height']:new};out['shifted_first_proof']=proof
    return out
