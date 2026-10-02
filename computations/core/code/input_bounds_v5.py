"""Analytically justified rational inputs for single- or paired-zero proof."""
from input_bounds import *
from pair_bounds import paired_constants

def gamma5(a,s,kind):
    if kind=='rr' and Q('.6')<=a<=Q('.85'):return Q('1.227')
    return gamma_for(a,s)

def make_input5(c,L,l2lo=None,second=None,den=500,gap=None,method='single'):
    a,b,p,r=map(Q,(c['lo'],c['hi'],c['lp'],c['source_l2']))
    effective=p if gap is None else Q(gap['lo']);assert effective>=p
    if gap is not None and gap['hi']!='infinity':assert Q(gap['hi'])>effective
    l2=r if l2lo is None else Q(l2lo);s=min(Q('1.9'),effective,l2)
    g=gamma5(a,s,c['kind']);ce=dict(c);ce['lp']=str(effective)
    ret=make_input(ce,L,l2lo,second,den,gamma=g);ret['case']=c
    ret['gap']=gap;ret['method']=method
    if method=='paired':
        assert c['kind'] in ('complex','rc')
        if c['kind']=='rc':pa,ph=a,b
        else:
            assert gap is not None and gap['hi']!='infinity';pa,ph=effective,Q(gap['hi'])
        C,cc=C_bound(g,max(Q(0),s-a))
        vf,Df,pf=paired_constants(g,s,a,b,pa,ph,c['kind'],C)
        ret['v_first']=vf;ret['Df']=Df;ret['pair_certificate']=pf
    else:assert method=='single'
    return ret
