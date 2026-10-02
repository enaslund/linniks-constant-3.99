"""Outward replacement for the published single-zero far weight only.

This module changes no near feature, source case, prime kernel or envelope.
It exports rigorous elementary inputs, not a new analytic density theorem.
"""
import copy
from functools import lru_cache
from fractions import Fraction as Q
from pathlib import Path
import sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent/'core/code'))
from base_enclosures import RigorousWeights as BaseFar,I,S,lower,upper
from config_v4 import ETA,EPS0
from endgame import make_endgame,wgt,parse_params
from compact_records import input_digest,expand_certificate

CANDIDATE=dict(c1='0.0821922',c2='0.2170903',theta='1.4964274',epsilon=str(EPS0),
    alpha=['0.0806195583','0.0862705300','0.0905489307','0.0944644867',
           '0.0982543287','0.1020315591','0.1058668825','0.1098131140',
           '0.1139152197','0.1182153903'])

class RigorousFar:
    r_integral=staticmethod(BaseFar.r_integral)
    exp_integral=staticmethod(BaseFar.exp_integral)
    J_i=BaseFar.J_i
    winv=BaseFar.winv
    w=BaseFar.w
    def __init__(self,parameters):
        assert set(parameters)=={'c1','c2','theta','epsilon','alpha'}
        self.parameters=copy.deepcopy(parameters)
        c1,c2,theta,eps=(Q(parameters[k]) for k in ('c1','c2','theta','epsilon'))
        alpha=tuple(map(Q,parameters['alpha']))
        assert c1>0 and c2>0 and eps>0 and len(alpha)==10
        assert all(a>0 for a in alpha) and sum(alpha)==1
        self.c1,self.c2,self.theta,self.eps=map(I,(c1,c2,theta,eps));self.M=10
        self.u=I(Q(1,3)+2*c1);self.v=I(Q(1,3)+2*c1+c2)
        self.x=I(Q(2,3)+3*c1+c2);self.alpha=alpha
        self.J=[self.J_i(i) for i in range(10)]
        self.V=100/(self.c1*self.c2**2)*sum(I(a)**2*j for a,j in zip(alpha,self.J))

@lru_cache(None)
def _cached_far(c1,c2,theta,epsilon,alpha):
    return RigorousFar(dict(c1=c1,c2=c2,theta=theta,epsilon=epsilon,alpha=list(alpha)))

def far_weights(parameters=None):
    p=CANDIDATE if parameters is None else parameters
    assert set(p)==set(CANDIDATE)
    return _cached_far(p['c1'],p['c2'],p['theta'],p['epsilon'],tuple(p['alpha']))

def replace_far(inp,parameters=None):
    """Regenerate all far-dependent data, including deductions and tail column."""
    assert 'far_parameters' not in inp
    assert not any(k in inp for k in ('hidden_rows','separated_block','same_family_adjustment','shadow','kernel_parameters'))
    assert inp['column_model']=='two-test-published-single-far'
    p=CANDIDATE if parameters is None else parameters
    f=far_weights(p);prime=wgt(inp['L'])
    decay=lower(prime.A-2*f.x)
    assert lower(prime.A-3)>0 and decay>0
    out=copy.deepcopy(inp)
    F=upper((1+I(ETA))*f.V)
    if inp['height']=='inside':F-=inp['n']*lower(f.w(Q(inp['case']['hi'])))
    elif inp['height']!='outside':raise ValueError('Unsupported first-height branch')
    if inp['second']:F-=inp['second']['n']*lower(f.w(Q(inp['second']['hi'])))
    for row in out['rows']:
        if row[1]=='infinity':
            row[2]=S
            row[3]=upper(prime.G(Q(row[0]))*f.winv(Q(row[0])))
        else:row[2]=lower(f.w(Q(row[1])))
    out.update(far_budget=F,far_parameters=copy.deepcopy(p),far_decay_margin=decay)
    return out

def make_far_endgame(spec,L,near_parameters,den=200,far_parameters=None):
    inp=make_endgame(spec,L,near_parameters,den)
    return None if inp is None else replace_far(inp,far_parameters)

def regenerate_far_record(spec,record,L):
    assert set(record)=={'parameters','lambda_den','far_parameters','input_sha256','certificate'}
    p=record['parameters'];assert set(p)=={'method','gg','gz','mix','zeta'}
    assert parse_params({'extension':dict(variant=p['method'],gG=p['gg'],gZ=p['gz'],mix=p['mix'],zeta=p['zeta'])})==p
    den=record['lambda_den'];assert type(den)==int and 50<=den<=10000
    inp=make_far_endgame(spec,L,record['parameters'],den,record['far_parameters'])
    assert inp is not None and input_digest(inp)==record['input_sha256'],'far input hash mismatch'
    return dict(input=inp,certificate=expand_certificate(record['certificate'],inp))

def verify_far_record(spec,record,L):
    """Regenerate interval data, then invoke the existing integer scenario checker."""
    from verify_progress import scenario
    return scenario(regenerate_far_record(spec,record,L))
