"""Independent quadrature diagnostics + exact negative tests.
The quadrature checks are diagnostics, not interval proofs or analytic validation.
"""
import json,gzip,copy
from pathlib import Path
from certificate_io import load_data,check_input
from shadow_certificate import regenerate,shadow_plan
from fractions import Fraction
import mpmath as mp
mp.mp.dps=65
PKG=Path(__file__).resolve().parents[1]
S=10**16

def q(x):
    a=Fraction(str(x));return mp.mpf(a.numerator)/a.denominator

def f(g,t):
    if t<0 or t>=2*g:return mp.mpf('0')
    u=t/(2*g);return mp.mpf(16)/15*g**5*(1-u)**3*(1+3*u+u*u)

def trans(g,z):
    return mp.quad(lambda t:f(g,t)*mp.exp(-z*t),[0,g,2*g])

with gzip.open(PKG/'results/shadow_local_4.25.jsonl.gz','rt')as fh:
    records=[json.loads(x)for x in fh]
base=load_data('selected_inputs.json')['2063'][0][1]
par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')
for rec,br in zip(records,shadow_plan(base)):
    rec['input']=check_input(regenerate(base,'4.25',br,par,rec['input']['lambda_den']),rec['input'])
gG=q('1.7504');gZ=q('1.09006');eps=q('.1385')*(gZ/gG)**5
eta=q('.000001');checks=[]
for idx in [0,1,20,21,50,51,78,79]:
    rec=records[idx];inp=rec['input'];sh=inp['shadow'];s=q(inp['shift']);h=q(sh['hi']);r=q(sh['local_minimum'])
    RG=trans(gG,-s)
    RB=mp.quad(lambda t:f(gZ,t)**2/f(gG,t)*mp.exp(s*t),[0,gZ,2*gZ])
    RB+=2*eps*trans(gZ,-s)+eps*eps*RG
    N=mp.sqrt(RG*RB)
    phi=q('1/4'if sh['real']else'1/3')
    def feat(t):return (trans(gZ,t-s)+eps*trans(gG,t-s)-phi*(f(gZ,0)+eps*f(gG,0))/2)/N-eta
    vg=feat(h);vc=feat(r)
    assert q(sh['v_global'])/S<=vg
    assert q(sh['v_existing_cap'])/S>=vc
    assert vg>=vc
    chosen=max((b for b in rec['certificate']if'upper'in b),key=lambda x:x['upper'])
    for t in [q(chosen['a'])/10**6,q(chosen['a']+chosen['b'])/(2*10**6),q(chosen['b'])/10**6]:
        D=q(inp['D'])/S;Dh=q(sh['diagonal'])/S
        delta=sh['ng']*(D/Dh*max(vg-t,0)**2-max(vc-t,0)**2)
        assert delta+mp.mpf('1e-60')>=q(chosen['bonus'])/S
    checks.append(dict(index=idx,RG=mp.nstr(RG,52),N=mp.nstr(N,52),global_feature=mp.nstr(vg,52),local_cap=mp.nstr(vc,52),bonus_checked=chosen['bonus']))
# Independent exact evaluation of the reported binding objective.
report=json.loads((PKG/'results/shadow_local_4.25_verification.json').read_text());b=report['binding'];t=b['tau'];DS=10**12
value=Fraction(b['first']+5*10**10,S)+Fraction(t['Y']*b['far_budget']+t['Z']*b['near_budget'],DS*S)
assert value<=Fraction(report['maximum_numerator'],S)<1
# Corrupted inputs must not be accepted. This calls no optimizer.
from shadow_certificate import verify_records
base=load_data('selected_inputs.json')['2063'][0][1]
par=dict(method='mixture',gg='1.7504',gz='1.09006',mix='.1385',zeta='3')
negative=[]
def rejected(label,rr,regen=False):
    try:verify_records(rr,base,'4.25',par,regen)
    except (AssertionError,ValueError):negative.append(label);return
    raise AssertionError('invalid certificate accepted: '+label)
rejected('missing global alternative',records[:-1])
rr=copy.deepcopy(records);rr[0]['certificate']=rr[0]['certificate'][1:];rejected('missing threshold interval',rr)
rr=copy.deepcopy(records)
for row in rr[0]['certificate']:
    if'upper'in row:row['Y']=row['Z']=0;break
rejected('zero dual coefficients',rr)
rr=copy.deepcopy(records);rr[0]['input']['shadow']['v_global']+=10**12;rejected('inflated global feature',rr,True)
out=dict(status='PASS: independent diagnostics and corruption tests',scope='Quadrature diagnostics, not interval or Dirichlet proofs',quadrature_cases=checks,bonus_endpoint_checks=24,exact_binding_value=str(value),rejected=negative)
(PKG/'results/independent_hidden_checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
