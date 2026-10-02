"""Source-certified parent implications, with refinable rational subcells.

The original v3 source audit supplies BASE. Two extra complex-character
rows are Table 2' (X p.62). Real-character/nonreal-zero improvements use
Table 3 (X p.45). No interpolated source bounds are used.
"""
from fractions import Fraction as Q
from case_cover import PARENTS as BASE
COMPLEX_PRIME=[('.76','.89'),('.80','.84')]
REAL_COMPLEX_PRIME=[('.66','1.67'),('.70','1.59'),('.74','1.52'),('.78','1.46'),
 ('.82','1.40'),('.86','1.35'),('.90','1.30'),('.94','1.25'),('.98','1.21'),
 ('1.02','1.17'),('1.06','1.13'),('1.099','1.099')]
PARENTS=[]
for kind,aa,bb,pp,rr in BASE:
    a,b,p,r=map(Q,(aa,bb,pp,rr))
    table=COMPLEX_PRIME if kind=='complex' else REAL_COMPLEX_PRIME if kind=='rc' else []
    points=sorted({a,b}|{Q(t) for t,v in table if a<Q(t)<b})
    for lo,hi in zip(points,points[1:]):
        applicable=[Q(v) for t,v in table if hi<=Q(t)]
        PARENTS.append((kind,lo,hi,max([p]+applicable),r))

def cell(parent,lo,hi):
    kind,a,b,p,r=PARENTS[parent];lo=Q(lo);hi=Q(hi)
    assert a<=lo<hi<=b
    return {'parent':parent,'kind':kind,'lo':str(lo),'hi':str(hi),
            'lp':str(max(p,lo)),'source_l2':str(max(r,lo))}

def roots(width=Q('.01')):
    out=[]
    for j,(kind,a,b,p,r) in enumerate(PARENTS):
        lo=a
        while lo<b:
            hi=min(b,lo+width);out.append(cell(j,lo,hi));lo=hi
    return out

def check_first_cover(cs):
    for c in cs:
        assert c==cell(c['parent'],c['lo'],c['hi']),'unsupported source implication'
    for kind,start in [('rr',Q('.1')),('rc',Q('.628')),('complex',Q('.44'))]:
        subset=sorted((c for c in cs if c['kind']==kind),key=lambda c:Q(c['lo']))
        pos=start
        for c in subset:
            assert Q(c['lo'])==pos;pos=Q(c['hi'])
        assert pos==Q('1.5')
    return True
