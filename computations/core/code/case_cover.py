"""Exact finite cover. Imported implications are stated in SOURCE_INPUTS.md.

No third-zero bound or integer count is used.
Further lambda_2 intervals reserve a second family; they do not import new conditional tables.
All intervals are left closed, right open; a boundary may instead be covered
by both adjacent rows without changing the proof.
"""
from fractions import Fraction as Q
PARENTS=[
('rr','.1','.2','2.195','2.01'),('rr','.2','.348','2.195','1.42'),
('rr','.348','.6','1.832','.92'),('rr','.6','.8','1.63','.745'),('rr','.8','1.5','1.294','.8'),
('rc','.628','.78','1.46','.93'),('rc','.78','1.5','1.099','.82'),
('complex','.44','.58','1.36','1.04'),('complex','.58','.64','1.15','.85'),
('complex','.64','.66','1.08','.79'),('complex','.66','.68','1.02','.74'),
('complex','.68','.70','.96','.704'),('complex','.70','.72','.93','.702'),
('complex','.72','.74','.91','.72'),('complex','.74','.78','.86','.74'),
('complex','.78','.82','.83','.78'),('complex','.82','1.5','.827','.82')]

def cases(width=Q(1,100)):
    out=[]
    for row,(kind,a,b,p,l2) in enumerate(PARENTS):
        a,b,p,l2=map(Q,(a,b,p,l2));lo=a
        while lo<b:
            hi=min(lo+width,b)
            out.append({'id':len(out),'parent':row,'kind':kind,'lo':str(lo),'hi':str(hi),
                        'lp':str(max(p,lo)),'l2':str(max(l2,lo))})
            lo=hi
    return out

def check_cover(cs):
    assert cs==cases(), 'Case records differ from the specified rational refinement'
    for kind,start in [('rr',Q(1,10)),('rc',Q(628,1000)),('complex',Q(44,100))]:
        subset=[c for c in cs if c['kind']==kind];p=start
        for c in subset:
            assert Q(c['lo'])==p and Q(c['hi'])>p
            assert Q(c['lp'])>=Q(c['lo']) and Q(c['l2'])>=Q(c['lo'])
            p=Q(c['hi'])
        assert p==Q(3,2)
    return True
