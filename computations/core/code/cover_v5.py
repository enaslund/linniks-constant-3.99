"""Source case cover: previous Xylouris rows plus Heath-Brown Tables 4,7."""
from fractions import Fraction as Q
from cover_v4 import PARENTS as OLD
H_PRIME=[('.3','2.293'),('.35','2.195'),('.4','2.108'),('.45','2.030'),('.5','1.958'),('.55','1.893'),('.6','1.832'),('.65','1.776'),('.7','1.724'),('.75','1.676'),('.8','1.630'),('.85','1.587'),('.9','1.547'),('.95','1.509'),('1','1.473'),('1.05','1.439'),('1.1','1.406'),('1.15','1.375'),('1.175','1.360'),('1.2','1.346'),('1.225','1.331'),('1.25','1.318'),('1.275','1.304'),('1.294','1.294')]
H_SECOND=[('.12','2.56'),('.14','2.39'),('.16','2.25'),('.18','2.12'),('.2','2.01'),('.25','1.77'),('.3','1.58'),('.35','1.42'),('.4','1.29'),('.45','1.18'),('.5','1.08'),('.55','1'),('.6','.92'),('.65','.85'),('.7','.79'),('.745','.745')]
PARENTS=[]
for kind,a,b,p,r in OLD:
    table=H_PRIME+H_SECOND if kind=='rr' else []
    points=sorted({a,b}|{Q(t) for t,v in table if a<Q(t)<b})
    for lo,hi in zip(points,points[1:]):
        ps=[Q(v) for t,v in H_PRIME if hi<=Q(t)] if kind=='rr' else []
        rs=[Q(v) for t,v in H_SECOND if hi<=Q(t)] if kind=='rr' else []
        PARENTS.append((kind,lo,hi,max([p]+ps),max([r]+rs)))
def cell(parent,lo,hi):
    kind,a,b,p,r=PARENTS[parent];lo=Q(lo);hi=Q(hi);assert a<=lo<hi<=b
    return {'parent':parent,'kind':kind,'lo':str(lo),'hi':str(hi),'lp':str(max(p,lo)),'source_l2':str(max(r,lo))}
def roots(width=Q('.01')):
    out=[]
    for j,(kind,a,b,p,r) in enumerate(PARENTS):
        lo=a
        while lo<b:
            hi=min(b,lo+width);out.append(cell(j,lo,hi));lo=hi
    return out
def check_first_cover(cs):
    for c in cs:assert c==cell(c['parent'],c['lo'],c['hi'])
    for kind,start in [('rr',Q('.1')),('rc',Q('.628')),('complex',Q('.44'))]:
        sub=sorted((c for c in cs if c['kind']==kind),key=lambda c:Q(c['lo']));pos=start
        for c in sub:assert Q(c['lo'])==pos;pos=Q(c['hi'])
        assert pos==Q('1.5')
