"""Fixed rational witnesses. Optimization is not part of verification."""
from fractions import Fraction as Q
ETA=Q(1,10**6)
FINAL=5*ETA
T=Q('.416829')
BETA=tuple(map(Q,['.02318741','.07159337','.12265085','.17627704',
 '.23237155','.29081583','.35147264','.41418551','.47877833','.54505502',
 '.61279917','.68177389','.75172165','.82236428','.89340300','.96451862']))
C1=Q('.09035');C2=Q('.235968');THETA=Q('1.28683');EPS0=Q('.0000001')
_a=tuple(map(Q,['.0788827218','.0849386148','.0895629779','.0938231516',
 '.0979710491','.1021284916','.1063732939','.1107651869','.1153565492']))
ALPHA=_a+(1-sum(_a),)
assert len(ALPHA)==10 and all(a>0 for a in ALPHA) and sum(ALPHA)==1
SMOOTH_DELTA=Q(1,10**18)
DUAL_SCALE=10**12;TAU_SCALE=10**6

def gamma_for(a,s):
 return Q('1.235') if Q('.78')<=a<=Q('1.1') else Q('1.27') if Q('.58')<=a<Q('.78') else Q('1.62')-Q('.55')*s
