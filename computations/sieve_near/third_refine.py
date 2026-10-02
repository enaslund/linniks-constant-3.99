"""Refined third-family bound for real characters with real first zeros.

Source: X (dissertation) Lemma 4.4, proof for chi_1 and rho_1 real.  For
lambda_1 in [0.44, 0.80] and lambda_2 <= 1.176 the inequality (4.31)

    0 <= F(-l2) - F(l3-l2) - F(0) - F(l1-l2) + (9/8) f(0) + eps

holds with X's test f of parameter gamma = 1.04 (case 2 through (4.34), which X
verifies on exactly this range).  X derives Table 10 from it on three coarse
lambda_1 intervals; here the same argument is applied to the leaf's own
interval [a,b].  If lambda_3 <= t then the global lambda_2 lies in
[a, min(t,h)], where h is the upper end of a reserved height-one second family
(as in the repository's complex refinement X_4_28).  For lambda_2 in a cell
[c,c'] and lambda_3 <= t, using that F(-l2)-F(t-l2) increases in l2 (t >= l2)
and that F decreases,

    RHS <= F(-c') - F(t-c') - F(0) - F(b-c) + (9/8) f(0) + eps.

If this is below -MARGIN on a cover of [a, min(t,h)] by cells, lambda_3 > t.
The bound is monotone in t, so the largest admissible t is found by bisection.
Applying the formula on X's own intervals reproduces Table 10
(1.1760 at the cap 1.176, 1.0558, 0.9524).
"""
import sys
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
CORE = Path(__file__).resolve().parents[1]/'core'/'code'
sys.path.insert(0, str(CORE))
from base_enclosures import RigorousTest, I, upper, S

GAMMA = Q(26, 25)
MARGIN = Q(1, 10**5)
T_LO, T_HI = Q(952, 1000), Q(1176, 1000)
_TEST = RigorousTest(GAMMA)


@lru_cache(maxsize=None)
def _F(x):
    return _TEST.F(Q(x))/_TEST.f0


def _cell_ok(c, c2, t, b):
    val = _F(-c2)-_F(t-c2)-_F(0)-_F(b-c)+I(Q(9, 8))
    return upper(val, 10**12) < -MARGIN*10**12


def _cover_ok(t, a, b, h, min_step=Q(1, 20000)):
    top = min(t, h) if h is not None else t
    stack = []
    x = a
    step = Q(1, 100)
    while x < top:
        stack.append((x, min(x+step, top)))
        x += step
    while stack:
        c, c2 = stack.pop()
        if _cell_ok(c, c2, t, b):
            continue
        if c2-c <= min_step:
            return False
        m = (c+c2)/2
        stack.append((c, m)); stack.append((m, c2))
    return True


@lru_cache(maxsize=None)
def rr_third(a, b, h=None):
    """Largest t on the 1/10000 grid in [0.952, 1.176] with lambda_3 > t, or None."""
    a, b = Q(a), Q(b)
    h = None if h is None else Q(h)
    if not (Q(44, 100) <= a <= b <= Q(80, 100)):
        return None
    lo, hi = int(T_LO*10000), int(T_HI*10000)
    if not _cover_ok(Q(lo, 10000), a, b, h):
        return None
    while lo < hi:
        mid = (lo+hi+1)//2
        if _cover_ok(Q(mid, 10000), a, b, h):
            lo = mid
        else:
            hi = mid-1
    return Q(lo, 10000)


def refine_third(inp):
    """Raise the third-family bound of a regenerated inside rr leaf and re-apply the
    repository's third rule (triple_inputs.input_with_third) with the new value."""
    import copy
    c = inp['case']
    if c['kind'] != 'rr':
        return inp
    sec = inp['second']
    t = rr_third(c['lo'], c['hi'], sec['hi'] if sec else None)
    r3 = Q(inp['third_lower'])
    if t is None or t <= r3:
        return inp
    out = copy.deepcopy(inp)
    rows, counts = [], []
    for row, cnt in zip(inp['rows'], inp['count_cost']):
        right = Q(row[1]) if row[1] != 'infinity' else None
        if sec and right is not None and right <= t:
            continue          # reserved local second: every remaining family is >= lambda_3
        rows.append(row)
        counts.append(S if (sec is None and right is not None and right <= t) else cnt)
    out['rows'] = rows
    out['count_cost'] = counts
    out['third_lower'] = str(t)
    out['third_certificate'] = list(inp['third_certificate'])+[dict(
        kind='X_4_31_refined', gamma=str(GAMMA), a=c['lo'], b=c['hi'],
        local_second_upper=(sec['hi'] if sec else None), lower=str(t), margin=str(MARGIN))]
    return out
