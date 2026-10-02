"""Family-inclusive near row at the safe anchor (inside leaves).

Mathematical statement: research/arguments/sieve-majorant-near.md, section 2a.
At a response anchor s with s1 <= s <= lambda1^lo, every zero of every character
has parameter >= s.  The local explicit formula at 1 - s/ell + i*gamma_j then
applies to every character, including the distinguished first family and the
reserved second family: all other zeros lie to the left of the test point and
are dropped.  No strip-representative condition and no exceptional-quotient
correction arises (c_j = 0).  The row is the sieve-majorant inequality with
these families included as fixed characters:

  n  first-family characters with feature >= v(lambda1^hi),
  n2 reserved second-family characters with feature >= v(lambda2^hi),

and every ordinary character (all have lambda >= ordinary_lower >= s).  In the
threshold form their terms n (v - tau)_+^2 / D are subtracted from the budget.

The floating proposal chooses the detector and Gram widths (sieve part H = 0)
to minimize the number of characters the row allows at the third-family bound.
"""
import json, os
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
CACHE = HERE/'family_cache.json'
PHI = 1/3
TS = np.linspace(0, 8.0, 8001)


def _trap(y):
    return np.trapezoid(y, TS)


def _fnorm(g):
    u = np.clip(TS/(2*g), 0, 1)
    return np.where(TS <= 2*g, (1-u)**3*(1+3*u+u*u), 0.0)


def allowed_count(gz, g1, s, s1, fixed, lam3):
    """Floating: max number of characters at lam3 permitted by the row (H = 0),
    given fixed [(count, lambda)] characters.  inf if the row says nothing."""
    if not (0.3 <= gz <= 2.5 and gz < g1 <= 3.5):
        return 1e6
    f = _fnorm(gz); om = _fnorm(g1)*np.exp(s1*TS); m = f > 0
    if np.any(om[m] <= 0):
        return 1e6
    IB = _trap(np.where(m, np.exp(2*s*TS)*f**2/np.where(om > 0, om, 1), 0))
    Df = _trap(om)
    d = (PHI/2)/Df; D = 1-d; N = np.sqrt(IB*Df)

    def v(lam):
        return (_trap(f*np.exp(-(lam-s)*TS))-1/6)/N
    tau = np.linspace(0, np.sqrt(d), 600)
    rest = 1-tau**2/d
    for n, lam in fixed:
        rest = rest-n*np.maximum(v(lam)-tau, 0)**2/D
    v3 = v(lam3)
    ok = (rest >= 0) & (tau < v3)
    if not np.any(ok):
        return 0.0 if v3 > 0 else 1e6
    return float(np.max(rest[ok]*D/(v3-tau[ok])**2))


def configuration(inp):
    """(s1, s, fixed characters, lam3) used by the proposal for one inside leaf."""
    from leaf_driver import safe_anchor
    s1 = safe_anchor(inp)
    fixed = [(inp['n'], float(Q(inp['case']['hi'])))]
    if inp['second']:
        fixed.append((inp['second']['n'], float(Q(inp['second']['hi']))))
    else:
        fixed.append((2, float(Q(inp['ordinary_lower']))))   # count row: at most two below lambda3
    lam3 = float(Q(inp['third_lower']))
    return s1, s1, fixed, lam3


def propose(inp):
    s1, s, fixed, lam3 = configuration(inp)
    key = json.dumps([str(s1), str(s), [[n, round(l, 6)] for n, l in fixed], round(lam3, 6)])
    cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    if key in cache:
        return dict(cache[key])
    best = None
    for x0 in ([1.05, 1.15], [0.9, 1.0], [1.2, 1.35], [0.8, 1.3]):
        r = minimize(lambda x: allowed_count(x[0], x[1], float(s), float(s1), fixed, lam3), x0,
                     method='Nelder-Mead', options=dict(maxiter=200, xatol=1e-4, fatol=1e-4))
        if best is None or r.fun < best.fun:
            best = r
    gz, g1 = best.x
    gzq = Q(gz).limit_denominator(1000)
    g1q = max(Q(g1).limit_denominator(1000), gzq+Q(1, 1000))
    p = dict(gamma=str(gzq), g1=str(g1q), t0=str(Q(34, 100)), mu=str(10**9), s=str(s), s1=str(s1),
             allowed=float(best.fun))
    disk = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    disk[key] = p
    tmp = CACHE.with_suffix(f'.tmp{os.getpid()}')
    tmp.write_text(json.dumps(disk, sort_keys=True, indent=0))
    os.replace(tmp, CACHE)
    return dict(p)


def family_row(inp, params):
    """Sieve-row dict {d, D, v, fam} for the rigorous test with the given rational parameters."""
    from leaf_driver import safe_anchor, sieve_test, sieve_rows
    assert inp['height'] == 'inside'
    s1, s = safe_anchor(inp), Q(params['s'])
    assert Q(params['s1']) == s1 and s1 <= s <= Q(inp['case']['lo'])
    lows = [Q(r[0]) for r in inp['rows'] if r[1] != 'infinity']
    assert min(lows) >= s and Q(inp['ordinary_lower']) >= s
    test = sieve_test({k: params[k] for k in ('gamma', 'g1', 't0', 'mu', 's', 's1')})
    row = sieve_rows(inp, test)
    fam = [(int(inp['n']), max(0, test.feature(Q(inp['case']['hi']))))]
    if inp['second']:
        assert Q(inp['second']['lo']) >= s
        fam.append((int(inp['second']['n']), max(0, test.feature(Q(inp['second']['hi'])))))
    row['fam'] = fam
    return row


def shifted_configuration(inp):
    """(s1, s, fixed characters, lam3) for the shifted row: anchor s = inp['shift'] >= lambda1^lo, the
    first family retained above its zero (feature from F(b-s)), second family at min(global l2, s)."""
    from leaf_driver import safe_anchor
    s1 = safe_anchor(inp)
    s = float(Q(inp['shift']))
    fixed = [(inp['n'], float(Q(inp['case']['hi'])))]
    if inp['second']:
        fixed.append((inp['second']['n'], float(Q(inp['second']['hi']))))
    else:
        fixed.append((2, float(Q(inp['ordinary_lower']))))
    return s1, s, fixed, float(Q(inp['third_lower']))


def propose_shifted(inp):
    """Floating (gamma, g1) for the shifted row, minimizing the allowed low-family count.
    Responses use F(lambda-s) also for lambda < s (first family above the anchor)."""
    s1, s, fixed, lam3 = shifted_configuration(inp)
    key = json.dumps(['shifted', str(s1), s, [[n, round(l, 6)] for n, l in fixed], round(lam3, 6)])
    cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    if key in cache:
        return dict(cache[key])
    best = None
    for x0 in ([1.05, 1.15], [0.9, 1.0], [1.2, 1.35], [0.8, 1.3], [1.4, 1.6]):
        r = minimize(lambda x: allowed_count(x[0], x[1], s, float(s1), fixed, lam3), x0,
                     method='Nelder-Mead', options=dict(maxiter=200, xatol=1e-4, fatol=1e-4))
        if best is None or r.fun < best.fun:
            best = r
    gz, g1 = best.x
    gzq = Q(gz).limit_denominator(1000)
    g1q = max(Q(g1).limit_denominator(1000), gzq+Q(1, 1000))
    p = dict(gamma=str(gzq), g1=str(g1q), t0=str(Q(34, 100)), mu=str(10**9), s=str(Q(inp['shift'])),
             s1=str(s1), allowed=float(best.fun))
    disk = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    disk[key] = p
    tmp = CACHE.with_suffix(f'.tmp{os.getpid()}')
    tmp.write_text(json.dumps(disk, sort_keys=True, indent=0))
    os.replace(tmp, CACHE)
    return dict(p)
