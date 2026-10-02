"""Floating proposals of sieve-near test parameters (not used by verification).

For a safe anchor s1 and response anchor s, choose (gamma, g1, t0, mu) of the
water-filling sieve test to minimize the crowd bound at lambda=s and s+0.05.
Results are cached in params_cache.json (rational strings).
"""
import json, os
from fractions import Fraction as Q
from pathlib import Path
import numpy as np
from scipy.optimize import minimize

HERE = Path(__file__).resolve().parent
CACHE = HERE/'params_cache_broad.json'
PHI = 1/3
TS = np.linspace(0, 8.0, 8001)


def trap(y):
    return np.trapezoid(y, TS)


def fnorm(g):
    u = np.clip(TS/(2*g), 0, 1)
    return np.where(TS <= 2*g, (1-u)**3*(1+3*u+u*u), 0.0)


def Ftrans(f, z):
    return trap(f*np.exp(-z*TS))


def model(gZ, g1, t0, s, s1, mu):
    f = fnorm(gZ); a = fnorm(g1)*np.exp(s1*TS)
    with np.errstate(all='ignore'):
        kk = np.where(TS > t0, 2*TS/np.maximum(TS-PHI, 1e-12), np.inf)
        H = np.where(np.isfinite(kk), np.maximum(0, np.exp(s*TS)*f/np.sqrt(mu*kk)-a), 0.0)
    om = a+H; m = f > 0
    if np.any(om[m] <= 0):
        return None
    with np.errstate(all='ignore'):
        IB = trap(np.where(m, np.exp(2*s*TS)*f**2/np.where(om > 0, om, 1), 0))
        Df = trap(a)+trap(np.where(H > 0, kk*H, 0))
    d = (PHI/2)/Df
    N = np.sqrt(IB*Df)
    return f, N, d, 1-d


def crowd(par, lam):
    gZ, g1, t0, s, s1, mu = par
    mm = model(gZ, g1, t0, s, s1, mu)
    if mm is None:
        return np.inf
    f, N, d, D = mm
    v = (Ftrans(f, lam-s)-1/6)/N
    return np.inf if v*v <= d else D/(v*v-d)


def optimize(s1, s):
    targets = [s+0.005, s+0.1, s+0.2, s+0.3]

    def obj(x):
        gZ, g1, t0, lm = x
        if not (0.3 <= gZ <= 2.5 and 0.1 <= g1 <= 3.0 and PHI+0.004 < t0 < 2*gZ-0.05 and 2*g1 >= t0+0.01):
            return 1e6
        mm = model(gZ, g1, t0, s, s1, 10**lm)
        if mm is None:
            return 1e6
        f, N, d, D = mm
        tot = 0
        for lam in targets:
            v = (Ftrans(f, lam-s)-1/6)/N
            if v <= 0:
                return 1e5
            tot += 1e3*(1+d/(v*v)) if v*v <= d else D/(v*v-d)
        return np.log(tot)
    best = None
    for x0 in [[0.9, 1.4, 0.35, -1.3], [0.9, 1.0, 0.36, -1.0], [1.0, 0.7, 0.35, 0.0],
               [0.85, 1.6, 0.345, -1.7], [1.1, 1.3, 0.38, -2.0], [0.8, 1.8, 0.34, -2.3]]:
        r = minimize(obj, x0, method='Nelder-Mead', options=dict(maxiter=900, xatol=1e-4, fatol=1e-6))
        if best is None or r.fun < best.fun:
            best = r
    gZ, g1, t0, lm = best.x
    return dict(gamma=str(Q(gZ).limit_denominator(1000)), g1=str(Q(g1).limit_denominator(1000)),
                t0=str(max(Q(t0).limit_denominator(1000), Q(336, 1000))), mu=str(Q(10**lm).limit_denominator(10**6)),
                s=str(Q(s).limit_denominator(1000)), s1=str(Q(s1).limit_denominator(1000)), score=float(np.exp(best.fun)))


_cache = None


def params(s1, s):
    global _cache
    if _cache is None:
        _cache = json.loads(CACHE.read_text()) if CACHE.exists() else {}
    key = f'{Q(s1)}|{Q(s)}'
    if key not in _cache:
        _cache[key] = optimize(float(Q(s1)), float(Q(s)))
        tmp = CACHE.with_suffix('.tmp')
        # merge with concurrent writers
        disk = json.loads(CACHE.read_text()) if CACHE.exists() else {}
        disk.update(_cache)
        tmp.write_text(json.dumps(disk, sort_keys=True, indent=0))
        os.replace(tmp, CACHE)
        _cache = disk
    p = dict(_cache[key])
    p.pop('score', None)
    return p
