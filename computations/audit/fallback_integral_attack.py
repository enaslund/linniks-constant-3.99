#!/usr/bin/env python3
"""Independent numerical attack on the analytic constants of paper section 9.6.

Targets are the existing enclosure routines, parameterized by the 37 rows in
the preceding full-replay report. References use direct quadrature and an
integration-by-parts moment recurrence, not the target transform routines.
Suprema are searched numerically; this is falsification, not interval proof.
The report does not assert a new corpus replay or a global Linnik theorem.
"""
import argparse
import hashlib
import json
import sys
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

import mpmath as mp
from scipy.optimize import minimize_scalar

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'computations/core/code'))
import two_test_enclosures as target
import extension_enclosures as extension

mp.mp.dps = 70
S = 10**16
ETA = mp.mpf('0.000001')
TOL = mp.mpf('1e-40')


def m(x):
    x = Q(x)
    return mp.mpf(x.numerator) / x.denominator


def f(g, t):
    u = t / (2*g)
    return 16*g**5/15 * (1-u)**3 * (1+3*u+u*u)


def transform(g, z):
    """Integrate the polynomial via moments int_0^1 u^k exp(-w*u) du."""
    g, z = m(g), mp.mpc(z)
    w = 2*g*z
    if abs(w) < mp.mpf('0.01'):
        return mp.quad(lambda t: f(g, t)*mp.exp(-z*t), [0, 2*g])
    ew = mp.exp(-w)
    moments = [-mp.expm1(-w)/w]
    for k in range(1, 6):
        moments.append((k*moments[-1]-ew)/w)
    return 32*g**6/15 * (moments[0]-5*moments[2]+5*moments[3]-moments[5])


@lru_cache(None)
def norms(gg, gz, s):
    g, z, ss = map(m, (gg, gz, s))
    rg = mp.quad(lambda t: f(g, t)*mp.exp(ss*t), [0, 2*g])
    rz = mp.quad(lambda t: f(z, t)**2/f(g, t)*mp.exp(ss*t), [0, 2*z])
    return rg, rz


def reference_selfcheck():
    """Compare the moment recurrence with direct complex quadrature."""
    worst = mp.mpf(0)
    count = 0
    for gamma in ('1.08', '1.35', '1.642553'):
        g = m(gamma)
        for x in ('-0.8', '0', '2.5'):
            for y in ('0.001', '0.25', '5', '30'):
                z = mp.mpc(x, y)
                reference = mp.quad(lambda t: f(g, t)*mp.exp(-z*t), [0, g, 2*g])
                error = abs(transform(gamma, z)-reference)/max(mp.mpf(1), abs(reference))
                worst = max(worst, error)
                count += 1
    assert worst < mp.mpf('1e-50'), ('reference transform failed', worst)
    return {'comparisons': count, 'maximum_scaled_difference': str(worst)}


def maximize(fun, end=60, step=mp.mpf('0.05')):
    """Search each local maximum of a grid, and include logarithmic tail probes."""
    n = int(mp.ceil(end/step))
    ys = [mp.mpf(j)*end/n for j in range(n+1)]
    vals = [fun(y) for y in ys]
    best, at = max(zip(vals, ys))
    for j in range(1, n):
        if vals[j] >= vals[j-1] and vals[j] >= vals[j+1]:
            opt = minimize_scalar(lambda y: -float(fun(mp.mpf(y))),
                                  bounds=(float(ys[j-1]), float(ys[j+1])),
                                  method='bounded', options={'xatol': 1e-12})
            value = fun(mp.mpf(opt.x))
            if value > best:
                best, at = value, mp.mpf(opt.x)
    for y in (80, 100, 200, 1000, 10000):
        value = fun(mp.mpf(y))
        if value > best:
            best, at = value, mp.mpf(y)
    return max(best, mp.mpf(0)), at


@lru_cache(None)
def negative_max(g, d):
    if d <= 0:
        return mp.mpf(0), mp.mpf(0)
    return maximize(lambda y: -transform(g, -m(d)+1j*y).real)


def check_row(row):
    data = row['data']
    gg, gz, s = map(Q, (data['gamma_G'], data['gamma_Z'], data['shift']))
    a, b = map(Q, (row['case']['lo'], row['case']['hi']))
    rg, rz = norms(gg, gz, s)
    nrm = mp.sqrt(rg*rz)
    g0, f0 = 16*m(gg)**5/15, 16*m(gz)**5/15
    d0 = g0/(6*rg)
    cg, cy = negative_max(gg, s-a)
    cg_int = target.cb(gg, s-a)[0]
    di, do, df, _ = target.constants(a, gg, gz, s, row['type'])
    lo, hi, sc = target.norm_bounds(gg, gz, s)
    errors = []
    def require(ok, message):
        if not ok:
            errors.append(message)
    require(mp.mpf(lo)/sc <= rz <= mp.mpf(hi)/sc, 'R_Z outside target enclosure')
    require(di == row['d'] and do == row['D'], 'targets differ from replay report')
    require(mp.mpf(di)/S + TOL >= (1+ETA)*(d0+ETA), 'correlation term too small')
    require(mp.mpf(cg_int)/S + TOL >= cg, 'C_G misses a sampled maximum')
    mult = 1 if row['type'] == 'rr' else 2
    require(mp.mpf(do)/S + TOL >= (1+ETA)*(1-d0+mult*cg/rg), 'ordinary diagonal too small')
    count, slack = 0, mp.inf
    mix = Q(data['mix']) if row['variant'] == 'mixture' else Q(0)
    epsilon = mix*(gz/gg)**5
    nrm_mix = mp.sqrt(rg*(rz+2*m(epsilon)*transform(gz, -m(s)).real+m(epsilon)**2*rg))
    def feature(lam, real=False):
        ref = ((transform(gz, m(lam-s)).real+m(epsilon)*transform(gg, m(lam-s)).real
                -(f0+m(epsilon)*g0)/(8 if real else 6))/nrm_mix-ETA)
        actual = (extension.mixfeature(gg, gz, s, mix, lam, real=real) if mix
                  else target.feat(gg, gz, s, lam, real=real))
        return ref-mp.mpf(actual)/S
    # Every 1/den grid endpoint between s and 3, plus all special endpoints.
    den = row['lambda_den']
    points = {Q(j, den) for j in range(int(s*den)+1, 3*den+1)} | {s, b}
    if row['second']:
        points.add(Q(row['second']['hi']))
    for lam in sorted(points):
        z = feature(lam)
        require(z >= -TOL, f'ordinary feature too large at {lam}')
        slack = min(slack, z)
        count += 1
    first_slack = None
    pair = None
    if row['variant'] != 'pair':
        first_slack = feature(b, row['type'] != 'complex')
        require(first_slack >= -TOL, 'first-family feature too large')
        require(mp.mpf(df)/S+TOL >= (1+ETA)*(1-d0+(cg/rg if row['type']=='complex' else 0)),
                'first-family diagonal too small')
    else:
        p, h = map(Q, (row['gap']['lo'], row['gap']['hi']))
        zeta = Q(data['zeta'])
        vf, dp, proof = extension.paired_first(gg, gz, s, a, b, p, h, row['type'], zeta)
        # All four paired rows have s=a, hence C_F=C_G=e=0 by Condition 2.
        require(s == a and proof['e'] == 0, 'unexpected paired correction')
        best, best_args = mp.mpf(0), None
        for lam in (a, (a+b)/2, b):
            for lp in (p, (p+h)/2, h):
                def pairfun(y):
                    return (transform(gg, -m(s)+1j*y).real/rg
                            -m(zeta)*(transform(gz, m(lam-s)+1j*y).real
                                      +transform(gz, m(lp-s)+1j*y).real)/(2*nrm))
                value, height = maximize(pairfun, end=40, step=mp.mpf('0.05'))
                if value > best:
                    best, best_args = value, [str(lam), str(lp), str(height)]
        bound = mp.mpf(proof['bound'])/S
        require(bound+TOL >= best, 'paired correlation bound misses a sampled value')
        ref_feature = (transform(gz, m(b-s)).real+transform(gz, m(h-s)).real)/(2*nrm)-f0/(6*nrm)-ETA
        require(mp.mpf(vf)/S <= ref_feature+TOL, 'paired feature too large')
        require(mp.mpf(dp)/S+TOL >= (1+ETA)*((1+bound)/2-d0), 'paired diagonal too small')
        pair = {'bound': str(bound), 'sampled_maximum': str(best), 'args': best_args,
                'slack': str(bound-best)}
    return {'root': row['root'], 'variant': row['variant'], 'features_checked': count,
            'norm_interval_width': str(mp.mpf(hi-lo)/sc), 'C_G_sampled': str(cg),
            'C_G_height': str(cy), 'C_G_slack': str(mp.mpf(cg_int)/S-cg),
            'minimum_feature_slack': str(slack), 'first_feature_slack': str(first_slack),
            'pair': pair, 'errors': errors}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--out', type=Path, required=True)
    args = ap.parse_args()
    source = ROOT/'computations/audit/adversarial_20261001/two-test.json'
    rows = json.loads(source.read_text())['leaves']
    selfcheck = reference_selfcheck()
    results = []
    for row in rows:
        result = check_row(row)
        results.append(result)
        print(row['root'], 'FAIL' if result['errors'] else 'PASS', flush=True)
    report = {'scope': 'Independent high-precision numerical falsification; supremum searches are not interval proofs.',
              'parameter_source': str(source.relative_to(ROOT)),
              'parameter_source_sha256': hashlib.sha256(source.read_bytes()).hexdigest(),
              'reference_selfcheck': selfcheck,
              'precision': mp.mp.dps, 'rows': results,
              'features_checked': sum(r['features_checked'] for r in results),
              'failures': sum(bool(r['errors']) for r in results)}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'rows'}), flush=True)
    return int(report['failures'] != 0)


if __name__ == '__main__':
    raise SystemExit(main())
