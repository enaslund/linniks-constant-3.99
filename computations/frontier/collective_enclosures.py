"""Elementary enclosures for a common-anchor collective envelope.

Analytic deduction: research/arguments/collective-envelope.md. This standalone
module does not change the previously verified candidate. The step kernel is
the retained exact kernel; its autocorrelation is integrated piece by piece.
"""
from functools import lru_cache
import math
import numpy as np
from far_enclosures import I, S, lower, upper, Q
from base_enclosures import iv, RigorousTest
from config_v4 import T, BETA
from two_test_enclosures import fq, f_poly, vsum
import vector_intervals as vi


def box(lo, hi, scale):
    assert lo <= hi
    return iv.mpf([I(Q(lo, scale)).a, I(Q(hi, scale)).b])


@lru_cache(None)
def coefficients(r):
    """f_r(t)=a_m exp(-rt)+b_m exp(rt) on the m-th kernel step."""
    r = Q(r)
    assert r > 0
    k = T / len(BETA)
    ee = [iv.exp(-2 * I(r * i * k)) for i in range(len(BETA) + 1)]
    beta = tuple(map(I, BETA)) + (I(0),)
    result = []
    for m in range(len(BETA)):
        a = sum(beta[i] * beta[i+m] * ee[i] for i in range(len(BETA)-m))
        a -= sum(beta[i] * beta[i+m+1] * ee[i+1] for i in range(len(BETA)-m-1))
        b = sum(beta[i] * (beta[i+m+1]-beta[i+m]) * ee[i+1]
                for i in range(len(BETA)-m)) * ee[m]
        result.append((a/I(r), b/I(r)))
    return tuple(result)


def autocorrelation(r, t, order=0):
    r, t = Q(r), Q(t)
    assert 0 <= t <= T and order in (0, 1, 2)
    m = min(len(BETA)-1, int(t/(T/len(BETA))))
    a, b = coefficients(r)[m]
    aa, bb = a*iv.exp(-I(r*t)), b*iv.exp(I(r*t))
    return aa+bb if order == 0 else I(r)*(bb-aa) if order == 1 else I(r*r)*(aa+bb)


@lru_cache(None)
def norm_enclosure(r, s, gamma, steps=64):
    """Bound integral f_r(t)^2/g_gamma(t) exp((2r-s)t) dt on [0,T].

    Each of the 16 smooth pieces has its own midpoint mesh. The second
    derivative formula is the quotient/product rule, with no numerical
    differentiation. Interval operations also enclose coefficient cancellation.
    """
    r, s, gamma = map(Q, (r, s, gamma))
    assert r > 0 and s >= 0 and 2*gamma > T
    assert type(steps) is int and steps >= 8
    mcount = len(BETA)
    n = mcount*steps
    jj = np.arange(n)
    left = vi.mul(fq(T), vi.rational(jj, n))
    right = vi.mul(fq(T), vi.rational(jj+1, n))
    interval = (left[0], right[1])
    midpoint = vi.mul(fq(T), vi.rational(2*jj+1, 2*n))
    coeff = coefficients(r)
    a = tuple(np.repeat([vi.bounds_iv(ab[0])[j] for ab in coeff], steps) for j in (0,1))
    b = tuple(np.repeat([vi.bounds_iv(ab[1])[j] for ab in coeff], steps) for j in (0,1))

    def ff(t):
        aa = vi.mul(a, vi.exp(vi.mul(fq(-r), t)))
        bb = vi.mul(b, vi.exp(vi.mul(fq(r), t)))
        f = vi.add(aa, bb)
        return f, vi.mul(fq(r), vi.sub(bb, aa)), vi.mul(fq(r*r), f)

    f, fp, fpp = ff(interval)
    g = f_poly(gamma, interval)
    gp, gpp = f_poly(gamma, interval, 1), f_poly(gamma, interval, 2)
    assert np.all(g[0] > 0)
    p = vi.sq(f)
    pp = vi.scale(vi.mul(f, fp), 2)
    ppp = vi.scale(vi.add(vi.sq(fp), vi.mul(f, fpp)), 2)
    c = 2*r-s
    one = vi.div(vi.add(vi.add(ppp, vi.mul(fq(2*c), pp)), vi.mul(fq(c*c), p)), g)
    two = vi.div(vi.mul(vi.add(vi.scale(pp, 2), vi.mul(fq(2*c), p)), gp), vi.sq(g))
    three = vi.div(vi.mul(p, gpp), vi.sq(g))
    four = vi.div(vi.scale(vi.mul(p, vi.sq(gp)), 2), vi.mul(vi.sq(g), g))
    d2 = vi.mul(vi.exp(vi.mul(fq(c), interval)), vi.add(vi.sub(vi.sub(one, two), three), four))
    bound = np.maximum(abs(d2[0]), abs(d2[1]))
    assert np.all(np.isfinite(bound))
    fm = ff(midpoint)[0]
    value = vi.div(vi.mul(vi.sq(fm), vi.exp(vi.mul(fq(c), midpoint))), f_poly(gamma, midpoint))
    error = vi.mul(vi.mul(vi.exact(bound), fq((T/n)**2)), fq(Q(1,24)))
    integral = vi.mul(fq(T/n), vi.add(value, (-error[1], error[1])))
    lo, hi = vsum(integral)
    assert math.isfinite(lo) and 0 < lo <= hi
    scale = 10**22
    return dict(lower=math.floor(Q.from_float(lo)*scale),
                upper=math.ceil(Q.from_float(hi)*scale), scale=scale,
                kernel_pieces=mcount, subintervals=n,
                method='Piecewise exponential autocorrelation; midpoint rule with interval second derivative')


@lru_cache(None)
def tangent(r, s, gamma, n0, L, error='0.00000001', steps=64):
    """Upward rational prime-cost intercept/slope for a finite cohort.

    The caller must check s<=global first-zero lower bound, and that every
    cohort character has height-one anchor at least r. Different cohorts use
    separate bounds. The positive error absorbs their finite asymptotic errors.
    """
    r, s, gamma, n0, L, error = map(Q, (r, s, gamma, n0, L, error))
    assert r > 0 and s >= 0 and n0 > 0 and error > 0 and L-2*T > 3
    rb = norm_enclosure(r, s, gamma, steps)
    RB = box(rb['lower'], rb['upper'], rb['scale'])
    test = RigorousTest(gamma)
    h = test.f0/6
    a = test.F(-s)-h
    assert lower(a, 10**22) > 0
    k = autocorrelation(r, 0)/6
    nn = I(n0)
    denom = 2*iv.sqrt(h*nn*nn+a*nn)
    intercept = iv.sqrt(RB)*a*nn/denom
    slope = k+iv.sqrt(RB)*(2*h*nn+a)/denom
    H0 = I((T/len(BETA)*sum(BETA))**2)
    factor = iv.exp(-I((L-2*T)*r))/H0
    return dict(anchor=str(r), shift=str(s), gamma=str(gamma), n0=str(n0), L=str(L),
                error=str(error), steps=steps, norm=rb,
                intercept=upper(factor*intercept+I(error)),
                slope=upper(factor*slope), scale=S,
                gram_remainder_lower=lower(a))
