"""Independent interval recheck of the two-piece small exceptional-zero branch at L=3.99.

The paper's Theorem 12.5 (research/PROOF.md, exterior regimes) splits u = lambda_1 in [u0, .1]
into P1 = [u0, .08], with the gap rule alpha*log(1/u), and P2 = [.08, .1], with Heath-Brown's
table rows (lambda_2 >= 2.829, lambda' >= 4.959).  On each piece the margin is

    varpi = M(u*) - V_d B_{1/3}(m) Q(m)/0.08 - (K^2 + K/4) e^{-A_s m1}/0.08,

with u* = .08, m = m1 = alpha*log(12.5) on P1 and u* = .1, m = 2.829, m1 = 4.959 on P2, where
M(u) = (K^2 - e^{-A_s u} F_2(u))/u, F_2(z) = ((1 - e^{-Kz})/z)^2,
B_phi(l) = (phi/2)(1 - e^{-2Kl})/l + (2Kl - 1 + e^{-2Kl})/(2l^2) and
Q(m) = (e^{-(A_s-a_d)m} - e^{-(A_s-b_d)m})/m.

This script shares no code with small_exception_tables.py or the enclosure library: it uses only
mpmath's interval context, directly from the formulas above.  It encloses every quantity and
checks that the stored bounds of computations/core/results/small_exception_tables_3.99.json lie
on the safe side (stored lower bounds below the enclosure, stored upper bounds above it).  It
certifies the elementary bounds only; the analytic lemmas and the monotonicity argument are in
the paper.

    python3 computations/core/code/independent_small_tables_check.py
"""
from fractions import Fraction
from pathlib import Path
import json
from mpmath import iv, mp

iv.dps = 60
ROOT = Path(__file__).resolve().parents[1]
STORED = ROOT/'results/small_exception_tables_3.99.json'
OUT = ROOT/'results/independent_small_tables_3.99.json'


def q(s):
    f = Fraction(s)
    return iv.mpf(f.numerator)/f.denominator


K, L = q('0.1821'), q('3.99')
As = L - 2*K
c1, c2, third = q('0.057'), q('0.1554'), q('1/3')
ad = q('4/3') + 6*c1 + 2*c2
bd = q('2/3') + 4*c1
Vd = (q('2/3') + 2*c1 + c2)/(4*c1*c2)
alpha = q('1.09')
mstar = alpha*iv.log(q('12.5'))
m2, m2p = q('2.829'), q('4.959')
B1 = K**2 + K/4


def F2(z):
    return ((1 - iv.exp(-K*z))/z)**2


def M(u):
    return (K**2 - iv.exp(-As*u)*F2(u))/u


def B(phi, lam):
    e = iv.exp(-2*K*lam)
    return (phi/2)*(1 - e)/lam + (2*K*lam - 1 + e)/(2*lam**2)


def Q(m):
    return (iv.exp(-(As - ad)*m) - iv.exp(-(As - bd)*m))/m


def ends(x, digits=20):
    """The endpoints of an interval as decimal strings, for display only (the checks use the enclosures)."""
    lo, hi = mp.make_mpf(x._mpi_[0]), mp.make_mpf(x._mpi_[1])
    with mp.workdps(digits):
        return mp.nstr(lo, digits), mp.nstr(hi, digits)


def pieces():
    u08, u10 = q('0.08'), q('0.1')
    p1 = dict(main=M(u08), other=Vd*B(third, mstar)*Q(mstar)/u08, first=B1*iv.exp(-As*mstar)/u08)
    p2 = dict(main=M(u10), other=Vd*B(third, m2)*Q(m2)/u08, first=B1*iv.exp(-As*m2p)/u08)
    for p in (p1, p2):
        p['margin'] = p['main'] - p['other'] - p['first']
    return p1, p2


def main():
    stored = json.loads(STORED.read_text())
    S = stored['scale']
    assert (stored['L'], stored['K'], stored['c1'], stored['c2'], stored['alpha']) == \
        ('399/100', '1821/10000', '57/1000', '777/5000', '109/100')
    # the exact rationals of the paper's fixed data
    assert ad.a <= q('3724/1875').a and q('3724/1875').b <= ad.b
    assert bd.a <= q('671/750').a and q('671/750').b <= bd.b
    assert Vd.a <= q('184750/6993').a and q('184750/6993').b <= Vd.b
    mono = As - ad - 1/alpha
    assert mono.a > 0                          # A_s - a_d - 1/alpha = 236171/327000 > 0
    report = dict(status=None, digits=iv.dps, pieces=[])
    for p, rec in zip(pieces(), stored['pieces']):
        # stored lower bounds must lie below the enclosure, upper bounds above it
        assert mp.mpf(rec['main_lower'])/S <= p['main'].a
        assert mp.mpf(rec['other_upper'])/S >= p['other'].b
        assert mp.mpf(rec['first_upper'])/S >= p['first'].b
        assert mp.mpf(rec['margin_lower'])/S <= p['margin'].a
        assert p['margin'].a > q('0.0304').b
        report['pieces'].append({k: [ends(v)[0], ends(v)[1]] for k, v in p.items()})
    report['status'] = ('PASS: independent interval enclosures of the two small-branch pieces agree '
                        'with small_exception_tables_3.99.json; both margins exceed 0.0304')
    report['scope'] = ('Elementary bounds of Theorem 12.5 only; the analytic inputs and the '
                       'monotonicity argument are in the paper.')
    OUT.write_text(json.dumps(report, indent=1) + '\n')
    print(json.dumps(report, indent=1))


if __name__ == '__main__':
    main()
