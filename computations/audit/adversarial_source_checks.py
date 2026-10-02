"""Targeted checks from the adversarial review of 2026-10-01.

1. Exhibit the missing sign assumption in paper Example 8.9(i).
2. Check HB Table 4's contradiction and side conditions using exact rationals.
3. Check HB Table 7's contradiction using 60-digit interval arithmetic and a
   closed-form Laplace integral, rather than numerical quadrature/root finding.

Only the transcribed TABLE4 and TABLE7 data are imported from the existing
source audit. No transform, root-finding, or checking function is imported.
The transcription was separately compared with HB's PDF by printed_tables_check
and hb_tables_recompute during the review. These checks do not prove the
analytic source lemmas, the zero-to-leaf reduction, or a global Linnik bound.

Run: .venv/bin/python computations/audit/adversarial_source_checks.py --out PATH
"""

import argparse
import json
from fractions import Fraction as Q
from pathlib import Path

from mpmath import iv, mp

from hb_tables_recompute import TABLE4, TABLE7


def rat(x):
    x = Q(x)
    return iv.mpf(x.numerator) / x.denominator


def display_interval(x):
    # Decimal strings are for display; all acceptance tests use iv endpoints.
    return [mp.nstr(mp.make_mpf(z), 25) for z in x._mpi_]


def exponential_integrals(z, length):
    """Integrals of exp(-z*t) and t*exp(-z*t) on [0, length], z != 0."""
    e = iv.exp(-z * length)
    return (1 - e) / z, (1 - (1 + z * length) * e) / (z * z)


def hb71_transform(lam, z):
    """F(z) for HB Lemma 7.1, at theta=1, by integration of its formula.

    Put zeta=lam*tan(theta), gamma=theta/zeta, c=lam*sec(theta)^2.
    With C_j=int t^j exp(-z*t) cos(zeta*t) dt, S_0 the sine integral,
    and I_j the untwisted integrals, the printed formula integrates to

      c [c(gamma*C_0-C_1/2) + (2*lam*gamma-2)I_0 - lam*I_1
         - C_0 + (2*cot(theta)-cot(2*theta))*S_0].

    Every integral is over [0, 2*gamma]. Complex exponential integrals
    evaluate C_j and S_0 with directed interval rounding.
    """
    is_zero = Q(z) == 0
    lam, z, theta = rat(lam), rat(z), rat(1)
    tangent = iv.tan(theta)
    zeta = lam * tangent
    gamma = theta / zeta
    c = lam * (1 + tangent * tangent)
    length = 2 * gamma
    i0, i1 = ((length, length * length / 2) if is_zero
              else exponential_integrals(z, length))
    j0, j1 = exponential_integrals(iv.mpc(z, -zeta), length)
    return c * (c * (gamma * j0.real - j1.real / 2)
                + (2 * lam * gamma - 2) * i0 - lam * i1 - j0.real
                + (2 / iv.tan(theta) - 1 / iv.tan(2 * theta)) * j0.imag)


def example_counterexample():
    n, v, diagonal, d = 2, Q(-1), Q(1), Q(1, 4)
    claimed_bound = diagonal / (v * v - d)
    assert v * v > d and n > claimed_bound
    return dict(
        source='paper/sections/08-near.tex:363', example='8.9(i)',
        N=n, v=str(v), D=str(diagonal), d=str(d),
        claimed_upper_bound=str(claimed_bound),
        quadratic_hypothesis=(
            'For all a_1,a_2 >= 0, (-(a_1+a_2))_+^2 = 0 <= '
            'a_1^2+a_2^2+(a_1+a_2)^2/4.'),
        threshold='tau=0 gives left side 0 and right side 1.',
        conclusion='The example needs v>0. This does not refute the threshold lemma.')


def table4():
    def p3(x):
        return x + x*x + Q(2, 3)*x*x*x

    rows = []
    for i, (b, h, a, k) in enumerate(TABLE4):
        b, h, a, k = map(Q, (b, h, a, k))
        # HB (8.7) must be >=0 for an admissible pair; negativity at the
        # printed endpoints is the contradiction used to obtain the row.
        lhs = ((k*k + Q(1, 2)) * (p3((a+b)/a) - p3(Q(1)))
               - 2*k*p3((a+b)/(a+h)) + (k+1)**2*(a+b)/8)
        assert lhs < 0
        row = dict(lambda1=str(b), printed=str(h), lhs=str(lhs))
        if i:
            left, previous_h = map(Q, TABLE4[i-1][:2])
            u = (a+left)/a
            s86 = (a+previous_h)**-3 + (a+b)**-3 - a**-3
            s88 = ((k*k + Q(1, 2))/a*(1+2*u+2*u*u)
                   + (k+1)**2/8 - 10*k/(a+left))
            assert s86 > 0 and s88 > 0
            row.update(side_86=str(s86), side_88=str(s88))
        rows.append(row)
    return rows


def table7():
    rows = []
    for b, lam, h in TABLE7:
        k = rat(Q('0.98') - Q('0.15')*Q(b))
        theta = rat(1)
        f0 = rat(lam)*(1+iv.tan(theta)**2)*(theta*iv.tan(theta)
                                               + 3*theta/iv.tan(theta) - 3)
        psi = (k*k + rat('1/2'))/8 + (4*k+1)/6
        # HB (8.10)-(8.11), with the printed k rule and epsilon=0.
        lhs = ((k*k + rat('1/2'))
               * (hb71_transform(lam, -Q(h)) - hb71_transform(lam, Q(b)-Q(h)))
               - 2*k*hb71_transform(lam, 0) + f0*psi)
        assert lhs.b < 0, (b, lhs)
        rows.append(dict(lambda1=b, printed=h, lhs_interval=display_interval(lhs)))
    return rows


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    if not __debug__:
        raise RuntimeError('Run with assertions enabled')
    iv.dps, mp.dps = 60, 70
    report = dict(
        status='PASS: local counterexample and source-table sign checks',
        example=example_counterexample(), table4_exact_rational=table4(),
        table7_interval=table7(), interval_digits=iv.dps,
        table4_first_row_scope=(
            'The first Table 4 row uses the published Table 3 fallback; '
            'its Table 4 side conditions are not asserted here.'),
        scope=(
            'Elementary sign checks only. Analytic source lemmas and their '
            'application in the global proof remain separate.'))
    args.out.write_text(json.dumps(report, indent=2) + '\n')
    print(report['status'])
    print(f"Table 4: {len(report['table4_exact_rational'])} rows; "
          f"Table 7: {len(report['table7_interval'])} rows.")


if __name__ == '__main__':
    main()
