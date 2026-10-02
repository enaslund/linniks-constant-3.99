"""Small real exceptional zero u=lambda1 in [u0,.1] at L=3.99, using Heath-Brown's tables near .1.

Same argument as small_exception_399.py (research/arguments/4.33.md §6), with one change: on
.08 <= u <= .1 the common gap alpha*log(1/u) is replaced by Heath-Brown's own table rows at
lambda1 <= .10 (H = Heath-Brown 1992, ORA pagination):
  Table 5 (p.46, from Lemma 8.5 with the k=2 function of Lemmas 7.1/7.5):
      every zero in R of every character other than chi1 has lambda >= 2.83 - eps;
  Table 2 (p.39, from Lemma 6.3): every other zero of L(s,chi1) in R has lambda >= 4.96 - eps.
Each row holds for all 0 <= lambda1 <= b and q >= q(eps,b) ("lambda0 >= lambda0b - eps ... whenever
0 <= lambda1 <= b", H p.38).  The piece u0 <= u <= .08 keeps the alpha-rule of small_exception_399,
whose monotonicity reduces it to its right end.  Below u0, Heath-Brown's effective q^(3+eps)
theorem for a sufficiently small exceptional zero (H p.6, citing Quart. J. Math. 41 (1990)) applies.

On a piece [a,b] with fixed gaps m (other characters) and m0 (chi1's other zeros):
  main  = (H(0)-H(u))/u >= (H(0)-H(b))/b      ((H(0)-H(u))/u decreases in u, 4.33 §6),
  other = V B(m) (e^{-(A-a_d)m} - e^{-(A-b_d)m}) / (m u) <= its value at u=a     (4.33 (6.1)),
  first = (K^2+K/4) e^{-A m0} / u <= its value at u=a                           (4.33 (6.2)).
This certifies the elementary bounds, not the source lemmas.
"""
from endgame import I, iv, Q, S, lower, upper, ROOT
import json

L = Q(399, 100); K = Q(1821, 10000); C1 = Q(57, 1000); C2 = Q(777, 5000); ALPHA = Q(109, 100)
EPS = Q(1, 1000)                        # the tables' "- eps", taken explicitly
# (piece, gap for other characters, gap for chi1's other zeros, source)
TABLE_PIECE = ((Q(8, 100), Q(10, 100)), Q(283, 100)-EPS, Q(496, 100)-EPS,
               'H Table 5 row .10 (p.46) and Table 2 row .10 (p.39)')
ALPHA_END = Q(8, 100)


def constants(L=L, K=K):
    A = L-2*K; aa = Q(4, 3)+6*C1+2*C2; bb = Q(2, 3)+4*C1; V = (Q(2, 3)+2*C1+C2)/(4*C1*C2)
    assert A > 3 and aa > bb > 0
    return A, aa, bb, V


def terms(m, m0, u_main, u_zero, L=L, K=K):
    """Interval enclosures of main (at u_main), other and first (at u_zero), all divided by u."""
    A, aa, bb, V = constants(L, K)
    m, m0, ki, ai = I(m), I(m0), I(K), I(A)
    e = iv.exp(-2*ki*m)
    B = I(Q(1, 3))*(1-e)/(2*m)+(2*ki*m-1+e)/(2*m*m)
    um, uz = I(u_main), I(u_zero)
    H = iv.exp(-ai*um)*((1-iv.exp(-ki*um))/um)**2
    main = (ki*ki-H)/um
    other = I(V)*B*(iv.exp(-I(A-aa)*m)-iv.exp(-I(A-bb)*m))/(m*uz)
    first = (ki*ki+ki/4)*iv.exp(-ai*m0)/uz
    return main, other, first


def check(L=L, K=K):
    A, aa, bb, V = constants(L, K)
    out = []
    # piece 1: u0 <= u <= .08, alpha-rule; monotone in u when alpha(A-a_d) > 1 (4.33 §6), so check u=.08
    assert ALPHA*(A-aa) > 1
    m = I(ALPHA)*iv.ln(1/I(ALPHA_END))
    main, other, first = terms(m, m, ALPHA_END, ALPHA_END, L, K)
    margin = main-other-first
    out.append(dict(piece=['u0', str(ALPHA_END)], rule='alpha*log(1/u), alpha=109/100 (H Lemmas 8.4, 8.8)',
                    gap_lower=lower(m), main_lower=lower(main), other_upper=upper(other),
                    first_upper=upper(first), margin_lower=lower(margin)))
    # piece 2: .08 <= u <= .10, Heath-Brown's rows at lambda1 <= .10
    (a, b), mg, m0, src = TABLE_PIECE
    main, other, first = terms(mg, m0, b, a, L, K)
    margin = main-other-first
    out.append(dict(piece=[str(a), str(b)], rule=src, gap_other=str(mg), gap_first=str(m0),
                    main_lower=lower(main), other_upper=upper(other), first_upper=upper(first),
                    margin_lower=lower(margin)))
    ok = all(p['margin_lower'] > 0 for p in out)
    return ok, out


if __name__ == '__main__':
    ok, pieces = check()
    assert ok, pieces
    rel = [p['margin_lower']/p['main_lower'] for p in pieces]
    rec = dict(status='PASS: small real exceptional zero, u0 <= u <= .1, at L=3.99 with Heath-Brown table rows near .1',
               L=str(L), K=str(K), c1=str(C1), c2=str(C2), alpha=str(ALPHA), eps=str(EPS), scale=S,
               pieces=pieces, relative_margin_lower=[round(r, 6) for r in rel],
               scope=('Real simple exceptional zero with u0 <= lambda1 <= .1, fixed u0 > 0, q large. For lambda1 <= u0 '
                      "use Heath-Brown's effective exponent 3+eps (eps=1/2), H p.6. Replaces the single alpha-rule "
                      'check of small_exception_399.py near .1; not a general Linnik exponent.'))
    (ROOT/'results/small_exception_tables_3.99.json').write_text(json.dumps(rec, indent=2))
    print(json.dumps(rec, indent=2))
