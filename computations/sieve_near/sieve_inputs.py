"""Outward inputs for the sieve-majorant near inequality.

Mathematical statement: research/arguments/sieve-majorant-near.md.
Detector f and short Gram g1 are the normalized parabolic autocorrelation
f_gamma/f_gamma(0) (c1 = 1).  The sieve weight H is a step function on a
rational mesh of [t0, 2 gamma]; cell k uses its own Selberg level
D_k = q^{delta_k}, delta_k = (t_k - 1/3)/2 - EPS_LEVEL, so its diagonal
contribution is exactly h_k (t_{k+1}^2 - t_k^2)/(2 delta_k).  Off-diagonal
terms are smooth character sums of length >= q^{1/3 + 2 EPS_LEVEL}.

Exports are integers on the repository's 10**16 grid:
  I_up      upper bound for int e^{2st} f^2/omega
  D_up      upper bound for the full Gram diagonal
  d1        (phi/2) g1(0) = 1/6, exact
  row features: lower bounds of r(lambda)/sqrt(I_up D_up) - ETA.
No optimizer is imported; parameters are rational proposals.
"""
import sys
from pathlib import Path
from fractions import Fraction as Q
from functools import lru_cache
import numpy as np
CORE = Path(__file__).resolve().parents[1]/'core'/'code'
sys.path.insert(0, str(CORE))
import vector_intervals as vi
from base_enclosures import I, iv, lower, upper, S, RigorousTest

PHI = Q(1, 3)
EPS_LEVEL = Q(1, 2000)
ETA = Q(1, 10**6)


def fnorm(g, t):
    """Interval enclosure of (1-u)^3(1+3u+u^2), u=t/(2g), for 0<=t<=2g (vector)."""
    u = vi.div(t, vi.rational(2*g.numerator, g.denominator))
    om = vi.sub(vi.exact(1.0), u)
    return vi.mul(vi.mul(vi.sq(om), om), vi.add(vi.add(vi.exact(1.0), vi.scale(u, 3.0)), vi.sq(u)))


def q2f(x):
    return vi.rational(np.array([x.numerator], dtype=float), np.array([x.denominator], dtype=float))


def cell_exp(c, t):
    """Enclosure of exp(c*t) for exact vector t and rational c."""
    return vi.exp(vi.mul(t, q2f(c)))


class SieveNearTest:
    """f = f_gamma/f_gamma(0) (detector), g1 = f_g1/f_g1(0) (short Gram, c1 = 1).
    Sieve weight: step heights h_k = (e^{s m} f(m)/sqrt(mu kappa_k) - g1(m) e^{s1 m})_+ at cell midpoints m."""
    def __init__(self, gamma, g1, t0, mu, s, s1, short_cells=2000, long_cells=2000):
        g, g1, t0, s, s1 = map(Q, (gamma, g1, t0, s, s1))
        assert t0 > PHI + 2*EPS_LEVEL and t0 < 2*g and s1 >= 0 and s >= s1 and 2*g1 >= t0
        self.params = dict(gamma=str(g), g1=str(g1), t0=str(t0), mu=str(mu), s=str(s), s1=str(s1),
                           short_cells=short_cells, long_cells=long_cells)
        self.g, self.g1, self.t0, self.s, self.s1 = g, g1, t0, s, s1
        T = 2*g
        # ---- short range [0,t0): omega = g1 e^{s1 t}; integrand e^{(2s-s1)t} f^2/g1 ----
        a = [t0*j/short_cells for j in range(short_cells)]
        b = [t0*(j+1)/short_cells for j in range(short_cells)]
        ta = vi.rational([x.numerator for x in a], [x.denominator for x in a])
        tb = vi.rational([x.numerator for x in b], [x.denominator for x in b])
        width = vi.rational([(y-x).numerator for x, y in zip(a, b)], [(y-x).denominator for x, y in zip(a, b)])
        fa = fnorm(g, ta)                               # f decreasing: max at left end
        g1b = fnorm(g1, tb)                             # g1 decreasing: min at right end
        assert np.all(g1b[0] > 0)
        e = cell_exp(2*s-s1, tb)
        short = vi.mul(vi.div(vi.mul(e, vi.sq(fa)), g1b), width)
        short_up = float(short[1].sum()) * (1+2**-40)
        # ---- long range [t0,2g): g1 part plus step sieve weight ----
        edges = [t0+(T-t0)*Q(k, long_cells) for k in range(long_cells+1)]
        la, lb = edges[:-1], edges[1:]
        ta = vi.rational([x.numerator for x in la], [x.denominator for x in la])
        tb = vi.rational([x.numerator for x in lb], [x.denominator for x in lb])
        width = vi.rational([(y-x).numerator for x, y in zip(la, lb)], [(y-x).denominator for x, y in zip(la, lb)])
        delta = [(x-PHI)/2-EPS_LEVEL for x in la]
        assert min(delta) > 0
        mid = np.array([float((x+y)/2) for x, y in zip(la, lb)])
        kap = np.array([float((y*y-x*x)/(2*d)/(y-x)) for x, y, d in zip(la, lb, delta)])
        u = mid/float(T); fm = (1-u)**3*(1+3*u+u*u)
        u1 = np.minimum(mid/float(2*g1), 1.0); g1m = (1-u1)**3*(1+3*u1+u1*u1)
        hprop = np.exp(float(s)*mid)*fm/np.sqrt(float(mu)*kap)-g1m*np.exp(float(s1)*mid)
        self.h = [Q(x).limit_denominator(10**12) if x > 0 else Q(0) for x in hprop]
        hq = vi.rational([x.numerator for x in self.h], [x.denominator for x in self.h])
        fa = fnorm(g, ta)
        # g1 on [t0,2g): may exceed its own support 2*g1; clip u at 1 (fnorm gives 0 beyond)
        tb1 = (np.minimum(tb[0], float(2*g1)), np.minimum(tb[1], float(2*g1)))
        g1b = fnorm(g1, tb1)
        g1b = (np.where(tb[0] >= float(2*g1), 0.0, g1b[0]), np.where(tb[0] >= float(2*g1), 0.0, g1b[1]))
        num = vi.mul(vi.sq(fa), cell_exp(2*s, tb))
        den = vi.add(vi.mul(g1b, cell_exp(s1, ta)), hq)
        assert np.all(den[0] > 0), 'omega must be positive on supp f'
        longI = vi.mul(vi.div(num, den), width)
        long_up = float(longI[1].sum()) * (1+2**-40)
        self.I_up = Q(short_up)+Q(long_up)
        D2 = sum((h*(y*y-x*x)/(2*d) for h, x, y, d in zip(self.h, la, lb, delta)), Q(0))
        f1 = RigorousTest(g1)
        D1 = f1.F(-s1)/f1.f0
        self.D1_up = Q(upper(D1), S)
        self.D2 = D2
        self.D_up = self.D1_up+D2
        self.d1 = PHI/2
        self.fz = RigorousTest(g)
        self.f1 = f1
        # graded rows: D2(delta) = sum_k c_k e^{-2 delta t_k}, c_k = h_k (t_{k+1}^2-t_k^2)/(2 delta_k)
        ck = [h*(y*y-x*x)/(2*d) for h, x, y, d in zip(self.h, la, lb, delta)]
        self._ck = vi.rational([c.numerator for c in ck], [c.denominator for c in ck])
        self._tk = vi.rational([x.numerator for x in la], [x.denominator for x in la])

    @lru_cache(maxsize=None)
    def feature(self, lam):
        """Lower bound of r(lam)/sqrt(I_up D_up) - ETA for lam >= s; S-scaled integer."""
        lam = Q(lam)
        assert lam >= self.s
        r = self.fz.F(lam-self.s)/self.fz.f0 - I(Q(1, 6))
        v = r/iv.sqrt(I(self.I_up)*I(self.D_up)) - I(ETA)
        return lower(v)

    @lru_cache(maxsize=None)
    def _feature_diff(self, diff):
        r = self.fz.F(diff)/self.fz.f0 - I(Q(1, 6))
        if not hasattr(self, '_norm'):
            self._norm = iv.sqrt(I(self.I_up)*I(self.D_up))
        return lower(r/self._norm - I(ETA))

    def feature_at(self, lam, anchor):
        """Graded rows: lower bound of (F(lam-anchor)/f(0)-1/6)/sqrt(I_up D_up) - ETA, anchor <= s.
        For a character with parameter in [anchor, lam] and response anchor `anchor`."""
        lam, anchor = Q(lam), Q(anchor)
        assert anchor <= self.s and lam >= anchor
        return self._feature_diff(lam-anchor)

    @lru_cache(maxsize=None)
    def diag_up(self, delta):
        """Upper bound (Fraction) of D(delta) = int g1 e^{(s1-2delta)t} dt + sum_k c_k e^{-2 delta t_k}.
        D is the Gram diagonal of a character whose response anchor is s - delta."""
        delta = Q(delta)
        assert delta >= 0
        if delta == 0:
            return self.D_up
        D1 = Q(upper(self.f1.F(2*delta-self.s1)/self.f1.f0), S)
        e = vi.exp(vi.mul(self._tk, q2f(-2*delta)))
        terms = vi.mul(self._ck, e)
        n = len(terms[1])
        D2 = float(np.sum(terms[1]))*(1+2**-40)+n*2**-1070
        return D1+Q(D2)

    @lru_cache(maxsize=None)
    def diag_norm(self, delta):
        """S-scaled upper bound of the normalized graded diagonal (1+ETA)(D(delta)-d1)/D_up.
        Returns None when D(delta)-d1 is not safely positive (the character is then omitted)."""
        num = self.diag_up(delta)-self.d1
        if num <= Q(1, 1000)*self.D_up:
            return None
        x = (1+ETA)*num/self.D_up
        return -((-x.numerator*S)//x.denominator)

    @lru_cache(maxsize=None)
    def shifted_first_feature(self, a, b, real_nonreal_zero):
        """First family in a row whose anchor s may exceed lambda1 in [a,b] (s <= lambda', lambda2):
        its zero is retained explicitly, F(lambda1-s) >= F(b-s); a real character with a nonreal
        zero also loses the conjugate zero's term, bounded below by -C_Z, C_Z = sup_{Re z>=a-s} -Re F(z).
        Lower bound of (F(b-s)/f0 - E C_Z/f0 - 1/6)/sqrt(I_up D_up) - ETA."""
        a, b = Q(a), Q(b)
        r = self.fz.F(b-self.s)/self.fz.f0 - I(Q(1, 6))
        if real_nonreal_zero and self.s > a:
            C, _ = self.fz.C_upper(self.s-a)
            r = r - I(Q(C, S))/self.fz.f0
        if not hasattr(self, '_norm'):
            self._norm = iv.sqrt(I(self.I_up)*I(self.D_up))
        return lower(r/self._norm - I(ETA))

    def pair_bounds(self, a, b, mu_lo, mu_hi, step=Q(1, 50)):
        """Real character with a nonreal first zero (rc family row, H = 0): for lambda1 in [a,b]
        and normalized height mu1 in [mu_lo, mu_hi] (mu_hi None = infinity) return
          R_lo: lower bound of Re F(lambda1 - s + 2 i mu1)/f(0)   (conjugate zero's response),
          c_hi: upper bound of Re G1(-s1 + 2 i mu1)/g1(0)          (pair Gram correlation).
        Point evaluations on a mu grid; between grid points g(mu) >= min(ends) - M2 h^2/8 and
        <= max(ends) + M2 h^2/8 with |d^2/dmu^2| <= 4 int t^2 (.) dt; in lambda1 the Lipschitz
        bound |d/dx Re F(x+iy)| <= int t f for x >= 0.  mu >= 10 uses the closed-form tail."""
        assert all(h == 0 for h in self.h), 'pair correlation is proved for the H = 0 family row'
        a, b, mu_lo = Q(a), Q(b), Q(mu_lo)
        assert self.s <= a <= b
        top = Q(10) if mu_hi is None else min(Q(mu_hi), Q(10))
        fz, f1 = self.fz, self.f1
        M1R = upper(fz.exponential_moment(1, 0)/fz.f0)
        M2R = 4*upper(fz.exponential_moment(2, 0)/fz.f0)
        M2c = 4*upper(f1.exponential_moment(2, self.s1)/f1.f0)
        x0 = (a+b)/2-self.s
        R_lo, c_hi = None, None
        if mu_lo < top:
            n = max(1, int(((top-mu_lo)/step).__ceil__()))
            grid = [mu_lo+(top-mu_lo)*k/n for k in range(n+1)]
            h = (top-mu_lo)/n
            Rv = [Q(lower((fz.F(iv.mpc(I(x0), I(2*m)))/fz.f0).real), S) for m in grid]
            cv = [Q(upper((f1.F(iv.mpc(-I(self.s1), I(2*m)))/f1.f0).real), S) for m in grid]
            slackR = Q(M2R, S)*h*h/8 + Q(M1R, S)*(b-a)/2
            slackc = Q(M2c, S)*h*h/8
            R_lo = min(min(Rv[k], Rv[k+1]) for k in range(n)) - slackR
            c_hi = max(max(cv[k], cv[k+1]) for k in range(n)) + slackc
        if mu_hi is None or Q(mu_hi) > 10:
            # Re F >= 0 on Re z >= 0 (admissible detector), and the closed-form tail of G1
            R_lo = Q(0) if R_lo is None else min(R_lo, Q(0))
            g = I(self.g1); d = I(self.s1); u = I(20); E = iv.exp(2*g*d)
            tail = (8*g**3/(3*u**3)+4*g*g*(1+E)/u**4+4*(1+E)/u**6+8*g*E*(u+d)/u**6)/self.f1.f0
            ct = Q(upper(tail), S)
            c_hi = ct if c_hi is None else max(c_hi, ct)
        return max(R_lo, Q(0)), c_hi

    def pair_term(self, a, b, mu_lo, mu_hi):
        """Family term (2, v', D') for the pair (chi1, +-gamma1) in this (family) row."""
        R_lo, c_hi = self.pair_bounds(a, b, mu_lo, mu_hi)
        r = self.fz.F(Q(b)-self.s)/self.fz.f0 + I(R_lo) - I(Q(1, 6))
        if not hasattr(self, '_norm'):
            self._norm = iv.sqrt(I(self.I_up)*I(self.D_up))
        v = lower(r/self._norm - I(ETA))
        Dp = (1+ETA)*(self.D_up-self.d1+max(c_hi-self.d1, Q(0)))/self.D_up
        return (2, max(0, v), -((-Dp.numerator*S)//Dp.denominator))

    def second_zero_bounds(self, a, b, p, p_hi, y_lo, y_hi, step=Q(1, 50)):
        """First family's second zero (research/PROOF.md §6.5): rho1 with lambda1 in [a,b] and another
        zero rho' of the same character with lambda' in [p,p_hi] (p_hi finite), at normalized height
        difference y in [y_lo, y_hi] (y_hi None = infinity); family row (H = 0).  Returns
          Rp: lower bound of Re F(lambda' - s + i y)/f(0)   (rho' seen from rho1's test point),
          Rq: lower bound of Re F(lambda1 - s + i y)/f(0)   (rho1 seen from rho''s test point),
          c_hi: upper bound of Re G1(-s1 + i y)/g1(0)        (Gram correlation of the two entries).
        Point evaluations on a y grid with second-derivative slack |d^2/dy^2| <= int t^2 (.) dt,
        Lipschitz slack in the real part |d/dx Re F(x+iy)| <= int t f (x >= 0), and for y >= 10
        admissibility (Re F >= 0 on Re z >= 0) and the closed-form tail of G1."""
        assert all(h == 0 for h in self.h), 'second-zero entries are proved for the H = 0 family row'
        a, b, p, p_hi, y_lo = Q(a), Q(b), Q(p), Q(p_hi), Q(y_lo)
        assert self.s <= a <= b and self.s <= p <= p_hi and y_lo >= 0
        top = Q(10) if y_hi is None else min(Q(y_hi), Q(10))
        fz, f1 = self.fz, self.f1
        M1R = upper(fz.exponential_moment(1, 0)/fz.f0)
        M2R = upper(fz.exponential_moment(2, 0)/fz.f0)
        M2c = upper(f1.exponential_moment(2, self.s1)/f1.f0)
        xp = (p+p_hi)/2-self.s
        xq = (a+b)/2-self.s
        Rp = Rq = c_hi = None
        if y_lo < top:
            n = max(1, int(((top-y_lo)/step).__ceil__()))
            grid = [y_lo+(top-y_lo)*k/n for k in range(n+1)]
            h = (top-y_lo)/n
            pv = [Q(lower((fz.F(iv.mpc(I(xp), I(y)))/fz.f0).real), S) for y in grid]
            qv = [Q(lower((fz.F(iv.mpc(I(xq), I(y)))/fz.f0).real), S) for y in grid]
            cv = [Q(upper((f1.F(iv.mpc(-I(self.s1), I(y)))/f1.f0).real), S) for y in grid]
            curv = Q(M2R, S)*h*h/8
            Rp = min(min(pv[k], pv[k+1]) for k in range(n))-curv-Q(M1R, S)*(p_hi-p)/2
            Rq = min(min(qv[k], qv[k+1]) for k in range(n))-curv-Q(M1R, S)*(b-a)/2
            c_hi = max(max(cv[k], cv[k+1]) for k in range(n))+Q(M2c, S)*h*h/8
        if y_hi is None or Q(y_hi) > 10:
            Rp = Q(0) if Rp is None else min(Rp, Q(0))
            Rq = Q(0) if Rq is None else min(Rq, Q(0))
            g = I(self.g1); d = I(self.s1); u = I(10); E = iv.exp(2*g*d)
            tail = (8*g**3/(3*u**3)+4*g*g*(1+E)/u**4+4*(1+E)/u**6+8*g*E*(u+d)/u**6)/self.f1.f0
            ct = Q(upper(tail), S)
            c_hi = ct if c_hi is None else max(c_hi, ct)
        return max(Rp, Q(0)), max(Rq, Q(0)), c_hi

    def second_zero_terms(self, n, a, b, p, p_hi, y_lo, y_hi):
        """Family terms [(n, v1, D'), (n, v2, D')] for the entries (chi, gamma1) and (chi, gamma') of each
        of the n first-family characters: responses F(b-s) + Rp and F(p_hi-s) + Rq; the correlation
        excess (c_hi - d1)_+ is added to both diagonals (2 a1 a2 c <= (a1^2 + a2^2) c for c >= 0)."""
        Rp, Rq, c_hi = self.second_zero_bounds(a, b, p, p_hi, y_lo, y_hi)
        if not hasattr(self, '_norm'):
            self._norm = iv.sqrt(I(self.I_up)*I(self.D_up))
        r1 = self.fz.F(Q(b)-self.s)/self.fz.f0+I(Rp)-I(Q(1, 6))
        r2 = self.fz.F(Q(p_hi)-self.s)/self.fz.f0+I(Rq)-I(Q(1, 6))
        v1 = lower(r1/self._norm-I(ETA)); v2 = lower(r2/self._norm-I(ETA))
        Dp = (1+ETA)*(self.D_up-self.d1+max(c_hi-self.d1, Q(0)))/self.D_up
        Dp = -((-Dp.numerator*S)//Dp.denominator)
        return [(int(n), max(0, v1), Dp), (int(n), max(0, v2), Dp)]

    def gram(self):
        """(D, d) on the S grid, both rounded upward, with the (1+ETA) slack."""
        dd = (1+ETA)*(self.d1/self.D_up+ETA)
        DD = (1+ETA)*(1-self.d1/self.D_up)
        return -((-dd.numerator*S)//dd.denominator), -((-DD.numerator*S)//DD.denominator)


if __name__ == '__main__':
    import time
    t = time.time()
    st = SieveNearTest(Q('0.893'), Q('1.535'), Q('0.346'), 10**-1.38, Q('1.75'), Q('0.76'))
    d, D = st.gram()
    print('I_up', float(st.I_up), 'D_up', float(st.D_up), 'd', d/S, 'D', D/S, 'sec', round(time.time()-t, 2))
    for lam in ['1.75', '1.8', '2.0', '2.25']:
        v = st.feature(Q(lam))/S
        n = (D/S)/(v*v-d/S) if v*v > d/S else float('inf')
        print(lam, 'v', v, 'crowd bound', n)
