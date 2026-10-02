"""Multi-threshold dual certificates for one leaf with extra sieve-near rows.

A leaf is the repository's regenerated LP input `inp` (rows, far budget,
old near data, distinguished families) together with K sieve-near tests.
Each near inequality has its own existential threshold.  The certificate is
a bisection tree over the threshold box [0,end_0] x ... x [0,end_K]
(integer ticks, scale TS).  A leaf box is either excluded by a negative
budget or carries integer duals (Y far, U count, Z_0 old near, Z_k sieve)
satisfying every column inequality exactly.  Verification uses integers
only; the optimizer is used only by `build`.
"""
import math
from fractions import Fraction as Q
import numpy as np

S = 10**16
TS = 10**6
DS = 10**12


def ceildiv(a, b):
    assert isinstance(a, int) and isinstance(b, int) and b > 0
    return -((-a)//b)


def isqrt_up(n):
    r = math.isqrt(n)
    return r+int(r*r < n)


class LeafData:
    """Integer data of one leaf: repository input plus sieve rows."""
    def __init__(self, inp, sieve):
        self.inp = inp
        rows = inp['rows']
        self.W = [r[2] for r in rows]
        self.G = [r[3] for r in rows]
        self.V0 = [r[4] for r in rows]
        self.cnt = list(inp['count_cost'])
        self.F = inp['far_budget']
        self.first = inp['first']
        self.final = inp['final']
        self.d0, self.D0, self.Df = inp['d'], inp['D'], inp['Df']
        self.vf = inp['v_first']
        self.n = inp['n']
        sec = inp['second']
        self.n2 = sec['n'] if sec else 0
        self.v2 = sec['v'] if sec else 0
        assert all(w > 0 for w in self.W)
        # sieve: list of dict(d=int, D=int, v=[int per row])
        self.sieve = sieve
        for sv in sieve:
            assert len(sv['v']) == len(rows) and sv['d'] > 0 and sv['D'] > 0
            # optional per-character diagonals 'Dv' (graded rows) and fixed family terms 'fam':
            # (n, v) or (n, v, Dn): n characters with feature >= v and diagonal <= Dn (default D)
            if 'Dv' in sv:
                assert len(sv['Dv']) == len(rows) and all(type(x) is int and x > 0 for x in sv['Dv'])
            for fm in sv.get('fam', []):
                assert len(fm) in (2, 3) and all(type(x) is int and x >= 0 for x in fm)
                assert len(fm) == 2 or fm[2] > 0
        self.ends = [isqrt_up(self.d0*TS*TS//S+1)] + [isqrt_up(sv['d']*TS*TS//S+1) for sv in sieve]
        self.old_window = self._old_window()

    def old_point(self, t):
        """Exact rational old-near budget B(t/TS) (normalized by S)."""
        d, D, Df = Q(self.d0, S), Q(self.D0, S), Q(self.Df, S)
        tau = Q(t, TS)
        return (D*(1-tau*tau/d)-self.n*(D/Df)*max(Q(self.vf, S)-tau, 0)**2
                - self.n2*max(Q(self.v2, S)-tau, 0)**2)

    def _old_window(self):
        """Ticks [lo, hi] outside which the old budget is negative.

        B is concave (D(1-t^2/d) concave, -(v-t)_+^2 concave). If B(hi) >= 0 > B(hi+1)
        then B < 0 on [hi+1, inf); if B(lo) >= 0 > B(lo-1) then B < 0 on (-inf, lo-1].
        Feasible real thresholds lie in [lo-1, hi+1] ticks.  Returns None if B<0 at every tick
        of a coarse scan (then the whole leaf is excluded only via ordinary box checks)."""
        end = self.ends[0]
        B = self.old_point
        # find a tick with B>=0 by scanning
        peak = max(range(0, end+1, max(1, end//2000)), key=B)
        if B(peak) < 0:
            return None
        lo, hi = 0, peak
        if B(0) >= 0:
            L0 = 0
        else:
            while hi-lo > 1:
                m = (lo+hi)//2
                lo, hi = (lo, m) if B(m) >= 0 else (m, hi)
            L0 = hi
            assert B(L0) >= 0 > B(L0-1) and B(L0) >= B(L0-1)
        lo, hi = peak, end
        if B(end) >= 0:
            R0 = end
        else:
            while hi-lo > 1:
                m = (lo+hi)//2
                lo, hi = (m, hi) if B(m) >= 0 else (lo, m)
            R0 = lo
            assert B(R0) >= 0 > B(R0+1) and B(R0) >= B(R0+1)
        return (L0, R0)

    def old_costs(self, b):
        sh = b*(S//TS)
        return [max(v-sh, 0)**2//S for v in self.V0]

    def old_budget(self, a, b):
        # identical to the repository's formula (verify_progress.scenario)
        sh = b*(S//TS)
        f1 = max(self.vf-sh, 0)
        f2 = max(self.v2-sh, 0)
        d, D, Df = self.d0, self.D0, self.Df
        de = TS*TS*d*Df*S
        nu = D*de-D*a*a*Df*S*S-self.n*D*f1*f1*TS*TS*d-self.n2*f2*f2*TS*TS*d*Df
        return ceildiv(nu, de)

    def sieve_costs(self, k, b):
        sv = self.sieve[k]
        sh = b*(S//TS)
        return [max(v-sh, 0)**2//Dk for v, Dk in zip(sv['v'], row_D(sv))]

    def sieve_budget(self, k, a, b=None):
        sv = self.sieve[k]
        # S*(1 - (a/TS)^2 / (d/S)) - sum_fam n (v - b/TS)_+^2 / (D/S), rounded up
        out = S-(S*S*a*a)//(TS*TS*sv['d'])
        if sv.get('fam'):
            sh = b*(S//TS)
            out -= sum((n*max(v-sh, 0)**2)//Dn for n, v, Dn in fam_terms(sv))
        return out


def row_D(sv):
    """Per-character diagonal upper bounds of a sieve row (S-scaled ints)."""
    return sv['Dv'] if 'Dv' in sv else [sv['D']]*len(sv['v'])


def fam_terms(sv):
    """Fixed family terms (n, v, Dn) of a sieve row."""
    return [(fm[0], fm[1], fm[2] if len(fm) == 3 else sv['D']) for fm in sv.get('fam', [])]


def old_effective(ld, a0, b0):
    """Old-threshold interval after removing ticks where the concave budget is negative."""
    if ld.old_window is None:
        return a0, b0
    L0, R0 = ld.old_window
    return max(a0, L0-1), min(b0, R0+1)


def box_data(ld, box):
    """Costs (lower bounds) and budgets (upper bounds) valid throughout the box."""
    (a0, b0) = old_effective(ld, *box[0])
    if a0 > b0:
        return None, [-1]
    costs = [ld.old_costs(b0)]
    budgets = [ld.old_budget(a0, b0)]
    for k, (a, b) in enumerate(box[1:]):
        costs.append(ld.sieve_costs(k, b))
        budgets.append(ld.sieve_budget(k, a, b))
    return costs, budgets


def check_box(ld, box, duals):
    costs, budgets = box_data(ld, box)
    if duals == 'excluded':
        assert min(budgets) < 0
        return -1, 0
    Y, U = duals['Y'], duals['U']
    Z = duals['Z']
    assert len(Z) == len(costs)
    assert all(type(x) is int and x >= 0 for x in [Y, U]+Z)
    assert min(budgets) >= 0
    for i in range(len(ld.G)):
        lhs = Y*ld.W[i]+U*ld.cnt[i]
        for z, c in zip(Z, costs):
            if z:
                lhs += z*c[i]
        assert lhs >= DS*ld.G[i], ('column', i)
    tot = Y*ld.F+U*2*S+sum(z*b for z, b in zip(Z, budgets))
    value = ceildiv(tot, DS)+ld.first+ld.final
    return value, len(ld.G)


def verify_tree(ld, node, box=None):
    """Returns (maximum, boxes, checks). Children must partition the parent."""
    if box is None:
        box = [(0, e) for e in ld.ends]
    if 'split' in node:
        k, mid = node['split'], node['mid']
        a, b = box[k]
        assert type(mid) is int and a < mid < b
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        m1, n1, c1 = verify_tree(ld, node['children'][0], left)
        m2, n2, c2 = verify_tree(ld, node['children'][1], right)
        return max(m1, m2), n1+n2, c1+c2
    value, checks = check_box(ld, box, node['duals'])
    assert value < S, ('box value', value/S, box)
    if 'value' in node:
        assert node['value'] == value
    return value, 1, checks


# ---------------------------------------------------------------- proposer
def _lp(G, A, b):
    import highspy
    m, n = A.shape
    h = highspy.Highs()
    h.setOptionValue('output_flag', False); h.setOptionValue('simplex_strategy', 4)
    lp = highspy.HighsLp()
    lp.num_col_ = n; lp.num_row_ = m
    lp.col_cost_ = -np.asarray(G, float); lp.col_lower_ = np.zeros(n)
    lp.col_upper_ = np.full(n, highspy.kHighsInf)
    lp.row_lower_ = np.full(m, -highspy.kHighsInf); lp.row_upper_ = np.asarray(b, float)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.arange(0, m*n+1, m)
    lp.a_matrix_.index_ = np.tile(np.arange(m), n)
    lp.a_matrix_.value_ = np.ascontiguousarray(A.T).reshape(-1)
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    sol = h.getSolution()
    return -h.getInfo().objective_function_value, np.array(sol.row_dual)


class Proposer:
    """Float LP proposals with cached per-endpoint cost vectors; exact checks via check_box."""
    def __init__(self, ld):
        self.ld = ld
        self.Gf = np.array(ld.G, float)/S
        self.Wf = np.array(ld.W, float)/S
        self.Cf = np.array(ld.cnt, float)/S
        self.V0 = np.array(ld.V0, float)/S
        self.Vk = [np.array(sv['v'], float)/S for sv in ld.sieve]
        self.Dk = [np.array(row_D(sv), float)/S for sv in ld.sieve]
        self.dk = [sv['d']/S for sv in ld.sieve]
        self.famk = [[(n, v/S, Dn/S) for n, v, Dn in fam_terms(sv)] for sv in ld.sieve]
        self.cache = {}

    def fcosts(self, k, b):
        key = (k, b)
        if key not in self.cache:
            t = b/TS
            if k == 0:
                self.cache[key] = np.maximum(self.V0-t, 0)**2
            else:
                self.cache[key] = np.maximum(self.Vk[k-1]-t, 0)**2/self.Dk[k-1]
        return self.cache[key]

    def fbudgets(self, box):
        ld = self.ld
        a0, b0 = old_effective(ld, *box[0])
        if a0 > b0:
            return [-1.0]
        out = [ld.old_budget(a0, b0)/S]
        for k, (a, b) in enumerate(box[1:]):
            out.append(1-(a/TS)**2/self.dk[k]-sum(n*max(v-b/TS, 0)**2/Dn for n, v, Dn in self.famk[k]))
        return out

    def eff(self, box):
        a0, b0 = old_effective(self.ld, *box[0])
        return [(a0, b0)]+list(box[1:])

    def value(self, box):
        bud = self.fbudgets(box)
        if min(bud) < 0:
            return -1.0, None
        A = np.vstack([self.Wf, self.Cf]+[self.fcosts(k, b) for k, (a, b) in enumerate(self.eff(box))])
        res = _lp(self.Gf, A, [self.ld.F/S, 2.0]+bud)
        if res is None:
            return None, None
        val, duals = res
        return val+(self.ld.first+self.ld.final)/S, [max(0.0, -x) for x in duals]


def integer_duals(ld, box, y):
    costs, budgets = box_data(ld, box)
    duals0 = [y[0], y[1]]+list(y[2:])
    # Uniform rescaling repair: the float dual is feasible up to solver tolerance.
    for factor in (1+1e-9, 1+1e-7, 1+1e-5, 1+1e-3):
        Y = max(0, math.ceil(duals0[0]*factor*DS)+1)
        U = max(0, math.ceil(duals0[1]*factor*DS)+1)
        Z = [max(0, math.ceil(z*factor*DS)+1) if z > 1e-15 else 0 for z in duals0[2:]]
        worst = None
        ok = True
        for i in range(len(ld.G)):
            lhs = Y*ld.W[i]+U*ld.cnt[i]+sum(z*c[i] for z, c in zip(Z, costs) if z)
            if lhs < DS*ld.G[i]:
                ok = False
                break
        if ok:
            duals = dict(Y=Y, U=U, Z=Z)
            value, _ = check_box(ld, box, duals)
            return duals, value
    # fallback: repair through the strictly positive far column
    need = 0
    for i in range(len(ld.G)):
        lhs = Y*ld.W[i]+U*ld.cnt[i]+sum(z*c[i] for z, c in zip(Z, costs) if z)
        deficit = DS*ld.G[i]-lhs
        if deficit > 0:
            need = max(need, ceildiv(deficit, ld.W[i]))
    duals = dict(Y=Y+need, U=U, Z=Z)
    value, _ = check_box(ld, box, duals)
    return duals, value


class CannotCertify(RuntimeError):
    def __init__(self, msg, box=None, value=None, x=None):
        super().__init__(msg)
        self.box, self.value, self.x = box, value, x


def build(ld, target=Q(9999999, 10000000), max_boxes=400000, min_width=1):
    """Adaptive bisection; split dimension chosen by dual-weighted threshold loss."""
    P = Proposer(ld)
    full = [(0, e) for e in ld.ends]
    count = [0]
    tgt = float(target)

    def lp_full(box):
        bud = P.fbudgets(box)
        if min(bud) < 0:
            return 'excluded', None, None
        A = np.vstack([P.Wf, P.Cf]+[P.fcosts(k, b) for k, (a, b) in enumerate(P.eff(box))])
        import highspy
        m, n = A.shape
        h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('simplex_strategy', 4)
        lp = highspy.HighsLp()
        lp.num_col_ = n; lp.num_row_ = m
        lp.col_cost_ = -P.Gf; lp.col_lower_ = np.zeros(n); lp.col_upper_ = np.full(n, highspy.kHighsInf)
        lp.row_lower_ = np.full(m, -highspy.kHighsInf); lp.row_upper_ = np.array([ld.F/S, 2.0]+bud)
        lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
        lp.a_matrix_.start_ = np.arange(0, m*n+1, m)
        lp.a_matrix_.index_ = np.tile(np.arange(m), n)
        lp.a_matrix_.value_ = np.ascontiguousarray(A.T).reshape(-1)
        h.passModel(lp); h.run()
        if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
            return None, None, None
        sol = h.getSolution()
        val = -h.getInfo().objective_function_value+(ld.first+ld.final)/S
        return val, [max(0.0, -x) for x in sol.row_dual], np.array(sol.col_value)

    def rec(box):
        count[0] += 1
        val, y, x = lp_full(box)
        if count[0] > max_boxes:
            raise CannotCertify('box budget exhausted', box, val, x)
        if val == 'excluded':
            costs, budgets = box_data(ld, box)
            assert min(budgets) < 0
            return dict(duals='excluded')
        if val is not None and val < tgt:
            duals, value = integer_duals(ld, box, y)
            if value < target*S:
                return dict(duals=duals, value=value)
        # dual-weighted loss per dimension
        best = None
        for k, (a, b) in enumerate(box):
            if b-a <= min_width:
                continue
            if y is None:
                loss = (b-a)/max(1, full[k][1])
            else:
                z = y[2+k]
                ca = P.fcosts(k, a); cb = P.fcosts(k, b)
                if k == 0:
                    dbud = (ld.old_budget(a, a)-ld.old_budget(b, b))/S
                else:
                    dbud = ((b/TS)**2-(a/TS)**2)/P.dk[k-1]
                loss = z*(abs(dbud)+float(np.dot(x, ca-cb)))+1e-12*(b-a)/max(1, full[k][1])
            if best is None or loss > best[0]:
                best = (loss, k)
        if best is None:
            if val is not None:
                duals, value = integer_duals(ld, box, y)
                if value < S:
                    return dict(duals=duals, value=value)
            raise CannotCertify('unresolved box', box, val, x)
        k = best[1]
        a, b = box[k]
        mid = (a+b)//2
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        return dict(split=k, mid=mid, children=[rec(left), rec(right)])
    tree = rec(full)
    mx, nb, checks = verify_tree(ld, tree)
    return tree, mx, nb, checks
