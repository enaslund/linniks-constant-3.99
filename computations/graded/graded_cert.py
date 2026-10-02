"""Leaf LP and exact certificates of the graded-near proof (research/PROOF.md §7).

A leaf has ordinary columns (the repository's parameter bins) and, for an outside
first zero, hidden columns (the first family's local zeros) with a hidden count.
Its constraints are:

  far row      sum_i W_i x_i + sum_h WH_h y_h <= F                (X Lemma 5.1)
  count row    sum_i cnt_i x_i <= 2                                (third-family rule)
  hidden count sum_h NH_h y_h <= ng                                (outside leaves)
  second       sum_j z_j = n2          (reserved second family as columns, optional)
  near rows k  exists tau_k in [0, sqrt d_k]:
               sum_i x_i (v_ik - tau_k)_+^2 / D_ik + sum_h y_h (vh_hk - tau_k)_+^2 / Dh_hk
               + sum_j z_j (vs_jk - tau_k)_+^2 / Ds_jk
               + sum_fam n (v_f - tau_k)_+^2 / D_f  <=  1 - tau_k^2 / d_k
               (graded near lemma, or the inherited two-test row of PROOF.md §6.6)

and the objective first + final + sum_i G_i x_i + sum_h GH_h y_h + sum_j GS_j z_j must stay below 1.
The second-family columns z_j also carry far costs WS_j; the equality has a free dual P - M.
Every near row is of the same kind; there is no distinguished first dimension.

A certificate is a bisection tree over the threshold box [0,end_1] x ... x [0,end_K]
(ticks of 1/TS).  Each tree leaf fixes, per dimension, the first-order relaxation
(order 2: costs at the upper threshold, budget at the lower) or the second-order
tangent pair (order 1: cases 0/1 from Phi(m) -+ h Phi'(m) <= const, Phi convex),
and records for every case either an exclusion (a constraint with nonnegative
costs and a negative budget) or integer duals (Y, V, U, P, M, Z_1..Z_K) satisfying
every column inequality exactly.  Weak duality then bounds the objective on the case.
"""
import itertools, math
from fractions import Fraction as Q
import numpy as np

S = 10**16           # input scale
TS = 10**6           # threshold ticks
DS = 10**12          # dual scale
HS = S//TS//2


def ceildiv(a, b):
    return -((-a)//b)


def isqrt_up(n):
    r = math.isqrt(n)
    return r if r*r == n else r+1


def ceil_q(x):
    return -((-x.numerator)//x.denominator)


def tangent_cost(v, m2, h2, case):
    """S-scaled lower bound of ((v-m)_+ +- h)^2 - h^2, m=m2/2, h=h2/2 ticks, v S-scaled."""
    x = v-m2*HS
    if x <= 0:
        return 0
    hS = h2*HS
    y = x*(x+2*hS) if case == 0 else x*(x-2*hS)
    return y//S


def tangent_exact(v, m, h, case):
    x = max(v-m, 0)
    if case == 0:
        return (x+h)**2-h*h
    return (x-h)**2-h*h if x > 0 else Q(0)


class Leaf:
    """Integer data of one leaf.  inp: the repository input (inside or outside model);
    rows: near-row dicts {d, D, v, Dv?, vh?, Dvh?, vs?, Dvs?, fam?} (graded_leaves.build_row)."""
    def __init__(self, inp, rows):
        self.inp = inp
        R = inp['rows']
        self.G = [r[3] for r in R]; self.W = [r[2] for r in R]
        assert all(w > 0 for w in self.W)
        self.cnt = list(inp.get('count_cost') or [0]*len(R))
        assert len(self.cnt) == len(R) and all(c in (0, S) for c in self.cnt)
        assert inp.get('count_budget', 2*S) == 2*S
        self.F = inp['far_budget']; self.first = inp['first']; self.final = inp['final']
        hh = inp.get('hidden_rows') or []
        self.GH = [r[3] for r in hh]; self.WH = [r[2] for r in hh]; self.NH = [r[5] for r in hh]
        self.ng = inp['n'] if hh else 0
        sc = inp.get('second_cols') or []
        self.GS = [r[3] for r in sc]; self.WS = [r[2] for r in sc]
        self.n2 = int(inp['second']['n']) if sc else 0
        self.nO, self.nH, self.nS = len(R), len(hh), len(sc)
        ints = self.G+self.W+self.GH+self.WH+self.NH+self.GS+self.WS+[self.F, self.first, self.final]
        assert all(type(x) is int for x in ints), 'leaf data must be Python integers'
        assert all(x > 0 for x in self.WH+self.WS) and all(x >= 0 for x in self.NH)
        assert S % (2*TS) == 0
        self.rows = rows
        for sv in rows:
            assert type(sv['d']) is int and type(sv['D']) is int
            assert len(sv['v']) == self.nO and sv['d'] > 0 and sv['D'] > 0
            assert all(type(x) is int and x >= 0 for x in sv['v'])
            if 'Dv' in sv:
                assert len(sv['Dv']) == self.nO and all(type(x) is int and x > 0 for x in sv['Dv'])
            if 'vh' in sv:
                assert len(sv['vh']) == self.nH and all(type(x) is int and x >= 0 for x in sv['vh'])
                assert len(sv.get('Dvh', [sv['D']]*self.nH)) == self.nH
                assert all(type(x) is int and x > 0 for x in sv.get('Dvh', []))
            if self.nS:
                assert len(sv.get('vs', [0]*self.nS)) == self.nS and all(type(x) is int and x >= 0 for x in sv.get('vs', []))
                assert len(sv.get('Dvs', [sv['D']]*self.nS)) == self.nS and all(type(x) is int and x > 0 for x in sv.get('Dvs', []))
            else:
                assert 'vs' not in sv
            for fm in sv.get('fam', []):
                assert len(fm) in (2, 3) and all(type(x) is int and x >= 0 for x in fm) and (len(fm) == 2 or fm[2] > 0)
        self.ends = [isqrt_up(sv['d']*TS*TS//S+1) for sv in rows]
        self._memo, self._fmemo = {}, {}
        z0, zS = [0]*self.nS, [S]*self.nS
        self._fixed = [np.array(self.W+self.WH+self.WS, float)/S,
                       np.array(self.cnt+[0]*self.nH+z0, float)/S,
                       np.array([0]*self.nO+self.NH+z0, float)/S,
                       np.array([0]*(self.nO+self.nH)+zS, float)/S,
                       -np.array([0]*(self.nO+self.nH)+zS, float)/S]
        self._G = np.array(self.G+self.GH+self.GS, float)/S
        # exact data of the column inequalities, all columns in one list (ordinary, hidden, second)
        self._Wall = self.W+self.WH+self.WS
        self._cnt_all = self.cnt+[0]*(self.nH+self.nS)
        self._NH_all = [0]*self.nO+self.NH+[0]*self.nS
        self._S_all = [0]*(self.nO+self.nH)+[S]*self.nS
        self._DSG = [DS*g for g in self.G+self.GH+self.GS]

    def _Dv(self, sv):
        return sv['Dv'] if 'Dv' in sv else [sv['D']]*self.nO

    def _Dvh(self, sv):
        return sv.get('Dvh', [sv['D']]*self.nH)

    def _vs(self, sv):
        return list(sv.get('vs', [0]*self.nS))

    def _Dvs(self, sv):
        return list(sv.get('Dvs', [sv['D']]*self.nS))

    @staticmethod
    def _fam(sv):
        return [(fm[0], fm[1], fm[2] if len(fm) == 3 else sv['D']) for fm in sv.get('fam', [])]

    def row_case(self, k, a, b, c):
        """Costs (ordinary then hidden; lower bounds) and budget (upper bound) of near row k on [a,b].
        Memoized: the value depends only on (k, a, b, c) and the leaf's fixed data."""
        key = (k, a, b, c)
        hit = self._memo.get(key)
        if hit is None:
            hit = self._memo[key] = self._row_case(k, a, b, c)
        return hit

    def row_float(self, k, a, b, c):
        """Floating copy of row_case's costs (proposal only)."""
        key = (k, a, b, c)
        hit = self._fmemo.get(key)
        if hit is None:
            costs, _ = self.row_case(k, a, b, c)
            hit = self._fmemo[key] = np.array(costs, float)/S
        return hit

    def _row_case(self, k, a, b, c):
        sv = self.rows[k]
        vs = list(sv['v'])+list(sv.get('vh', [0]*self.nH))+self._vs(sv)
        Ds = self._Dv(sv)+self._Dvh(sv)+self._Dvs(sv)
        if c == 2:
            sh = b*(S//TS)
            costs = [max(v-sh, 0)**2//Dk for v, Dk in zip(vs, Ds)]
            B = S-(S*S*a*a)//(TS*TS*sv['d'])
            B -= sum((n*max(v-sh, 0)**2)//Dn for n, v, Dn in self._fam(sv))
            return costs, B
        m2, h2 = a+b, b-a
        costs = [(tangent_cost(v, m2, h2, c)*S)//Dk for v, Dk in zip(vs, Ds)]
        dd = Q(sv['d'], S)
        p = Q(a if c == 0 else b, TS); hq = Q(h2, 2*TS)
        Bq = 1-(p*p-hq*hq)/dd
        Bq -= sum(n*tangent_exact(Q(v, S), Q(m2, 2*TS), hq, c)/Q(Dn, S) for n, v, Dn in self._fam(sv))
        return costs, ceil_q(Bq*S)


def cases(orders):
    return list(itertools.product(*[((0, 1) if o == 1 else (2,)) for o in orders]))


def case_data(leaf, box, eps):
    costs, budgets = [], []
    for k, (a, b) in enumerate(box):
        ck, bk = leaf.row_case(k, a, b, eps[k])
        costs.append(ck); budgets.append(bk)
    return costs, budgets


def excludable(cd):
    """Infeasible if some near row has a negative budget and only nonnegative costs."""
    costs, budgets = cd
    return any(b < 0 and min(c, default=0) >= 0 for c, b in zip(costs, budgets))


def check_case(leaf, cd, du):
    """Exact weak-duality bound (S-scaled) for one case; asserts every column inequality."""
    costs, budgets = cd
    Y, V, U, Z = du['Y'], du.get('V', 0), du.get('U', 0), du['Z']
    P, M = du.get('P', 0), du.get('M', 0)
    assert all(type(x) is int and x >= 0 for x in [Y, V, U, P, M]+Z) and len(Z) == len(costs)
    if not leaf.nH:
        assert U == 0
    if not leaf.nS:
        assert P == 0 and M == 0
    # every column (ordinary, hidden, second family) in one exact integer pass per row; a second-family
    # column has coefficient S in the <= row and -S in the >= row of its equality sum z = n2
    n = leaf.nO+leaf.nH+leaf.nS
    assert all(len(c) == n for c in costs)
    lhs = [Y*w for w in leaf._Wall]
    for mult, coef in ((V, leaf._cnt_all), (U, leaf._NH_all), (P-M, leaf._S_all)):
        if mult:
            lhs = [a+mult*c for a, c in zip(lhs, coef)]
    for z, c in zip(Z, costs):
        if z:
            lhs = [a+z*x for a, x in zip(lhs, c)]
    for i, (a, g) in enumerate(zip(lhs, leaf._DSG)):
        if a < g:
            raise AssertionError(('column', i))
    tot = Y*leaf.F+V*2*S+U*leaf.ng*S+(P-M)*leaf.n2*S+sum(z*b for z, b in zip(Z, budgets))
    return ceildiv(tot, DS)+leaf.first+leaf.final


def check_box(leaf, box, node):
    orders = node['orders']
    assert len(orders) == len(box) and all(o in (1, 2) for o in orders)
    allc = cases(orders)
    assert len(node['cases']) == len(allc)
    mx = -1
    for eps, du in zip(allc, node['cases']):
        cd = case_data(leaf, box, eps)
        if du == 'excluded':
            assert excludable(cd), 'exclusion needs a negative budget with nonnegative costs'
            continue
        mx = max(mx, check_case(leaf, cd, du))
    return mx


def verify_tree(leaf, node, box=None):
    """Returns (maximum, boxes).  Children partition their parent box."""
    if box is None:
        box = [(0, e) for e in leaf.ends]
    if 'split' in node:
        k, mid = node['split'], node['mid']
        a, b = box[k]
        assert type(mid) is int and a < mid < b
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        m1, n1 = verify_tree(leaf, node['children'][0], left)
        m2, n2 = verify_tree(leaf, node['children'][1], right)
        return max(m1, m2), n1+n2
    v = check_box(leaf, box, node)
    assert v < S, ('box value', v/S, box)
    return v, 1


# ------------------------------------------------------------------ proposer (floating; untrusted)
class CannotCertify(RuntimeError):
    def __init__(self, msg, box=None, value=None):
        super().__init__(msg)
        self.box, self.value = box, value


def _lp(G, A, b, basis_out=None):
    """Floating LP max G.x s.t. A x <= b, x >= 0 (proposal only).  With basis_out (a list), the
    optimal basis (basic columns, tight rows) is appended to it for reuse on nearby boxes."""
    import highspy
    m, n = A.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('simplex_strategy', 4)
    lp = highspy.HighsLp(); lp.num_col_ = n; lp.num_row_ = m
    lp.col_cost_ = -np.asarray(G, float); lp.col_lower_ = np.zeros(n); lp.col_upper_ = np.full(n, highspy.kHighsInf)
    lp.row_lower_ = np.full(m, -highspy.kHighsInf); lp.row_upper_ = np.asarray(b, float)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.arange(0, m*n+1, m); lp.a_matrix_.index_ = np.tile(np.arange(m), n)
    lp.a_matrix_.value_ = np.ascontiguousarray(A.T).reshape(-1)
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    sol = h.getSolution()
    if basis_out is not None:
        B = h.getBasis(); basic = highspy.HighsBasisStatus.kBasic
        J = [j for j, st in enumerate(B.col_status) if st == basic]
        R = [r for r, st in enumerate(B.row_status) if st != basic]
        if len(J) == len(R):
            basis_out.append((tuple(J), tuple(R)))
    return -h.getInfo().objective_function_value, [max(0.0, -x) for x in sol.row_dual], np.array(sol.col_value)


class ColumnLP:
    """max G.x s.t. A x <= b, x >= 0 by column generation on a working set shared across calls
    (proposal only; the exact check in check_case decides).  All columns are priced after each
    restricted solve, so a returned optimum is the optimum of the full LP up to tolerance.  Falls
    back to the full LP when the restricted problem is not optimal."""
    def __init__(self, cap=160, add=24):
        self.W = set(); self.cap = cap; self.add = add

    def solve(self, G, A, b, basis_out=None):
        m, n = A.shape
        if len(self.W) > self.cap:
            self.W = set()
        W = set(j for j in self.W if j < n)
        if len(W) < 2*m:
            ratio = G/np.maximum(A[0], 1e-300)
            W |= set(np.argsort(-ratio)[:max(self.add, 2*m)].tolist())
        scale = max(1.0, float(np.max(np.abs(G))))
        for _ in range(12):
            Wl = sorted(W)
            got = [] if basis_out is not None else None
            r = _lp(G[Wl], A[:, Wl], b, got)
            if r is None:
                break
            val, y, xW = r
            red = G-A.T@np.asarray(y)
            bad = np.where(red > 1e-9*scale)[0]
            if len(bad) == 0:
                x = np.zeros(n); x[Wl] = xW
                self.W = set(Wl[i] for i in np.nonzero(xW > 0)[0]) | set(self.W)
                if basis_out is not None and got:
                    J, R = got[0]
                    basis_out.append((tuple(Wl[j] for j in J), R))
                return val, y, x
            W |= set(bad[np.argsort(-red[bad])][:self.add].tolist())
        return _lp(G, A, b, basis_out)


def _from_basis(G, A, b, basis):
    """Dual and primal of a given basis of max G.x, A x <= b, x >= 0 (proposal only).  Returns
    (value, y, x) when the basis is dual feasible (y >= 0, A^T y >= G); its value b.y is then an
    upper bound of the LP optimum by weak duality.  None otherwise."""
    J, R = basis
    m, n = A.shape
    y = np.zeros(m)
    if J:
        M = A[np.ix_(R, J)]
        try:
            yR = np.linalg.solve(M.T, G[list(J)])
            xJ = np.linalg.solve(M, np.asarray(b, float)[list(R)])
        except np.linalg.LinAlgError:
            return None
        y[list(R)] = yR
    if np.any(y < -1e-12):
        return None
    y = np.maximum(y, 0.0)
    scale = max(1.0, float(np.max(np.abs(G))))
    if np.any(A.T @ y < G-1e-10*scale):
        return None
    x = np.zeros(n)
    if J:
        x[list(J)] = np.maximum(xJ, 0.0)
    return float(np.dot(np.asarray(b, float), y)), list(y), x


def _dual_lp(G, A, b):
    """min b.y s.t. A^T y >= G, y >= 0, b.y >= -1: a certificate also for an infeasible primal."""
    import highspy
    m, n = A.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False)
    lp = highspy.HighsLp(); lp.num_col_ = m; lp.num_row_ = n+1
    lp.col_cost_ = np.asarray(b, float); lp.col_lower_ = np.zeros(m); lp.col_upper_ = np.full(m, highspy.kHighsInf)
    M = np.vstack([A.T, np.asarray(b, float)[None, :]])
    lp.row_lower_ = np.concatenate([np.asarray(G, float), [-1.0]]); lp.row_upper_ = np.full(n+1, highspy.kHighsInf)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.arange(0, (n+1)*m+1, n+1); lp.a_matrix_.index_ = np.tile(np.arange(n+1), m)
    lp.a_matrix_.value_ = np.ascontiguousarray(M.T).reshape(-1)
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    y = np.array(h.getSolution().col_value)
    return float(np.dot(b, y)), [max(0.0, v) for v in y], None


def lp_matrix(leaf, cd, box=None, eps=None):
    costs, budgets = cd
    if box is not None:
        A = leaf._fixed+[leaf.row_float(k, a, b, e) for k, ((a, b), e) in enumerate(zip(box, eps))]
    else:
        A = leaf._fixed+[np.array(c, float)/S for c in costs]
    b = [leaf.F/S, 2.0, float(leaf.ng), float(leaf.n2), -float(leaf.n2)]+[x/S for x in budgets]
    return leaf._G, np.vstack(A), b


NFIX = 5     # fixed LP rows before the near rows: far, count, hidden count, second <=, second >=


def integer_duals(leaf, cd, y):
    for factor in (1+1e-9, 1+1e-7, 1+1e-5, 1+1e-3, 1.01):
        Y = max(0, math.ceil(y[0]*factor*DS)+1)
        V = max(0, math.ceil(y[1]*factor*DS)+1) if y[1] > 1e-15 else 0
        U = max(0, math.ceil(y[2]*factor*DS)+1) if (leaf.nH and y[2] > 1e-15) else 0
        # free dual of the equality: net value, rounded up on the <= side
        t = (y[3]-y[4])*DS if leaf.nS else 0.0
        P = max(0, math.ceil(t*factor)+1) if t > 0 else 0
        M = max(0, math.floor(-t/factor)-1) if t < 0 else 0
        Z = [max(0, math.ceil(z*factor*DS)+1) if z > 1e-15 else 0 for z in y[NFIX:]]
        du = dict(Y=Y, Z=Z)
        if V:
            du['V'] = V
        if U:
            du['U'] = U
        if P:
            du['P'] = P
        if M:
            du['M'] = M
        try:
            return du, check_case(leaf, cd, du)
        except AssertionError:
            continue
    return None, None


_FV_LP = {}


def float_value(leaf, taus):
    """Floating LP maximum at the threshold point taus (proposal only)."""
    box = [(t, t) for t in taus]
    eps = (2,)*len(box)
    cd = case_data(leaf, box, eps)
    G, A, b = lp_matrix(leaf, cd, box, eps)
    if USE_COLUMN_LP:
        if id(leaf) not in _FV_LP or _FV_LP[id(leaf)][0] is not leaf:
            if len(_FV_LP) > 50:
                _FV_LP.clear()
            _FV_LP[id(leaf)] = (leaf, ColumnLP())
        r = _FV_LP[id(leaf)][1].solve(G, A, b)
    else:
        r = _lp(G, A, b)
    return -1.0 if r is None else r[0]+(leaf.first+leaf.final)/S


def float_worst(leaf, starts=2, grid=12, sweeps=5, seed=0):
    """Approximate maximum over thresholds by coordinate search (proposal only)."""
    ends = leaf.ends
    grids = [[int(v) for v in np.unique(np.linspace(0, e, grid).astype(np.int64))] for e in ends]
    rng = np.random.default_rng(seed)
    best = -np.inf
    for st in range(starts):
        t = [int(g[rng.integers(len(g))]) if st else int(g[len(g)//2]) for g in grids]
        cur = float_value(leaf, t)
        step = [max(1, e//(2*grid)) for e in ends]
        for sw in range(sweeps):
            imp = False
            for k in range(len(t)):
                for cand in list(grids[k])+[max(0, t[k]-step[k]), min(ends[k], t[k]+step[k])]:
                    tt = list(t); tt[k] = int(cand)
                    v = float_value(leaf, tt)
                    if v > cur+1e-12:
                        cur, t, imp = v, tt, True
            step = [max(1, s//3) for s in step]
            if not imp and sw > 1:
                break
        best = max(best, cur)
    return best


TANGENT_HOPE = 0.35    # proposer heuristic: tangent cases are tried when pv + TANGENT_HOPE*(v1 - pv) < target
USE_COLUMN_LP = True   # proposer: column generation for the case LPs


def build(leaf, target=Q(9999999, 10000000), max_boxes=20000, min_width=1):
    """Adaptive bisection with mixed-order cases; every accepted case is checked exactly.

    Per box: the first-order case (one LP); if it fails, the LP value at the box centre (a lower
    bound for every certificate on the box; above the target the rows cannot succeed); then the
    tangent cases on the active dimensions, evaluated only when they can plausibly succeed and
    abandoned at the first failing case.  All of this only proposes duals; acceptance is exact."""
    full = [(0, e) for e in leaf.ends]
    K = len(full)
    count = [0]
    tgt = float(target)

    bases = {}           # last optimal basis per case pattern, reused on nearby boxes
    clp = ColumnLP() if USE_COLUMN_LP else None

    def evaluate(box, orders, stop=None, hints=True):
        out = []; mx = -1.0
        for eps in cases(orders):
            cd = case_data(leaf, box, eps)
            if excludable(cd):
                out.append((cd, 'excluded', None, -1.0)); continue
            G, A, b = lp_matrix(leaf, cd, box, eps)
            if hints and eps in bases:
                r = _from_basis(G, A, b, bases[eps])
                if r is not None and r[0]+(leaf.first+leaf.final)/S < tgt:
                    val, y, x = r
                    val += (leaf.first+leaf.final)/S
                    out.append((cd, y, x, val)); mx = max(mx, val)
                    continue
            got = []
            r = clp.solve(G, A, b, got) if clp is not None else _lp(G, A, b, got)
            if got:
                bases[eps] = got[0]
            if r is None:
                r = _dual_lp(G, A, b)
                if r is None:
                    out.append((cd, None, None, float('inf'))); mx = float('inf')
                    if stop is not None:
                        return mx, out, False
                    continue
            val, y, x = r
            val += (leaf.first+leaf.final)/S
            out.append((cd, y, x, val)); mx = max(mx, val)
            if stop is not None and val >= stop:
                return mx, out, False
        return mx, out, True

    def accept(out, orders):
        node = []; vmax = -1
        for cd, y, x, val in out:
            if isinstance(y, str):
                node.append('excluded'); continue
            du, v = integer_duals(leaf, cd, y)
            if du is None or v >= target*S:
                return None
            node.append(du); vmax = max(vmax, v)
        return dict(cases=node, orders=list(orders), value=vmax)

    def rec(box):
        count[0] += 1
        first = [2]*K
        v1, out, _ = evaluate(box, first)
        if v1 < tgt:
            nd = accept(out, first)
            if nd is None:            # rounding of a reused basis failed: retry with fresh LPs
                v1, out, _ = evaluate(box, first, hints=False)
                nd = accept(out, first) if v1 < tgt else None
            if nd is not None:
                return nd
        # every certificate bound on this box is at least the LP value at any point of it: if the
        # centre is already above the target, no subdivision can succeed with these rows
        centre = [(a+b)//2 for a, b in box]
        pv = float_value(leaf, centre)
        if pv >= tgt+1e-7:
            raise CannotCertify('point value above target', box, pv)
        worst = max(out, key=lambda o: o[3])
        yw = worst[1]
        orders = [1 if (yw is None or isinstance(yw, str) or yw[NFIX+k] > 1e-9) else 2 for k in range(K)]
        mx = v1
        if orders != first and pv+TANGENT_HOPE*(min(v1, 2.0)-pv) < tgt:
            v2, out2, complete = evaluate(box, orders, stop=tgt)
            if complete and v2 < tgt:
                nd = accept(out2, orders)
                if nd is None:
                    v2, out2, complete = evaluate(box, orders, stop=tgt, hints=False)
                    nd = accept(out2, orders) if complete and v2 < tgt else None
                if nd is not None:
                    return nd
            if complete:
                out, mx = out2, v2
        if count[0] > max_boxes:
            raise CannotCertify('box budget exhausted', box, mx)
        worst = max(out, key=lambda o: o[3])
        y, x = worst[1], worst[2]
        best = None
        for k, (a, b) in enumerate(box):
            if b-a <= min_width:
                continue
            h = (b-a)/(2*TS)
            if y is None or isinstance(y, str):
                est = (b-a)/max(1, full[k][1])
            else:
                z = max(y[NFIX+k], 0.5)
                mass = float(np.sum(x)) if x is not None else 1.0
                sv = leaf.rows[k]
                est = z*h*h*(S/sv['d']+mass*S/sv['D'])
            if best is None or est > best[0]:
                best = (est, k)
        if best is None:
            raise CannotCertify('unresolved box', box, mx)
        k = best[1]
        a, b = box[k]
        mid = (a+b)//2
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        return dict(split=k, mid=mid, children=[rec(left), rec(right)])
    tree = rec(full)
    return tree, tree_max(tree), tree_boxes(tree)


def tree_max(node):
    return max(tree_max(c) for c in node['children']) if 'split' in node else node.get('value', -1)


def tree_boxes(node):
    return sum(tree_boxes(c) for c in node['children']) if 'split' in node else 1
