"""Mixed-order threshold certificates: per box and dimension either the first-order
box relaxation (costs at the upper, budget at the lower threshold; one case) or the
second-order tangent disjunction (two cases).  Otherwise identical to certificate2.

Second-order (tangent-disjunction) threshold certificates.

Each near inequality has the form  Phi(tau) <= const  with

    Phi(tau) = sum_j c_j (v_j - tau)_+^2 + kappa tau^2 ,

convex and C^1 in tau (old near: c_j = 1 for ordinary characters, n D/Df and
n2 for the distinguished families, kappa = D/d, const = D; sieve near:
c_j = 1/D_k, kappa = 1/d_k, const = 1).  If some tau* in [a,b] satisfies it,
then with m=(a+b)/2, h=(b-a)/2, convexity gives Phi(tau*) >= Phi(m) + Phi'(m)(tau*-m),
hence either  Phi(m) - h Phi'(m) <= const  (case 0)  or  Phi(m) + h Phi'(m) <= const
(case 1).  Term by term,

    (v-m)_+^2 + 2h(v-m)_+ = ((v-m)_+ + h)^2 - h^2,
    (v-m)_+^2 - 2h(v-m)_+ = ((v-m)_+ - h)^2 - h^2,
    m^2 -+ 2hm = (m -+ h)^2 - h^2,

so each case is a linear constraint in the population with exact integer
coefficients.  A box is certified by one dual per case vector in {0,1}^(K+1);
the relaxation error is second order in the box width.
"""
import itertools, math
from fractions import Fraction as Q
import numpy as np
from certificate import LeafData, ceildiv, S, TS, DS, old_effective, row_D, fam_terms

HS = S//TS//2          # S/(2 TS): converts ticks to half-tick S-scaled units


def tangent_cost(v, m2, h2, case):
    """S-scaled lower bound of ((v-m)_+ +- h)^2 - h^2 with m=m2/2, h=h2/2 in ticks, v S-scaled."""
    x = v-m2*HS
    if x <= 0:
        return 0
    hS = h2*HS
    y = x*(x+2*hS) if case == 0 else x*(x-2*hS)
    return y//S


def floor_q(x):
    return x.numerator//x.denominator


def ceil_q(x):
    return -((-x.numerator)//x.denominator)


def case_data(ld, box, eps):
    """Costs (lower bounds, S-scaled ints) and budgets (upper bounds) for case vector eps."""
    a0, b0 = old_effective(ld, *box[0])
    if a0 > b0:
        return None
    costs, budgets = [], []
    m2, h2 = a0+b0, b0-a0
    c = eps[0]
    if c == 2:
        costs.append(ld.old_costs(b0)); budgets.append(ld.old_budget(a0, b0))
    else:
        costs.append([tangent_cost(v, m2, h2, c) for v in ld.V0])
    d, D, Df = Q(ld.d0, S), Q(ld.D0, S), Q(ld.Df, S)
    p = Q(a0 if c == 0 else b0, TS); hq = Q(h2, 2*TS)

    def T(v):  # exact tangent term for a rational v
        x = max(v-Q(m2, 2*TS), 0)
        return (x+hq)**2-hq*hq if c == 0 else (x-hq)**2-hq*hq if x > 0 else Q(0)
    if c != 2:
        B = D-(D/d)*(p*p-hq*hq)-ld.n*(D/Df)*T(Q(ld.vf, S))-ld.n2*T(Q(ld.v2, S))
        budgets.append(ceil_q(B*S))
    for k, (a, b) in enumerate(box[1:]):
        sv = ld.sieve[k]
        c = eps[k+1]
        if c == 2:
            costs.append(ld.sieve_costs(k, b)); budgets.append(ld.sieve_budget(k, a, b))
            continue
        m2, h2 = a+b, b-a
        # cost_i = T_i / D'  (D' = D/S): S-scaled -> S*T_i/D' = S^2 T_i / D ; tangent_cost gives S*T_i
        costs.append([(tangent_cost(v, m2, h2, c)*S)//Dk for v, Dk in zip(sv['v'], row_D(sv))])
        dd = Q(sv['d'], S)
        p = Q(a if c == 0 else b, TS); hq = Q(h2, 2*TS)
        B = 1-(p*p-hq*hq)/dd
        if sv.get('fam'):
            B -= sum(n*tangent_exact(Q(v, S), Q(m2, 2*TS), hq, c)/Q(Dn, S) for n, v, Dn in fam_terms(sv))
        budgets.append(ceil_q(B*S))
    return costs, budgets


def tangent_exact(v, m, h, case):
    """((v-m)_+ + h)^2 - h^2 (case 0) or ((v-m)_+ - h)^2 - h^2 (case 1), exact rationals."""
    x = max(v-m, 0)
    if case == 0:
        return (x+h)**2-h*h
    return (x-h)**2-h*h if x > 0 else Q(0)


def excludable(cd):
    """A case is infeasible if some constraint has a negative budget and only nonnegative costs.
    (Tangent case-1 costs ((v-m)_+ - h)^2 - h^2 can be negative; then a negative budget proves nothing.)"""
    costs, budgets = cd
    return any(b < 0 and min(c, default=0) >= 0 for c, b in zip(costs, budgets))


def _dual_lp(G, A, b):
    """min b.y s.t. A^T y >= G, y >= 0, b.y >= -1 (bounded); a certificate also when the primal is infeasible."""
    import highspy
    m, n = A.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('simplex_strategy', 4)
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
    return float(np.dot(b, y)), [max(0.0, v) for v in y]


def cases(K, orders=None):
    if orders is None:
        orders = [1]*(K+1)
    return list(itertools.product(*[((0, 1) if o == 1 else (2,)) for o in orders]))


def check_case(ld, cd, duals):
    costs, budgets = cd
    Y, U, Z = duals['Y'], duals['U'], duals['Z']
    assert all(type(x) is int and x >= 0 for x in [Y, U]+Z) and len(Z) == len(costs)
    # budgets may be negative: weak duality needs only Y,U,Z >= 0 and the column inequalities
    for i in range(len(ld.G)):
        lhs = Y*ld.W[i]+U*ld.cnt[i]
        for z, cc in zip(Z, costs):
            if z:
                lhs += z*cc[i]
        assert lhs >= DS*ld.G[i], ('column', i)
    tot = Y*ld.F+U*2*S+sum(z*b for z, b in zip(Z, budgets))
    return ceildiv(tot, DS)+ld.first+ld.final


def check_box(ld, box, node):
    """node['cases'] maps case index -> duals or 'excluded'. Returns maximum value."""
    K = len(box)-1
    mx = -1
    orders = node.get('orders', [1]*(K+1))
    assert len(orders) == K+1 and all(o in (1, 2) for o in orders)
    allc = cases(K, orders)
    assert len(node['cases']) == len(allc)
    for eps, du in zip(allc, node['cases']):
        cd = case_data(ld, box, eps)
        if du == 'excluded':
            assert cd is None or excludable(cd), 'exclusion needs a negative budget with nonnegative costs'
            continue
        assert cd is not None
        mx = max(mx, check_case(ld, cd, du))
    return mx


def verify_tree(ld, node, box=None):
    if box is None:
        box = [(0, e) for e in ld.ends]
    if 'split' in node:
        k, mid = node['split'], node['mid']
        a, b = box[k]
        assert type(mid) is int and a < mid < b
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        m1, n1 = verify_tree(ld, node['children'][0], left)
        m2, n2 = verify_tree(ld, node['children'][1], right)
        return max(m1, m2), n1+n2
    v = check_box(ld, box, node)
    assert v < S, ('box value', v/S, box)
    return v, 1


# ------------------------------------------------------------------ proposer
def _lp(G, A, b):
    import highspy
    m, n = A.shape
    h = highspy.Highs(); h.setOptionValue('output_flag', False); h.setOptionValue('simplex_strategy', 4)
    lp = highspy.HighsLp(); lp.num_col_ = n; lp.num_row_ = m
    lp.col_cost_ = -np.asarray(G, float); lp.col_lower_ = np.zeros(n)
    lp.col_upper_ = np.full(n, highspy.kHighsInf)
    lp.row_lower_ = np.full(m, -highspy.kHighsInf); lp.row_upper_ = np.asarray(b, float)
    lp.a_matrix_.format_ = highspy.MatrixFormat.kColwise
    lp.a_matrix_.start_ = np.arange(0, m*n+1, m); lp.a_matrix_.index_ = np.tile(np.arange(m), n)
    lp.a_matrix_.value_ = np.ascontiguousarray(A.T).reshape(-1)
    h.passModel(lp); h.run()
    if h.getModelStatus() != highspy.HighsModelStatus.kOptimal:
        return None
    sol = h.getSolution()
    return -h.getInfo().objective_function_value, [max(0.0, -x) for x in sol.row_dual], np.array(sol.col_value)


class CannotCertify(RuntimeError):
    def __init__(self, msg, box=None, value=None, x=None):
        super().__init__(msg)
        self.box, self.value, self.x = box, value, x


def integer_duals(ld, cd, y):
    costs, budgets = cd
    for factor in (1+1e-9, 1+1e-7, 1+1e-5, 1+1e-3, 1.01):
        Y = max(0, math.ceil(y[0]*factor*DS)+1)
        U = max(0, math.ceil(y[1]*factor*DS)+1)
        Z = [max(0, math.ceil(z*factor*DS)+1) if z > 1e-15 else 0 for z in y[2:]]
        ok = True
        for i in range(len(ld.G)):
            lhs = Y*ld.W[i]+U*ld.cnt[i]+sum(z*c[i] for z, c in zip(Z, costs) if z)
            if lhs < DS*ld.G[i]:
                ok = False; break
        if ok:
            du = dict(Y=Y, U=U, Z=Z)
            return du, check_case(ld, cd, du)
    need = 0
    for i in range(len(ld.G)):
        lhs = Y*ld.W[i]+U*ld.cnt[i]+sum(z*c[i] for z, c in zip(Z, costs) if z)
        if lhs < DS*ld.G[i]:
            need = max(need, ceildiv(DS*ld.G[i]-lhs, ld.W[i]))
    du = dict(Y=Y+need, U=U, Z=Z)
    return du, check_case(ld, cd, du)


FAST = False


def build(ld, target=Q(9999999, 10000000), max_boxes=200000, min_width=1):
    import fastlp
    WARM = {}
    Gf = np.array(ld.G, float)/S; Wf = np.array(ld.W, float)/S; Cf = np.array(ld.cnt, float)/S
    full = [(0, e) for e in ld.ends]
    K = len(full)-1
    allc = cases(K)
    count = [0]
    tgt = float(target)

    def evaluate(box, orders):
        """Float LP per case; returns (max value, list of (cd, y, x, val)) with cd None for excluded."""
        out = []; mx = -1.0
        for eps in cases(K, orders):
            cd = case_data(ld, box, eps)
            if cd is None or excludable(cd):
                out.append((None, None, None, -1.0)); continue
            costs, budgets = cd
            A = np.vstack([Wf, Cf]+[np.array(c, float)/S for c in costs])
            bvec = [ld.F/S, 2.0]+[b/S for b in budgets]
            key = (tuple(orders), eps)
            fr = fastlp.dual_active(A, Gf, bvec, WARM.get(key)) if FAST else None
            if fr is not None:
                WARM[key] = fr[3]
                r = (fr[0], list(fr[1]), fr[2])
            else:
                r = _lp(Gf, A, bvec)
            if r is None:
                dr = _dual_lp(Gf, A, bvec)
                if dr is None:
                    out.append((cd, None, None, float('inf'))); mx = float('inf'); continue
                r = (dr[0], dr[1], None)
            val, y, x = r
            val += (ld.first+ld.final)/S
            out.append((cd, y, x, val)); mx = max(mx, val)
        return mx, out

    def accept(out, orders):
        node = []; vmax = -1
        for cd, y, x, val in out:
            if cd is None:
                node.append('excluded'); continue
            du, v = integer_duals(ld, cd, y)
            if v >= target*S:
                return None
            node.append(du); vmax = max(vmax, v)
        return dict(cases=node, orders=list(orders), value=vmax)

    def rec(box):
        count[0] += 1
        first = [2]*(K+1)
        mx, out = evaluate(box, first)
        if mx < tgt:
            nd = accept(out, first)
            if nd is not None:
                return nd
        # second order on the dimensions whose first-order constraint is active
        worst = max(out, key=lambda o: o[3])
        yw = worst[1]
        orders = [1 if (yw is None or yw[2+k] > 1e-9) else 2 for k in range(K+1)]
        if orders != first:
            mx, out = evaluate(box, orders)
            if mx < tgt:
                nd = accept(out, orders)
                if nd is not None:
                    return nd
        if count[0] > max_boxes:
            worst = max(out, key=lambda o: o[3])
            raise CannotCertify('box budget exhausted', box, mx, worst[2])
        # split: second-order error estimate per dimension, weighted by the worst case's dual
        worst = max(out, key=lambda o: o[3])
        y, x = worst[1], worst[2]
        best = None
        for k, (a, b) in enumerate(box):
            if b-a <= min_width:
                continue
            h = (b-a)/(2*TS)
            if y is None:
                est = (b-a)/max(1, full[k][1])
            else:
                z = max(y[2+k], 0.5)
                mass = float(np.sum(x)) if x is not None else 1.0
                curv = (ld.D0/ld.d0 + mass) if k == 0 else (S/ld.sieve[k-1]['d'] + mass*S/ld.sieve[k-1]['D'])
                est = z*h*h*curv+1e-12*(b-a)/max(1, full[k][1])
            if best is None or est > best[0]:
                best = (est, k)
        if best is None:
            raise CannotCertify('unresolved box', box, mx, worst[2])
        k = best[1]
        a, b = box[k]
        mid = (a+b)//2
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        return dict(split=k, mid=mid, children=[rec(left), rec(right)])
    tree = rec(full)
    # every accepted case was checked exactly by check_case; summarize without re-checking
    return tree, tree_max(tree), tree_boxes(tree)


def tree_max(node):
    if 'split' in node:
        return max(tree_max(c) for c in node['children'])
    return node.get('value', -1)


def tree_boxes(node):
    if 'split' in node:
        return sum(tree_boxes(c) for c in node['children'])
    return 1
