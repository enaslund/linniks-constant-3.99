"""Sieve-near certificates for the outside-buffer regime (computations/near).

The old near row, hidden first-family columns, hidden count and far row are
exactly the repository's outside-buffer relaxation (first_outside_blocks.first_near
over a threshold interval [a0,b0]).  Sieve rows use the second-order tangent
disjunction of certificate2 on ordinary columns only; hidden columns have
sieve feature 0 (omitted from the sieve inequality, which is valid).
"""
import sys, math, itertools
from pathlib import Path
from fractions import Fraction as Q
import numpy as np
HERE = Path(__file__).resolve().parent
NC = HERE.parent/'near'/'code'
sys.path.insert(0, str(NC))
from certificate import ceildiv, isqrt_up, S, TS, DS, row_D, fam_terms
from certificate2 import tangent_cost, floor_q, ceil_q, _lp
from certificate3 import CannotCertify   # the class the drivers catch


def _fob():
    import first_outside_blocks as fob
    return fob


class OutLeaf:
    """model='outside': the outside-buffer regime (first_outside_blocks.first_near).
    model='block': the inside hidden-family branches of inside_repair 'identities' nodes
    (separated_blocks.near_block, verified in the repository by separated_blocks.verify_block).
    Both have ordinary columns, hidden columns with a hidden count, and one old near row."""
    def __init__(self, inp, sieve, model='outside'):
        fob = _fob()
        self.inp = inp; self.model = model
        self.rows = inp['rows']; self.hh = inp['hidden_rows']
        self.W = [r[2] for r in self.rows]; self.G = [r[3] for r in self.rows]
        self.WH = [r[2] for r in self.hh]; self.GH = [r[3] for r in self.hh]; self.NH = [r[5] for r in self.hh]
        self.F = inp['far_budget']; self.first = inp['first']; self.final = inp['final']
        self.sieve = sieve
        for sv in sieve:
            if 'vh' in sv:
                # hidden-family features (family row of distinct hidden-family branches)
                assert len(sv['vh']) == len(self.hh) and all(type(x) is int and x >= 0 for x in sv['vh'])
                assert len(sv.get('Dvh', [sv['D']]*len(self.hh))) == len(self.hh)
        # count row (repository third-family rule, triple_inputs.input_with_third): at most two
        # ordinary characters below the global lambda3; ordinary columns exclude the first family
        self.cnt = list(inp.get('count_cost') or [0]*len(self.rows))
        assert len(self.cnt) == len(self.rows) and all(c in (0, S) for c in self.cnt)
        assert inp.get('count_budget', 2*S) == 2*S
        if model == 'outside':
            self.ng = inp['n'] if self.hh else 0
            self.end0 = fob.threshold_end(inp)
            self._near = fob.first_near
        else:
            assert model == 'block'
            import separated_blocks as sb
            self.ng = inp['shadow']['ng']
            self.end0 = sb.threshold_end(inp)
            self._near = sb.near_block
        # dimension 0 in tangent form: Psi(tau) = sum_i x_i (V_i-tau)_+^2 + sum_terms k (v-tau)_+^2
        # + (D/d) tau^2 is convex; the hidden residuals are decreasing in tau and are taken at b.
        self.V0 = [r[4] for r in self.rows]
        self.terms0 = self._terms()
        self.ends = [self.end0]+[isqrt_up(sv['d']*TS*TS//S+1) for sv in sieve]
        self._old = {}

    def _terms(self):
        """(D, d, [(k, v)]) of the old near budget D(1-t^2/d)-sum k (v-t)_+^2, exactly as the
        repository's near function uses it (first_near / identity_model.quadratic_terms)."""
        inp = self.inp
        if self.model == 'block':
            import identity_model as im
            return im.quadratic_terms(inp)
        D, d, Df = Q(inp['D'], S), Q(inp['d'], S), Q(inp['Df'], S)
        sec = inp['second']; vf = Q(inp['v_first'], S)
        if inp['outside_subcase'] == 'outside_buffer':
            block = inp['first_block']; K = Q(block['K'], S); m = block['global_centers']
            beta = Df-K; denom = K+m*beta
            terms = [(inp['n']*D*m/denom, vf)]
        else:
            terms = [(inp['n']*D/Df, vf)]
        if sec:
            terms.append((Q(sec['n']), Q(sec['v'], S)))
        return D, d, terms

    def old_tangent(self, a, b, c):
        """Tangent case c of dimension 0 on [a,b]: ordinary costs ((V-m)_+ +- h)^2 - h^2, hidden
        costs at b (decreasing residuals), budget D - (D/d)((m-+h)^2-h^2) - sum k T(v)."""
        from certificate3 import tangent_exact
        m2, h2 = a+b, b-a
        costs = [tangent_cost(v, m2, h2, c) for v in self.V0]
        CH = self.old(a, b)[1]
        D, d, terms = self.terms0
        p = Q(a if c == 0 else b, TS); hq = Q(h2, 2*TS)
        B = D-(D/d)*(p*p-hq*hq)-sum(k*tangent_exact(v, Q(m2, 2*TS), hq, c) for k, v in terms)
        return costs, CH, ceil_q(B*S)

    def old(self, a, b):
        key = (a, b)
        if key not in self._old:
            C, CH, B = self._near(self.inp, a, b)
            self._old[key] = (C, CH, B)
        return self._old[key]

    def sieve_case(self, k, a, b, c):
        sv = self.sieve[k]
        if c == 2:
            # first order: costs at the upper threshold b (nonnegative), budget at the lower a,
            # family terms at b (their subtraction is then a lower bound over the box)
            sh = b*(S//TS)
            costs = [max(v-sh, 0)**2//Dk for v, Dk in zip(sv['v'], row_D(sv))]
            if 'vh' in sv:
                costs += [max(v-sh, 0)**2//Dk for v, Dk in zip(sv['vh'], sv.get('Dvh', [sv['D']]*len(sv['vh'])))]
            B = S-(S*S*a*a)//(TS*TS*sv['d'])
            if sv.get('fam'):
                B -= sum((n*max(v-sh, 0)**2)//Dn for n, v, Dn in fam_terms(sv))
            return costs, B
        m2, h2 = a+b, b-a
        costs = [(tangent_cost(v, m2, h2, c)*S)//Dk for v, Dk in zip(sv['v'], row_D(sv))]
        if 'vh' in sv:
            costs += [(tangent_cost(v, m2, h2, c)*S)//Dk
                      for v, Dk in zip(sv['vh'], sv.get('Dvh', [sv['D']]*len(sv['vh'])))]
        dd = Q(sv['d'], S)
        p = Q(a if c == 0 else b, TS); hq = Q(h2, 2*TS)
        B = 1-(p*p-hq*hq)/dd
        if sv.get('fam'):
            from certificate3 import tangent_exact
            B -= sum(n*tangent_exact(Q(v, S), Q(m2, 2*TS), hq, c)/Q(Dn, S) for n, v, Dn in fam_terms(sv))
        return costs, ceil_q(B*S)


def excludable_out(cd):
    costs, CH, budgets = cd
    if budgets[0] < 0 and min(costs[0], default=0) >= 0 and min(CH, default=0) >= 0:
        return True
    return any(b < 0 and min(c, default=0) >= 0 for c, b in zip(costs[1:], budgets[1:]))


def cases(K, orders=None):
    """Case vectors over the K sieve dimensions: order 1 = tangent pair (0,1), order 2 = first order."""
    if orders is None:
        orders = [1]*K
    return list(itertools.product(*[((0, 1) if o == 1 else (2,)) for o in orders]))


def case_data(ol, box, eps):
    """eps has K entries (sieve dimensions; dimension 0 first order) or K+1 (dimension 0 first)."""
    K = len(box)-1
    if len(eps) == K+1:
        e0, eps = eps[0], eps[1:]
    else:
        e0 = 2
    if e0 == 2:
        C, CH, B = ol.old(*box[0])
    else:
        C, CH, B = ol.old_tangent(box[0][0], box[0][1], e0)
    costs = [C]; budgets = [B]
    for k, (a, b) in enumerate(box[1:]):
        ck, bk = ol.sieve_case(k, a, b, eps[k])
        costs.append(ck); budgets.append(bk)
    return costs, CH, budgets


def check_case(ol, cd, du):
    costs, CH, budgets = cd
    Y, U, Z = du['Y'], du['U'], du['Z']
    V = du.get('V', 0)
    assert all(type(x) is int and x >= 0 for x in [Y, U, V]+Z) and len(Z) == len(costs)
    if not ol.hh:
        assert U == 0
    # budgets may be negative (weak duality)
    for i in range(len(ol.G)):
        lhs = Y*ol.W[i]+V*ol.cnt[i]+sum(z*c[i] for z, c in zip(Z, costs) if z)
        assert lhs >= DS*ol.G[i], ('column', i)
    nO = len(ol.G)
    for j in range(len(ol.GH)):
        lhs = Y*ol.WH[j]+Z[0]*CH[j]+U*ol.NH[j]
        lhs += sum(z*c[nO+j] for z, c in zip(Z[1:], costs[1:]) if z and len(c) > nO)
        assert lhs >= DS*ol.GH[j], ('hidden', j)
    tot = Y*ol.F+U*ol.ng*S+V*2*S+sum(z*b for z, b in zip(Z, budgets))
    return ceildiv(tot, DS)+ol.first+ol.final


def check_box(ol, box, node):
    K = len(box)-1
    orders = node.get('orders', [1]*K)
    assert len(orders) in (K, K+1) and all(o in (1, 2) for o in orders)
    allc = cases(len(orders), orders)
    assert len(node['cases']) == len(allc)
    mx = -1
    for eps, du in zip(allc, node['cases']):
        cd = case_data(ol, box, eps)
        if du == 'excluded':
            assert excludable_out(cd), 'exclusion needs a negative budget with nonnegative costs'
            continue
        mx = max(mx, check_case(ol, cd, du))
    return mx


def verify_tree(ol, node, box=None):
    if box is None:
        box = [(0, e) for e in ol.ends]
    if 'split' in node:
        k, mid = node['split'], node['mid']
        a, b = box[k]
        assert type(mid) is int and a < mid < b
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        m1, n1 = verify_tree(ol, node['children'][0], left)
        m2, n2 = verify_tree(ol, node['children'][1], right)
        return max(m1, m2), n1+n2
    v = check_box(ol, box, node)
    assert v < S, ('box value', v/S, box)
    return v, 1


def integer_duals(ol, cd, y):
    costs, CH, budgets = cd
    for factor in (1+1e-9, 1+1e-7, 1+1e-5, 1+1e-3, 1.01):
        Y = max(0, math.ceil(y['Y']*factor*DS)+1)
        U = max(0, math.ceil(y['U']*factor*DS)+1) if ol.hh else 0
        V = max(0, math.ceil(y.get('V', 0)*factor*DS)+1) if y.get('V', 0) > 1e-15 else 0
        Z = [max(0, math.ceil(z*factor*DS)+1) if z > 1e-15 else 0 for z in y['Z']]
        du = dict(Y=Y, U=U, Z=Z)
        if V:
            du['V'] = V
        try:
            return du, check_case(ol, cd, du)
        except AssertionError:
            continue
    return None, None


FAST = False
import os as _os
DIM0 = _os.environ.get('SIEVE_DIM0_TANGENT') == '1'   # tangent cases also on the old near dimension


def build(ol, target=Q(9999999, 10000000), max_boxes=20000, min_width=1):
    import fastlp
    WARM = {}
    Gall = np.array(ol.G+ol.GH, float)/S
    nO, nH = len(ol.G), len(ol.GH)
    full = [(0, e) for e in ol.ends]
    K = len(full)-1
    count = [0]
    tgt = float(target)

    def evaluate(box, orders):
        out = []; mx = -1.0
        for eps in cases(len(orders), orders):
            cd = case_data(ol, box, eps)
            costs, CH, budgets = cd
            if excludable_out(cd):
                out.append((cd, 'excluded', None, -1.0)); continue
            rowsA = [np.array(ol.W+ol.WH, float)/S,
                     np.array(costs[0]+CH, float)/S,
                     np.array([0]*nO+ol.NH, float)/S,
                     np.array(ol.cnt+[0]*nH, float)/S]
            for c in costs[1:]:
                rowsA.append(np.array(c if len(c) > nO else c+[0]*nH, float)/S)
            bud = [ol.F/S, budgets[0]/S, float(ol.ng), 2.0]+[b/S for b in budgets[1:]]
            key = (tuple(orders), eps)
            fr = fastlp.dual_active(np.vstack(rowsA), Gall, bud, WARM.get(key)) if FAST else None
            if fr is not None:
                WARM[key] = fr[3]
                r = (fr[0], list(fr[1]), fr[2])
            else:
                r = _lp(Gall, np.vstack(rowsA), bud)
            if r is None:
                from certificate3 import _dual_lp
                dr = _dual_lp(Gall, np.vstack(rowsA), bud)
                if dr is None:
                    out.append((cd, None, None, float('inf'))); mx = float('inf'); continue
                r = (dr[0], dr[1], None)
            val, yy, x = r
            val += (ol.first+ol.final)/S
            y = dict(Y=yy[0], Z=[yy[1]]+list(yy[4:]), U=yy[2], V=yy[3])
            out.append((cd, y, x, val)); mx = max(mx, val)
        return mx, out

    def accept(out, orders):
        node = []; vmax = -1
        for cd, y, x, val in out:
            if isinstance(y, str) and y == 'excluded':
                node.append('excluded'); continue
            du, v = integer_duals(ol, cd, y)
            if du is None or v >= target*S:
                return None
            node.append(du); vmax = max(vmax, v)
        return dict(cases=node, orders=list(orders), value=vmax)

    def rec(box):
        count[0] += 1
        first = [2]*(K+1) if DIM0 else [2]*K
        mx, out = evaluate(box, first)
        if mx < tgt:
            nd = accept(out, first)
            if nd is not None:
                return nd
        # tangent cases on the sieve dimensions active in the worst first-order case
        worst = max(out, key=lambda o: o[3])
        yw = worst[1]
        orders = [1 if (yw is None or isinstance(yw, str) or yw['Z'][k+1] > 1e-9) else 2 for k in range(K)]
        if DIM0:
            orders = [1 if (yw is None or isinstance(yw, str) or yw['Z'][0] > 1e-9) else 2]+orders
        if orders != first:
            mx, out = evaluate(box, orders)
            if mx < tgt:
                nd = accept(out, orders)
                if nd is not None:
                    return nd
        if count[0] > max_boxes:
            raise CannotCertify('box budget exhausted', box, mx, max(out, key=lambda o: o[3])[2])
        worst = max(out, key=lambda o: o[3])
        y, x = worst[1], worst[2]
        best = None
        for k, (a, b) in enumerate(box):
            if b-a <= min_width:
                continue
            if y is None or isinstance(y, str):
                est = (b-a)/max(1, full[k][1])
            elif k == 0:
                z = max(y['Z'][0], 0.5)
                D0, d0 = ol.inp['D']/S, ol.inp['d']/S
                est = z*4*(D0/d0)*(b/TS)*((b-a)/TS)
            else:
                h = (b-a)/(2*TS)
                mass = float(np.sum(x[:nO])) if x is not None else 1.0
                z = max(y['Z'][k], 0.5)
                est = z*h*h*(S/ol.sieve[k-1]['d']+mass*S/ol.sieve[k-1]['D'])
            if best is None or est > best[0]:
                best = (est, k)
        if best is None:
            raise CannotCertify('unresolved box', box, mx, x)
        k = best[1]
        a, b = box[k]
        mid = (a+b)//2
        left = list(box); left[k] = (a, mid)
        right = list(box); right[k] = (mid, b)
        return dict(split=k, mid=mid, children=[rec(left), rec(right)])
    tree = rec(full)
    return tree, _tmax(tree), _tbox(tree)


def _tmax(node):
    return max(_tmax(c) for c in node['children']) if 'split' in node else node.get('value', -1)


def _tbox(node):
    return sum(_tbox(c) for c in node['children']) if 'split' in node else 1
