#!/usr/bin/env python3
"""Negative test for ``independent_cert_check.py``: deliberately forged certificates.

Usage::

    python independent_cert_forgeries.py LEAVES.jsonl [--only NAME,NAME] [--audit-boxes N]

The input has the checker's protocol (one ``{"name", "leaf", "tree"}`` object per line).  For
every certificate the program

1. checks the certificate as given with ``independent_cert_check.check_certificate`` (it must be
   accepted), and surveys it: the box of largest value, and for every relaxation case with duals
   the slack of ``eq:dualfeasible`` at every column;
2. audits the rounding directions: for a sample of terminal boxes, every row and all three
   relaxations (first order, tangent 0, tangent 1), the checker's integer costs and budgets are
   compared with the exact coefficients and right sides of Lemmas "First-order relaxation" and
   "Tangent relaxation" (Section 10), computed here directly from the lemma statements with
   ``Fraction``.  Soundness needs ``cost <= S * coefficient`` and ``budget >= S * right side``; the
   audit also bounds the gaps (``< 1`` or ``< 1 + S/D`` for costs, ``< 1`` or ``< 1 + #family``
   for budgets), which shows that the checker computes the paper's rounded quantities and not
   merely safe ones;
3. applies each forgery below to a fresh copy of the certificate and runs the checker on it.

Forgeries come in three groups.

``reject``
    Provably invalid under Definition "Certificate": malformed structure or data, a dual lowered
    (or ``Y_E^-`` raised) by the *smallest* amount that breaks ``eq:dualfeasible`` at some column of
    some case, an objective coefficient raised by the smallest amount that breaks it, the far
    budget or the allowance raised by the smallest amount that makes some value ``>= S``, a column
    feature zeroed where its row's term is needed, an exclusion that no row justifies, and so on.
    The checker must reject every one.
``accept``
    Controls: the same perturbations one unit short of the breaking amount (still valid, which
    tests that the checks are exact at the boundary), and edits that carry no information (the
    stored terminal ``"value"``, an explicit default dual).  The checker must accept every one.
``either``
    Perturbations whose validity depends on the data: moving a split point by one tick, swapping
    the children of a split, pruning a subtree, swapping the tangent alternatives of a row,
    replacing a tangent row by a first-order one, removing a family term, raising a correlation
    term.  The outcome is reported with its reason; an accepted one is a certificate that is
    genuinely valid for the modified data (every case still satisfies Definition "Certificate").

Note on "gaps and overlaps": in this format the children of a split are *derived* from the
parent box and ``mid`` (``[a, mid]`` and ``[mid, b]``), so a certificate cannot express a gap or
an overlap between siblings.  The corresponding forgeries are a ``mid`` that is not strictly
inside ``(a, b)`` or not an integer, a split of a nonexistent row, a missing child, and (data
dependent) a shifted ``mid``.

The exit status is 1 if a ``reject`` forgery is accepted or a control is rejected.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import time
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import independent_cert_check as icc  # noqa: E402

S, T_S, D_S = icc.S, icc.T_S, icc.D_S


def node_at(tree, path):
    for i in path:
        tree = tree["children"][i]
    return tree


# ----------------------------------------------------------------------------- survey


class Survey:
    """One pass over an accepted certificate, collecting the data that the forgeries need."""

    def __init__(self, obj):
        leaf = self.leaf = icc.Leaf(obj["leaf"])
        K = self.K = leaf.K
        n = leaf.ncols
        self.internal = []  # (path, k, a, mid, b), root first
        self.terminals = []  # (path, box, orders, ncases)
        self.max_value = None  # largest value of a case with duals
        self.max_at = None  # (path, case index)
        self.lower = {}  # dual name -> (delta, path, case index, column): smallest breaking decrease
        self.raise_M = None  # (delta, path, case index, column): smallest breaking increase of M
        self.min_slack = [None] * n  # per column: min over cases of rhs_c - D_S G_c
        self.f_break = None  # (delta F, path, case index)
        self.feature = None  # (path, case index, column, row): Z_k cost_ck > slack_c, cost_ck > 0
        self.nonexcludable = None  # (path, case index): a dual case that no row can exclude
        self.negcost = None  # (path, case index, row): budget < 0 but a negative cost, no other row
        self.excl_rows = []  # rows justifying each of the certificate's own exclusions
        self.dual_cases = 0
        R = S - leaf.first - leaf.final
        stack = [(obj["tree"], leaf.root_box(), [])]
        while stack:
            node, box, path = stack.pop()
            if "split" in node:
                k, mid = node["split"], node["mid"]
                a, b = box[k]
                self.internal.append((path, k, a, mid, b))
                lbox, rbox = list(box), list(box)
                lbox[k], rbox[k] = (a, mid), (mid, b)
                stack.append((node["children"][1], rbox, path + [1]))
                stack.append((node["children"][0], lbox, path + [0]))
                continue
            orders = node["orders"]
            self.terminals.append((path, box, orders, len(node["cases"])))
            for ci, (iota, case) in enumerate(zip(icc.case_iotas(orders), node["cases"])):
                rows = [leaf.row(k, box[k][0], box[k][1], iota[k]) for k in range(K)]
                justified = [k for k in range(K) if rows[k][2] and rows[k][1] < 0]
                if case == "excluded":
                    self.excl_rows.append(justified)
                    continue
                self.dual_cases += 1
                if not justified:
                    if self.nonexcludable is None:
                        self.nonexcludable = (path, ci)
                    if self.negcost is None:
                        for k in range(K):
                            if iota[k] == 1 and rows[k][1] < 0 and not rows[k][2]:
                                self.negcost = (path, ci, k)
                                break
                Y, V, U, P, M, Z = icc.parse_duals(case, K, "survey")
                PM = P - M
                rhs = [Y * w + V * c + U * u + PM * e
                       for w, c, u, e in zip(leaf.W, leaf.C, leaf.N, leaf.E)]
                num = Y * leaf.F + 2 * S * V + leaf.ng * S * U + PM * leaf.nE * S
                for k in range(K):
                    if Z[k]:
                        rhs = [r + Z[k] * x for r, x in zip(rhs, rows[k][0])]
                        num += Z[k] * rows[k][1]
                slack = [r - g for r, g in zip(rhs, leaf.DSG)]
                value = icc.ceil_div(num, D_S) + leaf.first + leaf.final
                if self.max_value is None or value > self.max_value:
                    self.max_value, self.max_at = value, (path, ci)
                cands = [("Y", Y, leaf.W), ("V", V, leaf.C), ("U", U, leaf.N), ("P", P, leaf.E)]
                cands += [(f"Z{k}", Z[k], rows[k][0]) for k in range(K)]
                for name, x, coef in cands:
                    if x <= 0 or (name in self.lower and self.lower[name][0] == 1):
                        continue
                    best = min(((s // cf + 1, c) for c, (s, cf) in enumerate(zip(slack, coef))
                                if cf > 0), default=None)
                    if best is not None and best[0] <= x and (
                            name not in self.lower or best[0] < self.lower[name][0]):
                        self.lower[name] = (best[0], path, ci, best[1])
                if self.raise_M is None or self.raise_M[0] > 1:
                    best = min(((s // e + 1, c) for c, (s, e) in enumerate(zip(slack, leaf.E))
                                if e > 0), default=None)
                    if best is not None and (self.raise_M is None or best[0] < self.raise_M[0]):
                        self.raise_M = (best[0], path, ci, best[1])
                self.min_slack = [s if m is None or s < m else m
                                  for s, m in zip(slack, self.min_slack)]
                if Y > 0:
                    dF = ((R - 1) * D_S - num) // Y + 1
                    if self.f_break is None or dF < self.f_break[0]:
                        self.f_break = (dF, path, ci)
                if self.feature is None:
                    for k in range(K):
                        if Z[k] > 0:
                            for c, (x, s) in enumerate(zip(rows[k][0], slack)):
                                if x > 0 and Z[k] * x > s:
                                    self.feature = (path, ci, c, k)
                                    break
                        if self.feature is not None:
                            break
        # Column whose objective can be raised the least before eq:dualfeasible fails somewhere.
        self.g_break = min(((s // D_S + 1, c) for c, s in enumerate(self.min_slack)
                            if s is not None), default=None)


# ----------------------------------------------------------------------------- rounding audit


def exact_relaxation(leaf, k, a, b, iota):
    """S times the exact coefficients of x_c and the exact right side of row k's relaxed inequality.

    Written from the statements of Lemma "First-order relaxation" (iota = 2) and Lemma "Tangent
    relaxation" (iota = 0, 1), with thresholds a/T_S <= tau <= b/T_S, d = d_k/S, features
    u = v/S and weights c_j = x_c/(D/S) or n/(D/S).
    """
    d = Fraction(leaf.d[k], S)
    lo, hi = Fraction(a, T_S), Fraction(b, T_S)
    m, h = (lo + hi) / 2, (hi - lo) / 2

    def psi(u):
        if iota == 2:
            return max(u - hi, 0) ** 2
        if iota == 0:
            return (max(u - m, 0) + h) ** 2 - h ** 2
        return ((u - m) - h) ** 2 - h ** 2 if u > m else Fraction(0)

    if iota == 2:
        rhs = 1 - lo ** 2 / d
    elif iota == 0:
        rhs = 1 - ((m - h) ** 2 - h ** 2) / d
    else:
        rhs = 1 - ((m + h) ** 2 - h ** 2) / d
    for n, v, D in leaf.fam[k]:
        rhs -= n * psi(Fraction(v, S)) / Fraction(D, S)
    coefs = [S * psi(Fraction(v, S)) / Fraction(D, S) for v, D in zip(leaf.v[k], leaf.Dg[k])]
    return coefs, S * rhs


def audit_rounding(sv, max_boxes):
    """Compare the checker's integer costs and budgets with the exact lemma quantities."""
    leaf = sv.leaf
    boxes = sv.terminals[:max_boxes]
    if sv.max_at is not None:
        boxes = boxes + [t for t in sv.terminals if t[0] == sv.max_at[0]]
    n_cost = n_budget = 0
    bad = []
    worst_cost_gap = Fraction(0)  # max over c of (S coef - cost) / (1 + S/D) for tangent, / 1 first
    worst_budget_gap = Fraction(0)  # max of (budget - S rhs) / allowed gap
    for _, box, _, _ in boxes:
        for k in range(leaf.K):
            a, b = box[k]
            for iota in (2, 0, 1):
                costs, budget, _ = leaf.row(k, a, b, iota)
                coefs, rhs = exact_relaxation(leaf, k, a, b, iota)
                for c, (x, ex, D) in enumerate(zip(costs, coefs, leaf.Dg[k])):
                    n_cost += 1
                    allowed = 1 if iota == 2 else 1 + Fraction(S, D)
                    gap = ex - x
                    if gap < 0 or gap >= allowed:
                        bad.append(f"cost row {k} col {c} iota {iota} box {box}: {x} vs {ex}")
                    worst_cost_gap = max(worst_cost_gap, gap / allowed)
                n_budget += 1
                allowed = (1 + len(leaf.fam[k])) if iota == 2 else 1
                gap = budget - rhs
                if gap < 0 or gap >= allowed:
                    bad.append(f"budget row {k} iota {iota} box {box}: {budget} vs {rhs}")
                worst_budget_gap = max(worst_budget_gap, gap / allowed)
    return {"boxes": len(boxes), "costs": n_cost, "budgets": n_budget, "bad": bad,
            "worst_cost_gap": float(worst_cost_gap), "worst_budget_gap": float(worst_budget_gap)}


# ----------------------------------------------------------------------------- forgeries
#
# Each forgery takes a fresh copy ``o`` of the input object and the survey, mutates ``o`` and
# returns a one-line description, or returns None when it does not apply to this certificate.


def _root_split(sv):
    return sv.internal[0] if sv.internal and sv.internal[0][0] == [] else None


def _parent_of_max(sv):
    if sv.max_at is None or not sv.max_at[0]:
        return None
    ppath = sv.max_at[0][:-1]
    for rec in sv.internal:
        if rec[0] == ppath:
            return rec
    return None


def _terminal_with(sv, pred):
    for rec in sv.terminals:
        if pred(rec):
            return rec
    return None


def _case(o, path, ci):
    return node_at(o["tree"], path)["cases"][ci]


def f_mid_eq_a(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    path, k, a, mid, b = r
    node_at(o["tree"], path)["mid"] = a
    return f"root split (row {k}, [{a},{b}]): mid {mid} -> {a} = a"


def f_mid_eq_b(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    path, k, a, mid, b = r
    node_at(o["tree"], path)["mid"] = b
    return f"root split (row {k}, [{a},{b}]): mid {mid} -> {b} = b"


def f_mid_outside(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    path, k, a, mid, b = r
    node_at(o["tree"], path)["mid"] = b + 1
    return f"root split (row {k}, [{a},{b}]): mid {mid} -> {b + 1} > b"


def f_mid_float(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    path, k, a, mid, b = r
    node_at(o["tree"], path)["mid"] = mid + 0.5
    return f"root split: mid {mid} -> {mid + 0.5} (not an integer)"


def f_split_row_K(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    node_at(o["tree"], r[0])["split"] = sv.K
    return f"root split: row {r[1]} -> {sv.K} (no such row)"


def f_split_row_neg(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    node_at(o["tree"], r[0])["split"] = -1
    return f"root split: row {r[1]} -> -1"


def f_drop_child(o, sv):
    r = _root_split(sv)
    if r is None:
        return None
    node = node_at(o["tree"], r[0])
    node["children"] = node["children"][:1]
    return "root split: right child removed"


def f_order_2_to_1(o, sv):
    t = _terminal_with(sv, lambda rec: 2 in rec[2])
    if t is None:
        return None
    node = node_at(o["tree"], t[0])
    k = node["orders"].index(2)
    node["orders"][k] = 1
    return f"box {t[0]}: order of row {k} 2 -> 1, cases left as they are ({t[3]})"


def f_order_1_to_2(o, sv):
    t = _terminal_with(sv, lambda rec: 1 in rec[2])
    if t is None:
        return None
    node = node_at(o["tree"], t[0])
    k = node["orders"].index(1)
    node["orders"][k] = 2
    return f"box {t[0]}: order of row {k} 1 -> 2, cases left as they are ({t[3]})"


def f_order_3(o, sv):
    if sv.K == 0:
        return None
    t = sv.terminals[0]
    node_at(o["tree"], t[0])["orders"][0] = 3
    return f"box {t[0]}: order of row 0 -> 3"


def f_orders_short(o, sv):
    if sv.K == 0:
        return None
    t = sv.terminals[0]
    node = node_at(o["tree"], t[0])
    node["orders"] = node["orders"][:-1]
    return f"box {t[0]}: last order removed"


def f_drop_case(o, sv):
    path = sv.max_at[0] if sv.max_at else sv.terminals[0][0]
    node = node_at(o["tree"], path)
    node["cases"].pop()
    return f"box {path}: last relaxation case removed"


def f_dup_case(o, sv):
    path = sv.max_at[0] if sv.max_at else sv.terminals[0][0]
    node = node_at(o["tree"], path)
    node["cases"].append(node["cases"][0])
    return f"box {path}: first relaxation case duplicated"


def f_exclude_unjustified(o, sv):
    if sv.nonexcludable is None:
        return None
    path, ci = sv.nonexcludable
    node_at(o["tree"], path)["cases"][ci] = "excluded"
    return f"box {path} case {ci}: duals replaced by \"excluded\" (no row has costs >= 0, budget < 0)"


def f_exclude_negcost(o, sv):
    if sv.negcost is None:
        return None
    path, ci, k = sv.negcost
    node_at(o["tree"], path)["cases"][ci] = "excluded"
    return (f"box {path} case {ci}: \"excluded\"; row {k} (tangent 1) has budget < 0 but a "
            f"negative cost, no other row qualifies")


def f_exclude_misspelled(o, sv):
    path, ci = sv.max_at if sv.max_at else (sv.terminals[0][0], 0)
    node_at(o["tree"], path)["cases"][ci] = "exclude"
    return f"box {path} case {ci}: record -> \"exclude\""


def _lower(name, short_by):
    """Lower dual `name` by the smallest amount that breaks eq:dualfeasible (minus short_by)."""

    def f(o, sv):
        rec = sv.lower.get(name)
        if rec is None:
            return None
        delta, path, ci, c = rec
        delta -= short_by
        if delta <= 0:
            return None
        case = _case(o, path, ci)
        if name.startswith("Z"):
            k = int(name[1:])
            old = case["Z"][k]
            case["Z"][k] = old - delta
            what = f"Z_{k}"
        else:
            old = case.get(name, 0)
            case[name] = old - delta
            what = name
        tag = "breaking" if short_by == 0 else "one short of breaking"
        return (f"box {path} case {ci}: {what} {old} -> {old - delta} (decrease {delta}, "
                f"{tag}; binding column {c})")

    f.__name__ = f"lower_{name}" + ("" if short_by == 0 else "_control")
    return f


def _lower_Z(short_by):
    """Lower the Z_k that breaks with the smallest decrease."""

    def f(o, sv):
        zs = [(rec[0], name) for name, rec in sv.lower.items() if name.startswith("Z")]
        if not zs:
            return None
        return _lower(min(zs)[1], short_by)(o, sv)

    return f


def _raise_M(short_by):
    def f(o, sv):
        if sv.raise_M is None:
            return None
        delta, path, ci, c = sv.raise_M
        delta -= short_by
        if delta <= 0:
            return None
        case = _case(o, path, ci)
        old = case.get("M", 0)
        case["M"] = old + delta
        tag = "breaking" if short_by == 0 else "one short of breaking"
        return f"box {path} case {ci}: M {old} -> {old + delta} ({tag}; binding column {c})"

    return f


def f_negative_dual(o, sv):
    if sv.max_at is None:
        return None
    path, ci = sv.max_at
    case = _case(o, path, ci)
    case["M"] = -1
    return f"box {path} case {ci}: M = -1 (P - M grows by 1)"


def f_short_Z(o, sv):
    if sv.max_at is None or sv.K == 0:
        return None
    path, ci = sv.max_at
    case = _case(o, path, ci)
    case["Z"] = case["Z"][:-1]
    return f"box {path} case {ci}: Z has {sv.K - 1} entries"


def f_float_Y(o, sv):
    if sv.max_at is None:
        return None
    path, ci = sv.max_at
    case = _case(o, path, ci)
    case["Y"] = float(case["Y"])
    return f"box {path} case {ci}: Y given as the float {case['Y']!r}"


def _raise_G(short_by):
    def f(o, sv):
        if sv.g_break is None:
            return None
        g, c = sv.g_break
        g -= short_by
        if g <= 0:
            return None
        o["leaf"]["cols"][c][0] += g
        tag = "breaking" if short_by == 0 else "one short of breaking"
        return f"column {c}: G raised by {g} ({tag} eq:dualfeasible in the tightest case)"

    return f


def _raise_F(short_by):
    def f(o, sv):
        if sv.f_break is None:
            return None
        dF, path, ci = sv.f_break
        dF -= short_by
        if dF <= 0:
            return None
        o["leaf"]["F"] += dF
        tag = "value reaches S" if short_by == 0 else "value S - 1 at most"
        return f"F raised by {dF} ({tag} in box {path} case {ci})"

    return f


def _raise_final(short_by):
    def f(o, sv):
        if sv.max_value is None:
            return None
        delta = S - sv.max_value - short_by
        o["leaf"]["final"] += delta
        return f"final raised by {delta}: largest value becomes {sv.max_value + delta}"

    return f


def f_zero_feature(o, sv):
    if sv.feature is None:
        return None
    path, ci, c, k = sv.feature
    old = o["leaf"]["cols"][c][5][k]
    o["leaf"]["cols"][c][5][k] = 0
    return (f"column {c}: feature v_{k} {old} -> 0 (all its costs in row {k} become 0; needed in "
            f"box {path} case {ci})")


def f_zero_diagonal(o, sv):
    if sv.K == 0 or not o["leaf"]["cols"]:
        return None
    o["leaf"]["cols"][0][6][0] = 0
    return "column 0: diagonal D_0 -> 0"


def _first_family(o):
    for k, row in enumerate(o["leaf"]["rows"]):
        if row[1]:
            return k, row[1][0]
    return None


def f_negative_count(o, sv):
    ff = _first_family(o)
    if ff is None:
        return None
    k, term = ff
    old = term[0]
    term[0] = -1
    return f"row {k} family term 0: count {old} -> -1"


def f_zero_family_diag(o, sv):
    ff = _first_family(o)
    if ff is None:
        return None
    k, term = ff
    term[2] = 0
    return f"row {k} family term 0: diagonal -> 0"


def f_zero_d(o, sv):
    if sv.K == 0:
        return None
    o["leaf"]["rows"][0][0] = 0
    return "row 0: correlation term d -> 0"


def f_short_features(o, sv):
    if sv.K == 0 or not o["leaf"]["cols"]:
        return None
    o["leaf"]["cols"][0][5] = o["leaf"]["cols"][0][5][:-1]
    return f"column 0: {sv.K - 1} features"


def f_stored_value(o, sv):
    t = sv.terminals[0]
    node_at(o["tree"], t[0])["value"] = 0
    return f"box {t[0]}: stored \"value\" -> 0 (the key is ignored)"


def f_explicit_default(o, sv):
    if sv.max_at is None:
        return None
    path, ci = sv.max_at
    case = _case(o, path, ci)
    for key in ("V", "U", "P", "M"):
        if key not in case:
            case[key] = 0
            return f"box {path} case {ci}: explicit \"{key}\": 0 (the default)"
    return None


def f_mid_shift(step):
    def f(o, sv):
        r = _parent_of_max(sv)
        if r is None:
            return None
        path, k, a, mid, b = r
        if not a < mid + step < b:
            return None
        node_at(o["tree"], path)["mid"] = mid + step
        return f"parent of the largest box (row {k}, [{a},{b}]): mid {mid} -> {mid + step}"

    return f


def f_swap_children(o, sv):
    r = _parent_of_max(sv)
    if r is None:
        return None
    node = node_at(o["tree"], r[0])
    node["children"].reverse()
    return f"parent {r[0]} of the largest box: children swapped"


def f_prune(o, sv):
    r = _parent_of_max(sv)
    if r is None:
        return None
    path = r[0]
    node = node_at(o["tree"], path)
    left = node["children"][0]
    if path:
        node_at(o["tree"], path[:-1])["children"][path[-1]] = left
    else:
        o["tree"] = left
    return f"parent {path} of the largest box replaced by its left child"


def _tangent_row_of_max(sv, o):
    if sv.max_at is None:
        return None
    node = node_at(o["tree"], sv.max_at[0])
    if 1 not in node["orders"]:
        return None
    return node, node["orders"].index(1)


def f_swap_alternatives(o, sv):
    t = _tangent_row_of_max(sv, o)
    if t is None:
        return None
    node, k = t
    iotas = list(icc.case_iotas(node["orders"]))
    index = {io: i for i, io in enumerate(iotas)}
    cases = list(node["cases"])
    for io, i in index.items():
        if io[k] == 0:
            j = index[io[:k] + (1,) + io[k + 1:]]
            cases[i], cases[j] = node["cases"][j], node["cases"][i]
    node["cases"] = cases
    return f"largest box {sv.max_at[0]}: tangent alternatives of row {k} swapped"


def f_tangent_to_first(o, sv):
    t = _tangent_row_of_max(sv, o)
    if t is None:
        return None
    node, k = t
    old_index = {io: i for i, io in enumerate(icc.case_iotas(node["orders"]))}
    new_orders = list(node["orders"])
    new_orders[k] = 2
    new_cases = []
    for io in icc.case_iotas(new_orders):
        old = io[:k] + (0,) + io[k + 1:]
        new_cases.append(node["cases"][old_index[old]])
    node["orders"], node["cases"] = new_orders, new_cases
    return f"largest box {sv.max_at[0]}: row {k} first order, keeping the tangent-0 duals"


def f_drop_family(o, sv):
    if sv.max_at is None:
        return None
    path, ci = sv.max_at
    case = _case(o, path, ci)
    for k, row in enumerate(o["leaf"]["rows"]):
        if row[1] and case["Z"][k] > 0:
            old = row[1][0][0]
            row[1][0][0] = 0
            return f"row {k} family term 0: count {old} -> 0 (Z_{k} > 0 in the largest case)"
    return None


def f_raise_d(o, sv):
    if sv.K == 0:
        return None
    o["leaf"]["rows"][0][0] += 1
    return "row 0: correlation term d raised by 1"


FORGERIES = [
    # (group, kind, function)
    ("reject", "split mid = a", f_mid_eq_a),
    ("reject", "split mid = b", f_mid_eq_b),
    ("reject", "split mid > b", f_mid_outside),
    ("reject", "split mid not an integer", f_mid_float),
    ("reject", "split row = K", f_split_row_K),
    ("reject", "split row = -1", f_split_row_neg),
    ("reject", "split with one child", f_drop_child),
    ("reject", "order 2 -> 1, same cases", f_order_2_to_1),
    ("reject", "order 1 -> 2, same cases", f_order_1_to_2),
    ("reject", "order 3", f_order_3),
    ("reject", "orders too short", f_orders_short),
    ("reject", "relaxation case dropped", f_drop_case),
    ("reject", "relaxation case duplicated", f_dup_case),
    ("reject", "unjustified exclusion", f_exclude_unjustified),
    ("reject", "exclusion via a negative cost", f_exclude_negcost),
    ("reject", "misspelled exclusion", f_exclude_misspelled),
    ("reject", "Y lowered (breaking)", _lower("Y", 0)),
    ("reject", "Z lowered (breaking)", _lower_Z(0)),
    ("reject", "P lowered (breaking)", _lower("P", 0)),
    ("reject", "M raised (breaking)", _raise_M(0)),
    ("reject", "V lowered (breaking)", _lower("V", 0)),
    ("reject", "U lowered (breaking)", _lower("U", 0)),
    ("reject", "negative dual M = -1", f_negative_dual),
    ("reject", "Z too short", f_short_Z),
    ("reject", "Y as a float", f_float_Y),
    ("reject", "G raised (breaking)", _raise_G(0)),
    ("reject", "F raised (breaking)", _raise_F(0)),
    ("reject", "final raised to S", _raise_final(0)),
    ("reject", "needed column feature zeroed", f_zero_feature),
    ("reject", "column diagonal 0", f_zero_diagonal),
    ("reject", "family count -1", f_negative_count),
    ("reject", "family diagonal 0", f_zero_family_diag),
    ("reject", "correlation term 0", f_zero_d),
    ("reject", "column missing a feature", f_short_features),
    ("accept", "Y lowered (one short)", _lower("Y", 1)),
    ("accept", "Z lowered (one short)", _lower_Z(1)),
    ("accept", "P lowered (one short)", _lower("P", 1)),
    ("accept", "M raised (one short)", _raise_M(1)),
    ("accept", "G raised (one short)", _raise_G(1)),
    ("accept", "F raised (one short)", _raise_F(1)),
    ("accept", "final raised to S - 1", _raise_final(1)),
    ("accept", "stored value forged", f_stored_value),
    ("accept", "explicit default dual", f_explicit_default),
    ("either", "split mid + 1", f_mid_shift(+1)),
    ("either", "split mid - 1", f_mid_shift(-1)),
    ("either", "children swapped", f_swap_children),
    ("either", "subtree pruned", f_prune),
    ("either", "tangent alternatives swapped", f_swap_alternatives),
    ("either", "tangent row -> first order", f_tangent_to_first),
    ("either", "family term removed", f_drop_family),
    ("either", "correlation term + 1", f_raise_d),
]


# ----------------------------------------------------------------------------- driver


def run_leaf(line, audit_boxes, out):
    obj = json.loads(line)
    name = obj.get("name", "?")
    t0 = time.time()
    base = icc.check_certificate(obj)
    t_base = time.time() - t0
    if base["value"] is None:
        out(f"== {name}: the unforged certificate is REJECTED ({base['reason']}); skipped")
        return {"name": name, "skipped": True, "results": []}
    out(f"== {name}: accepted, value {base['value']}, {base['boxes']} terminal boxes, "
        f"{base['dual']} dual and {base['excluded']} excluded cases ({t_base:.1f} s)")
    sv = Survey(json.loads(line))
    assert sv.max_value is None or sv.max_value == base["value"] or base["value"] == -1
    excl_info = ""
    if sv.excl_rows:
        rows_used = sorted({k for js in sv.excl_rows for k in js})
        excl_info = f"; the certificate's own exclusions are justified by rows {rows_used}"
    out(f"   survey: {sv.dual_cases} dual cases; largest value in box {sv.max_at}{excl_info}")
    au = audit_rounding(sv, audit_boxes)
    out(f"   rounding audit on {au['boxes']} boxes, all rows, all 3 relaxations: {au['costs']} "
        f"costs <= S*coefficient, {au['budgets']} budgets >= S*right side: "
        f"{'all hold' if not au['bad'] else str(len(au['bad'])) + ' FAIL'}; largest gaps "
        f"{au['worst_cost_gap']:.6f} and {au['worst_budget_gap']:.6f} of their allowances "
        f"(each < 1 exactly)")
    for msg in au["bad"][:5]:
        out(f"      {msg}")
    results = []
    for group, kind, fn in FORGERIES:
        o = json.loads(line)
        desc = fn(o, sv)
        if desc is None:
            results.append((group, kind, "n/a", None, None, None))
            continue
        t1 = time.time()
        res = icc.check_certificate(o)
        dt = time.time() - t1
        got = "REJECTED" if res["value"] is None else "accepted"
        ok = {"reject": got == "REJECTED", "accept": got == "accepted", "either": True}[group]
        detail = res["reason"] if res["value"] is None else f"value {res['value']}"
        results.append((group, kind, got, ok, desc, detail))
        flag = "" if ok else "   <-- UNEXPECTED"
        out(f"   [{group:6}] {kind:32} {got:8} {dt:6.1f}s  {desc}{flag}")
        out(f"            {'':32} -> {detail[:220]}")
    for group, kind, got, _, _, _ in results:
        if got == "n/a":
            out(f"   [{group:6}] {kind:32} n/a (not applicable to this certificate)")
    au_ok = not au["bad"]
    return {"name": name, "skipped": False, "results": results, "audit_ok": au_ok}


def main(argv=None):
    ap = argparse.ArgumentParser(description="Forgery test for independent_cert_check.py")
    ap.add_argument("jsonl", help="leaves in the checker's input protocol")
    ap.add_argument("--only", help="comma-separated leaf names to test")
    ap.add_argument("--audit-boxes", type=int, default=30,
                    help="number of terminal boxes (plus the largest one) in the rounding audit")
    args = ap.parse_args(argv)
    only = set(args.only.split(",")) if args.only else None

    def out(s):
        print(s, flush=True)

    summaries = []
    with open(args.jsonl, encoding="utf-8") as fh:
        for line in fh:
            if not line.strip():
                continue
            if only is not None and json.loads(line).get("name") not in only:
                continue
            summaries.append(run_leaf(line, args.audit_boxes, out))

    out("")
    out("== summary")
    bad = 0
    kinds = {}
    for s in summaries:
        if s["skipped"]:
            bad += 1
            continue
        if not s["audit_ok"]:
            bad += 1
        for group, kind, got, ok, _, _ in s["results"]:
            if got == "n/a":
                continue
            kinds.setdefault((group, kind), []).append(got)
            if ok is False:
                bad += 1
    for group in ("reject", "accept", "either"):
        tried = [(kind, gots) for (g, kind), gots in kinds.items() if g == group]
        n = sum(len(gots) for _, gots in tried)
        nrej = sum(gots.count("REJECTED") for _, gots in tried)
        out(f"   {group}: {len(tried)} kinds, {n} forged certificates, {nrej} rejected, "
            f"{n - nrej} accepted")
        if group == "either":
            for kind, gots in tried:
                out(f"      {kind:32} rejected {gots.count('REJECTED')} of {len(gots)}")
    out(f"   leaves: {len(summaries)}; unexpected outcomes (or failed audits): {bad}")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
