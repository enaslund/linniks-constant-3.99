#!/usr/bin/env python3
"""Independent exact checker for the leaf-program certificates.

Provenance and independence
---------------------------
This program was written from the mathematical description of the certificates in the paper,
``paper/sections/10-lp.tex`` (Section 10, "Leaf programs and exact certificates"): the
definitions "Leaf program", "Root threshold box", "Integer costs and budgets" and "Certificate",
the theorem "Soundness of the integer certificates" and the lemmas "First-order relaxation" and
"Tangent relaxation".  The only other inputs were the macros in ``paper/linnik399.tex``, the
input protocol stated by the person who commissioned it (the JSON layout below), and the header
comment of ``lean-graded/CertRunNative.lean``, which describes the same layout.

No other certificate-checking code was opened, read, searched, imported or compared while writing
it: not ``computations/graded/graded_cert.py``, not ``lean-graded/CertCore.lean``, not
``lean-graded/GradedNear/Defs.lean`` or ``lean-graded/GradedNear/Cert/*.lean``, and not any other
checker in the repository.  The program imports nothing from the repository.  The replay's leaf
generator (``computations/graded/graded_lean_export.py``) was only *run* (its source was not
read), as the source of the leaves and as the harness that compares this program's output with the
first checker's.  After the checker was written, only data and documentation were consulted: the
stored certificate trees of ``computations/graded/corpora/3.99`` (for note 8 below), the run
summaries in ``computations/graded/lean_runs/``, and the READMEs for the full-corpus command line.

Only exact integer and ``fractions.Fraction`` arithmetic is used in the checking path.  (The only
floating-point numbers in this file are the timings printed in ``--file`` mode.)

What is checked
---------------
For every leaf (one JSON object per input line) the program checks, following Definition
"Certificate" of Section 10:

* *Well-formedness* of the leaf: every diagonal ``D_ck`` of a column and ``D`` of a family term is
  positive, every correlation term ``d_k`` is positive, every family count ``n`` is nonnegative,
  every column has exactly ``K`` features and ``K`` diagonals, and every number is an integer
  (JSON floats and booleans are rejected).
* *The tree*: it starts at the root box ``prod_k [0, e_k]`` with
  ``e_k = ceil(sqrt(floor(d_k T_S^2 / S) + 1))`` (exact integer square root).  An internal node
  ``{"split": k, "mid": mid, "children": [left, right]}`` must have an integer row index
  ``0 <= k < K`` (rows are 0-based in the JSON) and an integer ``a < mid < b``, where ``[a, b]`` is
  coordinate ``k`` of the node's box; ``left`` is checked on ``[a, mid]`` and ``right`` on
  ``[mid, b]``.
* *Terminal boxes* ``{"orders": [o_1..o_K], "cases": [...]}``: ``len(orders) = K``, each
  ``o_k`` in ``{1, 2}`` (2 = first order, 1 = tangent), and exactly ``2^(#tangent rows)`` cases,
  matched in order with ``itertools.product`` over the rows of ``(0, 1)`` (tangent) or ``(2,)``
  (first order).  A case is either the string ``"excluded"`` or a dict of integer duals
  ``Y`` (= Y_F), ``V`` (= Y_C), ``U`` (= Y_N), ``P`` (= Y_E^+), ``M`` (= Y_E^-), ``Z`` (= Z_1..Z_K);
  ``V``, ``U``, ``P``, ``M`` default to 0, ``Y`` and ``Z`` are required, all must be ``>= 0``.
* *Costs and budgets* exactly as in Definition "Integer costs and budgets" (see the functions
  ``Leaf._first_order`` and ``Leaf._tangent`` below, which transcribe it formula by formula).
* *Exclusion*: an ``"excluded"`` case is accepted iff some row ``k`` has, in that relaxation case,
  all its costs ``>= 0`` and budget ``< 0``.  (The record does not name the row; all rows are
  tried.)
* *Dual feasibility* (``eq:dualfeasible``): for every column ``c``,
  ``D_S G_c <= Y_F W_c + Y_C C_c + Y_N N_c + (Y_E^+ - Y_E^-) E_c + sum_k Z_k cost_ck``.
* *Values*: a dual case has value
  ``ceil((Y_F F + 2 S Y_C + n_g S Y_N + (Y_E^+ - Y_E^-) n_E S + sum_k Z_k budget_k) / D_S)
  + first + final``; a terminal box has the maximum of its case values (``-1`` if all cases are
  excluded); the certificate is accepted iff every terminal box has value ``< S``.

Any violation rejects the whole certificate.  A ``"value"`` key stored on a terminal box is
ignored (it is never used for acceptance; ``--file`` mode only reports whether it agrees).
Unknown keys anywhere else are rejected, so that a change of the data format cannot go unnoticed.

The paper's C_c, E_c in {0, S} and the listed values of N_c describe the leaf builders; they are
not hypotheses of the soundness theorem, so they are not checked here.

Interpretations where Section 10 leaves room (recorded so that they can be audited)
-------------------------------------------------------------------------------------
1. Child order: the paper lists the halves of a split as ``[a, mid]`` and ``[mid, b]``; the JSON
   ``children`` list is taken in that order.
2. Row indices in ``split`` are 0-based (the paper numbers rows ``1..K``).
3. The order of the relaxation cases inside a terminal box is not fixed by the paper; the
   ``itertools.product`` order above is used (a protocol convention, given with the input format).
4. ``m S = (a + b) S / (2 T_S)`` and ``2 h S = (b - a) S / T_S`` are integers because ``2 T_S``
   divides ``S``; the program computes ``m`` and ``h`` as exact rationals and asserts this, so the
   floors in the tangent cost are floors of rationals with denominator ``S``.
5. In the tangent cost the rounding is done twice, as written: ``Theta`` is floored at scale
   ``S`` and then ``S Theta / D`` is floored.  The tangent budget is a single ceiling of the exact
   rational ``S beta`` (its family terms use the *unrounded* ``Theta_iota(v/S)``), while in the
   first-order budget ``floor(S^2 a^2/(T_S^2 d_k))`` and each family term are floored separately.
6. An exclusion needs "costs all >= 0" for every column; with no columns this is vacuous.
7. The printed box count is the number of terminal boxes (``CertRunNative.lean``'s header says
   "number of tree nodes", but the reference output for the large first-zero leaf, 36, is the
   number of terminal boxes of its 71-node tree).  On rejection the line is ``name none boxes``
   with ``boxes`` counted structurally (0 if the tree cannot be read).
8. Box values below -1.  Section 10 defines the value of a terminal box as the maximum of the
   values of its relaxation cases, and -1 only if every case is excluded; that is what is
   implemented.  The stored (ignored) ``"value"`` keys of the certificates instead clamp at -1:
   a box whose only dual cases have values near -0.8 S (Farkas-type certificates of an empty
   relaxation) stores -1.  The two conventions give different *leaf* maxima only for a leaf all
   of whose boxes lie below -1; no leaf of the 3.99 corpora is of that kind (every stored tree
   with a negative maximum contains an all-excluded box), and acceptance is the same under both.

Additional options: ``--stats PATH`` (filter mode) appends one JSON line per leaf with the value,
the box count and the numbers of dual and excluded relaxation cases, so that a run through the
exporter's ``--checker`` can be totalled afterwards with ``--summarize-stats PATH``.

Usage
-----
Filter (long-running subprocess; one output line per non-blank input line, flushed)::

    python independent_cert_check.py < leaves.jsonl

prints ``name value boxes`` per leaf, where ``value`` is the S-scaled maximum of the terminal box
values, or ``none`` if the certificate is rejected.  Blank input lines are skipped.

File mode with a summary (and the reason for every rejection)::

    python independent_cert_check.py --file leaves.jsonl

``--verbose`` in filter mode writes rejection reasons to standard error.
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
import time
from fractions import Fraction
from math import isqrt

S = 10 ** 16  # scale of stored coefficients
T_S = 10 ** 6  # ticks per unit threshold
D_S = 10 ** 12  # scale of the dual multipliers

CASE_KEYS = frozenset({"Y", "V", "U", "P", "M", "Z"})
SPLIT_KEYS = frozenset({"split", "mid", "children"})
TERMINAL_KEYS = frozenset({"orders", "cases"})
TERMINAL_IGNORED_KEYS = frozenset({"value"})
LEAF_KEYS = frozenset({"cols", "rows", "F", "ng", "n2", "first", "final"})
TOP_KEYS = frozenset({"name", "leaf", "tree"})


class Reject(Exception):
    """The certificate or its leaf data is not accepted."""


# ----------------------------------------------------------------------------- exact helpers


def is_int(x) -> bool:
    """A JSON integer (Python int, but not bool)."""
    return isinstance(x, int) and not isinstance(x, bool)


def need_int(x, what: str) -> int:
    if not is_int(x):
        raise Reject(f"{what}: expected an integer, got {type(x).__name__} {x!r:.40}")
    return x


def need_list(x, what: str, length: int | None = None) -> list:
    if not isinstance(x, list):
        raise Reject(f"{what}: expected a list, got {type(x).__name__}")
    if length is not None and len(x) != length:
        raise Reject(f"{what}: expected length {length}, got {len(x)}")
    return x


def need_keys(obj: dict, allowed: frozenset, required: frozenset, what: str) -> None:
    extra = set(obj) - allowed
    if extra:
        raise Reject(f"{what}: unknown keys {sorted(extra)}")
    missing = required - set(obj)
    if missing:
        raise Reject(f"{what}: missing keys {sorted(missing)}")


def ceil_div(p: int, q: int) -> int:
    """ceil(p / q) for integers, q > 0."""
    assert q > 0
    return -((-p) // q)


def ceil_sqrt(n: int) -> int:
    """ceil(sqrt(n)) for an integer n >= 0, exactly."""
    assert n >= 0
    r = isqrt(n)
    return r if r * r == n else r + 1


def ceil_fraction(x: Fraction) -> int:
    return -((-x.numerator) // x.denominator)


def pos(x):
    """(x)_+ = max(x, 0)."""
    return x if x > 0 else 0


# The integer shift b S / T_S and the tangent centre m S = (a + b) S / (2 T_S) rely on T_S | S and
# 2 T_S | S.
assert S % (2 * T_S) == 0


# ----------------------------------------------------------------------------- the leaf


class Leaf:
    """Leaf data of Section 10 ("Leaf data" and Definition "Leaf program"), well-formedness checked.

    Stored column data (all at scale S): G, W, C, N (= NH, the hidden-count coefficient), E, and per
    row k the feature list v[k][c] and diagonal list Dg[k][c].  Row data: d[k] and fam[k], a list of
    family terms (n, v, D).  Leaf constants: F, ng (= n_g), nE (= n_E, JSON "n2"), first, final.
    """

    def __init__(self, obj):
        if not isinstance(obj, dict):
            raise Reject("leaf: expected an object")
        need_keys(obj, LEAF_KEYS, LEAF_KEYS, "leaf")

        rows = need_list(obj["rows"], "leaf.rows")
        self.K = K = len(rows)
        self.d: list[int] = []
        self.fam: list[list[tuple[int, int, int]]] = []
        for k, row in enumerate(rows):
            need_list(row, f"row {k}", 2)
            dk = need_int(row[0], f"row {k}: d")
            if dk <= 0:
                raise Reject(f"row {k}: correlation term d = {dk} is not positive")
            terms = []
            for j, term in enumerate(need_list(row[1], f"row {k}: family")):
                need_list(term, f"row {k} family term {j}", 3)
                n = need_int(term[0], f"row {k} family term {j}: n")
                v = need_int(term[1], f"row {k} family term {j}: v")
                D = need_int(term[2], f"row {k} family term {j}: D")
                if n < 0:
                    raise Reject(f"row {k} family term {j}: count n = {n} is negative")
                if D <= 0:
                    raise Reject(f"row {k} family term {j}: diagonal D = {D} is not positive")
                terms.append((n, v, D))
            self.d.append(dk)
            self.fam.append(terms)

        cols = need_list(obj["cols"], "leaf.cols")
        self.ncols = len(cols)
        self.G: list[int] = []
        self.W: list[int] = []
        self.C: list[int] = []
        self.N: list[int] = []
        self.E: list[int] = []
        self.v: list[list[int]] = [[] for _ in range(K)]
        self.Dg: list[list[int]] = [[] for _ in range(K)]
        for c, col in enumerate(cols):
            need_list(col, f"column {c}", 7)
            self.G.append(need_int(col[0], f"column {c}: G"))
            self.W.append(need_int(col[1], f"column {c}: W"))
            self.C.append(need_int(col[2], f"column {c}: C"))
            self.N.append(need_int(col[3], f"column {c}: NH"))
            self.E.append(need_int(col[4], f"column {c}: E"))
            feats = need_list(col[5], f"column {c}: features", K)
            diags = need_list(col[6], f"column {c}: diagonals", K)
            for k in range(K):
                self.v[k].append(need_int(feats[k], f"column {c}: v_{k}"))
                Dck = need_int(diags[k], f"column {c}: D_{k}")
                if Dck <= 0:
                    raise Reject(f"column {c}: diagonal D_{k} = {Dck} is not positive")
                self.Dg[k].append(Dck)

        self.F = need_int(obj["F"], "leaf.F")
        self.ng = need_int(obj["ng"], "leaf.ng")
        self.nE = need_int(obj["n2"], "leaf.n2")
        self.first = need_int(obj["first"], "leaf.first")
        self.final = need_int(obj["final"], "leaf.final")

        # D_S G_c, the left side of the dual feasibility inequality.
        self.DSG = [D_S * g for g in self.G]

        # Cache of row data, keyed by (k, a, b, iota).  Bounded so that big leaves stay in memory.
        self._cache: dict[tuple[int, int, int, int], tuple[list[int], int, bool]] = {}
        self._cache_limit = max(256, 4_000_000 // max(1, self.ncols))

    # --------------------------------------------------------------- Definition "Root threshold box"

    def root_box(self) -> list[tuple[int, int]]:
        box = []
        for dk in self.d:
            e = ceil_sqrt((dk * T_S * T_S) // S + 1)
            # e^2 S >= d_k T_S^2, so every tau_k with tau_k^2 <= d_k / S lies in [0, e / T_S].
            assert e * e * S >= dk * T_S * T_S and e >= 1
            box.append((0, e))
        return box

    # --------------------------------------------------------------- Definition "Integer costs and budgets"

    def row(self, k: int, a: int, b: int, iota: int) -> tuple[list[int], int, bool]:
        """(costs over the columns, budget, all costs >= 0) of row k on [a, b] in case iota.

        iota = 2 is the first-order relaxation; iota in {0, 1} is the tangent alternative.
        """
        key = (k, a, b, iota)
        hit = self._cache.get(key)
        if hit is not None:
            return hit
        assert 0 <= a < b
        if iota == 2:
            costs, budget = self._first_order(k, a, b)
        else:
            costs, budget = self._tangent(k, a, b, iota)
        res = (costs, budget, all(x >= 0 for x in costs))
        if len(self._cache) >= self._cache_limit:
            self._cache.clear()
        self._cache[key] = res
        return res

    def _first_order(self, k: int, a: int, b: int) -> tuple[list[int], int]:
        """(a) First order.

        cost_ck = floor((v_ck - b S/T_S)_+^2 / D_ck);
        budget_k = S - floor(S^2 a^2 / (T_S^2 d_k)) - sum_(n,v,D) floor(n (v - b S/T_S)_+^2 / D).
        """
        shift = b * S // T_S  # b S / T_S, an integer since T_S | S
        assert shift * T_S == b * S
        costs = [pos(v - shift) ** 2 // D for v, D in zip(self.v[k], self.Dg[k])]
        budget = S - (S * S * a * a) // (T_S * T_S * self.d[k])
        for n, v, D in self.fam[k]:
            budget -= (n * pos(v - shift) ** 2) // D
        return costs, budget

    def _tangent(self, k: int, a: int, b: int, iota: int) -> tuple[list[int], int]:
        """(b) Tangent, case iota in {0, 1}.

        m = (a+b)/(2T_S), h = (b-a)/(2T_S), vbar = v - m S;
        Theta = 0 if vbar <= 0, else floor(vbar (vbar + 2hS) / S) (iota = 0) or
        floor(vbar (vbar - 2hS) / S) (iota = 1);  cost = floor(S Theta / D);
        budget = ceil(S beta), beta = 1 - (p^2 - h^2)/(d_k/S) - sum n Theta_iota(v/S) / (D/S),
        p = a/T_S (iota = 0) or b/T_S (iota = 1),
        Theta_0(u) = ((u-m)_+ + h)^2 - h^2,  Theta_1(u) = ((u-m) - h)^2 - h^2 if u > m else 0.
        """
        assert iota in (0, 1)
        m = Fraction(a + b, 2 * T_S)
        h = Fraction(b - a, 2 * T_S)
        mS = m * S
        hS = h * S
        assert mS.denominator == 1 and hS.denominator == 1  # 2 T_S divides S
        mS = mS.numerator
        two_hS = 2 * hS.numerator
        costs = []
        for v, D in zip(self.v[k], self.Dg[k]):
            vbar = v - mS
            if vbar <= 0:
                theta = 0
            elif iota == 0:
                theta = (vbar * (vbar + two_hS)) // S
            else:
                theta = (vbar * (vbar - two_hS)) // S
            costs.append((S * theta) // D)

        p = Fraction(a, T_S) if iota == 0 else Fraction(b, T_S)
        beta = 1 - (p * p - h * h) / Fraction(self.d[k], S)
        for n, v, D in self.fam[k]:
            beta -= n * theta_exact(iota, Fraction(v, S), m, h) / Fraction(D, S)
        budget = ceil_fraction(S * beta)
        return costs, budget


def theta_exact(iota: int, u: Fraction, m: Fraction, h: Fraction) -> Fraction:
    """Theta_iota(u) of Definition "Integer costs and budgets"(b), exactly."""
    if iota == 0:
        t = pos(u - m) + h
        return t * t - h * h
    if u > m:
        t = (u - m) - h
        return t * t - h * h
    return Fraction(0)


# ----------------------------------------------------------------------------- Definition "Certificate"


def case_iotas(orders: list[int]):
    """All relaxation cases of a terminal box, in the stored order."""
    return itertools.product(*[((0, 1) if o == 1 else (2,)) for o in orders])


def parse_duals(case: dict, K: int, where: str) -> tuple[int, int, int, int, int, list[int]]:
    need_keys(case, CASE_KEYS, frozenset({"Y", "Z"}), where)
    Y = need_int(case["Y"], f"{where}: Y")
    V = need_int(case.get("V", 0), f"{where}: V")
    U = need_int(case.get("U", 0), f"{where}: U")
    P = need_int(case.get("P", 0), f"{where}: P")
    M = need_int(case.get("M", 0), f"{where}: M")
    Z = [need_int(z, f"{where}: Z") for z in need_list(case["Z"], f"{where}: Z", K)]
    for name, x in (("Y", Y), ("V", V), ("U", U), ("P", P), ("M", M)):
        if x < 0:
            raise Reject(f"{where}: dual {name} = {x} is negative")
    for k, z in enumerate(Z):
        if z < 0:
            raise Reject(f"{where}: dual Z_{k} = {z} is negative")
    return Y, V, U, P, M, Z


def check_dual_case(leaf: Leaf, box, iota, duals, where: str) -> int:
    """Check eq:dualfeasible for every column and return the value of the relaxation case."""
    Y, V, U, P, M, Z = duals
    PM = P - M
    # Right side of eq:dualfeasible, column by column.
    rhs = [Y * w + V * cc + U * nn + PM * e for w, cc, nn, e in zip(leaf.W, leaf.C, leaf.N, leaf.E)]
    total = Y * leaf.F + 2 * S * V + leaf.ng * S * U + PM * leaf.nE * S
    for k in range(leaf.K):
        z = Z[k]
        if z == 0:
            continue  # contributes nothing to eq:dualfeasible or to the value
        a, b = box[k]
        costs, budget, _ = leaf.row(k, a, b, iota[k])
        rhs = [r + z * x for r, x in zip(rhs, costs)]
        total += z * budget
    for c, (lhs, r) in enumerate(zip(leaf.DSG, rhs)):
        if lhs > r:
            raise Reject(f"{where}: dual feasibility fails at column {c} (short by {lhs - r})")
    return ceil_div(total, D_S) + leaf.first + leaf.final


def check_exclusion(leaf: Leaf, box, iota, where: str) -> int:
    """Find a row whose costs are all >= 0 and whose budget is < 0; return its index."""
    for k in range(leaf.K):
        a, b = box[k]
        _, budget, nonneg = leaf.row(k, a, b, iota[k])
        if nonneg and budget < 0:
            return k
    raise Reject(f"{where}: exclusion not justified by any row")


def check_terminal(leaf: Leaf, box, node: dict, where: str, stats: dict) -> int:
    """Check one terminal box and return its value (max over the relaxation cases, -1 if none)."""
    need_keys(node, TERMINAL_KEYS | TERMINAL_IGNORED_KEYS, TERMINAL_KEYS, where)
    orders = need_list(node["orders"], f"{where}: orders", leaf.K)
    for k, o in enumerate(orders):
        need_int(o, f"{where}: order {k}")
        if o not in (1, 2):
            raise Reject(f"{where}: order o_{k} = {o} is not 1 or 2")
    cases = need_list(node["cases"], f"{where}: cases")
    n_expected = 2 ** sum(1 for o in orders if o == 1)
    if len(cases) != n_expected:
        raise Reject(f"{where}: {len(cases)} cases, expected {n_expected}")
    values = []
    for i, (iota, case) in enumerate(zip(case_iotas(orders), cases)):
        cw = f"{where} case {i} {iota}"
        if isinstance(case, str):
            if case != "excluded":
                raise Reject(f"{cw}: unknown case record {case!r:.40}")
            check_exclusion(leaf, box, iota, cw)
            stats["excluded"] += 1
        elif isinstance(case, dict):
            duals = parse_duals(case, leaf.K, cw)
            values.append(check_dual_case(leaf, box, iota, duals, cw))
            stats["dual"] += 1
        else:
            raise Reject(f"{cw}: a case must be \"excluded\" or an object")
    # The maximum over the relaxation cases that carry duals; -1 if every case is excluded.
    value = max(values) if values else -1
    stored = node.get("value")
    if stored is not None:  # informational only; never used for acceptance
        stats["stored_values"] += 1
        if stored == value:
            stats["stored_agree"] += 1
        elif stored == -1 and value < -1:
            stats["stored_clamped"] += 1
    return value


def count_terminals(tree) -> int:
    """Structural count of terminal nodes (used for the output line only)."""
    count = 0
    stack = [tree]
    while stack:
        node = stack.pop()
        if isinstance(node, dict) and "split" in node:
            ch = node.get("children")
            if isinstance(ch, list):
                stack.extend(ch)
        else:
            count += 1
    return count


def new_result(obj, reason=None) -> dict:
    """The result record of one input line (value None = rejected)."""
    name = obj.get("name", "?") if isinstance(obj, dict) else "?"
    return {"name": name if isinstance(name, str) else str(name), "value": None, "boxes": 0,
            "reason": reason, "dual": 0, "excluded": 0, "stored_values": 0, "stored_agree": 0,
            "stored_clamped": 0, "argmax": None}


def check_certificate(obj) -> dict:
    """Check one input object {"name", "leaf", "tree"}.

    Returns a dict with keys name, value (int, or None if rejected), boxes, reason (None if
    accepted), the counters dual and excluded (relaxation cases), stored_values, stored_agree and
    stored_clamped (informational comparison with the ignored stored "value" keys), and argmax
    (path of a box of maximal value).
    """
    name = obj.get("name", "?") if isinstance(obj, dict) else "?"
    res = new_result(obj)
    try:
        if not isinstance(obj, dict):
            raise Reject("input line is not a JSON object")
        need_keys(obj, TOP_KEYS, TOP_KEYS, "input")
        if not isinstance(name, str):
            raise Reject("name is not a string")
        try:
            res["boxes"] = count_terminals(obj["tree"])
        except Exception:  # noqa: BLE001 - only used for the output line
            res["boxes"] = 0
        leaf = Leaf(obj["leaf"])
        stats = {"dual": 0, "excluded": 0, "stored_values": 0, "stored_agree": 0,
                 "stored_clamped": 0}
        best = None
        best_path = None
        terminals = 0
        # Depth-first traversal with an explicit stack: (node, box, path).
        stack = [(obj["tree"], leaf.root_box(), "root")]
        while stack:
            node, box, path = stack.pop()
            if not isinstance(node, dict):
                raise Reject(f"{path}: a tree node must be an object")
            if "split" in node:
                need_keys(node, SPLIT_KEYS, SPLIT_KEYS, path)
                k = need_int(node["split"], f"{path}: split")
                mid = need_int(node["mid"], f"{path}: mid")
                if not 0 <= k < leaf.K:
                    raise Reject(f"{path}: split row {k} out of range 0..{leaf.K - 1}")
                a, b = box[k]
                if not a < mid < b:
                    raise Reject(f"{path}: split at {mid} not strictly inside [{a}, {b}] of row {k}")
                left, right = need_list(node["children"], f"{path}: children", 2)
                lbox = list(box)
                rbox = list(box)
                lbox[k] = (a, mid)
                rbox[k] = (mid, b)
                # Push the right child first so that the left one is processed first.
                stack.append((right, rbox, f"{path}.1"))
                stack.append((left, lbox, f"{path}.0"))
            else:
                v = check_terminal(leaf, box, node, path, stats)
                terminals += 1
                if best is None or v > best:
                    best, best_path = v, path
        assert best is not None
        res.update(stats)
        res["boxes"] = terminals
        res["argmax"] = best_path
        if best >= S:
            raise Reject(f"terminal box {best_path} has value {best} >= S")
        res["value"] = best
    except Reject as exc:
        res["value"] = None
        res["reason"] = str(exc)
    except RecursionError:
        res["value"] = None
        res["reason"] = "input nested too deeply"
    return res


def check_line(line: str) -> dict:
    """Check one input line.  Any unexpected error rejects the certificate (never accepts it)."""
    try:
        obj = json.loads(line)
    except (ValueError, RecursionError) as exc:
        return new_result(None, f"bad JSON: {exc}")
    try:
        return check_certificate(obj)
    except Exception as exc:  # noqa: BLE001 - a bug or malformed input must reject, not crash
        return new_result(obj, f"internal error {type(exc).__name__}: {exc}")


def output_line(res: dict) -> str:
    val = "none" if res["value"] is None else str(res["value"])
    return f"{res['name']} {val} {res['boxes']}"


# ----------------------------------------------------------------------------- driver


def stats_record(res: dict) -> str:
    return json.dumps({"name": res["name"], "value": res["value"], "boxes": res["boxes"],
                       "dual": res["dual"], "excluded": res["excluded"],
                       "reason": res["reason"]}) + "\n"


def run_filter(verbose: bool, stats_path: str | None) -> int:
    out = sys.stdout
    stats = open(stats_path, "a", encoding="utf-8") if stats_path else None
    while True:
        line = sys.stdin.readline()
        if not line:
            break
        if not line.strip():
            continue
        res = check_line(line)
        out.write(output_line(res) + "\n")
        out.flush()
        if stats is not None:
            stats.write(stats_record(res))  # one short line per leaf, appended
            stats.flush()
        if verbose and res["reason"] is not None:
            sys.stderr.write(f"{res['name']}: rejected: {res['reason']}\n")
            sys.stderr.flush()
    return 0


def summarize_stats(path: str) -> int:
    """Summarize a --stats file written by one or more filter processes."""
    n = acc = boxes = dual = excl = 0
    best = None
    best_name = None
    rejected = []
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.strip():
                continue
            r = json.loads(line)
            n += 1
            if r["value"] is None:
                rejected.append((r["name"], r["reason"]))
                continue
            acc += 1
            boxes += r["boxes"]
            dual += r["dual"]
            excl += r["excluded"]
            if best is None or r["value"] > best:
                best, best_name = r["value"], r["name"]
    print(f"{n} leaves, {acc} accepted, {len(rejected)} rejected; {boxes} terminal boxes; "
          f"{dual + excl} relaxation cases ({dual} dual, {excl} excluded); "
          f"largest value {best} at {best_name}")
    for name, reason in rejected[:20]:
        print(f"  rejected {name}: {reason}")
    return 0 if not rejected else 1


def run_file(path: str) -> int:
    n = acc = rej = boxes = dual = excl = sv = sa = sc = 0
    best = None
    best_name = None
    t0 = time.time()
    with open(path, encoding="utf-8") as fh:
        for line in fh:
            if not line.strip():
                continue
            t1 = time.time()
            res = check_line(line)
            dt = time.time() - t1
            n += 1
            print(output_line(res), flush=True)
            if res["value"] is None:
                rej += 1
                print(f"  rejected: {res['reason']}", flush=True)
                continue
            acc += 1
            boxes += res["boxes"]
            dual += res["dual"]
            excl += res["excluded"]
            sv += res["stored_values"]
            sa += res["stored_agree"]
            sc += res["stored_clamped"]
            print(f"  accepted: {res['boxes']} terminal boxes, {res['dual']} dual cases, "
                  f"{res['excluded']} excluded cases, max at {res['argmax']}, "
                  f"{dt:.2f} s", flush=True)
            if best is None or res["value"] > best:
                best, best_name = res["value"], res["name"]
    print(f"summary: {n} leaves, {acc} accepted, {rej} rejected; {boxes} terminal boxes, "
          f"{dual + excl} relaxation cases ({dual} dual, {excl} excluded)")
    if best is not None:
        print(f"summary: largest value {best} (= {best}/10^16) at {best_name}; "
              f"S - value = {S - best}")
    if sv:
        print(f"summary (informational, not used for acceptance): of {sv} stored terminal "
              f"values, {sa} equal the recomputed box value, {sc} are -1 where every dual case "
              f"of the box has value < -1 (the stored values clamp at -1), "
              f"{sv - sa - sc} differ otherwise")
    print(f"summary: {time.time() - t0:.1f} s")
    return 0 if rej == 0 else 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--file", help="read a JSONL file and print a summary instead of filtering")
    ap.add_argument("--verbose", action="store_true",
                    help="filter mode: write rejection reasons to standard error")
    ap.add_argument("--stats", metavar="PATH",
                    help="filter mode: also append one JSON line per leaf (value, boxes, dual and "
                         "excluded case counts, rejection reason) to PATH")
    ap.add_argument("--summarize-stats", metavar="PATH",
                    help="print totals of a --stats file and exit")
    args = ap.parse_args(argv)
    sys.setrecursionlimit(max(10000, sys.getrecursionlimit()))  # for json.loads of deep trees
    if args.summarize_stats:
        return summarize_stats(args.summarize_stats)
    if args.file:
        return run_file(args.file)
    return run_filter(args.verbose, args.stats)


if __name__ == "__main__":
    sys.exit(main())
