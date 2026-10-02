"""Leaf inputs and near rows of the graded-near proof (research/PROOF.md §§5-7).

Leaf inputs are the repository's regular case models regenerated at the target
exponent (make_endgame for an inside first zero, first_out_input for an outside
one), without the collective envelope, with the refined real/real third-family
bound.  An inside_repair "identities" node is replaced by the regular model of its
own case: the hidden-family branches are not used.

Every near row except `old` is an instance of the graded near lemma (PROOF.md §6):

  family   reference anchor s1 = floor(lambda1^lo, 1/50), sieve part zero; first family
           (inside: its zero; rc: conjugate pair with a height range; outside: its global
           zero and, as hidden columns, its local zeros), reserved second family.
  shifted  reference anchor = the repository's validated shift min(1.9, lambda', global
           lambda2), used only when it is > s1 and >= lambda1^lo (inside; graded_driver.has_shifted):
           the first zero is retained above the anchor.
  graded   reference anchor s in a menu, sieve part; every ordinary character at its own
           anchor min(lambda_lo, s); first family (inside) and second family included.
  old      the regular model's own two-test near row, inherited from the 4.30 candidate
           (PROOF.md §6.6); inside fallback only.
"""
import os
import sys
from pathlib import Path
from fractions import Fraction as Q
HERE = Path(__file__).resolve().parent
SN = HERE.parent/'sieve_near'
sys.path.insert(0, str(SN))
import leaf_driver as LD            # noqa: E402  (enclosures, graded_row, repository builders)
import propose_params               # noqa: E402
import family_row                   # noqa: E402
import third_refine                 # noqa: E402

safe_anchor = LD.safe_anchor
RC_MU_SPLIT = LD.RC_MU_SPLIT


def _share_weight_objects():
    """two_test_enclosures.wgt(L) builds a fresh RigorousWeights on every call, so its per-instance
    memo of the far weight w(lambda) (an interval quadrature) is lost between leaves.  The object is
    deterministic in L and never mutated; sharing one instance per L makes the memo effective across
    the leaves a worker regenerates.  Values, and hence certificates, are unchanged."""
    from functools import lru_cache
    import two_test_enclosures as TT
    orig = getattr(TT.wgt, '__wrapped__', TT.wgt)
    if getattr(TT.wgt, '_graded_shared', False):
        return
    shared = lru_cache(maxsize=None)(orig)
    shared._graded_shared = True
    for mod in list(sys.modules.values()):
        if getattr(mod, 'wgt', None) is orig:
            mod.wgt = shared
    TT.wgt = shared


if os.environ.get('GRADED_SHARE_WEIGHTS', '1') == '1':
    _share_weight_objects()


# ------------------------------------------------------------------ inputs
def reserve_specs(sp, h):
    """Children of an unreserved specification at h (PROOF.md §8), split by its lowest local
    non-first family: reserved in [r,h) as one real character, reserved in [r,h) as a nonreal
    pair, or none below h (every non-first height-one representative has parameter >= h).
    Every configuration of the parent falls in one child."""
    import copy
    h = Q(h); r = Q(sp['ordinary_lower'])
    assert sp['second'] is None and r < h <= 2
    kids = []
    for n2 in (1, 2):
        c = copy.deepcopy(sp); c['second'] = {'lo': str(r), 'hi': str(h), 'n': n2}
        kids.append(c)
    c = copy.deepcopy(sp); c['ordinary_lower'] = str(h)
    kids.append(c)
    return kids


def apply_path(sp, path):
    """Follow a path of refinements: the repository's split_specs ('second', 'gap') or a
    reservation split ('reserve')."""
    from refinement_cover import split_specs
    for axis, mid, side in path:
        if axis == 'reserve':
            assert side in (0, 1, 2)
            sp = reserve_specs(sp, mid)[side]
        else:
            assert side in (0, 1)
            sp = split_specs(sp, axis, mid)[side]
    return sp


def inside_input(src, L, path=()):
    """Regular inside model at L from a captured repository input (scenario leaf or the
    4.33 template of an identities node), optionally along a path of refinements."""
    sp = apply_path(LD.spec_of(src), path)
    out = LD.make_endgame(sp, L, LD.parse_params(src), src['lambda_den'])
    if out is None:
        return None
    if src.get('far_parameters') and 'hidden_rows' not in src:
        out = LD.replace_far(out, src['far_parameters'])
    return third_refine.refine_third(out)


def outside_input(src, L, path=()):
    if not path:
        return LD.regen_out(src, L)
    if not any(axis == 'reserve' for axis, _, _ in path):
        return LD.regen_out_split(src, L, list(path))
    # as LD.regen_out_split, with reservation splits in the path
    nc = str(HERE.parent/'near'/'code')
    if nc not in sys.path:
        sys.path.insert(0, nc)
    import first_outside_blocks as fob
    from refine_probe import spec_from_input
    sp = apply_path(spec_from_input(src), path)
    e = src['extension']
    par = dict(method=e['variant'], gg=e['gG'], gz=e['gZ'], mix=e.get('mix', '0'), zeta=e.get('zeta', '3'))
    return fob.first_out_input(sp, L, 'outside_buffer', par, src['lambda_den'])


def second_columns(inp, den2):
    """The reserved second family as LP columns (PROOF.md §7).

    The leaf's input charges the family at fixed ends: objective n2 G(lo2) in `first`, far
    deduction n2 w(hi2) in the budget, near features at hi2.  Here those charges are removed
    and replaced by columns: sub-bins [l,r] of [lo2,hi2] (grid 1/den2) with far cost w(r),
    objective G(l) and near features at r, whose masses sum to n2.  The actual family (its
    n2 characters share one height-one parameter in [lo2,hi2]) is a feasible point."""
    import math
    from two_test_enclosures import wgt
    from far_enclosures import far_weights
    from enclosures import upper, lower
    sec = inp['second']
    assert sec and 'second_cols' not in inp
    W = far_weights(inp['far_parameters']) if inp.get('far_parameters') else wgt(inp['L'])
    pw = wgt(inp['L'])
    n2 = int(sec['n']); lo2, hi2 = Q(sec['lo']), Q(sec['hi'])
    real = n2 == 1
    assert sec['contribution'] == n2*upper(pw.G(lo2, real))
    inner = [Q(k, den2) for k in range(math.floor(lo2*den2)+1, math.ceil(hi2*den2)) if lo2 < Q(k, den2) < hi2]
    pts = [lo2]+inner+[hi2]
    out = dict(inp)
    out['second_cols'] = [[str(l), str(r), lower(W.w(r)), upper(pw.G(l, real))] for l, r in zip(pts, pts[1:])]
    out['first'] = inp['first']-sec['contribution']
    out['far_budget'] = inp['far_budget']+n2*lower(W.w(hi2))
    return out


# ------------------------------------------------------------------ rows
def row_spec(inp, kind, s=None, outside=False, mu_range=None, dz_range=None):
    s1 = safe_anchor(inp)
    if kind == 'old':
        assert not outside and mu_range is None and dz_range is None
        return dict(kind='old', parameters={})
    if kind == 'family':
        p = LD.family_parameters(inp)
    elif kind == 'shifted':
        p = family_row.propose_shifted(inp); p.pop('allowed', None)
    else:
        p = propose_params.params(s1, Q(s))
    spec = dict(kind=kind, parameters=p)
    if mu_range is not None:
        spec['mu_range'] = [str(mu_range[0]), None if mu_range[1] is None else str(mu_range[1])]
    if dz_range is not None:
        assert kind == 'family'
        spec['dz_range'] = [str(dz_range[0]), None if dz_range[1] is None else str(dz_range[1])]
    return spec


def old_row(inp):
    """The regular model's own two-test near row (the 4.30 route's near row, inherited; research/
    PROOF.md §6.6), in threshold form.  The repository's constraint
        sum_i x_i (V0_i - tau)_+^2 <= D(1 - tau^2/d) - n (D/Df)(v_first - tau)_+^2 - n2 (v2 - tau)_+^2
    divided by D: bin features V0_i = rows[i][4] with diagonal D, the first family as a fixed term
    with diagonal Df, a reserved second family as a fixed term at its range's feature v2.  Features
    enter only through (v - tau)_+ with tau >= 0, so negative features are replaced by 0 exactly."""
    fam = [(int(inp['n']), max(0, int(inp['v_first'])), int(inp['Df']))]
    sec = inp.get('second')
    if sec:
        fam.append((int(sec['n']), max(0, int(sec['v']))))
    return dict(d=int(inp['d']), D=int(inp['D']), v=[max(0, int(r[4])) for r in inp['rows']], fam=fam)


def build_row(inp, spec, outside):
    if spec['kind'] == 'old':
        # second-family columns keep the fixed term: v2 bounds the feature over the whole range
        assert not outside and not spec['parameters'] and 'mu_range' not in spec and 'dz_range' not in spec
        return old_row(inp)
    row = _build_row(inp, spec, outside)
    if inp.get('second_cols') and 'fam' in row:
        row = _columns_for_second(inp, spec, row)
    return row


def _columns_for_second(inp, spec, row):
    """Move the reserved second family from the row's fixed terms to per-column features.
    Each column [l,r] uses the fixed term's anchor rule with lo2 replaced by l (every zero of
    the family has parameter >= max(lambda1^lo, global lambda2 bound) and its representative
    has parameter >= l), and its feature at r."""
    test = LD.sieve_test(spec['parameters'])
    s = test.s
    a = Q(inp['case']['lo']); l2 = Q(inp['case']['source_l2'])
    row = dict(row); row['fam'] = list(row['fam'])
    n2, _, _ = row['fam'].pop()          # graded_row appends the second family last
    assert n2 == int(inp['second']['n'])
    vs, Dvs = [], []
    for l, r, _, _ in inp['second_cols']:
        l, r = Q(l), Q(r)
        anchor = min(max(a, min(l2, l)), s)
        _, v, Dn = LD._family_term(test, 1, r, anchor, row['D'])
        vs.append(v); Dvs.append(Dn)
    row['vs'], row['Dvs'] = vs, Dvs
    return row


def _build_row(inp, spec, outside):
    kind, p = spec['kind'], spec['parameters']
    mr = spec.get('mu_range')
    if mr is not None:
        mr = (mr[0], mr[1])
    dz = spec.get('dz_range')
    if kind == 'family':
        if outside:
            assert dz is None
            return LD.graded_row(inp, p, families='outside_first', sec_anchor='l2',
                                 hidden=('outside' if inp.get('hidden_rows') else False))
        return LD.graded_row(inp, p, families=True, mu_range=mr, sec_anchor='l2',
                             dz_range=(None if dz is None else (dz[0], dz[1])))
    assert dz is None
    if kind == 'shifted':
        assert not outside
        return LD.graded_row(inp, p, families='shifted', sec_anchor='l2')
    assert kind == 'graded'
    if outside:
        return LD.graded_row(inp, p, families=('second' if inp['second'] else False), sec_anchor='l2')
    return LD.graded_row(inp, p, families=True, sec_anchor='l2')


_ROWS = {}


def _row(inp, spec, outside):
    """build_row memoized per leaf input object (rows depend only on the input and the spec)."""
    import json
    key = (id(inp), json.dumps(spec, sort_keys=True), outside)
    hit = _ROWS.get(key)
    if hit is None or hit[0] is not inp:
        if len(_ROWS) > 400:
            _ROWS.clear()
        hit = _ROWS[key] = (inp, build_row(inp, spec, outside))
    return hit[1]


def leaf(inp, specs, outside):
    from graded_cert import Leaf
    return Leaf(inp, [_row(inp, sp, outside) for sp in specs])
