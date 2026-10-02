"""Staged certification of one leaf of the graded-near proof.

Row sets grow in stages (family row, shifted row, then graded anchors); the first
stage whose floating maximum clears its margin is certified exactly.  rc leaves
are certified separately on each range of the first zero's normalized height.
Hard leaves with a reserved second family are replaced by the repository's
second-family splits (children exhaust the parent).
"""
import os
import json
from fractions import Fraction as Q
import graded_leaves as LV
import graded_cert as CT

# normalized height difference between rho1 and the first family's other zero (PROOF.md §6.5)
DZ_SPLIT = (('0', '1'), ('1', '3/2'), ('3/2', '2'), ('2', '3'), ('3', '5'), ('5', None))
SECOND_COLS_GRID = 400                                              # grid 1/400 of second-family columns (PROOF.md §7)
SECOND_COLS = SECOND_COLS_GRID if os.environ.get('GRADED_SECOND_COLS', '1') != '0' else 0
STAGES = [[Q(19, 10)], [Q(19, 10), Q(23, 10)], [Q(3, 2), Q(19, 10), Q(23, 10)]]
MARGINS = (0.97, 0.98, 0.99)
MENU = [Q(x, 10) for x in range(11, 30, 2)]


def has_shifted(inp, outside):
    """The shifted row applies when the repository's shift s exceeds the safe anchor and s >= lambda1^lo
    (PROOF.md §6.5: a <= s <= min(lambda', lambda2)).  A source lambda2 bound below lambda1^lo can make
    the shift smaller than a; the row is then not used."""
    s = Q(inp['shift'])
    return not outside and s > LV.safe_anchor(inp) and s >= Q(inp['case']['lo'])


def _specs(inp, anchors, outside, mu_range, dz_range=None, old=False):
    s1 = LV.safe_anchor(inp)
    specs = [LV.row_spec(inp, 'family', outside=outside, mu_range=mu_range, dz_range=dz_range)]
    if has_shifted(inp, outside):
        specs.append(LV.row_spec(inp, 'shifted'))
    specs += [LV.row_spec(inp, 'graded', s=a) for a in sorted(anchors) if a > s1]
    if old:
        specs.append(LV.row_spec(inp, 'old'))
    return specs


# Row sets tried before the greedy menu: tokens F (family row), S (shifted row, when available)
# and graded anchors.  Fewer rows mean a lower-dimensional threshold box and a much smaller
# certificate, so four-row sets are tried before five (sieve-majorant-near.md §6f).
# 'S?' includes the shifted row when the leaf has one.
ROW_STAGES = [('F', 'S?', Q(19, 10)),
              ('S', Q(3, 2), Q(19, 10), Q(23, 10)),
              ('F', 'S?', Q(8, 5), Q(21, 10)),
              ('F', Q(3, 2), Q(19, 10), Q(23, 10)),
              ('F', 'S?', Q(3, 2), Q(19, 10), Q(23, 10))]
ROW_MARGINS = (0.985, 0.99, 0.985, 0.99, 0.99)   # thresholds for the strong search (§6f)

# Stages with the regular model's own two-test near row 'O' (inherited from the 4.30 route; PROOF.md
# §6.6), tried only when the graded rows alone fail (sieve-majorant-near.md §6h).  The old row goes
# last, so a height- or second-zero-split part keeps its family row first.
OLD_STAGES = [('F', Q(19, 10), 'O'),
              ('F', 'S?', Q(19, 10), 'O'),
              ('S', Q(3, 2), Q(19, 10), 'O'),
              ('F', Q(3, 2), Q(19, 10), 'O'),
              ('S', Q(3, 2), Q(19, 10), Q(23, 10), 'O')]
OLD_MARGINS = (0.985, 0.985, 0.99, 0.99, 0.99)


def _row_set(inp, tokens, outside, mu_range, dz_range=None):
    """Row specs for a stage, or None when the stage does not apply to this leaf."""
    s1 = LV.safe_anchor(inp)
    has_shift = has_shifted(inp, outside)
    specs = []
    for t in tokens:
        if t == 'F':
            specs.append(LV.row_spec(inp, 'family', outside=outside, mu_range=mu_range, dz_range=dz_range))
        elif t in ('S', 'S?'):
            if has_shift:
                specs.append(LV.row_spec(inp, 'shifted'))
            elif t == 'S':
                return None
        elif t == 'O':
            if outside:
                return None
            specs.append(LV.row_spec(inp, 'old'))
        elif t > s1:
            specs.append(LV.row_spec(inp, 'graded', s=t))
    if (mu_range is not None or dz_range is not None) and (not specs or specs[0]['kind'] != 'family'):
        return None           # a height-split part carries its range on the family row
    return specs


def _name(sp):
    return sp['kind']+(':'+sp['parameters']['s'] if 's' in sp['parameters'] else '')


def staged(inp, outside=False, mu_range=None, log=print, max_rows=6, max_boxes=20000, fail_fast=False,
           dz_range=None, old=False):
    stages, margins = (OLD_STAGES, OLD_MARGINS) if old else (ROW_STAGES, ROW_MARGINS)

    def worst(specs, strong=False):
        lf = LV.leaf(inp, specs, outside)
        return CT.float_worst(lf, starts=3, grid=14, sweeps=6) if strong else CT.float_worst(lf)

    def certify(specs):
        lf = LV.leaf(inp, specs, outside)
        tree, mx, nb = CT.build(lf, max_boxes=max_boxes)
        return dict(rows=specs, tree=tree, maximum=mx, boxes=nb)
    tried = []
    seen = set()
    for k, tokens in enumerate(stages):
        specs = _row_set(inp, tokens, outside, mu_range, dz_range)
        if specs is None or len(specs) > max_rows:
            continue
        key = tuple(json.dumps(sp, sort_keys=True) for sp in specs)
        if key in seen:
            continue
        seen.add(key)
        v = worst(specs, strong=True)     # the weak search underestimates by up to ~.05 (§6f)
        log(('stage', [_name(sp) for sp in specs], round(v, 6)))
        if v < margins[k]:
            try:
                return certify(specs)
            except CT.CannotCertify as e:
                log(('cert-fail', e.args[0], e.value))
                if specs == _specs(inp, [t for t in tokens if not isinstance(t, str)], outside, mu_range, dz_range,
                                   old):
                    tried.append(tuple(sorted(t for t in tokens if not isinstance(t, str))))
    anchors = list(STAGES[-1])
    specs = _specs(inp, anchors, outside, mu_range, dz_range, old)
    if len(specs) > max_rows or (len(specs) == max_rows and tuple(anchors) in tried):
        raise CT.CannotCertify('no row set certified within the row limit', None, None)
    val = worst(specs)
    if fail_fast and len(specs) >= max_rows and val >= MARGINS[-1]:
        raise CT.CannotCertify('floating maximum above margin at the row limit', None, val)
    for _ in range(3):
        while len(specs) < max_rows and (val >= MARGINS[-1] or tuple(anchors) in tried):
            best = None
            for c in MENU:
                if c <= LV.safe_anchor(inp) or any(abs(c-a) < Q(3, 20) for a in anchors):
                    continue
                vv = worst(_specs(inp, anchors+[c], outside, mu_range, dz_range, old))
                if best is None or vv < best[0]:
                    best = (vv, c)
            if best is None:
                break
            anchors = anchors+[best[1]]; val = best[0]
            specs = _specs(inp, anchors, outside, mu_range, dz_range, old)
            log(('greedy', [str(a) for a in sorted(anchors)], round(val, 6)))
            if val < MARGINS[-1] and tuple(anchors) not in tried:
                break
        if fail_fast and val >= MARGINS[-1]:
            raise CT.CannotCertify('floating maximum above margin', None, val)
        try:
            return certify(specs)
        except CT.CannotCertify as e:
            log(('cert-fail', e.args[0], e.value))
            tried.append(tuple(anchors))
            if len(specs) >= max_rows:
                raise
    raise CT.CannotCertify('staged driver exhausted')


def with_columns(inp):
    """(input, flag): the reserved second family as LP columns when enabled (PROOF.md §7)."""
    if SECOND_COLS and inp.get('second'):
        return LV.second_columns(inp, SECOND_COLS), SECOND_COLS
    return inp, None


def certify_leaf(inp, outside=False, log=print, **kw):
    """One leaf: rc inside leaves are split by the first zero's normalized height.  The flag
    'second_columns' records the column grid; verification re-applies it."""
    inp, flag = with_columns(inp)
    rec = _certify_leaf(inp, outside, log, **kw)
    if flag:
        rec['second_columns'] = flag
    return rec


def dz_applicable(inp, outside):
    gap = inp.get('gap')
    return (not outside and inp['case']['kind'] == 'complex' and bool(gap) and gap['hi'] != 'infinity')


def certify_dz(inp, outside=False, log=print, **kw):
    """Split a complex leaf with a finite gap by the height difference of the first family's second
    zero (DZ_SPLIT); every part carries its range on the family row (research/PROOF.md §6.5)."""
    assert dz_applicable(inp, outside)
    inp2, flag = with_columns(inp)
    parts = []
    for zr in DZ_SPLIT:
        log(('dz_range', zr))
        parts.append(_staged_either(inp2, False, log, dz_range=zr, **kw))
    rec = dict(dz_split=parts, maximum=max(p['maximum'] for p in parts), boxes=sum(p['boxes'] for p in parts))
    if flag:
        rec['second_columns'] = flag
    return rec


def _staged_either(inp, outside, log, **kw):
    """The graded rows first; if they fail (inside), the stages that add the regular model's own
    two-test near row (OLD_STAGES)."""
    try:
        return staged(inp, outside=outside, log=log, **kw)
    except CT.CannotCertify as e:
        if outside:
            raise
        log(('graded-failed', e.args[0], e.value))
    return staged(inp, outside=outside, log=log, old=True, **kw)


def _certify_leaf(inp, outside=False, log=print, **kw):
    if not outside and inp['case']['kind'] == 'rc':
        parts = []
        for mr in LV.RC_MU_SPLIT:
            log(('mu_range', mr))
            parts.append(_staged_either(inp, False, log, mu_range=mr, **kw))
        return dict(mu_split=parts, maximum=max(p['maximum'] for p in parts), boxes=sum(p['boxes'] for p in parts))
    return _staged_either(inp, outside, log, **kw)


def split_paths(mids):
    paths = []
    for i in range(len(mids)+1):
        path = []
        if i > 0:
            path.append(('second', str(mids[i-1]), 1))
        if i < len(mids):
            path.append(('second', str(mids[i]), 0))
        paths.append(path)
    return paths


def _input(src, L, outside, path=()):
    return (LV.outside_input if outside else LV.inside_input)(src, L, list(path))


def certify_split(src, L, k, outside=False, log=print, prefix=(), **kw):
    """Replace a case by its k-way second-family split (repository split_specs)."""
    base = _input(src, L, outside, prefix)
    lo, hi = Q(base['ordinary_lower']), Q(base['second']['hi'])
    mids = [lo+(hi-lo)*i/k for i in range(1, k)]
    children = []
    for sub in split_paths(mids):
        path = list(prefix)+sub
        inp = _input(src, L, outside, path)
        if inp is None:
            children.append(dict(path=path, excluded_by_location=True)); continue
        log(('split-child', path))
        rec = certify_leaf(inp, outside=outside, log=log, **kw)
        rec['path'] = path
        children.append(rec)
    return dict(split=[str(m) for m in mids], children=children,
                maximum=max(c.get('maximum', -1) for c in children), boxes=sum(c.get('boxes', 0) for c in children))


def certify_reserve(src, L, h, outside=False, log=print, prefix=()):
    """Replace an unreserved case by its reservation split at h (graded_leaves.reserve_specs);
    each child is certified with its own repairs."""
    children = []
    for k in range(3):
        path = list(prefix)+[('reserve', str(h), k)]
        log(('reserve-child', path))
        rec = certify_case(src, L, outside=outside, log=log, path=path, depth=1)
        rec['path'] = path
        children.append(rec)
    return dict(reserve=str(h), children=children,
                maximum=max(c.get('maximum', -1) for c in children), boxes=sum(c.get('boxes', 0) for c in children))


def certify_case(src, L, outside=False, log=print, path=(), fail_fast=True, depth=0):
    """Staged certification of the case at `path`; on failure: second-family splits (3 then 5
    ways) for a reserved case, a reservation split at the third-family bound for an unreserved
    one, and finally larger row and box budgets."""
    inp = _input(src, L, outside, path)
    if inp is None:
        return dict(excluded_by_location=True)
    # at most four rows first: a five-dimensional threshold box is rarely worth its size (§6f)
    try:
        return certify_leaf(inp, outside=outside, log=log, fail_fast=fail_fast, max_rows=4, max_boxes=12000)
    except CT.CannotCertify as e:
        log(('staged-failed', e.args[0], e.value))
    if dz_applicable(inp, outside):
        try:
            return certify_dz(inp, outside=outside, log=log, max_rows=4, max_boxes=12000, fail_fast=True)
        except CT.CannotCertify as e:
            log(('dz-failed', e.args[0], e.value))
    if inp.get('second'):
        for k in (3, 5, 9):          # 9 ways was first needed at depth 1, then for nodes 2397/1 and 2421/1
            try:
                return certify_split(src, L, k, outside=outside, log=log, prefix=path, max_rows=4,
                                     max_boxes=20000, fail_fast=True)
            except CT.CannotCertify as e:
                log(('split-failed', k, e.args[0], e.value))
    elif depth == 0:
        spec = LV.apply_path(LV.LD.spec_of(src) if not outside else _outside_spec(src), path)
        h = min(Q(inp['third_lower']), Q(2))
        if spec['second'] is None and Q(spec['ordinary_lower']) < h:
            try:
                return certify_reserve(src, L, h, outside=outside, log=log, prefix=path)
            except CT.CannotCertify as e:
                log(('reserve-failed', str(h), e.args[0], e.value))
    if os.environ.get('GRADED_LAST_RESORT', '0') != '1':
        raise CT.CannotCertify('repairs exhausted', None, None)
    return certify_leaf(inp, outside=outside, log=log, max_rows=6, max_boxes=80000)


def _outside_spec(src):
    import sys
    nc = str(LV.HERE.parent/'near'/'code')
    if nc not in sys.path:
        sys.path.insert(0, nc)
    from refine_probe import spec_from_input
    return spec_from_input(src)


def certify_with_repairs(src, L, outside=False, log=print, fail_fast=True):
    return certify_case(src, L, outside=outside, log=log, fail_fast=fail_fast)


# ------------------------------------------------------------------ verification
def verify_record(inp, rec, outside=False):
    if rec.get('second_columns'):
        assert inp.get('second') and rec['second_columns'] == SECOND_COLS_GRID
        inp = LV.second_columns(inp, rec['second_columns'])
    return _verify_record(inp, rec, outside)


def _verify_record(inp, rec, outside=False, mu=None, dz=None):
    """mu: the normalized-height range this record must cover (None: every height).  A row's
    mu_range restricts the rc conjugate-pair term to that range, so it is accepted only inside
    the matching part of a complete mu_split."""
    if 'dz_split' in rec:
        assert mu is None and dz is None and 'mu_split' not in rec and dz_applicable(inp, outside)
        parts = rec['dz_split']
        expected = [[a, b] for a, b in DZ_SPLIT]
        assert len(parts) == len(expected)
        assert not any(k in p for p in parts for k in ('second_columns', 'mu_split', 'dz_split'))
        res = [_verify_record(inp, p, outside, None, e) for p, e in zip(parts, expected)]
        mx = max(r[0] for r in res); assert mx == rec['maximum']
        return mx, sum(r[1] for r in res)
    if 'mu_split' in rec:
        assert mu is None and dz is None and not outside and inp['case']['kind'] == 'rc'
        parts = rec['mu_split']
        expected = [[str(a), None if b is None else str(b)] for a, b in LV.RC_MU_SPLIT]
        assert len(parts) == len(expected)
        assert not any('second_columns' in p or 'mu_split' in p for p in parts)
        res = [_verify_record(inp, p, outside, e) for p, e in zip(parts, expected)]
        mx = max(r[0] for r in res); assert mx == rec['maximum']
        return mx, sum(r[1] for r in res)
    for k, sp in enumerate(rec['rows']):
        mr = sp.get('mu_range')
        if mu is None:
            assert mr is None, 'height-restricted row outside a height split'
        elif k == 0:
            assert mr == mu and sp['kind'] == 'family'
        else:
            assert mr is None or mr == mu
        zr = sp.get('dz_range')
        if dz is None or k > 0:
            assert zr is None, 'second-zero row outside its height split'
        else:
            assert zr == dz and sp['kind'] == 'family' 
    lf = LV.leaf(inp, rec['rows'], outside)
    mx, nb = CT.verify_tree(lf, rec['tree'])
    assert mx == rec['maximum']
    return mx, nb


def verify_leaf(src, L, rec, outside=False, prefix=()):
    """Verify the record of the case at `prefix` (a path of refinements from the source)."""
    prefix = [tuple(p) for p in prefix]
    if rec.get('excluded_by_location'):
        assert _input(src, L, outside, prefix) is None
        return -1, 0
    if 'reserve' in rec:
        h = str(Q(rec['reserve']))
        assert rec['reserve'] == h and len(rec['children']) == 3
        mx = -1; nb = 0
        for k, ch in enumerate(rec['children']):
            path = prefix+[('reserve', h, k)]          # apply_path asserts the parent is unreserved, r < h <= 2
            assert [tuple(p) for p in ch['path']] == path
            m, n = verify_leaf(src, L, ch, outside, path)
            mx = max(mx, m); nb += n
        assert mx == rec['maximum']
        return mx, nb
    if 'split' in rec:
        mids = [Q(m) for m in rec['split']]
        assert all(a < b for a, b in zip(mids, mids[1:]))
        subs = split_paths(mids)
        assert len(subs) == len(rec['children'])
        base = _input(src, L, outside, prefix)
        lo, hi = Q(base['ordinary_lower']), Q(base['second']['hi'])
        assert lo < mids[0] and mids[-1] < hi
        mx = -1; nb = 0
        for sub, ch in zip(subs, rec['children']):
            path = prefix+[tuple(p) for p in sub]
            assert [tuple(p) for p in ch['path']] == path
            assert 'split' not in ch and 'reserve' not in ch
            m, n = verify_leaf(src, L, ch, outside, path)
            mx = max(mx, m); nb += n
        assert mx == rec['maximum']
        return mx, nb
    inp = _input(src, L, outside, prefix)
    return verify_record(inp, rec, outside)
