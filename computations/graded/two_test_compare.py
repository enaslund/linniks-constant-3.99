#!/usr/bin/env python3
"""Exact comparison of the inherited two-test near row with the 4.30 pipeline's own constraint.

The two-test row (paper §9.6: `thm:twotest`, `prop:mixture`, `prop:paired`; research/PROOF.md
§6.6) is the only near row of the corpus that the formal row checker does not cover.  The graded
certifier imposes it as `graded_leaves.old_row` (the leaf input's own `d`, `D`, `Df`, `v_first`,
bin features `rows[i][4]` and reserved-family feature `second['v']`), evaluated by
`graded_cert.Leaf.row_case`.  The 4.30 pipeline imposed the same inequality, not divided by `D`,
in `build_progress.near` (its builder) and in `verify_progress.scenario` (its checker):

    sum_i x_i (V_i - tau)_+^2 <= D (1 - tau^2/d) - n (D/Df) (v_f - tau)_+^2 - n2 (v2 - tau)_+^2 .

What this script does:

1. **Find the leaves.**  Every leaf record of the three stored corpora is scanned for a row of
   kind `old`.  The roots found are replayed with `graded_verify` (the replay re-checks every
   certificate of those roots exactly), and the `graded_cert.Leaf` objects of the leaves with an
   `old` row are captured, as `graded_lean_export` does, together with their 4.30 source input
   and refinement path.
2. **Compare the row, box by box.**  For the row's threshold dimension, on every interval that
   the leaf's stored certificate tree uses and on seeded random intervals `[a,b]` (integer ticks,
   `TS = 10^6`, inside `[0, e]`, `e = Leaf.ends[k]`), and for every relaxation case (first order;
   tangent cases 0 and 1), the exact rational costs and budget are computed
   * for the graded row, by evaluating the source code of `graded_cert.Leaf._row_case` (and
     `tangent_cost`) with every floor division `//` and the ceiling `ceil_q` replaced by exact
     rational division (an AST rewrite of the committed source; the unmodified method gives the
     integers actually used);
   * for the 4.30 constraint, by evaluating `build_progress.near` and the constraint statements
     of `verify_progress.scenario` (extracted from its AST) in the same way, on the 4.30 input of
     the leaf's case.  The 4.30 code has only the first-order relaxation.  For the tangent cases
     the same exact 4.30 code is evaluated at a dual number `tau = m + eps` (value and exact
     derivative at the box centre `m`) and the tangent rule `value -+ h * derivative` is applied;
   * from a direct transcription of the paper's threshold form (reference).
   It checks, exactly as rationals: graded cost = 4.30 cost * S/D for every ordinary column
   (matched by its bin; D is the 4.30 input's), graded budget = 4.30 budget * S/D, the builder
   and the checker agree, the paper transcription agrees, second-family columns cost 0; and that
   the integers of `Leaf.row_case` are rounded in the safe direction (costs down, budgets up),
   with the largest gaps (in units of 1/S).
3. **Regenerate the data.**  `d, D, Df, v_first`, every bin feature and the reserved family's
   feature are recomputed from the 4.30 enclosure routines (`two_test_enclosures.constants`,
   `feat`; `extension_enclosures.mixfeature`, `paired_first`), with their caches cleared, from the
   leaf's regenerated case and the 4.30 record's parameters, and compared with the leaf input,
   with the row, and with the 4.30 input of the case (for an unrefined leaf, the 4.30 record's own
   input).  Every column must also be a bin, with the same feature, of the 4.30 row builder
   (`published_single_inputs.single_rows`, or `extension_enclosures.mixrows`).  The paired variant's side condition `2D' >= zeta_* max(m',0)`, its margin and `B >= 0`
   are re-checked.
4. **Negative test.**  On every leaf, each of the row's integers (`D`, `d`, the largest bin
   feature, `v_first`, `Df`, `n`, `v2`) is moved by one unit (1/S) up and down, and each of a few
   data fields of the leaf input, of the 4.30 input and of the regenerated values by one unit; the
   comparisons must detect every perturbation (on the boxes [0,1], [e-1,e] and a certificate
   interval).

The random boxes use Python's `random.Random` seeded with the string
`two-test-compare/<seed>/<root>/<leaf index>/<record path>`.  Per leaf: the three boxes
[0,e], [0,1], [e-1,e], then `--boxes` boxes in rotation: uniform (two distinct uniform ticks),
narrow (log-uniform width), and kink boxes placed around a feature value in ticks (a bin
feature, v_first or v2 inside [0,e]).

  python3 computations/graded/two_test_compare.py --workers 16

writes `computations/graded/two_test_compare_<L>.json` (about 2.5 minutes with 16 workers; the
replays of roots 1218 and 1219 take about two minutes each).  `--roots` restricts to listed roots
(then no report is written unless `--out` is given).  Assertions must be enabled.
"""
import sys, os, re, json, gzip, time, argparse, ast, random, math, hashlib, traceback
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1'); os.environ.setdefault('OMP_NUM_THREADS', '1')
if not __debug__:
    raise RuntimeError('assertions must be enabled')
from fractions import Fraction as Q
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(HERE))
S = 10**16
TS = 10**6
OLD_RE = re.compile(r'"kind"\s*:\s*"old"')


# ------------------------------------------------------------------ corpus scan
def _walk(rec, path, out):
    """Leaf records (with `rows`) under a corpus entry, with their position in the record."""
    if 'rows' in rec:
        out.append((path, rec))
        return
    for key in ('children', 'mu_split', 'dz_split'):
        for j, c in enumerate(rec.get(key, [])):
            _walk(c, path+[[key, j]], out)


def scan_corpus(corpus):
    """Every leaf record with a row of kind 'old', in the three corpora."""
    found, census = [], {}
    for key in ('inside', 'nodes', 'outside'):
        fn = corpus/f'{key}.jsonl.gz'
        roots = leaves = 0
        with gzip.open(fn, 'rt') as f:
            for line in f:
                roots += 1
                if not OLD_RE.search(line):
                    continue
                d = json.loads(line)
                for lf in d['leaves']:
                    out = []
                    _walk(lf, [], out)
                    for path, rec in out:
                        kinds = [r['kind'] for r in rec['rows']]
                        if 'old' in kinds:
                            leaves += 1
                            found.append(dict(corpus=key, root=d['id'], index=lf['index'], record_path=path,
                                              kinds=kinds, boxes=rec['boxes'], maximum=rec['maximum']))
        census[key] = dict(roots=roots, leaves_with_old_row=leaves)
    return found, census


def sha256(fn):
    h = hashlib.sha256()
    with open(fn, 'rb') as f:
        for chunk in iter(lambda: f.read(1 << 22), b''):
            h.update(chunk)
    return h.hexdigest()


# ------------------------------------------------------------------ exact evaluation of the code
class Dual:
    """a + b*eps with eps^2 = 0 and exact rational parts: value and derivative at one point."""
    __slots__ = ('v', 'd')

    def __init__(self, v, d=0):
        self.v, self.d = Q(v), Q(d)

    @staticmethod
    def lift(o):
        return o if isinstance(o, Dual) else Dual(o, 0)

    def __add__(self, o):
        o = Dual.lift(o); return Dual(self.v+o.v, self.d+o.d)
    __radd__ = __add__

    def __sub__(self, o):
        o = Dual.lift(o); return Dual(self.v-o.v, self.d-o.d)

    def __rsub__(self, o):
        return Dual.lift(o)-self

    def __neg__(self):
        return Dual(-self.v, -self.d)

    def __mul__(self, o):
        o = Dual.lift(o); return Dual(self.v*o.v, self.v*o.d+self.d*o.v)
    __rmul__ = __mul__

    def __truediv__(self, o):
        o = Dual.lift(o)
        return Dual(self.v/o.v, (self.d*o.v-self.v*o.d)/(o.v*o.v))

    def __rtruediv__(self, o):
        return Dual.lift(o)/self

    def __pow__(self, k):
        assert type(k) is int and k >= 0
        out = Dual(1)
        for _ in range(k):
            out = out*self
        return out

    def _cmp(self, o):
        return (self.v > Dual.lift(o).v)-(self.v < Dual.lift(o).v)

    def __lt__(self, o): return self._cmp(o) < 0
    def __le__(self, o): return self._cmp(o) <= 0
    def __gt__(self, o): return self._cmp(o) > 0
    def __ge__(self, o): return self._cmp(o) >= 0

    def __eq__(self, o):
        raise TypeError('equality of dual numbers is not used')

    __hash__ = None


def _xdiv(x, y):
    """Exact division, replacing `x // y` and the ceilings `ceildiv(x, y)`."""
    if isinstance(x, Dual) or isinstance(y, Dual):
        return Dual.lift(x)/y
    return Q(x)/Q(y)


def _ident(x):
    return x


ROUNDING_CALLS = {'ceildiv': '_xdiv', 'ceil_q': '_ident'}
FORBIDDEN_CALLS = {'int', 'round', 'floor', 'ceil', 'isqrt', 'ceil_fraction', 'floor_fraction', 'trunc'}


class ExactDivision(ast.NodeTransformer):
    """Replace every `x // y` by `_xdiv(x, y)`, `ceildiv(x, y)` by `_xdiv(x, y)` and `ceil_q(x)` by x."""
    def __init__(self):
        self.replaced = {'//': 0, 'ceildiv': 0, 'ceil_q': 0}

    def visit_BinOp(self, node):
        self.generic_visit(node)
        if isinstance(node.op, ast.FloorDiv):
            self.replaced['//'] += 1
            return ast.copy_location(ast.Call(func=ast.Name('_xdiv', ast.Load()), args=[node.left, node.right],
                                              keywords=[]), node)
        return node

    def visit_AugAssign(self, node):
        self.generic_visit(node)
        assert not isinstance(node.op, ast.FloorDiv), 'augmented floor division'
        return node

    def visit_Call(self, node):
        self.generic_visit(node)
        if isinstance(node.func, ast.Name) and node.func.id in ROUNDING_CALLS:
            self.replaced[node.func.id] += 1
            node.func = ast.Name(ROUNDING_CALLS[node.func.id], ast.Load())
        return node


def _called_names(tree):
    out = set()
    for n in ast.walk(tree):
        if isinstance(n, ast.Call):
            f = n.func
            out.add(f.id if isinstance(f, ast.Name) else f.attr if isinstance(f, ast.Attribute) else '?')
    return out


def function_def(module, name, cls=None):
    """The FunctionDef of `name` (in class `cls`) parsed from the module's committed source file,
    so that monkeypatching (the replay's hooks) cannot change what is evaluated."""
    tree = ast.parse(Path(module.__file__).read_text())
    body = tree.body
    if cls is not None:
        body = [n for n in body if isinstance(n, ast.ClassDef) and n.name == cls]
        assert len(body) == 1, (module.__name__, cls)
        body = body[0].body
    fns = [n for n in body if isinstance(n, ast.FunctionDef) and n.name == name]
    assert len(fns) == 1, (module.__name__, cls, name)
    return fns[0]


def compile_function(fdef, glb, exact, overrides=None, label=''):
    """Compile a FunctionDef in the module globals `glb`, optionally with exact division.
    Returns (function, rewrite counts, source text)."""
    mod = ast.Module(body=[fdef], type_ignores=[])
    mod = ast.parse(ast.unparse(mod))          # a fresh copy of the nodes
    counts = None
    if exact:
        tr = ExactDivision()
        mod = tr.visit(mod)
        counts = tr.replaced
        left = _called_names(mod) & (FORBIDDEN_CALLS | set(ROUNDING_CALLS))
        assert not left, ('rounding call left in exact code', label, left)
        assert not any(isinstance(n, ast.BinOp) and isinstance(n.op, ast.FloorDiv) for n in ast.walk(mod))
    ast.fix_missing_locations(mod)
    ns = dict(glb)
    ns.update(_xdiv=_xdiv, _ident=_ident)
    ns.update(overrides or {})
    exec(compile(mod, f'<{"exact" if exact else "integer"} {label}>', 'exec'), ns)
    return ns[fdef.name], counts, ast.unparse(mod)


def scenario_constraint_def(VP):
    """A function (inp, a, b) -> (costs, B) made of the constraint statements of
    verify_progress.scenario: its reads of the row data, the per-branch statements defining
    sh, f1, f2, de, nu, B, and the per-column cost statement, unchanged."""
    fn = function_def(VP, 'scenario')
    want_pro = {'rows', 'd', 'D', 'Df', 'ss', 'n', 'n2'}
    pro, found = [], set()
    for st in fn.body:
        if isinstance(st, ast.Assign):
            names = {n.id for t in st.targets for n in ast.walk(t) if isinstance(n, ast.Name)}
            if names <= want_pro:
                pro.append(st); found |= names
    assert found == want_pro, found
    loops = [st for st in fn.body if isinstance(st, ast.For) and ast.unparse(st.iter) == "rec['certificate']['branches']"]
    assert len(loops) == 1
    body = []
    for st in loops[0].body:
        if (isinstance(st, ast.Assign) and len(st.targets) == 1 and isinstance(st.targets[0], ast.Name)
                and st.targets[0].id in ('sh', 'f1', 'f2', 'de', 'nu', 'B')):
            body.append(st)
    assert [st.targets[0].id for st in body] == ['sh', 'f1', 'f2', 'de', 'nu', 'B'], [ast.unparse(s) for s in body]
    inner = [st for st in loops[0].body if isinstance(st, ast.For) and ast.unparse(st.target) in ('row, count', '(row, count)')]
    assert len(inner) == 1
    cost = [st for st in inner[0].body if isinstance(st, ast.Assign) and ast.unparse(st.targets[0]) == 'cost']
    assert len(cost) == 1
    lines = ['def scenario_constraint(inp, a, b):']
    lines += ['    '+ast.unparse(st) for st in pro+body]
    lines += ['    _costs = []', '    for row in rows:', '        '+ast.unparse(cost[0]),
              '        _costs.append(cost)', '    return (_costs, B)']
    return ast.parse('\n'.join(lines)).body[0]


# ------------------------------------------------------------------ worker state and hooks
W = {}


def init_worker(L, corpus):
    for p in (ROOT/'frontier', ROOT/'core'/'code', ROOT/'near'/'code', HERE):
        if str(p) not in sys.path:
            sys.path.insert(0, str(p))
    import graded_cert as CT
    import build_progress as BP
    import verify_progress as VP
    # the implementations' own code, parsed from the committed files before any hook is installed
    rc = function_def(CT, '_row_case', cls='Leaf')
    tc = function_def(CT, 'tangent_cost')
    tc_exact, c_tc, _ = compile_function(tc, vars(CT), True, label='graded_cert.tangent_cost')
    W['graded_exact'], c_rc, _ = compile_function(rc, vars(CT), True, dict(tangent_cost=tc_exact),
                                                  label='graded_cert.Leaf._row_case')
    nr = function_def(BP, 'near')
    W['near_exact'], c_nr, _ = compile_function(nr, vars(BP), True, label='build_progress.near')
    W['near_int'] = BP.near
    sc = scenario_constraint_def(VP)
    W['scen_int'], _, W['scen_src'] = compile_function(sc, vars(VP), False, label='verify_progress.scenario')
    W['scen_exact'], c_sc, _ = compile_function(sc, vars(VP), True, label='verify_progress.scenario')
    W['rewrites'] = {'graded_cert.Leaf._row_case': c_rc, 'graded_cert.tangent_cost': c_tc,
                     'build_progress.near': c_nr, 'verify_progress.scenario (constraint statements)': c_sc}
    # the replay, with hooks recording each leaf's specs, 4.30 source input and refinement path
    import graded_verify as GV
    sources = dict(inside=corpus/'inside.jsonl.gz', nodes=corpus/'nodes.jsonl.gz')
    GV.setup('inside', L, sources)
    import graded_leaves as LV
    import graded_driver as DR
    W.update(GV=GV, CT=CT, LV=LV, DR=DR, L=L, cap=[], cur={})
    orig_vt = CT.verify_tree

    def verify_tree(leaf, node, box=None):
        out = orig_vt(leaf, node, box)
        if box is None:
            W['cap'].append((leaf, node, out))
        return out
    CT.verify_tree = verify_tree
    orig_leaf = LV.leaf

    def leaf(inp, specs, outside):
        lf = orig_leaf(inp, specs, outside)
        cur = W['cur']
        lf._specs, lf._outside = specs, outside
        lf._src, lf._index, lf._path = cur.get('src'), cur.get('index'), cur.get('path')
        return lf
    LV.leaf = leaf
    orig_ii = LV.inside_input

    def inside_input(src, L_, path=()):
        out = orig_ii(src, L_, path)
        W['cur'].update(path=[list(p) for p in path])
        return out
    LV.inside_input = inside_input
    orig_vl = DR.verify_leaf

    def verify_leaf(src, L_, rec, outside=False, prefix=()):
        if not prefix:
            W['cur'].update(src=src, index=rec.get('index'), path=[])
        return orig_vl(src, L_, rec, outside, prefix)
    DR.verify_leaf = verify_leaf


# ------------------------------------------------------------------ the 4.30 input of a leaf's case
def input_430(lf):
    """The 4.30 pipeline's input for the leaf's case: the 4.30 record's own input (the replay's
    capture) for an unrefined leaf, else the 4.30 builder `make_endgame` at the record's L on the
    refined case."""
    src, path = lf._src, lf._path
    if not path:
        return src, 'the 4.30 record input'
    import endgame as EG
    LV = W['LV']
    sp = LV.apply_path(LV.LD.spec_of(src), [tuple(p) for p in path])
    inp = EG.make_endgame(sp, src['L'], EG.parse_params(src), src['lambda_den'])
    assert inp is not None
    return inp, f"make_endgame at L={src['L']} on the refined case"


# ------------------------------------------------------------------ step 3: the row's integers
def builder_caches():
    import two_test_enclosures as TT, extension_enclosures as EE, published_single_inputs as PS
    return [TT.norm_bounds, TT.test, TT.cb, TT.norm, TT.feat, TT.constants, PS.single_rows,
            EE.vector_transform, EE.correlation_bound, EE.paired_first, EE.mixnorm, EE.mixfeature, EE.mixrows]


def clear_builder_caches():
    """Empty the memo of every 4.30 enclosure routine, so that the values are recomputed."""
    for f in builder_caches():
        f.cache_clear()


def builder_calls():
    """Number of evaluations (cache misses) of each enclosure routine since the caches were emptied."""
    return {f'{f.__module__}.{f.__name__}': f.cache_info().misses for f in builder_caches() if f.cache_info().misses}


def _same(x, y):
    """Equality of spec fields, rational strings compared as rationals."""
    if isinstance(x, dict) and isinstance(y, dict):
        return set(x) == set(y) and all(_same(x[k], y[k]) for k in x)
    if isinstance(x, str) and isinstance(y, str) and x != y:
        try:
            return Q(x) == Q(y)
        except ValueError:
            return False
    return x == y


def regenerate_data(lf, inp430, row):
    """Recompute the two-test data of the leaf from the 4.30 enclosure routines (fresh caches) and
    compare with the leaf input, the row and the 4.30 input.  Returns (report, failures, want)."""
    import endgame as EG, two_test_enclosures as TT, extension_enclosures as EE
    from config_v4 import ETA
    LV = W['LV']
    inp, src, path = lf.inp, lf._src, lf._path
    fails = []

    def check(name, ok, detail=None):
        if not ok:
            fails.append(dict(check=name, detail=detail))
    spec = LV.apply_path(LV.LD.spec_of(src), [tuple(p) for p in path])
    red, _ = EG.reduced_spec(spec)
    c = red['case']
    for k in ('case', 'gap'):
        check(f'regenerated {k} equals the leaf input', _same(red.get(k), inp.get(k)), [red.get(k), inp.get(k)])
    check('regenerated ordinary_lower equals the leaf input', Q(red['ordinary_lower']) == Q(inp['ordinary_lower']))
    check('reserved family range', (red['second'] is None) == (inp['second'] is None) and
          (red['second'] is None or all(Q(red['second'][k]) == Q(inp['second'][k]) for k in ('lo', 'hi', 'n'))))
    kind = c['kind']
    a, b, p = Q(c['lo']), Q(c['hi']), Q(c['lp'])
    gap = red.get('gap')
    if gap:
        p = Q(gap['lo'])
    s = min(Q('1.9'), p, Q(c['source_l2']))
    check('shift s = min(1.9, p*, source l2) is the leaf shift', s == Q(inp['shift']), [str(s), inp['shift']])
    par = EG.parse_params(src)
    check('parameters are the 4.30 record parameters', par == EG.parse_params(inp), [par, EG.parse_params(inp)])
    gG, gZ, t, zeta, variant = Q(par['gg']), Q(par['gz']), Q(par['mix']), Q(par['zeta']), par['method']
    n = 2 if kind == 'complex' else 1
    clear_builder_caches()
    t0 = time.time()
    d, D, Df, _ = TT.constants(a, gG, gZ, s, kind)
    pair = None
    if variant == 'single':
        vf = TT.feat(gG, gZ, s, b, kind != 'complex', kind == 'rc', a)
        def fe(h, real=False): return TT.feat(gG, gZ, s, h, real)
    elif variant == 'mixture':
        vf = EE.mixfeature(gG, gZ, s, t, b, kind != 'complex', kind == 'rc', a)
        def fe(h, real=False): return EE.mixfeature(gG, gZ, s, t, h, real)
    else:
        assert variant == 'pair', variant
        if kind == 'rc':
            pa, ph = a, b
        else:
            check('paired variant: finite gap', bool(gap) and gap['hi'] != 'infinity', gap)
            pa, ph = Q(gap['lo']), Q(gap['hi'])
        vf, Df, pf = EE.paired_first(gG, gZ, s, a, b, pa, ph, kind, zeta)
        def fe(h, real=False): return TT.feat(gG, gZ, s, h, real)
        # the side condition of prop:paired, 2D' >= zeta_* max(m', 0), zeta_* = (1+eta) zeta/2
        margin = 2*Q(Df, S)-(1+ETA)*zeta/2*max(Q(vf, S), Q(0))
        check('paired: 2D\' >= zeta_* max(m\',0)', margin >= 0 and Df > 0, str(margin))
        check('paired: stored margin is the recomputed one', Q(inp['pair_proof']['monotonicity_margin']) == margin)
        check('paired: B >= 0', pf['bound'] >= 0 and inp['pair_proof']['bound'] == pf['bound'])
        check('paired: first character nonreal', kind == 'complex', kind)
        pair = dict(margin=str(margin), margin_float=float(margin), B=pf['bound'], B_float=pf['bound']/S,
                    e=pf['e'], zeta=str(zeta), lambda_prime=[str(pa), str(ph)])
    sec = inp['second']
    want = dict(d=d, D=D, Df=Df, v_first=vf, n=n,
                features={(r[0], r[1]): (-S if r[1] == 'infinity' else fe(Q(r[1]))) for r in inp['rows']},
                second=None if not sec else dict(n=sec['n'], hi=Q(sec['hi']), v=fe(Q(sec['hi']), int(sec['n']) == 1)))
    fails += data_failures(inp, inp430, row, want)
    # the bins with their features as the 4.30 row builder lays them out (published_single_inputs.
    # single_rows on [ordinary_lower, max(3, ordinary_lower)] with grid 1/lambda_den, and the tail;
    # extension_enclosures.mixrows for the mixture): every column of the leaf is one of them
    import published_single_inputs as PS
    r0 = Q(red['ordinary_lower'])
    built = (EE.mixrows(r0, gG, gZ, s, t, inp['L'], inp['lambda_den']) if variant == 'mixture'
             else PS.single_rows(r0, gG, gZ, s, inp['L'], inp['lambda_den']))
    built = {(x[0], x[1]): x[4] for x in built}
    for i, r in enumerate(inp['rows']):
        check('column is a bin of the 4.30 row builder, with its feature', built.get((r[0], r[1])) == r[4],
              [i, r[0], r[1]])
    v2 = want['second']['v'] if sec else None
    negative = [i for i, r in enumerate(inp['rows']) if r[4] < 0 and r[1] != 'infinity']
    rep = dict(recomputed_by=builder_calls(), seconds=round(time.time()-t0, 1),
               bins=sum(1 for r in inp['rows'] if r[1] != 'infinity'),
               fields=['d', 'D', 'Df', 'v_first', 'rows[i][4]', 'second.v'] if sec else ['d', 'D', 'Df', 'v_first', 'rows[i][4]'],
               clamped=dict(negative_bin_features=len(negative), tail_feature=-S, v_first_negative=vf < 0,
                            v2_negative=None if v2 is None else v2 < 0),
               shift=str(s), gamma_G=str(gG), gamma_Z=str(gZ), mix=str(t), zeta=str(zeta))
    if pair:
        rep['paired'] = pair
    return rep, fails, want


def data_failures(inp, inp430, row, want):
    """Compare the regenerated two-test data `want` with the leaf input, the 4.30 input and the row."""
    fails = []

    def check(name, ok, detail=None):
        if not ok:
            fails.append(dict(check=name, detail=detail))
    for k in ('d', 'D', 'Df', 'v_first', 'n'):
        check(f'{k}: leaf input equals the regenerated value', inp[k] == want[k], [inp[k], want[k]])
        check(f'{k}: 4.30 input equals the regenerated value', inp430[k] == want[k], [inp430[k], want[k]])
    # bin features at the right ends; the tail has -S
    rows430 = {(r[0], r[1]): r for r in inp430['rows']}
    check('row has one feature per ordinary column', len(row['v']) == len(inp['rows']))
    for i, r in enumerate(inp['rows']):
        w = want['features'][(r[0], r[1])]
        check('bin feature equals the regenerated value', r[4] == w, [i, r[0], r[1], r[4], w])
        r4 = rows430.get((r[0], r[1]))
        check('bin present in the 4.30 input with the same feature', r4 is not None and r4[4] == w, [i, r[0], r[1]])
        check('row feature is the clamped regenerated feature', i < len(row['v']) and row['v'][i] == max(0, w), i)
    sec, ws = inp['second'], want['second']
    if ws:
        check('v2 equals the regenerated value at hi2', sec['v'] == ws['v'], [sec['v'], ws['v']])
        s4 = inp430['second']
        check('v2 in the 4.30 input', s4 is not None and s4['v'] == ws['v'] and s4['n'] == ws['n'] and Q(s4['hi']) == ws['hi'])
    else:
        check('no reserved family', not sec and inp430['second'] is None)
    # the row is old_row of the input: the first family (n, v_f, Df), the second (n2, v2), clamped
    fam = [(want['n'], max(0, want['v_first']), want['Df'])] + ([(int(ws['n']), max(0, ws['v']))] if ws else [])
    check('row d, D', row['d'] == want['d'] and row['D'] == want['D'], [row['d'], row['D']])
    check('row family terms', [tuple(x) for x in row['fam']] == fam, [row['fam'], fam])
    check('row has no other fields', set(row) == {'d', 'D', 'v', 'fam'}, sorted(row))
    return fails


# ------------------------------------------------------------------ step 2: box by box
def paper_relaxation(inp, a, b, c):
    """The paper's threshold form of the two-test row (paper §9.6, display after prop:paired),
    relaxed on tau in [a/TS, b/TS] as graded_cert does: case 2 costs at tau_b, budget with tau_a^2
    and the fixed terms at tau_b; tangent case 0 (1) the tangent at the centre m taken at a (b).
    Real units.  Features: V_i = rows[i][4], v_f, v2; negative features, the tail and the reserved
    columns give 0 (they enter through (v - tau)_+ with tau >= 0)."""
    d, D, Df = Q(inp['d'], S), Q(inp['D'], S), Q(inp['Df'], S)
    cols = [(Q(r[4], S), D) for r in inp['rows']] + [(Q(0), D)]*len(inp.get('second_cols') or [])
    fam = [(int(inp['n']), Q(inp['v_first'], S), Df)]
    if inp['second']:
        fam.append((int(inp['second']['n']), Q(inp['second']['v'], S), D))
    if c == 2:
        ta, tb = Q(a, TS), Q(b, TS)
        def g(v, Dd): return max(v-tb, Q(0))**2/Dd
        rhs = 1-ta*ta/d
    else:
        m, h, sg = Q(a+b, 2*TS), Q(b-a, 2*TS), (1 if c == 0 else -1)
        def g(v, Dd):
            x = max(v-m, Q(0))
            return (x*x+2*sg*h*x)/Dd
        rhs = 1-(m*m-2*sg*h*m)/d
    return [g(v, Dd) for v, Dd in cols], rhs-sum(n*g(v, Dd) for n, v, Dd in fam)


def ref_430(inp430, a, b, c, ad=None):
    """Exact 4.30 costs and budget (S-scaled, not divided by D) of the relaxation case, from the
    exact evaluation of build_progress.near and of scenario's statements.  Returns
    (near_costs, near_B, scen_costs, scen_B)."""
    if c == 2:
        C1, B1 = W['near_exact'](inp430, a, b)
        C2, B2 = W['scen_exact'](inp430, a, b)
        return [Q(x) for x in C1], Q(B1), [Q(x) for x in C2], Q(B2)
    (C1, B1), (C2, B2) = ad
    h = Q(b-a, 2)
    sg = 1 if c == 0 else -1

    def tan(x):
        x = Dual.lift(x)
        return x.v-sg*h*x.d
    return [tan(x) for x in C1], tan(B1), [tan(x) for x in C2], tan(B2)


def ad_430(inp430, a, b):
    m = Dual(Q(a+b, 2), 1)
    return W['near_exact'](inp430, m, m), W['scen_exact'](inp430, m, m)


class Stats:
    def __init__(self):
        self.cases = {0: 0, 1: 0, 2: 0}
        self.columns = 0
        self.gap = {k: Q(0) for k in ('cost_first', 'budget_first', 'cost_tangent', 'budget_tangent',
                                      'cost_first_430', 'budget_first_430')}
        self.fails = []

    def fail(self, what, **kw):
        if len(self.fails) < 20:
            self.fails.append(dict(check=what, **kw))
        else:
            self.fails[-1]['more'] = self.fails[-1].get('more', 0)+1

    def gapmax(self, k, v):
        if v > self.gap[k]:
            self.gap[k] = v


def compare_box(lf, k, inp430, colmap, a, b, st):
    """All three relaxation cases of the two-test row k on the threshold interval [a, b].  The 4.30
    constraint is divided by its own D (that of the 4.30 input)."""
    D = inp430['D']
    nO, nS = lf.nO, lf.nS
    ad = ad_430(inp430, a, b)
    for c in (2, 0, 1):
        st.cases[c] += 1
        gi_costs, gi_B = lf.row_case(k, a, b, c)                       # the integers used
        ge_costs, ge_B = W['graded_exact'](lf, k, a, b, c)             # the same code, exact
        ge_costs = [Q(x) for x in ge_costs]; ge_B = Q(ge_B)
        nc, nB, sc, sB = ref_430(inp430, a, b, c, ad)
        pc, pB = paper_relaxation(lf.inp, a, b, c)
        tag = dict(a=a, b=b, case=c)
        if len(gi_costs) != nO+nS or len(ge_costs) != nO+nS:
            st.fail('column count', **tag); continue
        if nc != sc or nB != sB:
            st.fail('build_progress.near and verify_progress.scenario differ (exact)', **tag)
        # graded = 4.30 / D (S-scaled on both sides: graded = 4.30 * S / D)
        for i in range(nO):
            j = colmap[i]
            if ge_costs[i] != nc[j]*S/D:
                st.fail('graded cost != 4.30 cost * S/D', column=i, **tag)
            if ge_costs[i] != pc[i]*S:
                st.fail('graded cost != paper cost', column=i, **tag)
        for i in range(nO, nO+nS):
            if ge_costs[i] != 0 or gi_costs[i] != 0 or pc[i] != 0:
                st.fail('second-family column has a cost in the two-test row', column=i, **tag)
        if ge_B != nB*S/D:
            st.fail('graded budget != 4.30 budget * S/D', graded=str(ge_B), ref=str(nB*S/D), **tag)
        if ge_B != pB*S:
            st.fail('graded budget != paper budget', **tag)
        st.columns += nO+nS
        # safe rounding of the integers used: costs down, budget up
        kind = 'first' if c == 2 else 'tangent'
        for i in range(nO+nS):
            if type(gi_costs[i]) is not int:
                st.fail('cost not an integer', column=i, **tag)
            g = ge_costs[i]-gi_costs[i]
            if g < 0:
                st.fail('cost rounded up', column=i, gap=str(g), **tag)
            st.gapmax('cost_'+kind, g)
        g = gi_B-ge_B
        if type(gi_B) is not int or g < 0:
            st.fail('budget rounded down', gap=str(g), **tag)
        st.gapmax('budget_'+kind, g)
        if c == 2:
            # the 4.30 integers: builder and checker agree, and are rounded safely
            C_int, B_int = W['near_int'](inp430, a, b)
            C_s, B_s = W['scen_int'](inp430, a, b)
            if C_int != C_s or B_int != B_s:
                st.fail('build_progress.near and verify_progress.scenario integers differ', **tag)
            for j, x in enumerate(C_int):
                if x > nc[j]:
                    st.fail('4.30 cost rounded up', column=j, **tag)
                st.gapmax('cost_first_430', nc[j]-x)
            if B_int < nB:
                st.fail('4.30 budget rounded down', **tag)
            st.gapmax('budget_first_430', B_int-nB)
            # and the graded first-order integers are exactly the floors of the exact costs
            for i in range(nO+nS):
                if gi_costs[i] != math.floor(ge_costs[i]):
                    st.fail('graded first-order cost is not the floor of the exact cost', column=i, **tag)


def cert_intervals(tree, ends, k):
    """{(a, b): orders} over the terminal boxes of a certificate tree, in dimension k."""
    out, n, uses = {}, 0, {1: 0, 2: 0}
    stack = [(tree, [(0, e) for e in ends])]
    while stack:
        node, box = stack.pop()
        if 'split' in node:
            j, mid = node['split'], node['mid']
            lo, hi = box[j]
            left = list(box); left[j] = (lo, mid)
            right = list(box); right[j] = (mid, hi)
            stack.append((node['children'][0], left)); stack.append((node['children'][1], right))
            continue
        n += 1
        o = node['orders'][k]
        uses[o] += 1
        out.setdefault(box[k], set()).add(o)
    return out, n, uses


def random_boxes(rng, e, targets, nbox):
    """[0,e], [0,1], [e-1,e], then nbox boxes: uniform, narrow (log-uniform width), kink."""
    boxes = [('edge', 0, e), ('edge', 0, 1), ('edge', e-1, e)]
    for j in range(nbox):
        t = ('uniform', 'narrow', 'kink')[j % 3]
        if t == 'kink' and not targets:
            t = 'uniform'
        if t == 'uniform':
            a, b = sorted(rng.sample(range(e+1), 2))
        elif t == 'narrow':
            w = max(1, min(e, int(math.exp(rng.uniform(0, math.log(e))))))
            a = rng.randint(0, e-w); b = a+w
        else:
            v = rng.choice(targets)+rng.randint(-2, 2)
            w = rng.choice([1, 2, 3, rng.randint(1, 200), rng.randint(1, 20000)])
            a = v-rng.randint(0, w); b = a+w
            a = min(max(a, 0), e-1); b = min(max(b, a+1), e)
        assert 0 <= a < b <= e
        boxes.append((t, a, b))
    return boxes


def compare_leaf(lf, tree, cfg):
    specs = lf._specs
    kinds = [sp['kind'] for sp in specs]
    k = kinds.index('old')
    inp = lf.inp
    row = lf.rows[k]
    LV = W['LV']
    res = dict(root=None, index=lf._index, refinement_path=lf._path, row_kinds=kinds, old_row=k,
               variant=inp['extension']['variant'], type=inp['case']['kind'], case=dict(inp['case']),
               gap=inp.get('gap'), second=None if not inp['second'] else {x: inp['second'][x] for x in ('lo', 'hi', 'n')},
               lambda_den=inp['lambda_den'], columns=dict(ordinary=lf.nO, second=lf.nS, hidden=lf.nH),
               end=lf.ends[k], d=row['d'], D=row['D'])
    fails = []
    if kinds.count('old') != 1 or k != len(kinds)-1 or specs[k] != dict(kind='old', parameters={}):
        fails.append(dict(check='one old row, last, without parameters', detail=kinds))
    if row != LV.old_row(inp):
        fails.append(dict(check='the leaf row is graded_leaves.old_row(input)'))
    # the certificate's threshold range [0, e/TS] of the row covers [0, sqrt(d)] (thm:twotest, prop:threshold)
    e = lf.ends[k]
    if not (e*e*S >= row['d']*TS*TS and e > 0):
        fails.append(dict(check='threshold range covers [0, sqrt d]', detail=[e, row['d']]))
    inp430, how = input_430(lf)
    res['input_430'] = how
    # the 4.30 record's own input (the replay's capture): the two-test data do not depend on L or on
    # the second-family refinements, so they must agree on d, D, Df, v_first and every common bin
    src = lf._src
    srows = {(x[0], x[1]): x for x in src['rows']}
    common = [(r, srows[(r[0], r[1])]) for r in inp['rows'] if (r[0], r[1]) in srows]
    agree = (all(inp[x] == src[x] for x in ('d', 'D', 'Df', 'v_first', 'n')) and
             all(r[4] == s4[4] for r, s4 in common))
    res['record_430'] = dict(L=src['L'], refined=bool(lf._path), columns=len(inp['rows']), record_rows=len(src['rows']),
                             common_bins=len(common), agree=agree)
    if not agree or (not lf._path and len(common) != len(inp['rows'])):
        fails.append(dict(check='two-test data equal those of the 4.30 record input', detail=res['record_430']))
    # step 3: data
    t0 = time.time()
    rep, f3, want = regenerate_data(lf, inp430, row)
    res['data'] = rep
    fails += f3
    # column map: graded ordinary column -> 4.30 row with the same bin
    idx430 = {(r[0], r[1]): j for j, r in enumerate(inp430['rows'])}
    colmap = [idx430.get((r[0], r[1])) for r in inp['rows']]
    if any(j is None for j in colmap):
        fails.append(dict(check='every graded bin is a bin of the 4.30 input'))
        res.update(status='FAIL', failures=fails)
        return res
    res['rows_430'] = len(inp430['rows'])
    # step 2: boxes
    ivs, nbox, uses = cert_intervals(tree, lf.ends, k)
    st_cert = Stats()
    for (a, b) in sorted(ivs):
        compare_box(lf, k, inp430, colmap, a, b, st_cert)
    seed = f"two-test-compare/{cfg['seed']}/{lf._root}/{lf._index}/{json.dumps(lf._record_path)}"
    rng = random.Random(seed)
    targets = sorted({x for x in [inp['v_first'], (inp['second'] or {}).get('v', -1)]+[r[4] for r in inp['rows']]
                      if 0 <= x*TS//S <= lf.ends[k]})
    targets = [x*TS//S for x in targets]
    boxes = random_boxes(rng, lf.ends[k], targets, cfg['boxes'])
    st_rand = Stats()
    for _, a, b in boxes:
        compare_box(lf, k, inp430, colmap, a, b, st_rand)
    res['certificate_boxes'] = dict(terminal_boxes=nbox, distinct_intervals=len(ivs),
                                    uses=dict(first_order=uses[2], tangent=uses[1]),
                                    cases_compared=st_cert.cases, column_comparisons=st_cert.columns)
    res['random_boxes'] = dict(seed=seed, boxes=len(boxes),
                               by_type={t: sum(1 for x in boxes if x[0] == t) for t in ('edge', 'uniform', 'narrow', 'kink')},
                               cases_compared=st_rand.cases, column_comparisons=st_rand.columns)
    gaps = {}
    for key in st_cert.gap:
        g = max(st_cert.gap[key], st_rand.gap[key])
        gaps[key] = dict(units_of_1_over_S=float(g), exact=str(g))
    res['max_rounding_gaps'] = gaps
    fails += [dict(where='certificate boxes', **f) for f in st_cert.fails]
    fails += [dict(where='random boxes', **f) for f in st_rand.fails]
    # negative test: every unit perturbation of the row or of the data must be detected
    res['negative_test'] = negative_test(lf, k, inp430, colmap, row, want, sorted(ivs))
    missed = [m for m, v in res['negative_test'].items() if not all(v.values())]
    if missed:
        fails.append(dict(check='negative test: perturbation not detected', detail=missed))
    res['seconds_compare'] = round(time.time()-t0, 1)
    res['failures'] = fails
    res['status'] = 'PASS' if not fails else 'FAIL'
    return res


def negative_test(lf, k, inp430, colmap, row, want, cert_ivs):
    """Perturb the row (as the certificate checker sees it) or the data by one unit (1/S) in either
    direction and report, per perturbation, whether the comparisons above detect it."""
    CT = W['CT']
    inp = lf.inp
    e = lf.ends[k]
    mid = cert_ivs[len(cert_ivs)//2]
    boxes = [(0, 1), (e-1, e), mid]
    i = max(range(lf.nO), key=lambda j: row['v'][j])          # the largest feature: active on every box
    n, vf, Df = row['fam'][0]
    muts = {'row D+1': dict(D=row['D']+1), 'row D-1': dict(D=row['D']-1),
            'row d+1': dict(d=row['d']+1), 'row d-1': dict(d=row['d']-1),
            f'row feature[{i}]+1': dict(v=[x+(j == i) for j, x in enumerate(row['v'])]),
            f'row feature[{i}]-1': dict(v=[x-(j == i) for j, x in enumerate(row['v'])]),
            'row v_first+1': dict(fam=[(n, vf+1, Df)]+row['fam'][1:]),
            'row v_first-1': dict(fam=[(n, vf-1, Df)]+row['fam'][1:]),
            'row Df+1': dict(fam=[(n, vf, Df+1)]+row['fam'][1:]),
            'row Df-1': dict(fam=[(n, vf, Df-1)]+row['fam'][1:]),
            'row n+1': dict(fam=[(n+1, vf, Df)]+row['fam'][1:])}
    if len(row['fam']) > 1:
        n2, v2 = row['fam'][1]
        muts['row v2+1'] = dict(fam=[row['fam'][0], (n2, v2+1)])
        muts['row v2-1'] = dict(fam=[row['fam'][0], (n2, v2-1)])
    out = {}
    for name, ch in muts.items():
        rows = list(lf.rows)
        rows[k] = dict(row, **ch)
        bad = CT.Leaf(inp, rows)
        st = Stats()
        for a, b in boxes:
            compare_box(bad, k, inp430, colmap, a, b, st)
        # detected by the box comparison (graded vs 4.30/D and paper) and by the data comparison
        out[name] = dict(boxes=bool(st.fails), data=bool(data_failures(inp, inp430, rows[k], want)))
    # data: the leaf input, the 4.30 input, or the regenerated value off by one unit
    dmuts = {'input v_first+1': ('inp', 'v_first', 1), 'input Df-1': ('inp', 'Df', -1),
             'input d+1': ('inp', 'd', 1), f'input feature[{i}]+1': ('inp', 'feature', 1),
             '4.30 input D+1': ('inp430', 'D', 1), '4.30 input feature-1': ('inp430', 'feature', -1),
             'regenerated D-1': ('want', 'D', -1), 'regenerated v_first-1': ('want', 'v_first', -1)}
    for name, (which, key, delta) in dmuts.items():
        x, y, w = inp, inp430, want
        if which == 'want':
            w = dict(want); w[key] += delta
        else:
            z = dict(inp if which == 'inp' else inp430)
            if key == 'feature':
                z['rows'] = [list(r) for r in z['rows']]
                j = i if which == 'inp' else colmap[i]
                z['rows'][j][4] += delta
            else:
                z[key] += delta
            x, y = (z, inp430) if which == 'inp' else (inp, z)
        out[name] = dict(data=bool(data_failures(x, y, row, w)))
    return out


def run_root(job):
    root, expected, cfg = job
    t = time.time()
    try:
        W['cap'].clear()
        out = W['GV'].check_root(root)          # replays the root; every certificate is re-checked
        found = []
        for lf, tree, (mx, nb) in W['cap']:
            if not any(sp['kind'] == 'old' for sp in lf._specs):
                continue
            found.append((lf, tree, mx, nb))
        res = []
        if len(found) != len(expected):
            return dict(root=root, error=f'{len(found)} captured leaves with an old row, {len(expected)} in the corpus')
        replay = round(time.time()-t, 1)
        for (lf, tree, mx, nb), ex in zip(found, expected):
            lf._root, lf._record_path = root, ex['record_path']
            r = compare_leaf(lf, tree, cfg)
            r['root'] = root
            r['record_path'] = ex['record_path']
            r['replay'] = dict(maximum=mx, boxes=nb, corpus_maximum=ex['maximum'], corpus_boxes=ex['boxes'])
            if (mx, nb) != (ex['maximum'], ex['boxes']) or lf._index != ex['index']:
                r['failures'].append(dict(check='replayed leaf is the corpus record', detail=[mx, nb, ex]))
                r['status'] = 'FAIL'
            res.append(r)
        return dict(root=root, root_replay=list(out), replay_seconds=replay, leaves=res, seconds=round(time.time()-t, 1),
                    rewrites=W['rewrites'], scenario_constraint=W['scen_src'])
    except Exception as ex:          # reported as a failure of the root
        return dict(root=root, error=repr(ex), trace=traceback.format_exc())


# ------------------------------------------------------------------ main
def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n\n')[0])
    ap.add_argument('--L', default='3.99')
    ap.add_argument('--corpus', default=None, help='corpus directory (default corpora/<L>)')
    ap.add_argument('--workers', type=int, default=16)
    ap.add_argument('--boxes', type=int, default=300, help='random boxes per leaf (plus three edge boxes)')
    ap.add_argument('--seed', default='20260930')
    ap.add_argument('--roots', default=None, help='comma-separated roots (partial run)')
    ap.add_argument('--out', default=None)
    a = ap.parse_args()
    corpus = Path(a.corpus).resolve() if a.corpus else HERE/'corpora'/a.L
    t = time.time()
    found, census = scan_corpus(corpus)
    print('scan', json.dumps(census), 'old-row leaves', len(found), 'sec', round(time.time()-t), flush=True)
    assert all(f['corpus'] == 'inside' for f in found), 'an old row outside the inside corpus'
    by_root = {}
    for f in found:
        by_root.setdefault(f['root'], []).append(f)
    roots = sorted(by_root)
    if a.roots:
        want = {int(x) for x in a.roots.split(',')}
        assert want <= set(roots), sorted(want-set(roots))
        roots = [r for r in roots if r in want]
    # the replay of a root with many boxes takes longest: start those first
    roots.sort(key=lambda r: -sum(f['boxes'] for f in by_root[r]))
    cfg = dict(boxes=a.boxes, seed=a.seed)
    jobs = [(r, by_root[r], cfg) for r in roots]
    results = []
    with ProcessPoolExecutor(max_workers=min(a.workers, len(jobs)), initializer=init_worker,
                             initargs=(a.L, corpus)) as ex:
        for r in ex.map(run_root, jobs, chunksize=1):
            results.append(r)
            if 'error' in r:
                print('root', r['root'], 'ERROR', r['error'], flush=True)
                print(r.get('trace', ''), flush=True)
                continue
            for lf in r['leaves']:
                print('root', r['root'], 'leaf', lf['index'], lf['record_path'], lf['variant'], lf['type'],
                      'cert intervals', lf.get('certificate_boxes', {}).get('distinct_intervals'),
                      'random', lf.get('random_boxes', {}).get('boxes'), lf['status'],
                      'replay', r['replay_seconds'], 's, total', r['seconds'], 's', flush=True)
                for f in lf['failures'][:5]:
                    print('   ', f, flush=True)
    results.sort(key=lambda r: r['root'])
    leaves = [lf for r in results if 'error' not in r for lf in r['leaves']]
    errors = [dict(root=r['root'], error=r['error'], trace=r.get('trace')) for r in results if 'error' in r]

    def total(sel, part, key):
        out = {}
        for lf in sel:
            for kk, v in lf[part][key].items():
                out[kk] = out.get(kk, 0)+v
        return out
    variants = {}
    for v in ('single', 'mixture', 'pair'):
        sel = [lf for lf in leaves if lf['variant'] == v]
        cc = total(sel, 'certificate_boxes', 'cases_compared') if sel else {}
        rc = total(sel, 'random_boxes', 'cases_compared') if sel else {}
        variants[v] = dict(leaves=len(sel), roots=sorted({lf['root'] for lf in sel}),
                           types=sorted({lf['type'] for lf in sel}),
                           certificate_terminal_boxes=sum(lf['certificate_boxes']['terminal_boxes'] for lf in sel),
                           certificate_intervals=sum(lf['certificate_boxes']['distinct_intervals'] for lf in sel),
                           random_boxes=sum(lf['random_boxes']['boxes'] for lf in sel),
                           cases_compared={'first_order': cc.get(2, 0)+rc.get(2, 0),
                                           'tangent_0': cc.get(0, 0)+rc.get(0, 0), 'tangent_1': cc.get(1, 0)+rc.get(1, 0)},
                           column_comparisons=sum(lf['certificate_boxes']['column_comparisons']
                                                  + lf['random_boxes']['column_comparisons'] for lf in sel))
    totals = dict(leaves=len(leaves), **{k: sum(variants[v][k] for v in variants) for k in
                  ('certificate_terminal_boxes', 'certificate_intervals', 'random_boxes', 'column_comparisons')},
                  cases_compared={c: sum(variants[v]['cases_compared'][c] for v in variants)
                                  for c in ('first_order', 'tangent_0', 'tangent_1')},
                  certificate_uses=dict(first_order=sum(lf['certificate_boxes']['uses']['first_order'] for lf in leaves),
                                        tangent=sum(lf['certificate_boxes']['uses']['tangent'] for lf in leaves)))
    totals['box_case_pairs'] = sum(totals['cases_compared'].values())
    totals['record_430_agreement'] = dict(leaves=sum(1 for lf in leaves if lf.get('record_430', {}).get('agree')),
                                          common_bins=sum(lf.get('record_430', {}).get('common_bins', 0) for lf in leaves))
    negative = dict(perturbations=sum(len(lf['negative_test']) for lf in leaves),
                    detected=sum(all(v.values()) for lf in leaves for v in lf['negative_test'].values()))
    replay = dict(roots=len(results)-len(errors),
                  leaves_equal_to_corpus=sum(1 for lf in leaves
                                             if (lf['replay']['maximum'], lf['replay']['boxes'])
                                             == (lf['replay']['corpus_maximum'], lf['replay']['corpus_boxes'])),
                  root_maxima={r['root']: r['root_replay'][2] for r in results if 'error' not in r})
    gaps = {}
    for lf in leaves:
        for kk, g in lf['max_rounding_gaps'].items():
            if kk not in gaps or Q(g['exact']) > Q(gaps[kk]['exact']):
                gaps[kk] = dict(g, leaf=[lf['root'], lf['index']])
    for kk in gaps:
        gaps[kk]['real'] = gaps[kk]['units_of_1_over_S']/S
    pairs = [lf['data']['paired'] for lf in leaves if 'paired' in lf['data']]
    claims = dict(
        leaves=len(leaves), roots=len({lf['root'] for lf in leaves}),
        one_old_row_per_leaf=all(lf['row_kinds'].count('old') == 1 for lf in leaves),
        variants={v: variants[v]['leaves'] for v in variants},
        paper_37_31_2_4=(len(leaves) == 37 and len({lf['root'] for lf in leaves}) == 37 and
                         [variants[v]['leaves'] for v in ('single', 'mixture', 'pair')] == [31, 2, 4]),
        paired_all_nonreal_first=all(lf['type'] == 'complex' for lf in leaves if lf['variant'] == 'pair'),
        paired_margins=None if not pairs else [min(p['margin_float'] for p in pairs), max(p['margin_float'] for p in pairs)],
        paired_B_min=None if not pairs else min(p['B_float'] for p in pairs))
    failed = [dict(root=lf['root'], index=lf['index'], failures=lf['failures']) for lf in leaves if lf['status'] != 'PASS']
    partial = a.roots is not None
    ok = not failed and not errors and (partial or claims['paper_37_31_2_4'])
    ok = ok and all(all(v.values()) for lf in leaves for v in lf['negative_test'].values())
    first = next((r for r in results if 'error' not in r), None)
    report = dict(
        L=a.L, corpus=str(corpus.relative_to(ROOT.parent)) if corpus.is_relative_to(ROOT.parent) else str(corpus),
        corpus_sha256={k: sha256(corpus/f'{k}.jsonl.gz') for k in ('inside', 'nodes', 'outside')},
        scan=census, partial=partial,
        compared=dict(
            graded=['graded_leaves.old_row (the row dict)', 'graded_cert.Leaf.row_case (integers used)',
                    'graded_cert.Leaf._row_case and tangent_cost, exact (floor divisions and ceil_q removed)'],
            reference_430=['build_progress.near (integer and exact)',
                           'verify_progress.scenario constraint statements (integer and exact)',
                           'tangent cases: the exact 4.30 code at tau = m + eps (dual numbers), value -+ h*derivative'],
            paper='transcription of the threshold form of paper §9.6 (display after prop:paired)',
            data_430=['two_test_enclosures.constants, feat', 'extension_enclosures.mixfeature, paired_first',
                      'the 4.30 record input (unrefined leaves) or make_endgame at L=4.30 (refined leaves)'],
            rewrites=None if first is None else first['rewrites'],
            scenario_constraint=None if first is None else first['scenario_constraint']),
        sampling=dict(rng='random.Random(str) with the seed string of each leaf (random_boxes.seed)',
                      seed=a.seed, boxes_per_leaf=a.boxes, edge_boxes_per_leaf=3,
                      types='rotation uniform / narrow (log-uniform width) / kink (around a feature value in ticks)',
                      certificate='every distinct interval of the row dimension over the terminal boxes of the '
                                  'stored certificate tree; all three cases on each'),
        claims=claims, variants=variants, totals=totals, max_rounding_gaps=gaps, negative_test=negative,
        replay=replay, leaves=leaves, errors=errors, failures=failed, seconds=round(time.time()-t),
        status='PASS' if ok else 'FAIL')
    out = Path(a.out) if a.out else (None if partial else HERE/f'two_test_compare_{a.L}.json')
    if out is not None:
        out.write_text(json.dumps(report, indent=1, default=str)+'\n')
    summary = {k: report[k] for k in ('L', 'claims', 'totals', 'max_rounding_gaps', 'negative_test', 'seconds',
                                      'status')}
    summary['replay'] = {k: v for k, v in replay.items() if k != 'root_maxima'}
    print(json.dumps(summary, indent=1, default=str))
    if out is not None:
        print('report', out)
    sys.exit(0 if ok else 1)


if __name__ == '__main__':
    main()
