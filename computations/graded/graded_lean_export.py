"""Export graded certificates as Lean data for the verified checker (lean-graded/, GradedNear.Cert).

The chosen roots are replayed with graded_verify's machinery.  Every leaf LP met on the way
(graded_cert.Leaf, with the integer data regenerated from the repository's inputs) and its stored
certificate tree are captured, together with graded_cert's value.  The Lean module written has,
per leaf, a `Leaf`, a `Tree` and the theorem that `checkLeaf` returns that value, proved by kernel
evaluation (`decide +kernel`; no `native_decide`).  With `GradedNear.Cert.certified` this gives the
leaf bound `objective < S` at every feasible point.

  python3 computations/graded/graded_lean_export.py --kind outside --roots 1193,1194 \\
      --out lean-graded/GradedNear/Cert/Samples.lean

With `--jsonl`, every leaf of the chosen roots (or of every root, `--roots all`) is instead streamed
as a JSON line to the Lean program `lean-graded/scripts/CertRun.lean`, which evaluates the verified
checker `GradedNear.Cert.checkLeaf` on it (compiled or interpreted code, not the kernel). Each
value and box count is compared with graded_cert's:

  python3 computations/graded/graded_lean_export.py --kind inside --roots all --jsonl \\
      --workers 6 --out summary_inside.json

The column order is ordinary, hidden, second family, as in graded_cert.check_case.

With `--numerics`, every leaf of the chosen roots is instead written as a JSON line to `--out` (gzip
if it ends in .gz): the metadata from which its numeric data can be recomputed (research/notes/
leaf-data-semantics-2026-09-29.md): per column its interval, objective function and far profile with
the stored G, W, C, NH, E; the components of the far budget F and of `first`.  Names are those of
`--jsonl` (`<root>_<j>`).  computations/graded/leaf_numerics_check.py reproduces every integer:

  python3 computations/graded/graded_lean_export.py --kind outside --roots 1193,1202 --numerics \\
      --workers 2 --out numerics_outside.jsonl.gz

With `--full`, as with `--jsonl`, but each JSON line also carries the leaf's metadata (`"meta"`, the
object `--numerics` writes) and goes to the native program `leafcheck` (lean-graded/
LeafCheckNative.lean, `lake build leafcheck`), which runs the certificate checker and the verified
numeric checker `LeafCheckCore.checkNum` (soundness: `GradedNear.Cert.checkNum_sound`) and prints
`name value boxes num`, `num` being `ok` or `fail:<reason>`.  A leaf passes if its value and box
count equal graded_cert's and `num` is `ok`.  Append `--timing` to the checker command for per-leaf
milliseconds (certificate check, numeric check) in the summary:

  python3 computations/graded/graded_lean_export.py --kind outside --roots 1193,1202 --full \\
      --workers 2 --checker "$PWD/lean-graded/.lake/build/bin/leafcheck --timing" --out summary.json

With `--full --num-only`, the numeric checks only, for leaves whose certificates are checked by another
run (`--jsonl` with certrun): leafcheck gets `--num-only` and no tree, answers
`name skipped skipped num`, and a leaf passes if `num` is `ok` (value and box count are not compared);
the report has `"mode": "numerics-only"`.  The replay still runs: it regenerates every leaf (most of its
time) and graded_cert checks every tree in Python.

  python3 computations/graded/graded_lean_export.py --kind inside --roots all --full --num-only \\
      --workers 2 --checker "$PWD/lean-graded/.lake/build/bin/leafcheck --timing" --out summary.json

With `--rows`, each leaf and the metadata of its near rows go to the native program `rowcheck`
(lean-graded/RowCheckNative.lean, `lake build rowcheck`), which runs the verified near-row checker
`RowCheckCore.checkRows` (soundness: `GradedNear.Row.checkRows_sound`; what an accepted row gives:
`GradedNear.Row.row_threshold`). A row's metadata is its test parameters and sieve heights, and the
semantics `(hi, anc)` of the entry of every column and family term, from the rules of
research/PROOF.md §6.5 (`row_meta`); the inherited two-test row has none, and so do the family terms
that are not single-zero entries (the rc pair, the first family's second zero, the shifted rc term).

  python3 computations/graded/graded_lean_export.py --kind outside --roots all --rows \\
      --workers 6 --checker "$PWD/lean-graded/.lake/build/bin/rowcheck" --out rows_outside.json
"""
import sys, os, json, argparse, time, subprocess, gzip
from fractions import Fraction
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
if not __debug__:
    raise RuntimeError('assertions must be enabled')
import graded_verify as GV
import graded_cert as CT

CAPTURED = []


def capture(orig):
    def verify_tree(leaf, node, box=None):
        out = orig(leaf, node, box)
        if box is None:
            CAPTURED.append((leaf, node, out))
        return out
    return verify_tree


def lean_int(x):
    assert type(x) is int
    return f'({x})' if x < 0 else str(x)


def lean_list(xs):
    return '[' + ', '.join(xs) + ']'


def leaf_data(lf):
    """The Lean `Leaf` fields of a graded_cert.Leaf."""
    nO, nH, nS = lf.nO, lf.nH, lf.nS
    feats, diags = [], []
    for sv in lf.rows:
        vs = list(sv['v']) + list(sv.get('vh', [0]*nH)) + lf._vs(sv)
        Ds = lf._Dv(sv) + lf._Dvh(sv) + lf._Dvs(sv)
        assert len(vs) == len(Ds) == nO+nH+nS
        feats.append(vs); diags.append(Ds)
    G = lf.G + lf.GH + lf.GS
    cols = []
    for i in range(nO+nH+nS):
        cols.append(dict(G=G[i], W=lf._Wall[i], C=lf._cnt_all[i], NH=lf._NH_all[i], E=lf._S_all[i],
                         v=[f[i] for f in feats], D=[D[i] for D in diags]))
    rows = [dict(d=sv['d'], fam=[tuple(t) for t in lf._fam(sv)]) for sv in lf.rows]
    return dict(cols=cols, rows=rows, F=lf.F, ng=lf.ng, n2=lf.n2, first=lf.first, final=lf.final)


def leaf_json(data):
    """The leaf in CertRun's JSON layout."""
    return dict(cols=[[c['G'], c['W'], c['C'], c['NH'], c['E'], c['v'], c['D']] for c in data['cols']],
                rows=[[r['d'], [list(t) for t in r['fam']]] for r in data['rows']],
                F=data['F'], ng=data['ng'], n2=data['n2'], first=data['first'], final=data['final'])


LEAN = {}


def lean_checker():
    """One CertRun process per worker, reading JSON lines."""
    if 'p' not in LEAN:
        # The Lean package: `lean-graded/` here, the repository root in the public repository.
        lg = GV.ROOT.parent/'lean-graded'
        if not (lg/'lakefile.toml').exists():
            lg = GV.ROOT.parent
        cmd = LEAN['cmd']
        LEAN['p'] = subprocess.Popen(cmd, cwd=str(lg), stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                                     text=True, bufsize=1 << 20)
    return LEAN['p']


def init_worker(kind, L, sources, cmd):
    GV.setup(kind, L, sources)
    CT.verify_tree = capture(CT.verify_tree)
    LEAN['cmd'] = cmd


def run_root(job):
    """Replay one root (graded_cert checks every tree) and check each captured leaf in Lean."""
    CAPTURED.clear()
    idx = job if isinstance(job, int) else job['id']
    GV.check_root(job)
    p = lean_checker()
    bad, boxes, mx = [], 0, -1
    for j, (lf, tree, (m, nb)) in enumerate(CAPTURED):
        name = f'{idx}_{j}'
        p.stdin.write(json.dumps(dict(name=name, leaf=leaf_json(leaf_data(lf)), tree=tree),
                                 separators=(',', ':')) + '\n')
        p.stdin.flush()
        out = p.stdout.readline().split()
        if out != [name, str(m), str(nb)]:
            bad.append(dict(name=name, python=[m, nb], lean=out))
        boxes += nb; mx = max(mx, m)
    return idx, len(CAPTURED), boxes, mx, bad


def run_root_full(job):
    """Replay one root and check each captured leaf's certificate and numeric data with leafcheck
    (with --num-only its numeric data only: no tree is sent, and leafcheck answers
    `name skipped skipped num`)."""
    CAPTURED.clear()
    idx = job if isinstance(job, int) else job['id']
    num_only = '--num-only' in LEAN['cmd']
    t0 = time.time()
    GV.check_root(job)
    replay_ms = round(1000*(time.time()-t0))
    p = lean_checker()
    bad, numfail, per, boxes, mx = [], [], [], 0, -1
    for j, (lf, tree, (m, nb)) in enumerate(CAPTURED):
        name = f'{idx}_{j}'
        meta = leaf_numerics(lf)
        line = dict(name=name, leaf=leaf_json(leaf_data(lf)), meta=meta)
        if not num_only:
            line['tree'] = tree
        t = time.time()
        p.stdin.write(json.dumps(line, separators=(',', ':')) + '\n')
        p.stdin.flush()
        out = p.stdout.readline().split()
        wall = time.time() - t
        want = [name, 'skipped', 'skipped'] if num_only else [name, str(m), str(nb)]
        if out[:3] != want or len(out) < 4:
            bad.append(dict(name=name, python=[m, nb], lean=out))
        elif out[3] != 'ok':
            numfail.append(dict(name=name, reason=out[3]))
        rec = dict(name=name, columns=len(meta['columns']), boxes=nb, wall_ms=round(1000*wall),
                   profile=meta['far_profile']['profile'], type=meta['case']['type'])
        if len(out) >= 6:
            rec.update(cert_ms=int(out[4]), num_ms=int(out[5]))
        per.append(rec)
        boxes += nb; mx = max(mx, m)
    return idx, len(CAPTURED), boxes, mx, bad, numfail, per, replay_ms


def lean_leaf(name, data):
    cols = ',\n    '.join(
        '⟨' + ', '.join(lean_int(c[k]) for k in ('G', 'W', 'C', 'NH', 'E')) + ', '
        + lean_list([lean_int(x) for x in c['v']]) + ', ' + lean_list([lean_int(x) for x in c['D']]) + '⟩'
        for c in data['cols'])
    rows = ', '.join(
        '⟨' + lean_int(r['d']) + ', '
        + lean_list(['(' + ', '.join(lean_int(x) for x in t) + ')' for t in r['fam']]) + '⟩'
        for r in data['rows'])
    return (f'def {name} : Leaf where\n'
            f'  cols := [\n    {cols}]\n'
            f'  rows := [{rows}]\n'
            f'  F := {lean_int(data["F"])}\n  ng := {lean_int(data["ng"])}\n  n2 := {lean_int(data["n2"])}\n'
            f'  first := {lean_int(data["first"])}\n  final := {lean_int(data["final"])}\n')


def lean_case(c):
    if c == 'excluded':
        return '.excluded'
    assert set(c) <= {'Y', 'V', 'U', 'P', 'M', 'Z'} and 'Y' in c and 'Z' in c   # as graded_cert.check_case
    vals = [c['Y']] + [c.get(k, 0) for k in ('V', 'U', 'P', 'M')]
    assert all(type(x) is int and x >= 0 for x in vals + c['Z'])
    return '.duals ⟨' + ', '.join(map(str, vals)) + ', ' + lean_list([str(z) for z in c['Z']]) + '⟩'


def lean_tree(t, indent=2):
    pad = ' ' * indent
    if 'split' in t:
        l, r = t['children']
        return (f'.split {t["split"]} {lean_int(t["mid"])}\n'
                f'{pad}({lean_tree(l, indent+2)})\n{pad}({lean_tree(r, indent+2)})')
    return '.node ' + lean_list([str(o) for o in t['orders']]) + ' ' + lean_list([lean_case(c) for c in t['cases']])


def tree_boxes(t):
    return sum(tree_boxes(c) for c in t['children']) if 'split' in t else 1


# ------------------------------------------------------------------ near rows (--rows)
def _grid_floor(x):
    """The largest multiple of 1/200 that is <= x (graded_leaves' DELTA_GRID)."""
    from fractions import Fraction
    g = Fraction(1, 200)
    return (Fraction(x) // g) * g


def _grid_ceil(x):
    """The smallest multiple of 1/200 that is >= x."""
    from fractions import Fraction
    g = Fraction(1, 200)
    return -((-Fraction(x)) // g) * g


_CZ_CELLS = {}


def _cz_cells(fz, d, tolerance=None):
    """The cells of `RigorousTest.C_upper(d)` (core/code/base_enclosures.py): the same adaptive
    refinement of [0, 20] on the line Re z = -d, returned as the sorted list of cell ends. The Lean
    checker recomputes every cell bound and the tail from these points (RowCheckCore.czC)."""
    import heapq
    import base_enclosures as BE
    from fractions import Fraction as F
    d = F(d)
    key = (fz.g, d)
    if key in _CZ_CELLS:
        return _CZ_CELLS[key]
    tolerance = F(1, 10**6) if tolerance is None else tolerance
    M2 = BE.upper(fz.exponential_moment(2, d)); T = F(20)
    di = BE.I(d); g = fz.gi; e = BE.iv.exp(2*g*di); Ti = BE.I(T)
    tail = (fz.f0*di/Ti**2+8*g**3/(3*Ti**3)+4*g*g*(1+e)/Ti**4+4*(1+e)/Ti**6+8*g*e/Ti**5)
    tail_u = BE.upper(tail)
    vals = {}

    def at(t):
        if t not in vals:
            z = BE.iv.mpc(-BE.I(d), BE.I(t)); x = -fz.F(z).real
            vals[t] = (BE.lower(x), BE.upper(x))
        return vals[t]

    def interval(a, b):
        u = max(at(a)[1], at(b)[1])+BE.ceil_fraction(F(M2, 8)*(b-a)**2)
        return (-u, a, b)
    heap = [interval(F(j, 10), F(j+1, 10)) for j in range(200)]
    heapq.heapify(heap)
    best = max(0, max(v[0] for v in vals.values()))
    tol = BE.ceil_fraction(tolerance*BE.S)
    while -heap[0][0] > max(best, tail_u)+tol:
        _, a, b = heapq.heappop(heap); m = (a+b)/2
        at(m); best = max(best, at(m)[0])
        heapq.heappush(heap, interval(a, m)); heapq.heappush(heap, interval(m, b))
        if len(vals) > 100000:
            raise RuntimeError('Supremum refinement failed')
    pts = sorted({x for _, a, b in heap for x in (a, b)})
    _CZ_CELLS[key] = pts
    return pts


def _grid_cells(lo, hi, top, step):
    """The builders' number of grid cells on [lo, min(hi, top)] (sieve_inputs.pair_bounds and
    second_zero_bounds); 1 when the grid is empty (the checker then uses the tail only)."""
    t = top if hi is None else min(hi, top)
    return max(1, int(((t-lo)/step).__ceil__())) if lo < t else 1


def row_meta(lf, spec, row, outside):
    """The metadata of one near row for `rowcheck`, or None for the inherited two-test row.

    Each entry's semantics follows research/PROOF.md §6.5: an entry takes its feature at `hi` from
    the response anchor `anc` (offset `s - anc` in the near lemma):
      ordinary bin [lo, hi]            (hi, min(lo, s)); the tail has none
      hidden column [lo, hi] (outside)  (hi, s), s = s1
      second-family column [l, r]       (r, min(max(a, min(l2, l)), s))
      first family (family, graded)     (b, min(a, s));  outside family row: (b, min(a, s))
      shifted first family              (b, s); type rc with s > a: with the C_Z term (`cz`)
      reserved family, fixed term       (hi2, min(max(a, min(l2, lo2)), s))
      rc pair (family row)              (b, s) with the conjugate zero's term (`two`, y = 2 mu)
      first family's second zero        (b, s) and (p_hi, s), each with the other zero's term (`two`)
    `del` and `delHi` are the grid points 1/200 below and above `s - anc`. A family term that keeps
    a second zero carries its `Spec` (RowCheckCore): `{"two": [xa, xb, ylo, yhi, ytop, n]}` for the
    real offsets x in [xa, xb] and height differences |y| in [ylo, yhi] of that zero, or
    `{"cz": [d, cells]}` for a zero anywhere in Re z >= -d."""
    from fractions import Fraction as F
    if spec['kind'] == 'old':
        return None
    import leaf_driver as LD
    test = LD.sieve_test(spec['parameters'])
    s, s1 = test.s, test.s1
    inp = lf.inp
    a, b = F(inp['case']['lo']), F(inp['case']['hi'])
    l2 = F(inp['case']['source_l2'])
    step = F(1, 50)

    def ent(hi, anc, sp=None):
        hi, anc = F(hi), F(anc)
        return (hi, anc, _grid_floor(s - anc), _grid_ceil(s - anc), sp)

    def two(xa, xb, ylo, yhi, ytop):
        return {'two': [str(xa), str(xb), str(ylo), None if yhi is None else str(yhi), str(ytop),
                        _grid_cells(ylo, yhi, ytop, step)]}
    cols = []
    for r in inp['rows']:
        cols.append(None if r[1] == 'infinity' else ent(r[1], min(F(r[0]), s)))
    for r in inp.get('hidden_rows') or []:
        cols.append(None if (r[1] == 'infinity' or 'vh' not in row) else ent(r[1], s))
    sc = inp.get('second_cols') or []
    for l, r, _, _ in sc:
        cols.append(ent(r, min(max(a, min(l2, F(l))), s)) if 'vs' in row else None)
    kind, mr, dz = spec['kind'], spec.get('mu_range'), spec.get('dz_range')
    sec = inp.get('second')
    if kind == 'family' and not outside:
        if dz is not None:
            # sieve_inputs.second_zero_terms: rho1's entry sees rho' (lambda' in [p, p_hi]), rho''s
            # entry sees rho1 (lambda1 in [a, b]), at height difference |y| in dz_range
            p, p_hi = F(inp['gap']['lo']), F(inp['gap']['hi'])
            ylo, yhi = F(dz[0]), (None if dz[1] is None else F(dz[1]))
            fam = [ent(b, min(a, s), two(p - s, p_hi - s, ylo, yhi, F(10))),
                   ent(p_hi, min(a, s), two(a - s, b - s, ylo, yhi, F(10)))]
        elif mr is not None and inp['case']['kind'] == 'rc' and s == s1:
            # sieve_inputs.pair_term: the conjugate zero at height difference 2 mu1, mu1 in mu_range
            mlo, mhi = F(mr[0]), (None if mr[1] is None else F(mr[1]))
            sp = two(a - s, b - s, 2*mlo, None if mhi is None else 2*mhi, F(20))
            sp['two'][5] = _grid_cells(mlo, mhi, F(10), step)
            fam = [ent(b, min(a, s), sp)]
        else:
            fam = [ent(b, min(a, s))]
    elif kind == 'family':
        fam = [ent(b, min(a, s))]
    elif kind == 'shifted':
        if inp['case']['kind'] == 'rc' and s > a:
            # sieve_inputs.shifted_first_feature: the conjugate zero anywhere in Re z >= a - s
            fam = [ent(b, s, {'cz': [str(s - a), [str(y) for y in _cz_cells(test.fz, s - a)]]})]
        else:
            fam = [ent(b, s)]
    elif kind == 'graded' and not outside:
        fam = [ent(b, min(a, s))]
    else:
        fam = []
    if sec and not sc:
        a2 = max(a, min(l2, F(sec['lo'])))
        fam.append(ent(sec['hi'], min(a2, s)))
    nfam = len(row.get('fam', []))
    if len(fam) != nfam:
        raise AssertionError(f'family terms: {len(fam)} semantics for {nfam} terms ({kind})')
    # the lists of feature points and offsets, and the entries' indices
    xs, ds = {}, {}

    def enc(e):
        if e is None:
            return None
        hi, anc, dl, dh, sp = e
        xi = xs.setdefault(hi - anc, len(xs))
        di = ds.setdefault(dl, len(ds))
        dj = ds.setdefault(dh, len(ds))
        out = [str(hi), str(anc), str(dl), str(dh), xi, di, dj]
        return out if sp is None else out + [sp]
    cols_j = [enc(e) for e in cols]
    fam_j = [enc(e) for e in fam]
    return dict(p=dict(gamma=str(test.g), g1=str(test.g1), t0=str(test.t0), s=str(s), s1=str(s1),
                       h=[str(x) for x in test.h]),
                xs=[str(x) for x in xs], ds=[str(x) for x in ds], cols=cols_j, fam=fam_j)


def init_rows(kind, L, sources, cmd):
    """As init_worker; graded_leaves.leaf also records each leaf's row specs."""
    init_worker(kind, L, sources, cmd)
    import graded_leaves as GLV
    orig = GLV.leaf

    def leaf(inp, specs, outside):
        lf = orig(inp, specs, outside)
        lf._specs, lf._outside = specs, outside
        return lf
    GLV.leaf = leaf


def rows_root(job):
    """Replay one root and check each captured leaf's near rows with rowcheck."""
    CAPTURED.clear()
    idx = job if isinstance(job, int) else job['id']
    GV.check_root(job)
    p = lean_checker()
    res = []
    for j, (lf, tree, (m, nb)) in enumerate(CAPTURED):
        name = f'{idx}_{j}'
        try:
            rows = [row_meta(lf, sp, row, lf._outside) for sp, row in zip(lf._specs, lf.rows)]
        except AssertionError as e:
            res.append(dict(name=name, status='export', reason=str(e)))
            continue
        p.stdin.write(json.dumps(dict(name=name, leaf=leaf_json(leaf_data(lf)), rows=rows),
                                 separators=(',', ':')) + '\n')
        p.stdin.flush()
        out = p.stdout.readline().split(maxsplit=1)
        if len(out) == 2 and out[0] == name and out[1].startswith('ok'):
            f = out[1].split()
            res.append(dict(name=name, status='ok', rows=int(f[1]), checked=int(f[2]), items=int(f[3]),
                            ms=int(f[4]), special=int(f[5]) if len(f) > 5 else 0,
                            kinds=[sp['kind'] for sp in lf._specs]))
        else:
            res.append(dict(name=name, status='fail', reason=' '.join(out[1:]) if len(out) > 1 else str(out)))
    return idx, res


def run_rows(a, out, ids_arg, sources):
    from concurrent.futures import ProcessPoolExecutor
    jobs = select_jobs(a.kind, ids_arg)
    t = time.time(); n = 0; allres = []
    with ProcessPoolExecutor(max_workers=a.workers, initializer=init_rows,
                             initargs=(a.kind, a.L, sources, a.checker.split())) as ex:
        for idx, res in ex.map(rows_root, jobs, chunksize=1):
            n += 1; allres += res
            bad = [r for r in res if r['status'] != 'ok']
            if n % 100 == 0 or bad or len(jobs) <= 100:
                print(a.kind, n, len(jobs), 'id', idx, 'leaves', len(allres),
                      'failures', sum(1 for r in allres if r['status'] != 'ok'), 'sec', round(time.time()-t),
                      flush=True)
                for r in bad:
                    print('  ', r['name'], r['status'], r.get('reason', ''), flush=True)
    ok = [r for r in allres if r['status'] == 'ok']
    rep = dict(kind=a.kind, L=a.L, mode='rows', roots=n, leaves=len(allres), passed=len(ok),
               rows=sum(r['rows'] for r in ok), rows_checked=sum(r['checked'] for r in ok),
               items=sum(r['items'] for r in ok), special=sum(r.get('special', 0) for r in ok),
               ms=sum(r['ms'] for r in ok),
               failures=[r for r in allres if r['status'] != 'ok'], seconds=round(time.time()-t),
               checker=a.checker, status='PASS' if len(ok) == len(allres) else 'FAIL')
    out.write_text(json.dumps(rep, indent=1) + '\n')
    print(json.dumps({k: v for k, v in rep.items() if k != 'failures'}), 'failures', len(rep['failures']))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--kind', choices=('inside', 'outside'), required=True)
    ap.add_argument('--roots', required=True, help='comma-separated root ids')
    ap.add_argument('--L', default='3.99')
    ap.add_argument('--corpus', default=str(HERE/'corpora'/'3.99'))
    ap.add_argument('--out', default=None, help='the Lean module (or, with --jsonl, the summary)')
    ap.add_argument('--module-doc', default='')
    ap.add_argument('--split-dir', default=None,
                    help='write one module per leaf into this directory (limits the kernel\'s memory)')
    ap.add_argument('--jsonl', action='store_true', help='check every leaf with CertRun instead')
    ap.add_argument('--numerics', action='store_true',
                    help='write every leaf\'s numeric metadata as JSON lines to --out instead')
    ap.add_argument('--full', action='store_true',
                    help='check every leaf\'s certificate and numeric data with leafcheck instead')
    ap.add_argument('--rows', action='store_true',
                    help='check every leaf\'s near rows with rowcheck instead')
    ap.add_argument('--num-only', action='store_true',
                    help='with --full: numeric data only (leafcheck --num-only; no certificate check in Lean)')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--checker', default=None,
                    help='command running CertRun (default `lake env lean --run scripts/CertRun.lean`), or '
                         'with --full leafcheck (default `.lake/build/bin/leafcheck`), from lean-graded/')
    a = ap.parse_args()
    if a.checker is None:
        a.checker = ('.lake/build/bin/rowcheck' if a.rows else '.lake/build/bin/leafcheck' if a.full
                     else 'lake env lean --run scripts/CertRun.lean')
    assert a.out or a.split_dir, 'give --out or --split-dir'
    if a.split_dir:
        a.split_dir = str(Path(a.split_dir).resolve())    # the outside replay changes directory
    out = Path(a.out).resolve() if a.out else None
    corpus = Path(a.corpus).resolve()
    sources = (dict(inside=corpus/'inside.jsonl.gz', nodes=corpus/'nodes.jsonl.gz') if a.kind == 'inside'
               else dict(outside=corpus/'outside.jsonl.gz'))
    if a.numerics:
        assert out is not None, 'give --out'
        return run_numerics(a, out, ids_arg=a.roots, sources=sources)
    assert a.full or not a.num_only, '--num-only goes with --full'
    if a.rows:
        assert out is not None, 'give --out'
        return run_rows(a, out, ids_arg=a.roots, sources=sources)
    if a.full:
        assert out is not None, 'give --out'
        return run_full(a, out, ids_arg=a.roots, sources=sources)
    if a.jsonl:
        return run_jsonl(a, out, ids_arg=a.roots, sources=sources)
    ids = [int(x) for x in a.roots.split(',')]
    GV.setup(a.kind, a.L, sources)
    CT.verify_tree = capture(CT.verify_tree)
    items = []
    if a.kind == 'inside':
        for idx in ids:
            CAPTURED.clear()
            GV.check_root(idx)
            items += [(f'i{idx}_{j}', *c) for j, c in enumerate(CAPTURED)]
    else:
        sys.path.insert(0, str(GV.ROOT/'near'/'code'))
        from certificate_io import load_outside
        jobs = {j['id']: j for j in load_outside('4.30')}
        for idx in ids:
            CAPTURED.clear()
            GV.check_root(jobs[idx])
            items += [(f'o{idx}_{j}', *c) for j, c in enumerate(CAPTURED)]
    def header(names):
        # a module (Palomar requires the module system), public with exposed definitions: the
        # kernel evaluates `checkLeaf` of `GradedNear.Defs` from here
        return ['module\n\npublic import GradedNear.Cert.Sound\n',
                '/-!\n# Kernel-checked certificates\n\n'
                'Generated by `computations/graded/graded_lean_export.py` '
                f'(`--kind {a.kind} --roots {a.roots}`), at `L = {a.L}`: leaf {", ".join(names)}.\n'
                'Each leaf is the integer data regenerated by the repository\'s builders, and each tree is\n'
                'the stored certificate. `checkLeaf` is evaluated by the kernel (`decide +kernel`), and\n'
                '`certified` turns each result into the bound `objective < S` at every feasible point.\n'
                + (('\n' + a.module_doc + '\n') if a.module_doc else '') + '-/\n',
                '@[expose] public section\n',
                'namespace GradedNear.Cert.Samples\n\nopen GradedNear.Cert\n\n'
                '-- long list literals (hundreds of columns) nest deeply when elaborated\n'
                'set_option maxRecDepth 100000\n']
    blocks, summary = [], []
    for name, lf, tree, (mx, nb) in items:
        assert nb == tree_boxes(tree)
        b = [lean_leaf(f'leaf_{name}', leaf_data(lf)),
             f'def tree_{name} : Tree :=\n  {lean_tree(tree, 4)}\n',
             f'/-- `checkLeaf` accepts the certificate of leaf `{name}` ({nb} boxes) with value '
             f'{mx}/10¹⁶. -/\n'
             f'theorem check_{name} : checkLeaf leaf_{name} tree_{name} = some {mx} := by\n'
             f'  decide +kernel\n',
             f'/-- Leaf `{name}`: every feasible point of its LP has objective below `S`. -/\n'
             f'theorem bound_{name} (x : Fin leaf_{name}.cols.length → ℝ) (τ : ℕ → ℝ)\n'
             f'    (h : Feasible leaf_{name} x τ) : objective leaf_{name} x < S :=\n'
             f'  certified check_{name} x τ h\n']
        blocks.append((name, b))
        summary.append(dict(name=name, boxes=nb, maximum=mx, columns=len(lf.G + lf.GH + lf.GS), rows=len(lf.rows)))
    if a.split_dir:
        d = Path(a.split_dir).resolve(); d.mkdir(parents=True, exist_ok=True)
        for name, b in blocks:
            stem = name[0].upper() + name[1:]
            (d / f'{stem}.lean').write_text('\n'.join(header([name]) + b + ['end GradedNear.Cert.Samples\n']))
    else:
        out.write_text('\n'.join(header([n for n, _ in blocks]) + [x for _, b in blocks for x in b]
                                  + ['end GradedNear.Cert.Samples\n']))
    print(json.dumps(summary))


def select_jobs(kind, ids_arg):
    """The replay jobs of the chosen roots: inside spec indices or outside source records."""
    sys.path.insert(0, str(GV.ROOT/'core'/'code'))
    if kind == 'inside':
        from endgame import specs
        jobs = list(range(len(specs())))
    else:
        sys.path.insert(0, str(GV.ROOT/'near'/'code'))
        cwd = os.getcwd(); os.chdir(str(GV.ROOT/'near'/'code'))
        from certificate_io import load_outside
        jobs = load_outside('4.30'); os.chdir(cwd)
    if ids_arg != 'all':
        want = set(int(x) for x in ids_arg.split(','))
        jobs = [j for j in jobs if (j if isinstance(j, int) else j['id']) in want]
    return jobs


def run_jsonl(a, out, ids_arg, sources):
    from concurrent.futures import ProcessPoolExecutor
    jobs = select_jobs(a.kind, ids_arg)
    t = time.time(); n = leaves = boxes = 0; mx = -1; bad = []
    with ProcessPoolExecutor(max_workers=a.workers, initializer=init_worker,
                             initargs=(a.kind, a.L, sources, a.checker.split())) as ex:
        for idx, nl, nb, m, b in ex.map(run_root, jobs, chunksize=1):
            n += 1; leaves += nl; boxes += nb; mx = max(mx, m); bad += b
            if n % 100 == 0 or b:
                print(a.kind, n, len(jobs), 'id', idx, 'leaves', leaves, 'boxes', boxes, 'bad', len(bad),
                      'sec', round(time.time()-t), flush=True)
    rep = dict(kind=a.kind, L=a.L, roots=n, leaves=leaves, boxes=boxes, maximum_numerator=mx,
               mismatches=bad, seconds=round(time.time()-t), checker=a.checker,
               status='PASS' if not bad else 'FAIL')
    out.write_text(json.dumps(rep, indent=1) + '\n')
    print(json.dumps({k: v for k, v in rep.items() if k != 'mismatches'}), 'mismatches', len(bad))


def run_full(a, out, ids_arg, sources):
    """--full: certificate and numeric checks of every leaf by leafcheck (see the module docstring);
    with --num-only the numeric checks only."""
    from concurrent.futures import ProcessPoolExecutor
    jobs = select_jobs(a.kind, ids_arg)
    if ids_arg != 'all':
        assert len(jobs) == len(set(int(x) for x in ids_arg.split(','))), 'unknown root id'
    cmd = a.checker.split()
    if a.num_only and '--num-only' not in cmd:
        cmd.append('--num-only')
    t = time.time(); n = leaves = boxes = 0; mx = -1; bad = []; numfail = []; per = []; replay = []
    with ProcessPoolExecutor(max_workers=a.workers, initializer=init_worker,
                             initargs=(a.kind, a.L, sources, cmd)) as ex:
        for idx, nl, nb, m, b, nf, pl, rms in ex.map(run_root_full, jobs, chunksize=1):
            n += 1; leaves += nl; boxes += nb; mx = max(mx, m); bad += b; numfail += nf; per += pl
            replay.append(dict(replay_ms=rms))
            if n % 100 == 0 or b or nf or len(jobs) <= 100:
                print(a.kind, n, len(jobs), 'id', idx, 'leaves', leaves, 'boxes', boxes, 'bad', len(bad),
                      'numeric_failures', len(numfail), 'sec', round(time.time()-t), flush=True)

    def stats(key):
        xs = sorted(r[key] for r in per if key in r)
        if not xs:
            return None
        return dict(total=sum(xs), mean=round(sum(xs)/len(xs), 1), median=xs[len(xs)//2], max=xs[-1])
    rs = sorted(r['replay_ms'] for r in replay)
    rep = dict(kind=a.kind, L=a.L, mode='numerics-only' if a.num_only else 'full',
               roots=n, leaves=leaves, boxes=boxes, maximum_numerator=mx,
               mismatches=bad, numeric_failures=len(numfail), numeric_failure_list=numfail,
               passed=leaves-len(bad)-len(numfail), seconds=round(time.time()-t), checker=' '.join(cmd),
               timing_ms=dict(wall=stats('wall_ms'), cert=stats('cert_ms'), num=stats('num_ms'),
                              replay_per_root=None if not rs else dict(
                                  total=sum(rs), mean=round(sum(rs)/len(rs), 1), median=rs[len(rs)//2],
                                  max=rs[-1])),
               status='PASS' if not bad and not numfail else 'FAIL', per_leaf=per)
    if a.num_only:
        rep['note'] = ('numerics only: the certificates are not checked in Lean here (leafcheck --num-only); '
                       'boxes and maximum_numerator are graded_cert\'s, from the replay')
    out.write_text(json.dumps(rep, indent=1) + '\n')
    print(json.dumps({k: v for k, v in rep.items() if k not in ('mismatches', 'numeric_failure_list', 'per_leaf')}),
          'mismatches', len(bad), 'numeric_failures', len(numfail))


# ------------------------------------------------------------------ numeric metadata (--numerics)
# Where each field of lf.inp comes from (tags of research/notes/leaf-data-semantics-2026-09-29.md,
# paths under computations/):
#   case, gap, ordinary_lower, second.lo  endgame.reduced_spec (EG:15-40), stored by make_single (PS:29)
#   rows          bins and W: published_single_inputs.single_rows (PS:7-13; kept by EX:110-112);
#                 G and count_cost: triple_inputs.input_with_third (TI:52-56); third_lower and row
#                 deletions: TI:49-56, third_refine.refine_third (TR:86-112); W and the tail's G with the
#                 retuned weight: far_enclosures.replace_far (FE:65-69), which stores far_parameters
#   hidden_rows   first_outside_blocks.first_out_input (FO:19-27); p_h = first_block['anchor'] (FO:18)
#   second_cols   graded_leaves.second_columns (GL:139-143; grid graded_driver.SECOND_COLS_GRID = 400)
#   far_budget    make_single (PS:22-27) or replace_far (FE:61-64); second_columns' add-back (GL:145)
#   first         J_old: input_with_third (TI:57-62); min with J_new: use_shifted (TI:91-105, rule in
#                 shifted_first_proof); minus the outside charge (FO:17) or minus J2 (GL:144)
def _q(x):
    """Exact rational string ('399/100', '3') of a rational given as str, int or Fraction."""
    return str(Fraction(x))


def far_profile(inp):
    """The far weight of the leaf's ordinary and second-family far costs, ordinary tail and V:
    replace_far's parameters (stored as inp['far_parameters']) or the inherited config_v4 profile of
    two_test_enclosures.wgt."""
    from config_v4 import C1, C2, THETA, EPS0, ALPHA
    from far_enclosures import CANDIDATE
    p = inp.get('far_parameters')
    if p is None:
        return dict(profile='inherited', c1=_q(C1), c2=_q(C2), theta=_q(THETA), eps=_q(EPS0),
                    alpha=[_q(x) for x in ALPHA])
    return dict(profile='retuned' if p == CANDIDATE else 'custom', c1=_q(p['c1']), c2=_q(p['c2']),
                theta=_q(p['theta']), eps=_q(p['epsilon']), alpha=[_q(x) for x in p['alpha']])


def leaf_numerics(lf):
    """Metadata of a graded_cert.Leaf's numeric data, read from its input lf.inp.

    columns (Lean order: ordinary, hidden, second family), each with
      family  'ordinary' | 'hidden' | 'second';  kind 'bin' | 'tail' (a tail covers [lo, infinity))
      lo, hi  exact rationals (hi = 'infinity' for a tail)
      obj     {'G': phi}: e^{-A lam} B_phi(lam) at lam = lo (ordinary: phi = 1/3; second: phi2);
              {'hidden': {'phi', 'p'}}: t -> e^{-A t} B_phi(p) at t = lo.  A tail's objective is
              obj(R) w^{-1}(R), R = lo
      w       far profile of W (bin: w(hi); tail: W = S) and of the tail's w^{-1}(R)
      G W C NH E  the stored integers: objective, far cost, count cost (S or 0), hidden-count
              coefficient (S on hidden bins, floor_S w^{-1}(R) on the hidden tail, else 0) and
              second-family coefficient (S on second-family columns, else 0)
    far       F = ceil_S((1+eta) V) - [inside] n floor_S w(b) - [reserved] n2 floor_S w(hi2)
              (+ n2 floor_S w(hi2) when added_back: second-family columns)
    first     inside: min(ceil_S J_old, ceil_S J_new if J_new) ; outside: 0 (the first family is in the
              hidden columns); plus J2 = n2 ceil_S G_phi2(lo2) unless removed for columns."""
    inp = lf.inp
    c, gap, sec = inp['case'], inp.get('gap'), inp.get('second')
    typ, height = c['kind'], inp['height']
    assert typ in ('complex', 'rc', 'rr') and height in ('inside', 'outside')
    n = int(inp['n'])
    assert n == (2 if typ == 'complex' else 1)
    prof = far_profile(inp)
    hh = inp.get('hidden_rows') or []
    sc = inp.get('second_cols') or []
    rows = inp['rows']
    # the Leaf's stored integers, all columns in its order (graded_cert.Leaf)
    G = lf.G+lf.GH+lf.GS
    stored = [G, lf._Wall, lf._cnt_all, lf._NH_all, lf._S_all]
    assert all(len(x) == len(rows)+len(hh)+len(sc) for x in stored)
    phi_first = '1/4' if typ != 'complex' else '1/3'   # enclosures.RigorousWeights.first: real = kind != complex
    cols = []

    def col(family, r, obj, w):
        tail = r[1] == 'infinity'
        return dict(family=family, kind='tail' if tail else 'bin', lo=_q(r[0]),
                    hi='infinity' if tail else _q(r[1]), obj=obj, w=w)
    for r in rows:
        cols.append(col('ordinary', r, {'G': '1/3'}, prof['profile']))
    if hh:
        assert height == 'outside' and inp['outside_subcase'] == 'outside_buffer'
        ph = _q(inp['first_block']['anchor'])
        phi_h = '1/4' if typ == 'rc' else '1/3'           # first_out_input: real = kind == rc
        for r in hh:
            cols.append(col('hidden', r, {'hidden': {'phi': phi_h, 'p': ph}}, 'inherited'))
    if sc:
        n2 = int(sec['n'])
        for r in sc:
            cols.append(col('second', r, {'G': '1/4' if n2 == 1 else '1/3'}, prof['profile']))
    for i, cd in enumerate(cols):
        cd.update(zip(('G', 'W', 'C', 'NH', 'E'), (x[i] for x in stored)))
    # the stored rows agree with the Leaf's lists (graded_cert.Leaf reads them from inp)
    assert [r[3] for r in rows+hh+sc] == G and [r[2] for r in rows+hh+sc] == lf._Wall
    assert lf._NH_all == [0]*len(rows)+[r[5] for r in hh]+[0]*len(sc)

    reserved = None
    if sec:
        reserved = dict(n2=int(sec['n']), hi2=_q(sec['hi']), added_back=bool(sc))
    from config_v4 import ETA, FINAL
    far = dict(V=prof['profile'], eta=_q(ETA),
               inside=dict(n=n, b=_q(c['hi'])) if height == 'inside' else None,
               reserved=reserved, F=lf.F)
    assert lf.final == int(FINAL*CT.S)

    if height == 'inside':
        p = Fraction(gap['lo']) if gap else Fraction(c['lp'])   # make_single, input_with_third, shifted_first
        b = Fraction(c['hi'])
        rule = inp['shifted_first_proof']['rule']
        assert rule == ('shifted_autocorrelation_coupled_height' if p >= b else 'old_bound_retained'), rule
        fam1 = dict(inside=dict(n=n, alpha=2 if typ == 'rc' else 1, phi_t=phi_first, a=_q(c['lo']), b=_q(b),
                                p=_q(p), J_new=p >= b), outside=None)
    else:
        fb = inp['first_block']
        fam1 = dict(inside=None, outside=dict(n=n, p_h=_q(fb['anchor']), phi='1/4' if typ == 'rc' else '1/3',
                                              removed=fb['removed_objective'], hidden_columns=len(hh)))
    J2 = None
    if sec:
        n2 = int(sec['n'])
        J2 = dict(n2=n2, phi2='1/4' if n2 == 1 else '1/3', lo2=_q(sec['lo']), removed_for_columns=bool(sc))
    first = dict(fam1, J2=J2, first=lf.first, final=lf.final)

    case = dict(type=typ, height=height, lo=_q(c['lo']), hi=_q(c['hi']), lp=_q(c['lp']),
                source_l2=_q(c['source_l2']),
                gap=None if not gap else dict(lo=_q(gap['lo']), hi=gap['hi'] if gap['hi'] == 'infinity' else _q(gap['hi'])),
                ordinary_lower=_q(inp['ordinary_lower']), third_lower=_q(inp['third_lower']),
                second=None if not sec else dict(lo=_q(sec['lo']), hi=_q(sec['hi']), n=int(sec['n'])),
                den=int(inp['lambda_den']), second_columns_den=400 if sc else None)
    return dict(L=_q(inp['L']), far_profile=prof, case=case, columns=cols, far=far, first=first)


NUM = {}


def init_numerics(kind, L, sources):
    GV.setup(kind, L, sources)
    CT.verify_tree = capture(CT.verify_tree)
    orig = GV.check_records

    def check_records(idx, key, srcs, outside):     # records which corpus each captured leaf came from
        start = len(CAPTURED)
        out = orig(idx, key, srcs, outside)
        NUM['keys'] += [key]*(len(CAPTURED)-start)
        return out
    GV.check_records = check_records


def numerics_root(job):
    """Replay one root (graded_cert checks every tree) and return each captured leaf's metadata."""
    CAPTURED.clear(); NUM['keys'] = []
    idx = job if isinstance(job, int) else job['id']
    GV.check_root(job)
    assert len(NUM['keys']) == len(CAPTURED)
    out = []
    for j, ((lf, _tree, (m, nb)), key) in enumerate(zip(CAPTURED, NUM['keys'])):
        d = dict(name=f'{idx}_{j}', kind=GV.STATE['kind'], corpus=key, root=idx, maximum=m, boxes=nb)
        d.update(leaf_numerics(lf))
        out.append(json.dumps(d, separators=(',', ':')))
    return idx, out


def run_numerics(a, out, ids_arg, sources):
    from concurrent.futures import ProcessPoolExecutor
    jobs = select_jobs(a.kind, ids_arg)
    if ids_arg != 'all':
        assert len(jobs) == len(set(int(x) for x in ids_arg.split(','))), 'unknown root id'
    t = time.time(); n = leaves = 0
    fh = gzip.open(out, 'wt') if out.suffix == '.gz' else open(out, 'w')
    with fh, ProcessPoolExecutor(max_workers=a.workers, initializer=init_numerics,
                                 initargs=(a.kind, a.L, sources)) as ex:
        for idx, lines in ex.map(numerics_root, jobs, chunksize=1):
            n += 1; leaves += len(lines)
            for line in lines:
                fh.write(line + '\n')
            fh.flush()
            print(a.kind, n, len(jobs), 'id', idx, 'leaves', leaves, 'sec', round(time.time()-t), flush=True)
    print(json.dumps(dict(kind=a.kind, L=a.L, roots=n, leaves=leaves, out=str(out), seconds=round(time.time()-t))))


if __name__ == '__main__':
    main()
