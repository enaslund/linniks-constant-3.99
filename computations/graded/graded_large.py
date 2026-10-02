"""The large first-zero range (lambda_1 >= 1.5) as a leaf of the graded pipeline (paper Theorem 12.6).

The program is the one of the earlier exterior check (core/code/published_single_inputs.make_large,
record core/results/large_branch_3.99.json): the bins [3/2 + j/100, 3/2 + (j+1)/100), 0 <= j < 150,
and the tail [3, oo); every character is placed by the parameter of its height-one representative
(lambda_chi >= lambda_1 >= 3/2); objective G_{1/3} at the left end of a bin, far weight w at the right
end, far profile I (config_v4), far budget ceil_S((1+eta) V), first = 0 and final = 5 eta; no count,
hidden-count or second-family constraint. Its objective and far integers are regenerated with
make_large and compared with the stored record.

Its near row is rebuilt here as a row of the graded pipeline without family terms
(sieve_inputs.SieveNearTest with gamma = 1, g1 = 3/2, s = s1 = 3/2 and mu = 10^9, so that every sieve
height is 0): paper Corollary 8.10 with I_u the builders' upper Riemann sum. Every zero of every
nonprincipal L-function in R(l) has parameter >= lambda_1 >= 3/2 = s1, so the safe-anchor hypothesis
holds, and the entry of a bin [lo, hi) (lo >= 3/2) takes its feature at hi from the anchor s = 3/2,
with no zero to the right. The verified row checker (lean-graded/RowCheckCore.lean) recomputes this
normalization. The row stored in the earlier record was normalized with a tighter integral, and that
checker does not accept it.

The certificate is a comb tree over the threshold intervals of the earlier record, with the
first-order relaxation on each; the integer duals are proposed by a floating LP (SciPy's HiGHS) and
every case is checked exactly by graded_cert.check_case.

  python3 computations/graded/graded_large.py                  # build, check, write large_3.99.json
  python3 computations/graded/graded_large.py --lean           # also run certrun, leafcheck, rowcheck
  python3 computations/graded/graded_large.py --lean-module lean-graded/GradedNear/Cert/Samples/Large.lean
"""
import sys, json, argparse, time, subprocess, hashlib
from fractions import Fraction as Q
from pathlib import Path
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
for p in (ROOT/'core'/'code', ROOT/'frontier', ROOT/'sieve_near', HERE):
    sys.path.insert(0, str(p))
if not __debug__:
    raise RuntimeError('assertions must be enabled')
import graded_cert as CT

L = '3.99'
T0 = Q(1)                   # the split point of the Riemann sum: 2000 cells on [0, 1), 2000 on [1, 2)
MU = Q(10**9)               # no sieve part
GAMMA, G1, S_ANCHOR = Q(1), Q(3, 2), Q(3, 2)
RECORD = ROOT/'core'/'results'/'large_branch_3.99.json'
OUT = HERE/f'large_{L}.json'
LEAN_OUT = HERE/'lean_runs'/f'large_{L}.json'
# The Lean package: `lean-graded/` here, the repository root in the public repository.
LEAN_DIR = (ROOT.parent/'lean-graded' if (ROOT.parent/'lean-graded'/'lakefile.toml').exists()
            else ROOT.parent)


def large_input():
    """The program's columns, far budget, first and final, regenerated (make_large) and compared
    with the stored record."""
    from published_single_inputs import make_large
    rec = json.loads(RECORD.read_text())
    inp = make_large(L)
    assert inp == rec['input'], 'regenerated large-branch input differs from the stored record'
    return inp, rec


def large_row(inp):
    """The near row: SieveNearTest at s = s1 = 3/2 with zero sieve heights; the bins' features at their
    right ends from the anchor s, the tail's feature 0; every diagonal D(0), normalized."""
    from sieve_inputs import SieveNearTest
    test = SieveNearTest(GAMMA, G1, T0, MU, S_ANCHOR, S_ANCHOR)
    assert all(h == 0 for h in test.h), 'the sieve part must vanish'
    d, D = test.gram()
    v = []
    for r in inp['rows']:
        if r[1] == 'infinity':
            v.append(0)
        else:
            assert Q(r[0]) >= S_ANCHOR
            v.append(max(0, test.feature(Q(r[1]))))
    return test, dict(d=d, D=D, v=v, Dv=[D]*len(v))


def _lp(G, A, b):
    """Floating LP max G.x s.t. A x <= b, x >= 0 with SciPy's HiGHS (proposal only, like
    graded_cert._lp): (value, row duals y >= 0, x)."""
    import numpy as np
    from scipy.optimize import linprog
    res = linprog(-np.asarray(G, float), A_ub=np.asarray(A, float), b_ub=np.asarray(b, float),
                  bounds=(0, None), method='highs')
    if res.status != 0:
        return None
    return -res.fun, [max(0.0, -m) for m in res.ineqlin.marginals], res.x


def box_node(lf, box):
    """First-order relaxation on one threshold interval, with integer duals checked exactly."""
    eps = (2,)
    cd = CT.case_data(lf, [box], eps)
    if CT.excludable(cd):
        return dict(orders=[2], cases=['excluded'], value=-1)
    G, A, b = CT.lp_matrix(lf, cd, [box], eps)
    r = _lp(G, A, b)
    assert r is not None, ('LP failed', box)
    du, v = CT.integer_duals(lf, cd, r[1])
    assert du is not None, ('no integer duals', box)
    return dict(orders=[2], cases=[du], value=v)


def comb(lf, cuts):
    """A tree whose leaves are the intervals between consecutive cuts of [0, e]."""
    e = lf.ends[0]
    cuts = [c for c in cuts if 0 < c < e]
    assert cuts == sorted(set(cuts))
    boxes = list(zip([0]+cuts, cuts+[e]))
    nodes = [box_node(lf, bx) for bx in boxes]

    def build(i):
        if i == len(boxes)-1:
            return nodes[i]
        return dict(split=0, mid=boxes[i][1], children=[nodes[i], build(i+1)])
    return build(0), boxes


def leaf_numerics(lf):
    """The leaf's metadata in the layout of graded_lean_export.py --numerics: ordinary columns with
    objective G_{1/3}, far profile I, no first family, no reserved family."""
    import graded_lean_export as EX
    from config_v4 import ETA
    prof = EX.far_profile(lf.inp)
    assert prof['profile'] == 'inherited'
    cols = []
    for r, G, W in zip(lf.inp['rows'], lf.G, lf.W):
        tail = r[1] == 'infinity'
        cols.append(dict(family='ordinary', kind='tail' if tail else 'bin', lo=EX._q(r[0]),
                         hi='infinity' if tail else EX._q(r[1]), obj={'G': '1/3'}, w=prof['profile'],
                         G=G, W=W, C=0, NH=0, E=0))
    return dict(L=EX._q(L), far_profile=prof, case=None, columns=cols,
                far=dict(V=prof['profile'], eta=EX._q(ETA), inside=None, reserved=None, F=lf.F),
                first=dict(inside=None, outside=None, J2=None, first=lf.first, final=lf.final))


def row_meta(lf, test):
    """The near row's metadata for rowcheck: each bin's entry (hi, anc = s, offsets 0); the tail has
    none (feature 0)."""
    import graded_lean_export as EX
    s = test.s
    xs, ds = {}, {}
    cols = []
    for r in lf.inp['rows']:
        if r[1] == 'infinity':
            cols.append(None)
            continue
        hi, anc = Q(r[1]), min(Q(r[0]), s)
        dl, dh = EX._grid_floor(s-anc), EX._grid_ceil(s-anc)
        xi = xs.setdefault(hi-anc, len(xs)); di = ds.setdefault(dl, len(ds)); dj = ds.setdefault(dh, len(ds))
        cols.append([str(hi), str(anc), str(dl), str(dh), xi, di, dj])
    return dict(p=dict(gamma=str(test.g), g1=str(test.g1), t0=str(test.t0), s=str(test.s), s1=str(test.s1),
                       h=[str(x) for x in test.h]),
                xs=[str(x) for x in xs], ds=[str(x) for x in ds], cols=cols, fam=[])


def run_checker(binary, line, args=()):
    p = subprocess.run([str(LEAN_DIR/'.lake'/'build'/'bin'/binary), *args], input=json.dumps(line, separators=(',', ':'))+'\n',
                       capture_output=True, text=True, cwd=str(LEAN_DIR), check=True)
    return p.stdout.split()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--lean', action='store_true', help='run the native Lean checkers')
    ap.add_argument('--lean-module', default=None, help='write a kernel-checked Lean module here')
    a = ap.parse_args()
    t = time.time()
    inp, rec = large_input()
    test, row = large_row(inp)
    lf = CT.Leaf(inp, [row])
    cuts = [br['b'] for br in rec['certificate']['branches']]
    tree, boxes = comb(lf, cuts)
    mx, nb = CT.verify_tree(lf, tree)
    assert nb == len(boxes)
    binding = max(zip(boxes, [n for n in _leaves(tree)]), key=lambda x: x[1]['value'])
    out = dict(L=L, status='PASS: graded_cert accepts the certificate of the large first-zero range',
               program=dict(source=str(RECORD.relative_to(ROOT.parent)), bins=len(inp['rows'])-1, tail=inp['rows'][-1][0],
                            far_budget=lf.F, first=lf.first, final=lf.final, profile='inherited (profile I)'),
               row=dict(parameters=dict(gamma=str(GAMMA), g1=str(G1), t0=str(T0), mu=str(MU), s=str(S_ANCHOR),
                                        s1=str(S_ANCHOR)),
                        I_up=str(test.I_up), D_up=str(test.D_up), d=row['d'], D=row['D'], v=row['v']),
               certificate=tree, boxes=nb, maximum_numerator=mx, maximum=mx/CT.S,
               binding=dict(box=list(binding[0]), duals=binding[1]['cases'][0], value=binding[1]['value']),
               earlier_maximum_numerator=rec['certificate']['maximum'], seconds=round(time.time()-t, 1))
    OUT.write_text(json.dumps(out, indent=1)+'\n')
    print('graded_cert: maximum', mx, mx/CT.S, 'boxes', nb, 'binding', binding[0], 'seconds', round(time.time()-t))
    if a.lean or a.lean_module:
        import graded_lean_export as EX
        data = EX.leaf_data(lf)
        leafj = EX.leaf_json(data)
        name = 'large_3_99'
        if a.lean:
            cert = run_checker('certrun', dict(name=name, leaf=leafj, tree=tree))
            full = run_checker('leafcheck', dict(name=name, leaf=leafj, tree=tree, meta=leaf_numerics(lf)), ('--timing',))
            rows = run_checker('rowcheck', dict(name=name, leaf=leafj, rows=[row_meta(lf, test)]))
            ok = (cert == [name, str(mx), str(nb)] and full[:4] == [name, str(mx), str(nb), 'ok']
                  and len(rows) >= 2 and rows[:2] == [name, 'ok'])
            rep = dict(L=L, leaf=name, certrun=cert, leafcheck=full, rowcheck=rows, graded_cert=[mx, nb],
                       status='PASS' if ok else 'FAIL',
                       checkers={b: hashlib.sha256((LEAN_DIR/'.lake'/'build'/'bin'/b).read_bytes()).hexdigest()
                                 for b in ('certrun', 'leafcheck', 'rowcheck')})
            if LEAN_OUT.exists():          # keep the record of the kernel check (lake build ... Samples.Large)
                old = json.loads(LEAN_OUT.read_text())
                for k in ('kernel', 'note'):
                    if k in old:
                        rep[k] = old[k]
            LEAN_OUT.write_text(json.dumps(rep, indent=1)+'\n')
            print(json.dumps(rep))
            assert ok, 'a Lean checker did not accept the large-range leaf'
        if a.lean_module:
            mod = Path(a.lean_module)
            doc = ('The large first-zero range (paper Theorem 12.6), generated by\n'
                   '`computations/graded/graded_large.py --lean-module`: the leaf of the range '
                   '`λ₁ ≥ 3/2`\n(150 bins and a tail, one near row) and its certificate '
                   f'({nb} threshold intervals).')
            src = ['module\n\npublic import GradedNear.Cert.Sound\n',
                   f'/-!\n# A kernel-checked certificate: the large first-zero range\n\n{doc}\n'
                   '`checkLeaf` is evaluated by the kernel (`decide +kernel`), and `certified` turns the result\n'
                   'into the bound `objective < S` at every feasible point.\n-/\n',
                   '@[expose] public section\n',
                   'namespace GradedNear.Cert.Samples\n\nopen GradedNear.Cert\n\n'
                   '-- long list literals (hundreds of columns) nest deeply when elaborated\n'
                   'set_option maxRecDepth 100000\n',
                   EX.lean_leaf(f'leaf_{name}', data),
                   f'def tree_{name} : Tree :=\n  {EX.lean_tree(tree, 4)}\n',
                   f'/-- `checkLeaf` accepts the certificate of the large first-zero range ({nb} boxes) '
                   f'with value {mx}/10¹⁶. -/\n'
                   f'theorem check_{name} : checkLeaf leaf_{name} tree_{name} = some {mx} := by\n'
                   '  decide +kernel\n',
                   '/-- The large first-zero range: every feasible point of its LP has objective below `S`. -/\n'
                   f'theorem bound_{name} (x : Fin leaf_{name}.cols.length → ℝ) (τ : ℕ → ℝ)\n'
                   f'    (h : Feasible leaf_{name} x τ) : objective leaf_{name} x < S :=\n'
                   f'  certified check_{name} x τ h\n',
                   'end GradedNear.Cert.Samples\n']
            mod.write_text('\n'.join(src))
            print('wrote', mod)


def _leaves(node):
    if 'split' in node:
        for c in node['children']:
            yield from _leaves(c)
    else:
        yield node


if __name__ == '__main__':
    main()
