"""Negative tests of the graded replay: perturb regenerated inputs or certificate data slightly in the
unfavourable direction and check that the exact verifier rejects the stored certificate.

  python3 computations/graded/graded_mutation_test.py <inside root>[,<inside root>...] [--corpus DIR]

The corpus directory holds the inside and nodes certificates, as per-root directories or as the packed
files that corpora/assemble.sh rebuilds (default computations/graded/corpora/3.99).

For every certified leaf of each root (captured exactly as graded_verify captures it), run:
  base      unmodified (must pass)
  far+     far budget F * (1+1e-3)
  G+       every ordinary objective coefficient * (1+1e-3)
  first+   first-family objective + 1e-4
  d+       every near row's d * (1+1e-3)          (weaker near constraint)
  v-       every near row's ordinary features * (1-1e-3)
  dualY-   the first dual certificate's Y * (1-1e-3)
  final0   final allowance removed (lowers the bound; caught by the exact equality with the stored maximum)
A mutation 'caught' means verify_leaf raised.  On tight leaves (maximum close to 1) an unfavourable input
mutation must push a box value above 1 or break a column inequality; on every leaf the replay's exact
equality with the stored maximum rejects any change of the value, favourable or not.
"""
import sys, os, copy, json, time
from pathlib import Path
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import graded_verify as GV

L = '3.99'
C = sys.argv[sys.argv.index('--corpus')+1] if '--corpus' in sys.argv else str(HERE/'corpora'/L)
# Per-root directories when present, otherwise the packed corpus files (corpora/assemble.sh).
GV.setup('inside', L, {k: (C+'/'+k if Path(C, k).is_dir() else C+'/'+k+'.jsonl.gz') for k in ('inside', 'nodes')})
import graded_driver as DR, graded_leaves as LV, graded_cert as CT
S = CT.S
orig_inside = LV.inside_input
orig_build = LV.build_row


def patch_input(fn):
    def wrapped(src, L_, path=()):
        out = orig_inside(src, L_, path)
        return None if out is None else fn(copy.deepcopy(out))
    return wrapped


def far_plus(inp):
    inp['far_budget'] = inp['far_budget']*1001//1000
    return inp


def g_plus(inp):
    for r in inp['rows']:
        r[3] = r[3]*1001//1000+1
    return inp


def first_plus(inp):
    inp['first'] = inp['first']+S//10000
    return inp


def final_zero(inp):
    inp['final'] = 0
    return inp


def row_patch(fn):
    def wrapped(inp, spec, outside):
        return fn(copy.deepcopy(orig_build(inp, spec, outside)))
    return wrapped


def d_plus(row):
    row['d'] = row['d']*1001//1000+1
    return row


def v_minus(row):
    row['v'] = [x*999//1000 for x in row['v']]
    return row


def first_dual(node):
    """The first tree leaf with a dual case (depth-first)."""
    if 'split' in node:
        for ch in node['children']:
            r = first_dual(ch)
            if r is not None:
                return r
        return None
    for du in node['cases']:
        if du != 'excluded':
            return du
    return None


def records(rec):
    """Plain certificate records inside a (possibly split / reserved / dz / mu) record."""
    if 'tree' in rec:
        yield rec
    for key in ('children', 'dz_split', 'mu_split'):
        for ch in rec.get(key, []):
            yield from records(ch)


def dual_minus(rec):
    rec = copy.deepcopy(rec)
    for r in records(rec):
        du = first_dual(r['tree'])
        if du is not None:
            du['Y'] = du['Y']*999//1000
            return rec
    return None


def run(src, rec, mode):
    LV.inside_input = orig_inside; LV.build_row = orig_build; LV._ROWS.clear()
    if mode == 'far+':
        LV.inside_input = patch_input(far_plus)
    elif mode == 'G+':
        LV.inside_input = patch_input(g_plus)
    elif mode == 'first+':
        LV.inside_input = patch_input(first_plus)
    elif mode == 'final0':
        LV.inside_input = patch_input(final_zero)
    elif mode == 'd+':
        LV.build_row = row_patch(d_plus)
    elif mode == 'v-':
        LV.build_row = row_patch(v_minus)
    elif mode == 'dualY-':
        rec = dual_minus(rec)
        if rec is None:
            return 'n/a'
    try:
        m, n = DR.verify_leaf(src, L, rec, outside=False)
        return 'pass %.7f' % (m/S)
    except (AssertionError, KeyError, ZeroDivisionError) as e:
        return 'caught ' + repr(e)[:60]
    finally:
        LV.inside_input = orig_inside; LV.build_row = orig_build; LV._ROWS.clear()


MODES = ['base', 'far+', 'G+', 'first+', 'd+', 'v-', 'dualY-', 'final0']
from endgame import specs, with_height
import collective_cover as cc
for idx in map(int, sys.argv[1].split(',')):
    GV.STATE['cap'].clear(); GV.STATE['ncap'].clear()
    cc.verify_tree(with_height(specs()[idx], 'inside'), cc.load_root(idx)['inside'])
    cert = GV.load_cert(idx, 'inside')
    srcs = list(GV.STATE['cap'])
    assert len(srcs) == len(cert['leaves'])
    for j, (src, rec) in enumerate(zip(srcs, cert['leaves'])):
        if 'maximum' not in rec:
            continue
        t = time.time()
        res = {m: run(src, rec, m) for m in MODES}
        print(json.dumps(dict(root=idx, leaf=j, maximum=rec['maximum']/S, results=res,
                              seconds=round(time.time()-t))), flush=True)
