"""Pack per-root graded-near certificate files into one ordered JSON-lines corpus (logs removed).

  python3 computations/graded/graded_pack.py <dest.jsonl.gz> <cert dir> [<repair dir> ...] --kind inside --expect N

Later directories override earlier ones root by root (re-certified roots).  Every packed
root must have status ok, method graded-near and the requested kind.
"""
import gzip, json, glob, os, hashlib, argparse

ap = argparse.ArgumentParser()
ap.add_argument('dest')
ap.add_argument('src', nargs='+')
ap.add_argument('--kind', choices=('inside', 'nodes', 'outside'), required=True)
ap.add_argument('--expect', type=int, default=0, help='expected number of roots')
a = ap.parse_args()
roots = {}
for src in a.src:
    for fn in glob.glob(os.path.join(src, '*.json.gz')):
        roots[int(os.path.basename(fn).split('.')[0])] = fn
assert not a.expect or len(roots) == a.expect, (len(roots), a.expect)


def strip(rec):
    rec.pop('log', None)
    for key in ('mu_split', 'dz_split', 'children'):
        for sub in rec.get(key, []):
            strip(sub)
    return rec


leaves = boxes = 0
mx = -1
with gzip.open(a.dest, 'wt') as out:
    for idx in sorted(roots):
        d = json.load(gzip.open(roots[idx], 'rt'))
        assert d['status'] == 'ok' and d['id'] == idx, (roots[idx], d['status'])
        assert d.get('method') == 'graded-near' and d['kind'] == a.kind, (roots[idx], d.get('method'), d['kind'])
        for l in d['leaves']:
            strip(l)
            if l.get('excluded_by_location'):
                continue
            assert 'maximum' in l, (roots[idx], l.get('failure'))
            leaves += 1
            boxes += l['boxes']
            mx = max(mx, l['maximum'])
        d.pop('seconds', None)
        out.write(json.dumps(d, separators=(',', ':'), sort_keys=True)+'\n')
h = hashlib.sha256(open(a.dest, 'rb').read()).hexdigest()
print(json.dumps(dict(kind=a.kind, roots=len(roots), leaves=leaves, boxes=boxes, maximum_numerator=mx,
                      maximum=mx/1e16, sha256=h), indent=1))
