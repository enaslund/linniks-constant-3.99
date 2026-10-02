"""Certify every leaf of one corpus of the graded-near proof at a target exponent.

  python3 computations/graded/graded_batch.py --kind inside   --leaves <captured> --L 3.99 --out <dir>
  python3 computations/graded/graded_batch.py --kind outside  --leaves <captured> --L 3.99 --out <dir>
  python3 computations/graded/graded_batch.py --kind nodes    --leaves <captured identities> --L 3.99 --out <dir>

Captured inputs are pickles written while replaying the repository's verified 4.30
trees (see verify_all.py); the certificates never trust them: the replay regenerates
every leaf from the repository's own source trees.  One output file per root.
"""
import sys, os, json, gzip, pickle, time, argparse
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1'); os.environ.setdefault('OMP_NUM_THREADS', '1')
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
HERE = Path(__file__).resolve().parent


def node_sources(contexts):
    """Distinct identities nodes (consecutive branch contexts share one 4.33 template)."""
    import graded_leaves as LV
    out = []; last = None
    for c in contexts:
        key = json.dumps(LV.LD.spec_of(c['base']), sort_keys=True, default=str)
        if key != last:
            out.append(c['base']); last = key
    return out


def job(args):
    path, idx, L, outdir, kind = args
    sys.path.insert(0, str(HERE))
    import graded_driver as DR
    dest = Path(outdir)/f'{idx:04d}.json.gz'
    if dest.exists():
        return idx, 'cached', None
    if os.environ.get('GRADED_LOCK') == '1':
        try:
            os.close(os.open(str(dest)+'.lock', os.O_CREAT | os.O_EXCL | os.O_WRONLY))
        except FileExistsError:
            return idx, 'cached', None
    t = time.time()
    data = pickle.load(open(path, 'rb'))
    srcs = node_sources(data) if kind == 'nodes' else [d['input'] for d in data]
    out = dict(id=idx, L=L, kind=kind, leaves=[], method='graded-near')
    status = 'ok'
    for j, src in enumerate(srcs):
        logs = []
        try:
            rec = DR.certify_with_repairs(src, L, outside=(kind == 'outside'), log=lambda m: logs.append(repr(m)),
                                          fail_fast=os.environ.get('GRADED_FAIL_FAST', '1') == '1')
            rec['index'] = j; rec['log'] = logs
            out['leaves'].append(rec)
        except Exception as e:
            status = 'fail'
            out['leaves'].append(dict(index=j, failure=repr(e)[:500], log=logs))
    out['seconds'] = time.time()-t
    out['status'] = status
    with gzip.open(dest, 'wt') as f:
        json.dump(out, f, separators=(',', ':'))
    mx = max([l.get('maximum', -1) for l in out['leaves']]+[-1])
    return idx, status, mx


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--kind', choices=('inside', 'outside', 'nodes'), required=True)
    ap.add_argument('--leaves', required=True)
    ap.add_argument('--L', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--ids', default='')
    ap.add_argument('--desc', action='store_true')
    a = ap.parse_args()
    Path(a.out).mkdir(parents=True, exist_ok=True)
    files = sorted(Path(a.leaves).glob('*.pkl'))
    jobs = [(str(f), int(f.stem), a.L, a.out, a.kind) for f in files]
    if a.ids:                                    # given order (hardest first, say)
        order = [int(x) for x in a.ids.split(',')]
        by = {j[1]: j for j in jobs}
        jobs = [by[i] for i in order if i in by]
    jobs = [j for j in jobs if os.path.getsize(j[0]) > 0]
    if a.desc:
        jobs = jobs[::-1]
    t = time.time(); n = 0; fails = 0; worst = -1
    with ProcessPoolExecutor(max_workers=a.workers) as ex:
        for idx, status, mx in ex.map(job, jobs, chunksize=1):
            n += 1; fails += status == 'fail'
            if mx is not None:
                worst = max(worst, mx)
            if n % 20 == 0 or status == 'fail':
                print(n, len(jobs), 'id', idx, status, 'worst', worst/1e16 if worst > 0 else worst, 'fails', fails,
                      'sec', round(time.time()-t), flush=True)
    print('DONE', n, 'fails', fails, 'worst', worst/1e16 if worst > 0 else worst)
