"""Replay of the graded-near proof at a target exponent (research/PROOF.md §8).

The repository's verified 4.30 source trees supply the case tree.  They are
traversed by their own verifiers, which re-check every location row, exclusion
and split.  Every LP leaf met on the way is intercepted and replaced:

  inside scenario leaf (core, far, collective): the regular inside model of its case
      at L, certified by the stored graded record;
  inside_repair 'identities' node: not descended; the regular inside model of the
      node's own case at L, certified by the stored graded record (the hidden-family
      branches are not used);
  outside-buffer leaf: the regular outside model at L, certified by the stored record.

Every certificate tree is checked with exact integers (graded_cert.verify_tree).

  python3 computations/graded/graded_verify.py --L 3.99 --inside <corpus> --nodes <corpus> \
      --outside <corpus> --workers 4

A corpus is a directory of per-root files or a packed JSON-lines file (graded_pack.py).
"""
import sys, os, gzip, json, time, argparse
os.environ.setdefault('OPENBLAS_NUM_THREADS', '1'); os.environ.setdefault('OMP_NUM_THREADS', '1')
if not __debug__:
    raise RuntimeError('assertions must be enabled')
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor
HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
S = 10**16
IDENTITIES_NODES = 233
STATE = {}


def setup(kind, L, sources):
    sys.path.insert(0, str(ROOT/'frontier')); sys.path.insert(0, str(ROOT/'core'/'code'))
    sys.path.insert(0, str(ROOT/'near'/'code')); sys.path.insert(0, str(HERE))
    STATE.update(kind=kind, L=L, sources={k: Path(v) for k, v in sources.items()}, cap=[], ncap=[])
    if kind == 'inside':
        import far_enclosures  # noqa: F401
        import verify_progress
        orig = verify_progress.scenario

        def hook(rec):
            out = orig(rec)
            STATE['cap'].append(rec['input'])
            return out
        verify_progress.scenario = hook
        import collective_cover, inside_repair, collective_model  # noqa: F401
        inside_repair.verify_core = hook
        collective_model.scenario = hook
        lorig = inside_repair.verify_leaf

        def lhook(sp, L4, sourcepar, node):
            if set(node) != {'identities', 'maximum'}:
                return lorig(sp, L4, sourcepar, node)
            # the node's own case, as the repository builds it before its hidden-family branches
            par0 = dict(sourcepar)
            if par0['method'] == 'pair':
                par0 = dict(inside_repair.SINGLE_PAR)
            STATE['ncap'].append(inside_repair.make_endgame(sp, '4.33', par0, 200))
            return [dict(maximum=node['maximum'], branches=0, checks=0)]
        inside_repair.verify_leaf = lhook
        # collective_cover imported verify_leaf by name; its fallthrough must be intercepted too
        if getattr(collective_cover, 'verify_leaf', None) is lorig:
            collective_cover.verify_leaf = lhook

        def no_branch(*args, **kw):
            raise AssertionError('an identities branch escaped interception')
        inside_repair.verify_branch = no_branch
    else:
        os.chdir(str(ROOT/'near'/'code'))
        import first_outside_blocks as fob
        import outside_regime as orr
        orig = fob.first_verify

        def hook(inp, rows):
            out = orig(inp, rows)
            STATE['cap'].append(inp)
            return out
        orr.first_verify = hook


def load_cert(idx, key):
    src = STATE['sources'][key]
    if src.is_dir():
        fn = src/f'{idx:04d}.json.gz'
        return json.load(gzip.open(fn, 'rt')) if fn.exists() else None
    # A packed corpus has one root per line, sorted by id (graded_pack).  It is streamed rather than
    # loaded whole: within a worker the requested ids increase, so one pass suffices; a request for an
    # id at or below the last one reopens the file.  Memory stays at one record per worker.
    st = STATE.get('packed_'+key)
    if st is None or (st['last'] is not None and idx <= st['last']):
        if st is not None:
            st['f'].close()
        st = STATE['packed_'+key] = dict(f=gzip.open(src, 'rt'), last=None, pending=None)
    st['last'] = idx
    while True:
        d = st['pending']
        st['pending'] = None
        if d is None:
            line = st['f'].readline()
            if not line:
                return None
            d = json.loads(line)
        if d['id'] == idx:
            return d
        if d['id'] > idx:
            st['pending'] = d
            return None


def node_bases(bases):
    """One source per identities node; consecutive equal cases collapse (graded_batch.node_sources)."""
    import graded_leaves as LV
    out = []; last = None
    for b in bases:
        key = json.dumps(LV.LD.spec_of(b), sort_keys=True, default=str)
        if key != last:
            out.append(b); last = key
    return out


def check_records(idx, key, srcs, outside):
    import graded_driver as DR
    if not srcs:
        return 0, -1, 0
    cert = load_cert(idx, key)
    assert cert is not None, ('missing certificate file', key, idx)
    assert cert['id'] == idx and cert['L'] == STATE['L'] and cert.get('method') == 'graded-near', (key, idx)
    assert cert['kind'] == {'inside': 'inside', 'nodes': 'nodes', 'outside': 'outside'}[key], (key, idx)
    assert cert['status'] == 'ok' and len(cert['leaves']) == len(srcs), ('leaf count', key, idx)
    mx = -1; nb = 0
    for j, (src, rec) in enumerate(zip(srcs, cert['leaves'])):
        assert rec['index'] == j, (key, idx, j)
        m, n = DR.verify_leaf(src, STATE['L'], rec, outside=outside)
        assert m < S, (key, idx, j, m)
        mx = max(mx, m); nb += n
    return len(srcs), mx, nb


def check_root(idx_or_record):
    STATE['cap'].clear(); STATE['ncap'].clear()
    if STATE['kind'] == 'inside':
        import collective_cover as cc
        from endgame import specs, with_height
        idx = idx_or_record
        cc.verify_tree(with_height(specs()[idx], 'inside'), cc.load_root(idx)['inside'])
        n1, m1, b1 = check_records(idx, 'inside', list(STATE['cap']), False)
        n2, m2, b2 = check_records(idx, 'nodes', node_bases(STATE['ncap']), False)
        return idx, n1+n2, max(m1, m2), b1+b2, len(STATE['ncap'])
    import outside_regime as orr
    rt = idx_or_record; idx = rt['id']
    orr.verify_job((rt, '4.30'))
    n, m, b = check_records(idx, 'outside', list(STATE['cap']), True)
    return idx, n, m, b, 0


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--L', required=True)
    ap.add_argument('--inside', required=True, help='certificates of inside scenario leaves')
    ap.add_argument('--nodes', required=True, help='certificates of inside identities nodes')
    ap.add_argument('--outside', required=True, help='certificates of outside-buffer leaves')
    ap.add_argument('--workers', type=int, default=4)
    ap.add_argument('--inside-roots', default=None, help='partial replay: comma-separated inside roots (no report)')
    ap.add_argument('--outside-roots', default=None, help='partial replay: comma-separated outside roots (no report)')
    a = ap.parse_args()
    for key in ('inside', 'nodes', 'outside'):          # absolute: the outside replay changes directory
        setattr(a, key, str(Path(getattr(a, key)).resolve()))
    t = time.time(); report = dict(L=a.L, method='graded-near')
    partial = a.inside_roots is not None or a.outside_roots is not None
    for kind in ('inside', 'outside'):
        sel = a.inside_roots if kind == 'inside' else a.outside_roots
        if partial and not sel:
            continue
        only = set(int(x) for x in sel.split(',')) if partial else None
        sys.path.insert(0, str(ROOT/'core'/'code'))
        from endgame import specs
        assert len(specs()) == 2768
        if kind == 'inside':
            jobs = list(range(len(specs())))
            sources = dict(inside=a.inside, nodes=a.nodes)
        else:
            sys.path.insert(0, str(ROOT/'near'/'code')); os.chdir(str(ROOT/'near'/'code'))
            from certificate_io import load_outside, validate_outside_records
            jobs = load_outside('4.30')
            validate_outside_records(jobs, '4.30')          # every non-rr specification, in order
            sources = dict(outside=a.outside)
        if only is not None:
            jobs = [j for j in jobs if (j if kind == 'inside' else j['id']) in only]
        mx = -1; leaves = 0; boxes = 0; n = 0; nodes = 0
        with ProcessPoolExecutor(max_workers=a.workers, initializer=setup, initargs=(kind, a.L, sources)) as ex:
            for idx, nl, m, nb, nn in ex.map(check_root, jobs, chunksize=2):
                n += 1; leaves += nl; boxes += nb; mx = max(mx, m); nodes += nn
                if n % 200 == 0 or only is not None:
                    print(kind, n, len(jobs), 'id', idx, 'max', mx/S, 'sec', round(time.time()-t), flush=True)
        report[kind] = dict(roots=n, leaves=leaves, boxes=boxes, maximum_numerator=mx, maximum=mx/S)
        if kind == 'inside':
            report[kind]['identities_nodes'] = nodes
            if only is None:
                # the verified 4.30 inside corpus has 233 identities nodes, all under repair nodes
                assert nodes == IDENTITIES_NODES, ('identities nodes intercepted', nodes)
        print(kind, report[kind], flush=True)
    report['seconds'] = time.time()-t
    if partial:
        print('partial replay passed', json.dumps(report))
        sys.exit(0)
    report['status'] = ('PASS: every LP leaf and identities node of the verified 4.30 inside and outside source '
                        'trees has a verified graded-near certificate at L')
    (HERE/f'verification_{a.L}.json').write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))
