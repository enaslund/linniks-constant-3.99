"""Complete source cover combining retained and collective-envelope witnesses.

The prior far_full corpus stays unchanged. New roots are overlays, later packed
as a self-contained corpus. Every accepted source leaf is regenerated; final
verification independently traverses all original sources and all thresholds.
"""
import argparse, ast, copy, gzip, hashlib, json, time
if not __debug__:
    raise RuntimeError('Assertions must be enabled for proof verification')
from concurrent.futures import ProcessPoolExecutor, as_completed
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path
import far_full as legacy
from far_storage import canonical_root, root_digest, digest_rows, CANONICAL_RULE
from inside_integrate import unresolved_sources
from inside_repair import verify_leaf, regenerate_location_row, real_update
from inside_complex_rows import regenerate_complex_row, complex_update
from collective_model import verify_record

HERE = Path(__file__).resolve().parent
L = '4.30'
DIRECTORY = HERE/'collective_full_4.30'
PACKED = DIRECTORY/'roots.jsonl.gz'
S = 10**16


def dump(path, data):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix('.tmp')
    if path.suffix == '.gz':
        with gzip.open(tmp, 'wt') as stream:
            json.dump(data, stream, separators=(',', ':'), allow_nan=False)
    else:
        tmp.write_text(json.dumps(data, indent=2, allow_nan=False)+'\n')
    tmp.replace(path)


def verify_inner(sp, exponent, parameters, node):
    if 'collective' in node:
        assert set(node) == {'collective', 'maximum'}
        report = verify_record(sp, exponent, node['collective'])
        assert report['maximum'] == node['maximum']
        report.update(kind='collective', L=exponent)
        return [report]
    if 'split' in node:
        assert set(node) == {'split', 'mid', 'children', 'maximum'}
        assert len(node['children']) == 2
        scopes = legacy.split_new(sp, node['split'], node['mid'])
        reports = []
        for scope, child in zip(scopes, node['children']):
            reports += verify_inner(scope, exponent, parameters, child)
        assert node['maximum'] == max((r['maximum'] for r in reports), default=-1)
        return reports
    for kind, regenerate, update in (
        ('real_location', regenerate_location_row, real_update),
        ('complex_location', regenerate_complex_row, complex_update),
    ):
        if kind not in node:
            continue
        row = node[kind]
        assert regenerate(row) == row
        scope = update(sp, row)
        if scope is None:
            assert node == {kind: row, 'excluded': True, 'maximum': -1}
            return []
        assert set(node) == {kind, 'child', 'maximum'}
        reports = verify_inner(scope, exponent, parameters, node['child'])
        assert node['maximum'] == max((r['maximum'] for r in reports), default=-1)
        return reports
    return verify_leaf(sp, exponent, parameters, node)


def verify_tree(sp, node, target=L):
    if 'split' in node:
        assert set(node) == {'split', 'mid', 'children'} and len(node['children']) == 2
        scopes = legacy.split_new(sp, node['split'], node['mid'])
        reports = []
        for scope, child in zip(scopes, node['children']):
            reports += verify_tree(scope, child, target)
        return reports
    if 'collective_repair' in node:
        assert set(node) == {'collective_repair'}
        record = node['collective_repair']
        assert set(record) == {'L', 'parameters', 'tree'}
        legacy.eligible_exponent(record['L'], target)
        return verify_inner(sp, record['L'], record['parameters'], record['tree'])
    return legacy.verify_tree_new(sp, node, target)


def tree_maximum(node):
    if 'split' in node:
        return max(tree_maximum(child) for child in node['children'])
    if 'collective_repair' in node:
        return node['collective_repair']['tree'].get('maximum', -1)
    return max((r['maximum'] for r in legacy.counts(node)), default=-1)


@lru_cache(maxsize=4)
def read_initial(path, mtime, size):
    return json.loads(Path(path).read_text())


def initial_manifest():
    path = DIRECTORY/'initial.json'
    stat = path.stat()
    return read_initial(str(path.resolve()), stat.st_mtime_ns, stat.st_size)


@lru_cache(maxsize=2)
def packed_rows(path, mtime, size):
    with gzip.open(path, 'rb') as stream:
        rows = tuple(canonical_root(json.loads(line)) for line in stream)
    assert len(rows) == len(legacy.specs())
    for idx, row in enumerate(rows):
        value = json.loads(row)
        assert value['id'] == idx and value['target'] == L
    return rows


def load_root(idx):
    assert type(idx) is int and 0 <= idx < len(legacy.specs())
    file = DIRECTORY/f'{idx:04d}.json.gz'
    if file.exists():
        with gzip.open(file, 'rt') as stream:
            root = json.load(stream)
    elif PACKED.exists():
        stat = PACKED.stat()
        root = json.loads(packed_rows(str(PACKED.resolve()), stat.st_mtime_ns, stat.st_size)[idx])
    else:
        root = legacy.load_root(idx, L)
        assert root_digest(root) == initial_manifest()['root_sha256'][str(idx)]
    assert root['id'] == idx and root['target'] == L
    return root


def load_roots():
    return [load_root(idx) for idx in range(len(legacy.specs()))]


def corpus_digest():
    return digest_rows((root['id'], root_digest(root)) for root in load_roots())


def initialize():
    assert not (DIRECTORY/'initial.json').exists()
    roots = legacy.load_roots(L)
    record = dict(date=datetime.now(timezone.utc).isoformat(), L=L,
                  source_corpus_sha256=digest_rows((r['id'], root_digest(r)) for r in roots),
                  root_sha256={str(r['id']): root_digest(r) for r in roots},
                  scope='Frozen prior partial source corpus; new repairs use separate overlays')
    dump(DIRECTORY/'initial.json', record)
    return inventory()


def inventory():
    scopes = []
    roots = load_roots()
    for root in roots:
        for path, (sp, failure) in unresolved_sources(root).items():
            scopes.append(dict(id=root['id'], path=path, spec=sp,
                               parameters=failure['parameters'], lambda_den=failure['lambda_den'],
                               current_root_sha256=root_digest(root)))
    report = dict(L=L, source_roots=len(roots), complete_roots=sum(r['all_pass'] for r in roots),
                  pending_roots=len({s['id'] for s in scopes}), pending_leaves=len(scopes),
                  corpus_sha256=digest_rows((r['id'], root_digest(r)) for r in roots),
                  scope='Coverage inventory only; complete numerical replay still required')
    dump(DIRECTORY/'pending.json.gz', dict(report, scopes=scopes))
    dump(DIRECTORY/'summary.json', report)
    return report


def checked_overlay(base, current, record):
    assert base['id'] == current['id'] == record['id']
    assert base['target'] == current['target'] == record['L'] == L
    assert record['source_root_sha256'] == root_digest(base)
    original, pending = unresolved_sources(base), unresolved_sources(current)
    assert record['source_failed_leaves'] == len(original)
    assert record['attempted_leaves'] == len(record['attempts'])
    seen, replacements, reports = set(), {}, []
    passed = 0
    for attempt in record['attempts']:
        path = attempt['path']
        assert path in original and path not in seen
        seen.add(path)
        sp, failure = original[path]
        assert attempt['spec'] == sp and attempt['parameters'] == failure['parameters']
        assert type(attempt['passed']) is bool
        if not attempt['passed']:
            continue
        passed += 1
        node = attempt['node']
        assert len(node) == 1 and next(iter(node)) in ('repair', 'collective_repair')
        wrapper = next(iter(node.values()))
        assert set(wrapper) == {'L', 'parameters', 'tree'}
        assert wrapper['L'] == L and wrapper['parameters'] == failure['parameters']
        checked = verify_tree(sp, node)
        assert attempt['maximum'] == max((r['maximum'] for r in checked), default=-1)
        assert attempt['maximum'] == wrapper['tree'].get('maximum', -1)
        assert attempt['intervals'] == sum(r['branches'] for r in checked)
        assert attempt['checks'] == sum(r['checks'] for r in checked)
        reports += checked
        if path in pending:
            assert pending[path] == original[path]
            replacements[path] = node
    assert record['repaired_leaves'] == passed
    assert record['all_original_failures_repaired'] == (passed == len(original))
    def replace(node, path):
        if path in replacements:
            return copy.deepcopy(replacements[path])
        if 'split' in node:
            return dict(split=node['split'], mid=node['mid'],
                        children=[replace(child, path+str(i)) for i, child in enumerate(node['children'])])
        return copy.deepcopy(node)
    tree = replace(current['inside'], '')
    failures = [f for path, (_, f) in pending.items() if path not in replacements]
    result = dict(current, inside=tree, failures=failures, all_pass=not failures,
                  maximum=tree_maximum(tree))
    # Old proposer-specific counts are no longer a reliable description of the new tree.
    if replacements:
        result.pop('kinds', None)
        result.pop('reused_4_30', None)
    else:
        result = copy.deepcopy(current)
    assert list(unresolved_sources(result)) == [p for p in pending if p not in replacements]
    report = dict(id=base['id'], installed_leaves=len(replacements),
                  remaining_leaves=len(failures), all_pass=not failures,
                  intervals=sum(r['branches'] for r in reports), checks=sum(r['checks'] for r in reports),
                  source_root_sha256=root_digest(base), current_root_sha256=root_digest(current),
                  result_root_sha256=root_digest(result))
    return result, report


def integrate_file(path):
    start = time.time()
    with gzip.open(path, 'rt') as stream:
        record = json.load(stream)
    idx = record['id']
    base, current = legacy.load_root(idx, L), load_root(idx)
    assert root_digest(base) == initial_manifest()['root_sha256'][str(idx)]
    result, report = checked_overlay(base, current, record)
    assert root_digest(load_root(idx)) == report['current_root_sha256'], 'Concurrent root writer'
    if report['installed_leaves']:
        dump(DIRECTORY/f'{idx:04d}.json.gz', result)
    return dict(report, file=str(path.relative_to(HERE)), seconds=time.time()-start)


def verification_commitments():
    commitments = legacy.verification_commitments()
    pending, seen = [Path(__file__)], set()
    while pending:
        path = pending.pop()
        if path in seen:
            continue
        seen.add(path)
        for node in ast.walk(ast.parse(path.read_text())):
            modules = ([node.module] if isinstance(node, ast.ImportFrom) and node.module else
                       [a.name for a in node.names] if isinstance(node, ast.Import) else [])
            for module in modules:
                child = HERE/(module.split('.')[0]+'.py')
                if child.exists() and child not in seen:
                    pending.append(child)
    for path in seen:
        commitments[str(path.relative_to(HERE.parents[1]))] = hashlib.sha256(path.read_bytes()).hexdigest()
    return dict(sorted(commitments.items()))


def verify_job(idx):
    root = load_root(idx)
    assert root['all_pass'] and not root['failures']
    assert not unresolved_sources(root)
    reports = verify_tree(legacy.with_height(legacy.specs()[idx], 'inside'), root['inside'])
    maximum = max((r['maximum'] for r in reports), default=-1)
    assert maximum == root['maximum'] and maximum < S
    return dict(id=idx, maximum=maximum, leaves=len(reports),
                branches=sum(r['branches'] for r in reports), checks=sum(r['checks'] for r in reports),
                root_sha256=root_digest(root))


def pack():
    roots = load_roots()
    raw = [canonical_root(root) for root in roots]
    digest = corpus_digest()
    tmp = PACKED.with_suffix('.tmp')
    with tmp.open('wb') as file:
        with gzip.GzipFile(filename='', fileobj=file, mode='wb', mtime=0) as stream:
            for row in raw:
                stream.write(row+b'\n')
    with gzip.open(tmp, 'rb') as stream:
        assert [canonical_root(json.loads(line)) for line in stream] == raw
    assert corpus_digest() == digest
    tmp.replace(PACKED)
    for idx in range(len(roots)):
        path = DIRECTORY/f'{idx:04d}.json.gz'
        if path.exists():
            with gzip.open(path, 'rt') as stream:
                assert canonical_root(json.load(stream)) == raw[idx]
            path.unlink()
    assert corpus_digest() == digest
    report = dict(logical_identity_verified=True, corpus_sha256=digest,
                  packed_sha256=hashlib.sha256(PACKED.read_bytes()).hexdigest(),
                  packed_bytes=PACKED.stat().st_size, source_roots=len(roots),
                  all_roots_pass=all(root['all_pass'] for root in roots))
    dump(DIRECTORY/'transport.json', report)
    return report


def main():
    ap = argparse.ArgumentParser()
    group = ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--init', action='store_true')
    group.add_argument('--inventory', action='store_true')
    group.add_argument('--integrate')
    group.add_argument('--verify', action='store_true')
    group.add_argument('--pack', action='store_true')
    ap.add_argument('--ids', default='')
    ap.add_argument('--workers', type=int, default=4)
    a = ap.parse_args()
    assert a.workers > 0
    if a.init:
        print(json.dumps(initialize())); return
    if a.inventory:
        print(json.dumps(inventory())); return
    if a.pack:
        print(json.dumps(pack())); return
    wanted = set(map(int, a.ids.split(','))) if a.ids else None
    start = time.time()
    if a.integrate:
        source = HERE/a.integrate
        files = sorted(source.glob('[0-9]*.json.gz'))
        files = [p for p in files if wanted is None or int(p.name.split('.')[0]) in wanted]
        assert files and all(p.name == f'{int(p.name.split(".")[0]):04d}.json.gz' for p in files)
        assert len({p.name for p in files}) == len(files)
        results = []
        with ProcessPoolExecutor(max_workers=a.workers) as pool:
            for future in as_completed([pool.submit(integrate_file, p) for p in files]):
                row = future.result(); results.append(row); print(json.dumps(row), flush=True)
        report = dict(records=len(results), installed_leaves=sum(r['installed_leaves'] for r in results),
                      reports=sorted(results, key=lambda r:r['id']), inventory=inventory(), seconds=time.time()-start)
        dump(source/f'collective_integration_{time.time_ns()}.json', report)
        print(json.dumps({k:v for k,v in report.items() if k != 'reports'})); return
    before = verification_commitments()
    checks = legacy.global_checks(L)
    ids = sorted(wanted) if wanted is not None else list(range(len(legacy.specs())))
    results = []
    with ProcessPoolExecutor(max_workers=a.workers) as pool:
        for future in as_completed([pool.submit(verify_job, idx) for idx in ids]):
            row = future.result(); results.append(row)
            if len(results) % 50 == 0:
                print(json.dumps(dict(done=len(results), id=row['id'], seconds=time.time()-start)), flush=True)
    results.sort(key=lambda r:r['id'])
    after = verification_commitments()
    assert before == after, 'Proof inputs or code changed during replay'
    complete = [r['id'] for r in results] == list(range(len(legacy.specs())))
    digest = digest_rows((r['id'], r['root_sha256']) for r in results)
    if complete:
        assert digest == corpus_digest(), 'Corpus changed during replay'
    maximum = max(r['maximum'] for r in results)
    report = dict(date=datetime.now(timezone.utc).isoformat(), target=L, verified=True,
                  all_pass=complete, complete_source_enumeration=complete, source_roots=len(results),
                  maximum=maximum/S, maximum_numerator=maximum, scale=S,
                  leaves=sum(r['leaves'] for r in results), branches=sum(r['branches'] for r in results),
                  checks=sum(r['checks'] for r in results), source_input_checks=checks,
                  certificate_corpus_sha256=digest, corpus_hash_rule=CANONICAL_RULE,
                  commitments_before=before, commitments_after=after, commitments_unchanged=True,
                  source_sha256=hashlib.sha256(legacy.SOURCE.read_bytes()).hexdigest(),
                  seconds=time.time()-start)
    dump(DIRECTORY/('verification.json' if complete else f'partial_verification_{time.time_ns()}.json'), report)
    print(json.dumps({k:v for k,v in report.items() if not k.startswith('commitments_') and k != 'source_input_checks'}))


if __name__ == '__main__':
    main()
