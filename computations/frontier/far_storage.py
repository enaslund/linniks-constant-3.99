"""Lossless transport of frontier roots, independent of numerical verification.

Canonical commitments bind parsed root contents, so packing changes transport
without changing any checked scalar, subdivision, dual, or source scope.
"""
import gzip,hashlib,json
from datetime import datetime,timezone
from functools import lru_cache
from pathlib import Path

if not __debug__:raise RuntimeError('Assertions must be enabled for certificate transport and verification')

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'core/results/certificate_4.33.jsonl.gz'
CANONICAL_RULE=('SHA-256 of increasing-ID lines: four-digit ID.json, space, '
                'SHA-256 of UTF-8 JSON with sorted keys, compact separators, '
                'ASCII escapes and no NaN, newline')
LEGACY_RULE=('SHA-256 of increasing-ID lines: four-digit ID.json.gz, space, '
             'SHA-256 of that gzip file, newline')


def canonical_root(root):
    return json.dumps(root,sort_keys=True,separators=(',',':'),ensure_ascii=True,
                      allow_nan=False).encode('utf-8')


def root_digest(root):
    return hashlib.sha256(canonical_root(root)).hexdigest()


def digest_rows(rows):
    """Combine (id, canonical-root SHA-256) pairs in the stated order."""
    return hashlib.sha256(''.join(f'{idx:04d}.json {digest}\n'for idx,digest in rows).encode()).hexdigest()


@lru_cache(None)
def source_count():
    with gzip.open(SOURCE,'rt')as stream:ids=[json.loads(line)['id']for line in stream]
    assert ids==list(range(len(ids)))
    return len(ids)


@lru_cache(maxsize=4)
def packed_records(path,L,mtime,size):
    records=[]
    with gzip.open(path,'rb')as stream:
        for idx,line in enumerate(stream):
            root=json.loads(line)
            assert root['id']==idx and root['target']==L
            records.append(canonical_root(root))
    assert len(records)==source_count()
    return tuple(records)


def load_root(idx,L):
    assert type(idx)==int and 0<=idx<source_count()
    workfile=HERE/f'far_full_{L}'/f'{idx:04d}.json.gz'
    if workfile.exists():
        with gzip.open(workfile,'rt')as stream:root=json.load(stream)
    else:
        packed=HERE/f'far_full_{L}.jsonl.gz';stat=packed.stat()
        root=json.loads(packed_records(str(packed.resolve()),L,stat.st_mtime_ns,stat.st_size)[idx])
    assert root['id']==idx and root['target']==L
    return root


def load_roots(L):
    return [load_root(idx,L)for idx in range(source_count())]


def corpus_digest(L):
    return digest_rows((root['id'],root_digest(root))for root in load_roots(L))


def legacy_corpus_digest(L):
    lines=[]
    for idx in range(source_count()):
        path=HERE/f'far_full_{L}'/f'{idx:04d}.json.gz'
        lines.append(f'{idx:04d}.json.gz {hashlib.sha256(path.read_bytes()).hexdigest()}\n')
    return hashlib.sha256(''.join(lines).encode()).hexdigest()


def pack_corpus(L):
    """Check transport identity; carry forward a replay only if its digest matches.

    Call after all writers for this target have stopped. Incomplete exploratory
    roots may also be packed; this never marks them numerically verified.
    """
    roots=load_roots(L);before=[canonical_root(root)for root in roots]
    digest=digest_rows((i,hashlib.sha256(row).hexdigest())for i,row in enumerate(before))
    directory=HERE/f'far_full_{L}';report_file=directory/'verification.json'
    report=None;prior_bytes=None;legacy=None
    if report_file.exists():
        prior_bytes=report_file.read_bytes();report=json.loads(prior_bytes)
    verified=bool(report and report.get('verified')and report.get('all_pass')
                  and report.get('complete_source_enumeration'))
    if verified:
        assert report['target']==L and report['source_roots']==len(roots)
        rule=report['corpus_hash_rule']
        if rule==LEGACY_RULE:
            legacy=legacy_corpus_digest(L)
            assert report['certificate_corpus_sha256']==legacy,'Replay does not bind the current working corpus'
        else:
            assert rule==CANONICAL_RULE
            assert report['certificate_corpus_sha256']==digest,'Replay does not bind the current logical corpus'
    packed=HERE/f'far_full_{L}.jsonl.gz';temporary=packed.with_suffix('.tmp')
    with temporary.open('wb')as raw:
        with gzip.GzipFile(filename='',fileobj=raw,mode='wb',mtime=0)as stream:
            for row in before:stream.write(row+b'\n')
    with gzip.open(temporary,'rb')as stream:
        after=[canonical_root(json.loads(line))for line in stream]
    assert after==before,'Packing changed a root, its order, or source cardinality'
    assert corpus_digest(L)==digest,'Working roots changed during packing'
    packed_sha=hashlib.sha256(temporary.read_bytes()).hexdigest()
    transport=dict(date=datetime.now(timezone.utc).date().isoformat(),target=L,source_roots=len(roots),logical_identity_verified=True,
        numerical_replay_carried_forward=verified,canonical_corpus_sha256=digest,
        corpus_hash_rule=CANONICAL_RULE,legacy_corpus_sha256=legacy,
        packed_file=packed.name,packed_bytes=temporary.stat().st_size,packed_sha256=packed_sha,
        all_roots_marked_pass=all(root['all_pass']and not root['failures']for root in roots))
    if verified:
        transport['previous_verification']=report
        transport['previous_verification_file_sha256']=hashlib.sha256(prior_bytes).hexdigest()
        # Keep the exact prior report available in the transport record as well.
        # This also checks its reconstruction, preserving the historical digest.
        reconstructed=(json.dumps(report,indent=2,allow_nan=False)+'\n').encode()
        assert reconstructed==prior_bytes,'Unexpected previous report encoding'
    temporary.replace(packed)
    if verified:
        new=dict(report,certificate_corpus_sha256=digest,corpus_hash_rule=CANONICAL_RULE,
                 transport=dict(file=packed.name,packed_sha256=packed_sha,
                                identity_report=f'far_full_{L}/transport.json'))
        tmp=report_file.with_suffix('.tmp');tmp.write_text(json.dumps(new,indent=2,allow_nan=False)+'\n');tmp.replace(report_file)
    transport_file=directory/'transport.json';tmp=transport_file.with_suffix('.tmp')
    tmp.write_text(json.dumps(transport,indent=2,allow_nan=False)+'\n');tmp.replace(transport_file)
    for idx,row in enumerate(before):
        workfile=directory/f'{idx:04d}.json.gz'
        if workfile.exists():
            with gzip.open(workfile,'rt')as stream:current=canonical_root(json.load(stream))
            assert current==row,'Working root changed before removal'
            workfile.unlink()
    assert corpus_digest(L)==digest,'Packed loader changed the logical corpus'
    return {k:v for k,v in transport.items()if k!='previous_verification'}
