"""Lossless mathematical-input compaction for the current 4.33 certificate.

Store exact proposal parameters and a canonical SHA-256 commitment instead of
repeating all regenerated scalar arrays. Every input field is regenerated and
hash-checked before the unchanged integer dual checker accepts a record.
This module uses the standard library; expansion imports the interval model.
"""
import argparse
import copy
import gzip
import hashlib
import json
from pathlib import Path

FORMAT = 'linnik-core-compact-v1'


def input_digest(inp):
    return hashlib.sha256(json.dumps(inp, sort_keys=True, separators=(',', ':'),
                                     allow_nan=False).encode()).hexdigest()


def compact_certificate(cert):
    assert set(cert) == {'branches', 'maximum'}
    packed = []
    pos = 0
    for br in cert['branches']:
        assert br['a'] == pos
        pos = br['b']
        if br.get('excluded'):
            assert set(br) == {'a', 'b', 'excluded', 'budget'}
            packed.append([pos, 'near', br['budget']])
        elif br.get('excluded_far'):
            assert set(br) == {'a', 'b', 'excluded_far', 'budget'}
            packed.append([pos, 'far', br['budget']])
        else:
            assert set(br) == {'a', 'b', 'Y', 'Z', 'U', 'upper'}
            packed.append([pos, br['Y'], br['Z'], br['U']])
    return dict(branches=packed, maximum=cert['maximum'], sha256=input_digest(cert))


def expand_certificate(cert, inp):
    assert set(cert) == {'branches', 'maximum', 'sha256'}
    S, TS, DS = inp['S'], inp['tau_scale'], inp['dual_scale']
    d, D, Df = inp['d'], inp['D'], inp['Df']
    second = inp['second']
    n2 = second['n'] if second else 0
    branches = []
    a = 0
    for row in cert['branches']:
        assert type(row) == list and len(row) in (3, 4)
        b = row[0]
        assert type(b) == int and b > a
        if len(row) == 3:
            assert row[1] in ('near', 'far') and type(row[2]) == int
            br = dict(a=a, b=b, budget=row[2])
            br['excluded' if row[1] == 'near' else 'excluded_far'] = True
        else:
            Y, Z, U = row[1:]
            assert all(type(x) == int and x >= 0 for x in (Y, Z, U))
            sh = b * (S // TS)
            f1 = max(inp['v_first'] - sh, 0)
            f2 = max(second['v'] - sh, 0) if second else 0
            de = TS * TS * d * Df * S
            nu = D * de - D * a * a * Df * S * S - inp['n'] * D * f1 * f1 * TS * TS * d - n2 * f2 * f2 * TS * TS * d * Df
            B = -((-nu) // de)
            value = -((-(Y * inp['far_budget'] + Z * B + U * 2 * S)) // DS) + inp['first'] + inp['final']
            br = dict(a=a, b=b, Y=Y, Z=Z, U=U, upper=value)
        branches.append(br)
        a = b
    out = dict(branches=branches, maximum=cert['maximum'])
    assert input_digest(out) == cert['sha256'], 'regenerated certificate hash mismatch'
    return out


def compact_node(node):
    if 'split' in node:
        return dict(node, children=[compact_node(c) for c in node['children']])
    if 'record' not in node:
        return copy.deepcopy(node)
    record = node['record']
    inp = record['input']
    e = inp['extension']
    return {'record': {
        'parameters': dict(method=e['variant'], gg=e['gG'], gz=e['gZ'],
                           mix=e['mix'], zeta=e['zeta']),
        'lambda_den': inp['lambda_den'],
        'input_sha256': input_digest(inp),
        'certificate': compact_certificate(record['certificate']),
    }}


def compact_root(root):
    out = {k: compact_node(v) if k in ('inside', 'outside') else v
           for k, v in root.items()}
    out['format'] = FORMAT
    return out


def regenerate_record(spec, record, L):
    from endgame import make_endgame, parse_params
    assert set(record) == {'parameters', 'lambda_den', 'input_sha256', 'certificate'}
    par = record['parameters']
    assert set(par) == {'method', 'gg', 'gz', 'mix', 'zeta'}
    parsed = parse_params({'extension': dict(variant=par['method'], gG=par['gg'],
                                            gZ=par['gz'], mix=par['mix'], zeta=par['zeta'])})
    assert parsed == par
    den = record['lambda_den']
    assert type(den) == int and 50 <= den <= 10000
    inp = make_endgame(spec, L, par, den)
    assert inp is not None
    assert input_digest(inp) == record['input_sha256'], 'regenerated input hash mismatch'
    return {'input': inp, 'certificate': expand_certificate(record['certificate'], inp)}


def expand_node(spec, node, L):
    from endgame import split_new
    if 'split' in node:
        assert set(node) == {'split', 'mid', 'children'} and len(node['children']) == 2
        left, right = split_new(spec, node['split'], node['mid'])
        return dict(node, children=[expand_node(s, c, L)
                                   for s, c in zip((left, right), node['children'])])
    if 'record' not in node:
        return copy.deepcopy(node)
    assert set(node) == {'record'}
    return {'record': regenerate_record(spec, node['record'], L)}


def expand_root(root):
    """Restore a historical full-input root, verifying each regenerated input hash."""
    if 'format' not in root:
        return root
    from endgame import specs, with_height
    assert root['format'] == FORMAT
    idx = root['id']
    assert type(idx) == int and 0 <= idx < len(specs())
    spec = specs()[idx]
    keys = {'format', 'id', 'L', 'seconds', 'inside'}
    if spec['case']['kind'] != 'rr':
        keys.add('outside')
    assert set(root) == keys
    return {k: expand_node(with_height(spec, k), v, root['L'])
            if k in ('inside', 'outside') else v
            for k, v in root.items() if k != 'format'}


def full_roots(path):
    with gzip.open(path, 'rt') as stream:
        for line in stream:
            yield expand_root(json.loads(line))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('destination', type=Path)
    args = parser.parse_args()
    assert args.source.resolve() != args.destination.resolve()
    count = 0
    # Fixed metadata and compact JSON make the gzip output reproducible.
    with gzip.open(args.source, 'rt') as src, args.destination.open('wb') as raw:
        with gzip.GzipFile(filename='', fileobj=raw, mode='wb', mtime=0) as out:
            for line in src:
                root = json.loads(line)
                assert 'format' not in root and root['id'] == count
                out.write((json.dumps(compact_root(root), separators=(',', ':')) + '\n').encode())
                count += 1
    print(json.dumps({'roots': count, 'source_bytes': args.source.stat().st_size,
                      'compact_bytes': args.destination.stat().st_size}))


if __name__ == '__main__':
    main()
