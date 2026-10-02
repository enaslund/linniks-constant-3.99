"""Compact imported witnesses; every regenerated scalar input is hash-checked.

Hashes bind JSON values (sorted keys, compact separators, UTF-8, finite numbers),
not original whitespace. Rational witnesses and coverage trees are unchanged.
"""
import gzip
import hashlib
import json
from pathlib import Path

PROJECT = Path(__file__).resolve().parents[1]

def load_data(name):
    with gzip.open(PROJECT / 'results' / (name + '.gz'), 'rt') as stream:
        return json.load(stream)

def input_summary(inp):
    if inp.get('compact_input') == 1:
        return inp
    e = inp['extension']
    return dict(compact_input=1, sha256=input_digest(inp), lambda_den=inp['lambda_den'],
                parameters=dict(method=e['variant'], gg=e['gG'], gz=e['gZ'],
                                mix=e.get('mix', '0'), zeta=e.get('zeta', '3')))

def input_digest(inp):
    data = json.dumps(inp, sort_keys=True, separators=(',', ':'), allow_nan=False)
    return hashlib.sha256(data.encode()).hexdigest()

def check_input(inp, stored):
    if stored.get('compact_input') == 1:
        assert input_summary(inp) == stored, 'regenerated input differs from imported hash/parameters'
    else:
        assert inp == stored
    return inp

def parameters_of(stored):
    return input_summary(stored)['parameters']

def load_outside(L):
    combined = PROJECT / 'results' / f'outside_regime_{L}.jsonl.gz'
    if combined.exists():
        rebuilt = PROJECT / 'results' / f'outside_regime_{L}'
        if any(rebuilt.glob('*.json.gz')):
            raise ValueError('Both imported compact and rebuilt outside witnesses exist; move one aside before verification')
        with gzip.open(combined, 'rt') as stream:
            return [json.loads(line) for line in stream]
    records = []
    for path in sorted((PROJECT / 'results' / f'outside_regime_{L}').glob('*.json.gz')):
        with gzip.open(path, 'rt') as stream:
            records.append(json.load(stream))
    return records

def expand_local_tree(base, L, tree):
    """Restore original inputs for independent diagnostics and corruption tests."""
    from adaptive_local_blocks import make_block_input, PAR
    if 'children' in tree:
        for child in tree['children']:
            expand_local_tree(base, L, child)
    else:
        record = tree['record']
        inp = make_block_input(base, L, tree['branch'], PAR, 400)
        record['input'] = check_input(inp, record['input'])
    return tree

def expand_outside_tree(sp, L, tree):
    from outside_regime import split_new, first_out_input
    if 'split' in tree:
        a, b = split_new(sp, tree['split'], tree['mid'])
        for child, spec in zip(tree['children'], (a, b)):
            expand_outside_tree(spec, L, child)
    elif 'buffered_first' in tree:
        record = tree['buffered_first']; old = record['input']
        inp = first_out_input(sp, L, 'outside_buffer', parameters_of(old), old['lambda_den'])
        record['input'] = check_input(inp, old)
    return tree


def validate_outside_records(records, L):
    from endgame import specs
    ids = [i for i, sp in enumerate(specs()) if sp['case']['kind'] != 'rr']
    assert [r['id'] for r in records] == ids, 'missing, duplicate, or reordered source records'
    assert all(r['L'] == L for r in records)
    return ids
