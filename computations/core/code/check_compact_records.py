"""Adversarial checks for the compact certificate reader and exact acceptance.

Run from any directory. Optionally pass the historical certificate to compare
selected expanded roots field-for-field before removing that original file.
"""
import argparse
import copy
import gzip
import json
from pathlib import Path

from compact_records import compact_root, expand_root, input_digest
from verify_progress import ROOT, task


def records(node):
    if 'record' in node:
        yield node['record']
    for child in node.get('children', []):
        yield from records(child)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path)
    args = parser.parse_args()
    chosen = {0, 428, 1301, 2421, 2767}
    path = ROOT / 'results/certificate_4.33.jsonl.gz'
    with gzip.open(path, 'rt') as f:
        compact = {i: json.loads(line) for i, line in enumerate(f) if i in chosen}
    full = {i: expand_root(root) for i, root in compact.items()}
    compared = []
    if args.original:
        with gzip.open(args.original, 'rt') as f:
            for i, line in enumerate(f):
                if i in chosen:
                    assert json.loads(line) == full[i], ('round-trip mismatch', i)
                    compared.append(i)
        assert set(compared) == chosen
    for i in chosen:
        assert compact_root(full[i]) == compact[i]
    rejected = []

    def reject(name, root):
        try:
            task((json.dumps(root), '4.33'))
        except (AssertionError, ValueError, TypeError, KeyError):
            rejected.append(name)
            return
        raise AssertionError('corruption accepted: ' + name)

    root = copy.deepcopy(compact[0])
    del root['inside']
    reject('missing required inside-height case', root)
    root = copy.deepcopy(compact[1301])
    del root['outside']
    reject('missing required outside-height case', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    rec['input_sha256'] = '0' * 64
    reject('altered input commitment', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    rec['parameters']['gg'] = '17/10'
    reject('altered exact model parameter', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    rec['certificate']['sha256'] = '0' * 64
    reject('altered branch commitment', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    rec['certificate']['branches'].pop()
    reject('missing threshold witness', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    rec['certificate']['branches'][:2] = reversed(rec['certificate']['branches'][:2])
    reject('reordered threshold witnesses', root)
    root = copy.deepcopy(compact[0])
    rec = next(records(root['inside']))
    branch = next(b for b in rec['certificate']['branches'] if len(b) == 4)
    branch[1] += 1
    reject('altered dual witness', root)
    # Recompute valid commitments around an invalid dual: hashes must never
    # substitute for checking the mathematical inequalities themselves.
    root = copy.deepcopy(full[0])
    rec = next(records(root['inside']))
    branch = next(b for b in rec['certificate']['branches'] if 'Y' in b)
    branch.update(Y=0, Z=0, U=0,
                  upper=rec['input']['first'] + rec['input']['final'])
    rec['certificate']['maximum'] = max(b.get('upper', -1)
                                        for b in rec['certificate']['branches'])
    reject('invalid dual with correctly recomputed commitments', compact_root(root))
    root = copy.deepcopy(full[0])
    rec = next(records(root['inside']))
    rec['input']['first'] -= 10**11
    reject('forged input with correctly recomputed commitment', compact_root(root))
    report = dict(status='PASS', round_trip_roots=sorted(chosen),
                  compared_original_roots=compared, rejected_corruptions=rejected,
                  scope='Compact transport and exact-checker tests; not analytic proof.')
    (ROOT / 'results/compact_integrity_checks.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
