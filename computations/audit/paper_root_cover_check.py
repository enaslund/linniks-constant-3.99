#!/usr/bin/env python3
"""Check the root cover directly against the manuscript's parent table.

Uses exact rationals and imports no case builder or certificate checker.
This checks the source cover, not the subsequent refinement trees or the
analytic truth of the parent implications.
"""
import argparse
from collections import Counter
from fractions import Fraction as Q
import gzip
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[2]


def tiled(intervals, start, end):
    pos = start
    for lo, hi in sorted(intervals):
        assert lo == pos and lo < hi, ('gap, overlap or empty interval', pos, lo, hi)
        pos = hi
    assert pos == end, ('wrong terminal endpoint', pos, end)


def check(paper, cover):
    table = paper.split(r'\label{prop:parentrows}', 1)[1].split(r'\label{tab:parents}', 1)[0]
    pattern = (r'\$\\mathrm\{(rr|rc|complex)\}\$\s*&\s*'
               r'\$\[([0-9.]+),([0-9.]+)\]\$\s*&\s*'
               r'\$([0-9.]+)\$\s*&\s*\$([0-9.]+)\$')
    parents = [(kind, *map(Q, nums)) for kind, *nums in re.findall(pattern, table)]
    order = {'rr': 0, 'rc': 1, 'complex': 2}
    parents.sort(key=lambda row: (order[row[0]], row[1]))
    assert len(parents) == 58
    starts = {'rr': Q('.1'), 'rc': Q('.628'), 'complex': Q('.44')}
    for kind, start in starts.items():
        tiled([(a, b) for t, a, b, p, r in parents if t == kind], start, Q('1.5'))

    counts = Counter()
    base_by_parent = {j: [] for j in range(len(parents))}
    spec_id = 0
    infinity = float('inf')

    def check_cell(c):
        kind, a, b, p, r = parents[c['parent']]
        lo, hi = Q(c['lo']), Q(c['hi'])
        assert c['kind'] == kind and a <= lo < hi <= b
        # These inequalities are the implications of section 11.3, step (3).
        assert lo <= Q(c['lp']) <= max(p, lo)
        assert lo <= Q(c['source_l2']) <= max(r, lo)
        return lo, hi

    for base in cover:
        root = base['root']
        lo, hi = check_cell(root)
        assert hi - lo <= Q('.01')
        base_by_parent[root['parent']].append((lo, hi))
        counts['base_cells'] += 1
        intervals = []
        for leaf in base['leaves']:
            c = leaf['case']
            aa, bb = check_cell(c)
            assert c['parent'] == root['parent'] and lo <= aa < bb <= hi
            intervals.append((aa, bb))
            counts['first_zero_cells'] += 1
            gap_intervals = []
            for pr in leaf['proofs']:
                gap = pr['gap']
                if gap is None:
                    assert leaf['gap_mode'] == 'none' and len(leaf['proofs']) == 1
                else:
                    assert leaf['gap_mode'] == 'partition' and c['kind'] == 'complex'
                    gap_intervals.append((Q(gap['lo']), infinity if gap['hi'] == 'infinity' else Q(gap['hi'])))
                counts['gap_cases'] += 1
                reservations = {1: [], 2: []}
                tails = []
                for rec in pr['records']:
                    assert rec['spec_id'] == spec_id
                    spec_id += 1
                    inp = rec['input']
                    assert inp['case'] == c and inp['gap'] == gap
                    r = Q(inp['ordinary_lower'])
                    assert Q(c['source_l2']) <= r <= 3
                    sec = inp['second']
                    if sec is None:
                        tails.append(r)
                    else:
                        assert sec['n'] in (1, 2) and Q(sec['lo']) == r < Q(sec['hi']) <= 2
                        reservations[sec['n']].append((r, Q(sec['hi'])))
                    counts['specifications'] += 1
                    counts['type_' + c['kind']] += 1
                    counts['inside_roots'] += 1
                    counts['outside_roots'] += c['kind'] != 'rr'
                assert len(tails) == 1, 'missing or duplicated unreserved tail'
                if pr['mode'] == 'unreserved':
                    assert not reservations[1] and not reservations[2]
                    assert tails == [Q(c['source_l2'])]
                else:
                    assert pr['mode'] == 'reserved' and Q(pr['tail_start']) == tails[0]
                    for n in (1, 2):
                        tiled(reservations[n], Q(c['source_l2']), tails[0])
                    assert sorted(reservations[1]) == sorted(reservations[2])
            if gap_intervals:
                tiled(gap_intervals, Q(c['lp']), infinity)
        tiled(intervals, lo, hi)
    for j, (kind, a, b, p, r) in enumerate(parents):
        tiled(base_by_parent[j], a, b)
    return {'parents': len(parents), **dict(counts)}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    paper = ROOT/'paper/sections/07-location.tex'
    source = ROOT/'computations/core/results/source_cover.json.gz'
    with gzip.open(source, 'rt') as stream:
        cover = json.load(stream)
    result = check(paper.read_text(), cover)
    result.update(status='PASS', scope='Root cover only; parent implications are analytic premises.',
                  inputs={str(path.relative_to(ROOT)): hashlib.sha256(path.read_bytes()).hexdigest()
                          for path in (paper, source)})
    args.out.parent.mkdir(parents=True, exist_ok=True)
    args.out.write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result))


if __name__ == '__main__':
    main()
