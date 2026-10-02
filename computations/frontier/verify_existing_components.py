"""Fresh replay of the complementary outside and exterior components.

Preserves historical reports. Before/after commitments bind every retained
core/near Python file, the source inputs, and the exact certificate bytes to this
run. This verifies numerical implications; analytic deductions remain premises.
"""
import argparse
from concurrent.futures import ProcessPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import sys
import time

os.environ['OPENBLAS_NUM_THREADS'] = '1'
os.environ['OMP_NUM_THREADS'] = '1'
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
CORE = HERE.parent / 'core'
NEAR = HERE.parent / 'near'
OUTSIDE = NEAR / 'results/outside_regime_4.30.jsonl.gz'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def commitments():
    paths = [Path(__file__).resolve(), OUTSIDE,
             CORE / 'results/source_cover.json.gz',
             CORE / 'results/polynomial_table.json',
             CORE / 'results/certificate_4.33.jsonl.gz',
             CORE / 'results/large_branch_3.99.json',
             CORE / 'results/small_exception_3.99.json',
             CORE / 'results/small_exception_tables_3.99.json',
             CORE / 'results/verification_4.33.json',
             NEAR / 'results/outside_regime_4.30_verified.json']
    paths += [p for base in (CORE / 'code', NEAR / 'code') for p in base.glob('*.py')]
    return {str(p.relative_to(REPO)): sha(p) for p in sorted(set(paths))}


def run(workers=2):
    if not __debug__:
        raise RuntimeError('Assertions must be enabled')
    assert workers >= 1
    start = time.time()
    before = commitments()
    sys.path.insert(0, str(NEAR / 'code'))
    import outside_regime as outside
    from certificate_io import load_outside, validate_outside_records
    from endgame import specs, S
    from small_exception_399 import check as check_small
    from small_exception_tables import check as check_small_tables
    from verify_published_single import scenario as check_large

    records = load_outside('4.30')
    ids = validate_outside_records(records, '4.30')
    assert ids == [i for i, sp in enumerate(specs()) if sp['case']['kind'] != 'rr']
    assert len(ids) == 1685
    answers = []
    with ProcessPoolExecutor(max_workers=workers) as pool:
        futures = [pool.submit(outside.verify_job, (record, '4.30')) for record in records]
        for future in as_completed(futures):
            answer = future.result()
            answers.append(answer)
            if len(answers) % 50 == 0 or len(answers) == len(ids):
                print(json.dumps(dict(component='outside', done=len(answers), total=len(ids),
                                      maximum_numerator=max(r['maximum'] for r in answers),
                                      seconds=round(time.time()-start, 1))), flush=True)
    answers.sort(key=lambda r: r['id'])
    assert [r['id'] for r in answers] == ids
    best = max(answers, key=lambda r: r['maximum'])
    assert best['maximum'] < S
    outside_report = dict(
        L='4.30', status='PASS complete finite outside-buffer first-zero regime',
        source_records=len(ids), complete_source_enumeration=True, regenerated_inputs=True,
        certificate=str(OUTSIDE.relative_to(REPO)),
        certificate_sha256=before[str(OUTSIDE.relative_to(REPO))],
        maximum_numerator=best['maximum'], scale=S,
        margin_numerator=S-best['maximum'], binding=best,
        **{key: sum(r[key] for r in answers) for key in ('leaves', 'branches', 'checks', 'excluded')})

    large_record = json.loads((CORE / 'results/large_branch_3.99.json').read_text())
    large = check_large(large_record, None, '3.99', True)
    small = check_small()
    assert large['maximum'] < S and small['remaining_linear_lower'] > 0
    assert small == json.loads((CORE / 'results/small_exception_3.99.json').read_text())
    # the small branch as used in research/PROOF.md §9: Heath-Brown's table rows near lambda1=.1
    small_tables_ok, small_tables = check_small_tables()
    assert small_tables_ok
    assert small_tables == json.loads((CORE / 'results/small_exception_tables_3.99.json').read_text())['pieces']
    old = json.loads((CORE / 'results/verification_4.33.json').read_text())
    assert large == old['large_case_at_3_99'] and small == old['small_exception_at_3_99']
    previous_outside = json.loads((NEAR / 'results/outside_regime_4.30_verified.json').read_text())
    for key in ('L', 'source_records', 'maximum_numerator', 'scale', 'leaves', 'branches', 'checks', 'excluded', 'binding'):
        assert outside_report[key] == previous_outside[key]

    after = commitments()
    assert before == after, 'A committed code, input, certificate, or historical report changed during replay'
    report = dict(
        status='PASS fresh complementary-component numerical replay; analytic premises remain unformalized',
        scope='Complete finite outside-buffer regime at 4.30 and both exterior regimes at 3.99; no inside middle regime',
        workers=workers, assertions_enabled=True, seconds=time.time()-start,
        outside=outside_report,
        exteriors=dict(L='3.99', regenerated_inputs=True,
                       regimes=['0<lambda1<=0.1', 'lambda1>=1.5'], large=large, small=small,
                       small_tables=small_tables),
        historical_reports_preserved=True, previous_mathematical_reports_match=True,
        commitments_before=before, commitments_after=after, commitments_unchanged=True,
        command=f'python3 computations/frontier/verify_existing_components.py --workers {workers}',
        equivalent_component_commands=[
            'python3 computations/near/code/outside_regime.py --L 4.30 --workers 2 --verify',
            'python3 computations/near/code/verify_exterior_399.py'])
    destination = HERE / 'existing_components_verified.json'
    temporary = destination.with_suffix('.tmp')
    temporary.write_text(json.dumps(report, indent=2, allow_nan=False) + '\n')
    temporary.replace(destination)
    print(json.dumps(dict(status=report['status'], seconds=report['seconds'],
                          outside_checks=outside_report['checks'],
                          outside_maximum_numerator=outside_report['maximum_numerator'],
                          exterior_large_checks=large['checks'],
                          committed_files=len(before))), flush=True)
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--workers', type=int, default=2)
    args = parser.parse_args()
    run(args.workers)
