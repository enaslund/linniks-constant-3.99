"""Assemble the candidate record of the graded-near proof at L from a passing replay.

  python3 computations/graded/graded_assemble.py --L 3.99 \
      --inside <inside.jsonl.gz> --nodes <nodes.jsonl.gz> --outside <outside.jsonl.gz>

The replay report (verification_<L>.json, written by graded_verify.py on the same
corpora) must exist and pass.  The exterior regimes are taken from the repository's
verified component record.  The result is a numerical implication conditional on the
premises of research/PROOF.md §11; it is not a theorem.
"""
import argparse, hashlib, json
from datetime import datetime, timezone
from fractions import Fraction as Q
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


ap = argparse.ArgumentParser()
ap.add_argument('--L', required=True)
ap.add_argument('--inside', required=True)
ap.add_argument('--nodes', required=True)
ap.add_argument('--outside', required=True)
a = ap.parse_args()

report_path = HERE/f'verification_{a.L}.json'
rep = json.loads(report_path.read_text())
assert rep['status'].startswith('PASS') and rep['L'] == a.L and rep.get('method') == 'graded-near'
assert rep['inside']['maximum_numerator'] < 10**16 and rep['outside']['maximum_numerator'] < 10**16
assert rep['inside']['identities_nodes'] == 233
ext = json.loads((ROOT/'computations/frontier/existing_components_verified.json').read_text())
assert ext['status'].startswith('PASS') and Q(ext['exteriors']['L']) <= Q(a.L)

record = dict(
    date=datetime.now(timezone.utc).isoformat(),
    target=a.L,
    method='graded-near (research/PROOF.md)',
    status=('Complete numerical implication at the target exponent, assembled from verified components; '
            'conditional on the analytic premises of research/PROOF.md §11. Not a theorem; not formalized.'),
    scope='All moduli and coprime residue classes, conditional on the premises listed in research/PROOF.md §11',
    components=dict(
        middle_inside=dict(L=a.L, replay=rep['inside'],
                           corpus=a.inside, corpus_sha256=sha(a.inside),
                           nodes_corpus=a.nodes, nodes_corpus_sha256=sha(a.nodes),
                           description=('Every LP leaf and identities node of the verified 4.30 inside source trees, '
                                        'replaced by the regular inside model of its case at the target and certified '
                                        'with graded near rows, second-family columns and exact integer duals; '
                                        'location rows, exclusions and splits of the trees are re-checked by the '
                                        'repository verifiers during the replay.')),
        middle_outside=dict(L=a.L, replay=rep['outside'], corpus=a.outside, corpus_sha256=sha(a.outside),
                            description=('Every outside-buffer leaf of the verified 4.30 outside source trees, '
                                         'replaced by the regular outside model at the target and certified with '
                                         'the outside family row and graded rows.')),
        exteriors=dict(L=ext['exteriors']['L'], regimes=ext['exteriors']['regimes'],
                       source='computations/frontier/existing_components_verified.json'),
    ),
    mathematical_join=('research/PROOF.md §10: no zero in R(l); lambda1 <= .1 (small exterior); .1 <= lambda1 < 1.5 '
                       '(inside or outside the buffer, covered by the replayed trees); lambda1 >= 1.5 (large '
                       'exterior). Finitely many leaves with fixed tests give a common q0.'),
    analytic_premises='research/PROOF.md §11 (premise table with review status)',
    replay_command=(f'python3 computations/graded/graded_verify.py --L {a.L} --inside {a.inside} '
                    f'--nodes {a.nodes} --outside {a.outside} --workers 4'),
    replay_report=str(report_path.relative_to(ROOT)), replay_report_sha256=sha(report_path),
)
out = HERE/f'candidate_{a.L}.json'
out.write_text(json.dumps(record, indent=2))
print(out)
