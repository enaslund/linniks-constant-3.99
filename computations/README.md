# Certificates, programs and verification records

This directory holds the computer-assisted part of the proof of *Linnik's constant is at most 3.99*
([`paper/linnik399.pdf`](../paper/linnik399.pdf)):
* the stored certificates;
* the programs that regenerate every leaf program and check the certificates against it;
* the independent checks;
* the reports of every recorded run.

§14 of the paper describes the checks. This file says where each one is and how to rerun it.
Paths are given from the repository root, and the layout is that of the research repository in
which the work was done, so references of the form `computations/...` resolve here.

## Contents

| Path | Content |
| --- | --- |
| `graded/corpora/3.99/` | The certificates: `inside.jsonl.gz`, `nodes.jsonl.gz` and `outside.jsonl.gz`, one JSON line per root (4,453 roots, 4,788 leaves, 5,591 certificate trees, 4,196,879 terminal boxes). The two large files are committed in parts under GitHub's 100 MB limit; [`assemble.sh`](graded/corpora/assemble.sh) rebuilds them and checks their SHA-256 ([README](graded/corpora/README.md)). |
| `graded/` | The leaf programs and certificates (`graded_cert.py`, `graded_leaves.py`, `graded_driver.py`), the replay (`graded_verify.py`), the record of the claim (`graded_assemble.py` → `candidate_3.99.json`), the mutation test, the export to the Lean checkers (`graded_lean_export.py`), the audit of the leaf integers (`leaf_numerics_check.py`), the two-test comparison and the large first-zero range. The programs that made the certificates (`graded_batch.py`, `graded_pack.py`) are included too ([README](graded/README.md)). |
| `graded/lean_runs/` | Reports of the native runs of the formally verified checkers on the whole corpus. |
| `audit/` | The independent certificate checker and its forgery test, the recomputation of Heath-Brown's tables, the check of every printed number the proof uses, and the programs and raw results of the two adversarial reviews in [`paper/reviews/`](../paper/reviews/) ([README](audit/README.md)). |
| `frontier/`, `core/`, `near/`, `sieve_near/` | The case tree and the code that regenerates the leaves from it. They contain the stored source trees (`frontier/collective_full_4.30/roots.jsonl.gz` for the inside roots, `near/results/outside_regime_4.30.jsonl.gz` for the outside roots), the location rows and their checks (`core/code/poly_rows.py`, `alias_check.py`, `x434_check.py`, `independent_polynomial_checks.py`), the far and near enclosures, and the exterior components with their verification (`frontier/verify_existing_components.py`). |
| `requirements.txt` | The Python packages, at the versions of the recorded runs. |

The source trees and some of this code were first built for computations at other exponents, and
their file names say so. The subdivisions and zero-location arguments of the case tree do not
depend on the exponent. Every leaf is regenerated and certified at 3.99 (paper §§11 and 14).

[`research/`](../research/) holds the verification notes, the reviews made while the paper was
written, and the earlier working write-up [`research/PROOF.md`](../research/PROOF.md) (the paper is the
authoritative account; the section numbers differ).

## Setup

```bash
python3 -m venv .venv && .venv/bin/pip install -r computations/requirements.txt   # Python 3.13
bash computations/graded/corpora/assemble.sh 3.99         # rebuild the corpora, check SHA-256
```

The Lean checkers are built from the package at the repository root (see the
[README](../README.md)): `lake build certrun leafcheck rowcheck`. These native programs do not
compile Mathlib, but `lake` needs the dependencies fetched (`lake exe cache get`).

## The checks

The times are wall-clock times of the recorded runs on a 16-core machine.

| Check (paper §14) | Command | Recorded result |
| --- | --- | --- |
| (1) Replay: every split, location node and exclusion of the case tree, and every leaf program regenerated and its certificate checked exactly (1.7 h with 5 workers) | `.venv/bin/python computations/graded/graded_verify.py --L 3.99 --inside computations/graded/corpora/3.99/inside.jsonl.gz --nodes computations/graded/corpora/3.99/nodes.jsonl.gz --outside computations/graded/corpora/3.99/outside.jsonl.gz --workers 12` | [`graded/verification_3.99.json`](graded/verification_3.99.json): PASS. Inside: 2,768 roots, 3,146 leaves, 233 identities nodes, 4,109,455 boxes, maximum 0.9999998223456688. Outside: 1,685 roots, 1,642 leaves, 87,424 boxes, maximum 0.9999942478462508. |
| (2) Independent checker, written from the paper's §10 alone, on every certificate (inside 29 min with 10 workers) | `.venv/bin/python computations/graded/graded_lean_export.py --kind inside --roots all --jsonl --workers 10 --checker "$PWD/.venv/bin/python $PWD/computations/audit/independent_cert_check.py --stats inside-stats.jsonl" --out inside-independent.json`, and the same with `--kind outside` | [`audit/independent_cert_3.99.json`](audit/independent_cert_3.99.json): PASS, every value and box count equal to the replay's (29,397,336 relaxation cases). Forgery test: `computations/audit/independent_cert_forgeries.py` on leaves saved by `capture_leaves.py`; log [`audit/independent_cert_forgeries_3.99.txt`](audit/independent_cert_forgeries_3.99.txt) (all 308 applicable forgeries rejected, all 82 applicable controls accepted). |
| (3) Mutation test of the replay | `.venv/bin/python computations/graded/graded_mutation_test.py 1671,1320,1416` | [`graded/mutation_test_3.99.jsonl`](graded/mutation_test_3.99.jsonl): 19 leaves; every unmutated leaf passes and all 133 mutations are rejected. |
| (4) Leaf integers recomputed in 50-digit arithmetic | `graded_lean_export.py --numerics` for the chosen roots, then `computations/graded/leaf_numerics_check.py <file> --report <report>` | [`graded/lean_runs/numerics_check_3.99.json`](graded/lean_runs/numerics_check_3.99.json): 117 roots, 154 leaves, 530,942 integers, 0 mismatches. |
| (5) Two-test rows compared with a separate implementation | `.venv/bin/python computations/graded/two_test_compare.py --workers 16 --out <report>` | [`graded/two_test_compare_3.99.json`](graded/two_test_compare_3.99.json): 37 leaves (31 single, 2 mixture, 4 paired), 1,079 certificate intervals and 11,211 random intervals in all three relaxations. |
| Formally verified checkers, natively, on every certificate, leaf's numeric data and near row (about 5 h in all) | `graded_lean_export.py --kind inside --roots all --full --workers 6 --out <report>`, then `--rows` instead of `--full`, and both with `--kind outside` | [`graded/lean_runs/`](graded/lean_runs/): `leafcheck` passes all 3,949 inside and 1,642 outside certificate trees with their numeric data, and `rowcheck` passes all their near rows (16,842 rows checked; the two-test rows are outside its scope). |
| Exterior ranges: the small range `λ₁ ≤ 0.1` and the components outside the buffer | `.venv/bin/python computations/frontier/verify_existing_components.py --workers 4` (2 min); `computations/core/code/small_exception_399.py`, `small_exception_tables.py`, `independent_small_tables_check.py` | [`frontier/existing_components_verified.json`](frontier/existing_components_verified.json), [`core/results/small_exception_3.99.json`](core/results/small_exception_3.99.json), [`core/results/independent_small_tables_3.99.json`](core/results/independent_small_tables_3.99.json) (60-digit interval recomputation; both margins exceed 0.0304). |
| The large range `λ₁ ≥ 3/2` (paper Theorem 12.6) | `.venv/bin/python computations/graded/graded_large.py --lean` | [`graded/large_3.99.json`](graded/large_3.99.json) and [`graded/lean_runs/large_3.99.json`](graded/lean_runs/large_3.99.json): maximum 0.9966813270344512, accepted by the replay's checker, the independent checker and all three verified checkers (and in the Lean kernel by `GradedNear/Cert/Samples/Large.lean`). It supersedes the earlier certificate of the same program, with a differently normalized near row, recorded in `near/results/exterior_399_verified.json`. |
| Location rows checked by separate programs (complex polynomial rows, side conditions) | `poly_rows.verify_polynomial_table()`, `alias_check.check()`, `x434_check.check()`, `independent_polynomial_checks.aliases()` and `.refs()`, with `computations/core/code` on the import path | [`audit/adversarial_20261001/location-checks.json`](audit/adversarial_20261001/location-checks.json), [`polynomial-diagnostics.json`](audit/adversarial_20261001/polynomial-diagnostics.json) |
| Source tables: Heath-Brown's Tables 4 and 7 recomputed; every printed number the proof uses compared with the source pages | `computations/audit/hb_tables_recompute.py`; `computations/audit/printed_tables_check.py --out <report>` | [`audit/hb_tables_recompute.json`](audit/hb_tables_recompute.json), [`audit/printed_tables_check.json`](audit/printed_tables_check.json) |
| The adversarial reviews' checks | see [`audit/README.md`](audit/README.md) and the reproduction sections of the reports | [`audit/adversarial_20261001/`](audit/adversarial_20261001/), [`audit/adversarial_20261002/`](audit/adversarial_20261002/) |

[`graded/candidate_3.99.json`](graded/candidate_3.99.json) records the claim's components with the
SHA-256 of the three corpus files and of the replay report.

**The literature PDFs.** The two source-table checks read the printed pages of
Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic
progression*, Proc. London Math. Soc. (3) 64 (1992), 265–338
([doi:10.1112/plms/s3-64.2.265](https://doi.org/10.1112/plms/s3-64.2.265)), and of Xylouris's
dissertation ([Universität Bonn, 2011](https://bonndoc.ulb.uni-bonn.de/xmlui/handle/20.500.11811/5074)).
These are copyrighted and not redistributed here. To rerun the two checks, save them as
`literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf` (SHA-256
`365dee4a7e32ebc5963c3c0eecfa266c226486bc54f487f13497b190219ef0bb`) and
`literature/xylouris-2011-dissertation.pdf` (SHA-256
`637dcecf7c3a835e042d2bd6599340f4d782d7dbf995f663763bafd039d7f98e`); the recorded reports list
these hashes.

## Reproduction of this repository's copy

On 2026-10-02 the following were rerun in a fresh copy of the files of this repository, with a fresh
Python environment from `requirements.txt` and the native checkers built from the root package:
* the corpus rebuild and its SHA-256 check;
* the full replay (1);
* the mutation test (3);
* samples of the independent checker and of the verified native checkers;
* the exterior and source-table checks.

The results are in [`reproduction_2026-10-02.md`](reproduction_2026-10-02.md).
