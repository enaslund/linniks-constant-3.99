# Reproduction from this repository alone (2026-10-02)

The checks of [`README.md`](README.md) were rerun from a copy of exactly the files this repository
commits. The copy was made outside any other checkout, with:
* a fresh Python 3.13 environment from [`requirements.txt`](requirements.txt);
* the corpora rebuilt from their parts by `graded/corpora/assemble.sh`;
* the native Lean checkers built from the root package (`lake build certrun leafcheck rowcheck`).

The machine has 16 cores. The outputs are in
[`reproduction_2026-10-02/`](reproduction_2026-10-02/). Every result agrees with the recorded one,
up to run times, dates, worker counts and file paths.

This run found one gap, which is fixed in this repository: `numba`, imported by the outside replay,
was missing from `requirements.txt`.

| Check | Run | Result |
| --- | --- | --- |
| Corpus rebuild | `assemble.sh 3.99` | The three files have the SHA-256 of `graded/corpora/3.99/SHA256SUMS`. |
| (1) Full replay | `graded_verify.py`, 12 workers, 17 min | PASS. Inside: 2,768 roots, 3,146 leaves, 233 identities nodes, 4,109,455 boxes, maximum 9999998223456687/10¹⁶. Outside: 1,685 roots, 1,642 leaves, 87,424 boxes, maximum 9999942478462508/10¹⁶. The report equals [`graded/verification_3.99.json`](graded/verification_3.99.json) except for its run time. |
| (2) Independent checker, whole corpus | `graded_lean_export.py --jsonl` with `audit/independent_cert_check.py`, 12 workers, 32 min | PASS on all 3,949 inside and 1,642 outside certificate trees, with every value and box count equal to the replay's. The per-leaf statistics give 29,397,336 relaxation cases: 29,387,906 bounded by integer duals and 9,430 excluded. |
| (3) Mutation test | `graded_mutation_test.py 1671,1320,1416` | The 19 leaves have the recorded outcomes: every unmutated leaf passes and all 133 mutations are rejected. |
| Verified checkers, outside | `--full` and `--rows`, 1,685 roots | `leafcheck` passes all 1,642 certificate trees and their numeric data (87,424 boxes). `rowcheck` passes all 3,314 near rows. |
| Verified checkers, inside sample | `--full` and `--rows` on roots 10, 212, 600, 1100, 1155, 1218, 1320, 1416, 1671, 2000, 2432, 2603 and 2766 (the two-test kinds, the identities nodes, the three types and the tightest roots) | `leafcheck` passes all 52 trees, which contain 176,014 boxes and reach the corpus maximum 9999998223456687/10¹⁶. `rowcheck` passes all 52 leaves (187 rows checked). The whole inside corpus was checked by these checkers on 2026-09-29/30 ([`graded/lean_runs/`](graded/lean_runs/)). |
| (4) Leaf integers | `--numerics` on roots 600, 1416 and 2603, then `leaf_numerics_check.py` | 17,999 integers of 8 leaves, all exact. |
| (5) Two-test rows | `two_test_compare.py`, all 37 leaves | Identical to [`graded/two_test_compare_3.99.json`](graded/two_test_compare_3.99.json). |
| Large range `λ₁ ≥ 3/2` | `graded_large.py --lean` | Value 9966813270344512/10¹⁶ on 36 boxes, accepted by `certrun`, `leafcheck` and `rowcheck` (150 entries), as recorded. |
| Exterior components | `frontier/verify_existing_components.py` | PASS, with the recorded maxima. The report also hashes two programs added after the recorded run. |
| Small range | `core/code/small_exception_399.py`, `small_exception_tables.py`, `independent_small_tables_check.py` | The three reports are rewritten byte-identically. |
| Location rows | `poly_rows`, `alias_check`, `x434_check`, `independent_polynomial_checks` | PASS (50,032 character pairs matched). |
| Source tables | `hb_tables_recompute.py`, `printed_tables_check.py`, with the two literature PDFs of the stated hashes supplied | Identical to the recorded reports. |
| Adversarial-review checks | `adversarial_source_checks.py`, `paper_root_cover_check.py`, `fallback_integral_attack.py` | Identical to the recorded reports. |
