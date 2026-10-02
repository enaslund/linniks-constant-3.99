# Graded-near proof: certificates and replay

This directory holds the code for the finite part of the proof: §§8–11 of the paper
([`paper/linnik399.pdf`](../../paper/linnik399.pdf)), §§6–8 of the earlier working write-up
[research/PROOF.md](../../research/PROOF.md). How to run every check, and the recorded results, are
in [computations/README.md](../README.md).

| File | Role |
| --- | --- |
| `graded_leaves.py` | Leaf inputs at a target `L`. Inside leaves use the repository's `make_endgame` with the refined `λ₃`, without the collective envelope. Outside leaves use `first_out_input`. Also builds the near rows: family, shifted and graded (PROOF.md §6.5). |
| `graded_cert.py` | Leaf LP (far, count, hidden count and near rows), certificate construction, and the exact checker `verify_tree`. |
| `graded_driver.py` | Staged row selection, the rc height split, second-family splits and record verification (`verify_leaf`). |
| `graded_batch.py` | Certifies one corpus (`inside`, `nodes` or `outside`) root by root. |
| `graded_verify.py` | Replay. Traverses the verified 4.30 source trees with the repository's verifiers, intercepts every LP leaf and identities node, and checks the stored graded certificates. |
| `graded_pack.py` | Packs per-root files into one JSON-lines corpus per kind. Later directories override earlier ones, for re-certified roots. |
| `graded_assemble.py` | Writes `candidate_<L>.json` from a passing replay report and the repository's verified exterior components. |
| `graded_mutation_test.py` | Negative test of the replay. It perturbs regenerated inputs (far budget, objective, first-family charge, near-row `d` and features) or a certificate dual by 0.1% in the unfavourable direction, and checks that the exact replay rejects every stored certificate. Run 2026-09-29 on inside roots 1671, 1320 and 1416: 19 leaves, including the three tightest (up to .9999998). Every unmutated leaf passed and all 133 mutations were rejected. |
| `graded_lean_export.py` | Exports leaves, stored trees and leaf metadata to the formally verified checkers of [lean-graded](../../README.md). Results are in `lean_runs/`. The modes:<ul><li>**default:** Lean modules whose `checkLeaf` result is proved by kernel evaluation (`--split-dir`: one module per leaf);</li><li>**`--jsonl`:** streams every leaf of the chosen roots to a certificate checker and compares each value and box count with `graded_cert`'s. The checker is the native `certrun` or the interpreted `scripts/CertRun.lean` (`--checker`);</li><li>**`--numerics`:** writes each leaf's metadata (`research/notes/leaf-data-semantics-2026-09-29.md`);</li><li>**`--full`:** streams leaf, tree and metadata to the native `leafcheck`, which runs the certificate check and the verified numeric check `checkNum`;</li><li>**`--full --num-only`:** runs only the numeric check, for leaves whose certificates are checked by another run;</li><li>**`--rows`:** streams each leaf with its near rows' metadata (parameters, and each column's and family term's semantics, including the special terms' ranges and the `C_Z` cells) to the native `rowcheck`, which checks the rows' stored radius, features and diagonals against a concrete instance of the near lemma (`research/notes/near-rows-formalization-2026-09-30.md`).</li></ul> |
| `leaf_numerics_check.py` | Recomputes every column and budget integer (`G`, `W`, `C`, `NH`, `E`; `F`, `first`, `final`) from the exported metadata alone, in mpmath at 50 digits, with the builders' rounding rules. Summary in `lean_runs/numerics_check_3.99.json` (154 leaves, 530,942 integers, all exact). |
| `corpora/` | The stored certificates at 3.99, one gzip JSON-lines file per kind (4,453 roots, 4,196,879 boxes). `inside` and `nodes` are committed in parts under 100 MB. Run `corpora/assemble.sh` after cloning; it rebuilds them and checks their SHA-256. Format and provenance: [corpora/README.md](corpora/README.md). |
| `graded_large.py` | The large first-zero range `λ₁ ≥ 3/2` (paper Theorem 12.6) as a graded leaf. It regenerates the 150 bins and the tail of the earlier exterior program (`make_large`) and compares them with `core/results/large_branch_3.99.json`. It rebuilds the near row with the builders' normalization (`SieveNearTest`, `γ = 1`, `g₁ = 3/2`, `s = s₁ = 3/2`, `t₀ = 1`, no sieve part). It certifies the program on the earlier record's 36 threshold intervals and checks the certificate with `graded_cert`, maximum 0.9966813270344512 (`large_3.99.json`). With `--lean` it runs `certrun`, `leafcheck` and `rowcheck`, and all three accept (`lean_runs/large_3.99.json`). With `--lean-module` it writes the kernel-checked module `lean-graded/GradedNear/Cert/Samples/Large.lean`. |
| `two_test_compare.py` | Replays the 37 roots that use the two-test row. It compares that row, as `graded_cert` uses it, with the 4.30 implementation (`build_progress.near`, `verify_progress.scenario`), exactly. The comparison runs on every interval the certificates use and on 11,211 random intervals, in all three relaxation cases. It also regenerates the row's integers. Report: `two_test_compare_3.99.json`. |
| `exterior_probe.py` | Floating probes of the two exterior regimes below 3.99. Proposals only; see sieve-majorant-near §6e. |

The analytic enclosures (`I_B`, `D(δ)`, features, conjugate-pair bounds) and
the repository builders are imported from ../sieve_near.

## Pipeline

1. **Capture leaf inputs.** Replay the 4.30 trees and record the input of each
   LP leaf and identities node. The scratch scripts that did this intercepted
   the following:
   * `verify_progress.scenario`, `inside_repair.verify_core` and
     `collective_model.scenario` for inside leaves;
   * `inside_repair.verify_branch` bases for identities nodes;
   * `first_outside_blocks.first_verify` for outside leaves.

   The certificates never trust these captures, because the replay
   regenerates every leaf.
2. **Certify.**

   ```bash
   python3 computations/graded/graded_batch.py --kind inside  --leaves <captured> --L 3.99 --out <dir>
   python3 computations/graded/graded_batch.py --kind nodes   --leaves <captured identities> --L 3.99 --out <dir>
   python3 computations/graded/graded_batch.py --kind outside --leaves <captured outside> --L 3.99 --out <dir>
   ```

   `--ids` gives an explicit order, for example the hardest roots first.
   `GRADED_LOCK=1` lets several batch processes share one output directory.
3. **Replay** (assertions enabled; writes `verification_<L>.json`). After a clone, first run
   `computations/graded/corpora/assemble.sh` to rebuild the packed corpora from their parts:

   ```bash
   python3 computations/graded/graded_verify.py --L 3.99 --inside <dir> --nodes <dir> --outside <dir> --workers 4
   ```

   `--inside-roots` and `--outside-roots` restrict the replay to listed roots
   for a partial check and write no report. A corpus may be a directory of
   per-root files or a packed file. A packed file is streamed in id order, so
   each worker holds one record at a time.
4. **Pack, replay the packed files, assemble.** The replay report that
   `graded_assemble.py` cites should come from the same packed files whose
   hashes it records.

   ```bash
   python3 computations/graded/graded_pack.py inside.jsonl.gz <dir> --kind inside --expect 2768
   python3 computations/graded/graded_pack.py nodes.jsonl.gz <dir> --kind nodes --expect 199
   python3 computations/graded/graded_pack.py outside.jsonl.gz <dir> --kind outside --expect 1685
   python3 computations/graded/graded_verify.py --L 3.99 --inside inside.jsonl.gz --nodes nodes.jsonl.gz --outside outside.jsonl.gz --workers 5
   python3 computations/graded/graded_assemble.py --L 3.99 --inside inside.jsonl.gz --nodes nodes.jsonl.gz --outside outside.jsonl.gz
   ```
5. **Negative test** (optional): `graded_mutation_test.py <roots>` perturbs
   inputs and duals and checks that the replay rejects every certificate.

## Certificates

Each root file holds one record per leaf.

* A **plain record** holds the rows (kind and rational parameters), a box tree
  and the certified maximum. The maximum is scaled by `10¹⁶` and includes
  `first` and the `5·10⁻⁶` allowance.
* An **rc record** has `mu_split` parts for `μ₁∈[0,1]` and `μ₁≥1`.
* A **split record** has children along the repository's second-family split
  paths. The verifier regenerates every child and checks that the paths
  exhaust the parent.
* A **reserve record** is a reservation split of an unreserved case at `h`
  (`graded_leaves.reserve_specs`). It has three children: one real character
  reserved in `[r,h)`, a nonreal pair reserved in `[r,h)`, and no non-first
  family below `h`.
  * Each child may itself carry second-family splits.
  * Paths such as `[('reserve', h, k), ('second', mid, side)]` locate every
    child.
  * `graded_driver.verify_leaf` follows them recursively.
* `second_columns: 400` means the leaf's reserved second family is carried
  by LP columns on a `1/400` grid (PROOF.md §7). The verifier re-applies
  `graded_leaves.second_columns` before rebuilding the leaf.
  `GRADED_SECOND_COLS=0` disables this when certifying.
* A row of kind `old` is the regular model's own two-test near row
  (`graded_leaves.old_row`, PROOF.md §6.6).
  * The driver adds it only when the graded stages fail on an inside leaf
    (`OLD_STAGES`), and always as the last row.
  * The verifier rebuilds it from the regenerated input.

**Box tree.** Each box records its dimension orders:
* order 2: first-order relaxation;
* order 1: the two tangent cases.

Each case is either an exclusion or integer duals `(Y,V,U,Z₁…Z_K)`. An
exclusion is allowed only for a constraint whose costs are all nonnegative
and whose budget is negative.

**Rows.** A row is regenerated from its kind and parameters. The kinds are:
* `family`: anchor `s₁=⌊λ₁^{lo}⌋_{1/50}`, sieve part zero;
* `shifted`: anchor at the repository shift;
* `graded`: a menu anchor with a sieve part.

Their analytic content is PROOF.md §6.5.
