# The independent certificate checker, rewritten and committed (2026-09-30)

**Why.** The paper (§14, item 2) and the
[independent checks](independent-checks-2026-09-29.md) of 2026-09-29 describe a second
certificate verifier. It was written from a description of the certificates, without the replay's
checking code, and it accepted every certificate of the corpus. Its code stayed in that session's
scratchpad (`indep_check/`) and was never committed. That directory has since been deleted, and no
Claude or Codex session transcript on the machine contains the code. The claim therefore could
not be reproduced from the repository. The author asked for the checker to be committed and run
on the new leaf of the large first-zero range.

**What was done.** A fresh agent wrote `computations/audit/independent_cert_check.py` from the
paper's §10 alone, under these rules:
* it did not open, search or import `graded_cert.py`, `CertCore.lean`, `GradedNear/Defs.lean` or
  the Lean `Cert` modules;
* the replay's exporter was only run, as the source of the leaves and as the comparison harness;
* only integer and `Fraction` arithmetic is used, and nothing is imported from the repository.

The program's docstring records these rules and every interpretation it made. The negative test
is `independent_cert_forgeries.py`, and `capture_leaves.py` saves exporter leaves as its input.

**Results** (`computations/audit/independent_cert_3.99.json`).

| Run | Trees | Boxes | Relaxation cases (excluded) | Maximum | Mismatches with `graded_cert` |
| --- | --- | --- | --- | --- | --- |
| inside, all 2,768 roots (10 workers, 28.6 min) | 3,949 | 4,109,455 | 29,076,245 (8,711) | 0.9999998223456687 | 0 |
| outside, all 1,685 roots (5 workers, 5.5 min) | 1,642 | 87,424 | 321,091 (719) | 0.9999942478462508 | 0 |
| large first-zero range (`graded_large.py`) | 1 | 36 | 36 (0) | 0.9966813270344512 | 0 |

The totals equal those of the paper and of the lost checker: 5,591 trees, 4,196,879 boxes and
29,397,336 relaxation cases, 9,430 of them excluded. Every value and box count is exactly the
replay's. The lost checker had reported maxima up to 9·10⁻¹⁶ below the stored ones; this
checker reports none.

**Forgery test** (`independent_cert_forgeries_3.99.txt`). It ran on ten leaves: the large
range, three outside leaves, and six inside leaves including the tightest (2432_1).
* **Invalid:** 34 kinds, 308 certificates, all rejected. They include structural damage,
  unjustified exclusions, duals lowered by the smallest amount that breaks a column inequality,
  and coefficients, budget or allowance raised by the smallest breaking amount.
* **Controls:** 9 kinds, 82 certificates, all accepted. These are the same perturbations one unit
  short of breaking, which shows the checks are exact at the boundary.
* **Data-dependent:** 8 kinds, 65 certificates, 49 rejected. The 16 accepted ones are still valid
  certificates of the modified data.

**What the rewrite found in §10.** The paper was corrected accordingly.
1. §10 defined a terminal box's value as the maximum of its case values, `−1` if all are
   excluded. The replay and the Lean checker take the maximum of `−1` and the case values. The two
   differ only on boxes whose dual cases all have values below `−1`, which occurs. Acceptance
   (`< S`) is unaffected, and no leaf maximum differs. §10 now states the `max(−1, …)` rule.
2. §10 did not fix three conventions: the order of a split's children, the numbering of rows from
   0, and the order of the relaxation cases in a terminal box. It now states all three.
3. `mS` and `2hS` are integers because `2T_S` divides `S`; §10 now says so.
4. The header of `lean-graded/CertRunNative.lean` said `boxes` counts tree nodes; it counts
   terminal boxes. The comment is corrected, and the rebuilt binary is byte-identical.

**The constant audit.** The same lost code also did the 2026-09-29 audit of the leaf constants on
38 leaves (paper §14, item 4). That program cannot be rerun either. The Lean numeric and row
checkers now check the same quantities for every leaf, except the two-test rows, and the paper
says so.
