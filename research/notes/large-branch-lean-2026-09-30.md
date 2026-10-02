# The large first-zero range in the verified checkers (2026-09-30)

**Question.** The exterior certificate for `λ₁ ≥ 1.5` (paper Theorem 12.6) had been checked by
only one program: the exact checker of the 4.33 computation (`verify_published_single.py`, rerun
2026-09-29 in `existing_components_verified.json`). The graded replay, the independent checker
and the Lean checkers had never seen it. The author asked for it to be checked in Lean.

**What was done.** `computations/graded/graded_large.py` rebuilds the program as a leaf of the
graded pipeline and checks it.
* **Columns.** The 150 bins `[3/2 + j/100, 3/2 + (j+1)/100)` and the tail `[3, ∞)`, with the
  objective `G_{1/3}` at the left end, far weight `w` at the right end (profile I),
  `F = ⌈S(1+η)V⌉`, `first = 0` and `final = 5η`. These are regenerated with `make_large` and
  compared with `core/results/large_branch_3.99.json`: identical.
* **Near row.** It is rebuilt as a row of the graded pipeline with no family terms:
  * `SieveNearTest(γ = 1, g₁ = 3/2, t₀ = 1, μ = 10⁹, s = s₁ = 3/2)`, all sieve heights 0;
  * each bin's feature at its right end from the anchor `3/2`;
  * the tail's feature is 0.

  Every zero in `R(l)` has parameter `≥ λ₁ ≥ 3/2 = s₁`, so the safe-anchor hypothesis holds. This
  is Corollary 8.10 of the paper with `I_u` the builders' upper Riemann sum (2,000 cells on each
  of `[0, 1)` and `[1, 2)`).
* **Certificate.** A comb tree over the 36 threshold intervals of the earlier certificate, with
  the first-order relaxation on each. The duals are proposed with SciPy's HiGHS (`highspy` is not
  installed here) and checked exactly by `graded_cert.check_case`.

**Result.**

| Check | Result |
| --- | --- |
| `graded_cert.verify_tree` | maximum 0.9966813270344512, 36 boxes, binding interval [0.1625, 0.165] |
| `certrun` (compiled verified checker) | same value and box count |
| `leafcheck` (certificate and `checkNum`) | same value and box count; numerics `ok` |
| `rowcheck` (`checkRows`) | `ok`: 1 row, 150 entries checked |
| kernel (`GradedNear/Cert/Samples/Large.lean`, `decide +kernel`) | `checkLeaf … = some 9966813270344512`; 12 s, 3.8 GB; axioms `propext`, `Classical.choice`, `Quot.sound` |
| `leanchecker GradedNear.Cert.Samples.Large` | ok |
| `lean-graded/scripts/verify.sh`, full rerun | PASS: 78 modules through `leanchecker`, 96 audited declarations with the standard axioms, Palomar's static checks unchanged (10 min with cached builds) |

The records are `computations/graded/large_3.99.json` (the program, the row and the certificate)
and `computations/graded/lean_runs/large_3.99.json` (the checker outputs and the kernel run).
Since the leaf passes all three native checks, `checked_leaf_rows_gives_prime` applies to it,
with the same kind of zero-level hypotheses as a leaf of the case tree.

**Why the value changed from 0.99465 to 0.99668.**
* The earlier row was normalized with a tight enclosure of `I_B = ∫ e^{st} f²/g`: exactly
  1.45483…, for the normalized parabolic tests.
* The builders' and the Lean row checker's upper Riemann sum is 1.45675…, 0.13% larger. Every
  feature is therefore 0.066% smaller (ratio 0.999341); `d` and `D` are unchanged.
* Near the binding threshold `τ ≈ 0.16` the row enters through `(v − τ)²` with `v − τ ≈ 0.05`,
  so that small change moves the certified value by 0.002.
* The row checker rejects the earlier features. Its normalization is the Riemann sum, and the
  earlier features exceed what that sum allows by about 1.5·10⁻⁴.
* A finer grid would recover most of the difference; for example, more sieve cells, which
  `RowP` allows. This was not needed: the margin below 1 is 0.0033.

**Scope.** The Lean checks cover the certificate, the objective and far integers, and the near
row. Two things are not formalized:
* that every modulus with `λ₁ ≥ 1.5` satisfies the program's zero-level hypotheses: every
  character counted at its height-one representative, with the envelope bound of Corollary 5.7;
* the small exceptional-zero range.

The rewritten independent checker (`computations/audit/independent_cert_check.py`, see the
[independent checker](independent-checker-2026-09-30.md)) accepts this leaf's certificate with
the same value, 0.9966813270344512, on 36 boxes.

**Other changes.**
* The paper's Theorem 12.6 now states `W ≤ 0.9966814 − 2η`.
* §14, the status table and the proof map record the checks.
* The kernel audit (`Audit.lean`) covers `bound_large_3_99`: 96 declarations, all with the
  standard axioms.
* The Lean package's `Samples` library lists the new module. The Palomar targets (Challenge,
  Solution) are unchanged, and `palomar_check.py` passes as before.
