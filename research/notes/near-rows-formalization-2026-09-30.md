# Verified near rows, the special family terms, and Palomar readiness

Date: 2026-09-29/30. This round continued [`lean-graded/`](../../README.md) after the
[leaf formalization](leaf-formalization-2026-09-29.md), on a larger machine. It did four things:
1. finished the inside corpus run of the native certificate and numeric checks;
2. ported the project to Lean's module system and checked Palomar's static requirements;
3. formalized the concrete tests (Heath-Brown's Conditions 1–2 for the parabolic tests);
4. verified the near rows of the leaves: every column and every family term, including the
   three that keep a second zero.

Everything compiles with standard axioms only, with no `sorry` and no `native_decide`. The native
runs are compiled Lean programs; their results transfer to the proved statements through
soundness and equality proofs, but a run is not a kernel check.

## 1. The inside corpus run

`graded_lean_export.py --kind inside --roots all --full` with the native `leafcheck`
(`computations/graded/lean_runs/leafcheck_full_inside_3.99.json`):
* **PASS**: 2,768 roots, 4,109,455 boxes, maximum numerator 9999998223456687, 0 mismatches and
  0 numeric failures. Every value and box count equals `graded_cert`'s, and every leaf passes
  `checkNum`.
* 10,169 s of wall time with 12 workers. The `leafcheck` calls took 78,777 s in all (certificates
  75,797 s, numerics 2,547 s); per tree the median was 5.9 s and the maximum 811 s.
* **What "leaves" counts.** The run reports 3,949 leaves; the corpus has 3,146 leaf records
  (2,913 inside leaves and 233 identities nodes). Both are right: some leaf records are split
  into parts (the `rc` pair's `μ` split and the second zero's `y` pieces), and each part has its
  own certificate tree. The run counts trees. The corpus holds exactly 3,949 trees, and the run's
  per-root tree count equals the corpus's for all 2,768 roots. The box total is the corpus's.

With the outside run (1,685 roots, 1,642 leaves, 87,424 boxes), every certificate and every
leaf's numeric data of the 3.99 corpus now pass the native checks.

## 2. Palomar readiness

* **Modules.** Every `.lean` file of `lean-graded/` is a module (`module`, `public import`,
  `@[expose] public section`), as Palomar requires. `scripts/port_modules.py` converted them;
  `--check` reports files that are not modules.
* **Static requirements.** `scripts/palomar_check.py` checks: modules of at most 10,000 lines; the
  Challenge's size (989 lines, 50,370 bytes, under the hard limits of 1,000 lines and 100 KiB)
  and imports; the Mathlib and toolchain pins (`v4.35.0-rc3`, at least Palomar's `v4.35.0-rc2`);
  `comparator.json`; the licence (Apache-2.0); the shapes of `formalization.yaml` (v0.4).
  `verify.sh` runs it first. It passes with three warnings: the Challenge is above Palomar's
  300-line advisory size, and the authors and maintainers of `formalization.yaml` are left as
  `TO CONFIRM` for the submitter.
* **Comparator.** The Lean FRO Comparator accepts the package with both kernels: "nanoda kernel
  accepts the solution. Lean default kernel accepts the solution. Your solution is okay!"
  (2026-09-30, 9 min; the committed `comparator.json` with `enable_nanoda: true`, and the
  machine's `nanoda_bin` 0.4.17). It ran locally with a pass-through `landrun`, which only matters
  for untrusted solutions; Palomar runs the sandbox on submission.
* **What a submission needs** (not done; no submission without the user):
  * a standalone repository holding `lean-graded/`, since the monorepo's `lean/` directory is not
    made of modules and the repository exceeds Palomar's 500 MiB;
  * the authors and responsible maintainers;
  * Palomar's own preflight, which runs as a public GitHub Actions workflow.

## 3. The concrete tests

The rows use the normalized parabolic autocorrelation `f(t) = P(t/c)` on `[0, c]`,
`P(u) = (1−u)³(1+3u+u²)`, as detector (`c = 2γ`) and Gram test (`c = 2g₁`).
* `fpar_condition1`: Condition 1 with `B = 10/c²`.
* `condition2_of_imag_axis`: Condition 1, `f ≥ 0` and `Re F(iy) ≥ 0` give Condition 2
  (Heath-Brown's argument, by Phragmén–Lindelöf applied to `exp(−F)`).
* `integral_P_cos`: `∫₀¹ P(s) cos(ws) ds = 60 (w cos(w/2) − 2 sin(w/2))²/w⁶`, so `Re F(iy) ≥ 0`, and
  `fpar_condition2` follows.

## 4. Verified near rows

Each near row of a leaf is a concrete instance of the near lemma (`GradedNear/Row.lean`):
`Params` holds the row's rational parameters (`γ`, `g₁`, `t₀`, `s`, `s₁` and the sieve heights),
and `Params.near` is its `NearData`, proved valid. `I_B` is at most the builders' upper Riemann
sum, and `D(δ) = 2g₁Φ(2g₁(2δ − s₁)) + Σ_k c_k e^{−2δt_k}` decreases in `δ`.

`RowCheckCore.rowCheck` (Mathlib-free, run natively as `rowcheck`) recomputes `I_L ≥ I_B`, the
diagonals `D(δ)` and the transforms `F(x)` in interval arithmetic, chooses the normalizer, and
checks every stored feature, diagonal and radius. The chain of proved statements:
* `rowCheck_sound`, `checkRow_sound`: an accepted row is valid (`RowNum`), and every column or
  family term with a positive feature has a checked entry;
* `row_threshold`: the stored integers satisfy (T) for every configuration of entries that the
  row describes, under the zero-level conditions of `builder_threshold`;
* `row_at_masses`: with `near_row_of_bins`, the row of the leaf LP holds at the configuration's
  masses. This is the hypothesis `hrows` of `valid_leaf_gives_prime` for that row;
* `checked_leaf_rows_gives_prime` (`Row/LeafRows.lean`): the composition with the leaf theorem
  `checked_leaf_gives_prime`. For a leaf whose certificate, numerics and near rows pass the native
  checks, the near-row integers no longer enter as hypotheses: each checked row enters through
  its zero-level configuration (`RowZero`), and only a row without metadata enters as the row
  itself.

**Finding: the diagonal's positivity was checked at the wrong offset.** The builders test
`D(δ) − d₁ > 0` at the offset rounded down to the grid `1/200`, where `D` is larger. The proof
needs it at the true offset `s − anc`. The entries therefore carry the grid point above,
`delHi ≥ s − anc`, and the checker verifies `D(delHi) > 1/6`. On the corpus the smallest margin
is 0.0805 over 4,193 parameter sets, so no entry was affected.

**Precision.** The builders' `I_up` exceeds the checker's `I_L` by about `9.2·10⁻¹³` relative
(the builders' `(1 + 2⁻⁴⁰)` factor). This margin absorbs the differences between the two
enclosures of `F` and `D`.

## 5. The special family terms

Three family terms keep a second zero (PROOF.md §6.5):
* the **`rc` pair**: the conjugate zero `ρ̄₁`, at height difference `2μ₁`;
* the **first family's second zero**: `ρ′` for `ρ₁`'s entry and `ρ₁` for `ρ′`'s entry, at height
  difference `y`, both left of the test point;
* the **shifted `rc` entry**: the conjugate zero anywhere in `Re z ≥ a − s`, with `C_Z`.

Their bounds are now checked. An entry's semantics carries a `Spec`, and the checker computes its
values `(add, exc)`: a lower bound for the second zero's term and an upper bound for the pair
excess. `SpecSem` states what they mean, and `specVals_sound` proves it:
* **`two`** (pair and second zero). `add ≤ Re F(x + iy)` for `x ∈ [xa, xb]` and `|y|` in the
  entry's range, and `Re G(−s₁ + iy) − 1/6 ≤ exc`. The checker evaluates `Re F` at the midpoint
  `x₀` and `Re G` on the builders' grid of `y`; the slack is `c³m₂h²/8` and `c²m₁(xb − xa)/2` for
  `F`, and `c₁³E₂(c₁s₁)h²/8` for `G`. Beyond `y = 10` (`20` for the pair), it uses `Re F ≥ 0` and
  the closed-form tail of `G`.
* **`cz`** (shifted `rc`). `add = −C` with `Re F(z) ≥ −C` on `Re z ≥ −d`, `d = s − a`. The checker
  bounds `−Re F` on the line `Re z = −d` from the builders' adaptive cells (slack
  `c³E₂(cd)(b − a)²/8`) and the closed-form tail beyond `|y| = 20`. The minimum principle extends
  this to the half-plane.

The ingredients, all proved:
* `laplace_fpar_eq`, `PhiC_eq_closed`, `PhiC_sub_taylor`: `F(z) = cΦC(cz)` at complex points, with
  the closed form and the Taylor polynomial of `ΦC`;
* `E2_eq_closed`, `E2_sub_taylor`, `moment2_exp_eq`: the exponential moment
  `E₂(α) = ∫₀¹ s²P(s)e^{αs} ds` (eight integrations by parts), which bounds the second derivative
  on a line left of the imaginary axis;
* `cosSinI_sound`, `rePhiCI_sound`, `reFI_sound`, `e2I_sound`: the checker's enclosures. `cos` and
  `sin` come from the Taylor sum at `q/2^k` (`|q/2^k| ≤ 1/2`, 30 terms, exact rational complex
  arithmetic) and `k` angle doublings;
* `interp_lower`, `grid_lower`: a function with `g'' ≤ M` is at least `min(g(a), g(b)) − M(b−a)²/8`
  on `[a, b]` (a concavity argument), and its grid form;
* `vert_grid_lower`, `vert_grid_upper`, `vert_cell_upper`: along a vertical line the second
  derivative is `−Re G₂`, bounded by `∫ t²f(t)e^{−xt} dt`;
* `horiz_lipschitz`: `|Re F(x + iy) − Re F(x₀ + iy)| ≤ c²m₁|x − x₀|` for `x, x₀ ≥ 0`;
* `tail_re_le`, `tail_neg_re_le`: from the closed form,
  `Re F(−d + iy) ≤ cR(cU, e^{cd})` and `−Re F(−d + iy) ≤ d/U² + cR(cU, e^{cd})` for `|y| ≥ U`, with
  `R(u, E) = 10/u³ + 30/u⁴ + 120/u⁶ + E(30/u⁴ + 120/u⁵ + 120/u⁶)`. These are the builders' tails;
* `re_ge_of_line`: the minimum principle, by Phragmén–Lindelöf for `exp(−F(w − d))` on `Re w ≥ 0`.

`row_threshold` and `row_at_masses` now take, for each entry, the zero-level statement: for every
values `(add, exc)` satisfying `SpecSem`, the kept zeros give at least `F(hi − anc) + add − 1/6`
(or that number is `≤ 0`), and the pair excess is at most `exc`. `keptBound_single`,
`keptBound_pair` and `keptBound_pair_neg_real` give it from the zeros' locations.

**The checker's values agree with the builders'.** On roots 1083 (the pair and the shifted
entry) and 1283 (the second zero, six `y` pieces), the Lean values equal the Python builders'
`R_lo`, `Rp`, `Rq`, `c_hi` and `C_Z` to six printed digits, for example:

| Entry | Lean `(add, exc)` | Builders |
| --- | --- | --- |
| 1083, pair, `μ ∈ [0, 1]` | `(0.322071, 1.375602)` | `(0.3220712, 1.3756017)` |
| 1083, shifted `rc`, `d = 0.302` (216 cell ends) | `(−0.034119, 0)` | `C_Z = 0.0341187` |
| 1283, second zero, `y ∈ [0, 1]` | `(0.593990, 1.393292)`, `(0.707512, 1.393292)` | `(0.5939901, 1.3932916)`, `(0.7075124, 1.3932916)` |

The exporter (`graded_lean_export.py --rows`) writes each special term's `Spec` from the row
specification: the pair's and second zero's ranges and grid sizes, and for the shifted entry the
cells of the builders' adaptive refinement (`_cz_cells`, the same refinement as `C_upper`). The
exporter is unverified glue; the checker recomputes every bound from the parameters.

## 6. The row runs

* **Outside** (`computations/graded/lean_runs/rowcheck_outside_3.99.json`): PASS. All 1,685 roots
  and 1,642 leaves, 3,314 rows, all with metadata, and 2,021,521 checked entries, in 395 s with 12 workers. The
  outside rows have no special terms.
* **Inside** (`computations/graded/lean_runs/rowcheck_inside_3.99.json`): **PASS.** All 2,768
  roots and 3,949 certificate trees: 13,565 rows, of which the 13,528 with metadata pass; the other 37 are the
  inherited two-test rows. 9,113,802 checked entries, of which 1,706 keep a second zero (the `rc`
  pair, the second zero's pieces and the shifted `rc` entry). 3,665 s with 12 workers; the
  checker's own time was 16,158 s in all, the rest is the replay.

## 7. Verification

* `lean-graded/scripts/verify.sh`: **PASS** (2026-09-30, 26 min). It runs Palomar's static checks,
  regenerates the Challenge (unchanged), builds everything (the library, the six kernel-checked
  samples, `certrun`, `leafcheck` and `rowcheck`), compares the Challenge with the Solution
  (18 statements, 53,995 reachable constants, 0 problems), audits the axioms (95 declarations,
  all `[propext, Classical.choice, Quot.sound]`) and replays all 77 modules with `leanchecker`.
* The Lean FRO Comparator with both kernels (§2).
* The special entries' values against the Python builders (§5).

## 8. What remains

* The **inherited two-test row** (PROOF.md §6.6) has no row checker. The corpus uses it once in
  each of 37 inside roots: 10, 11, 15–18, 20–36, 1198–1201, 1212–1215, 1218, 1219, 2603, 2608,
  2613 and 2633. Of the 13,565 near rows of the inside run, these 37 are the only ones without
  metadata.
* The **zero-level configurations** of the rows (`RowZero`: which zeros each entry keeps, their
  locations and separations, and the bins) are hypotheses of `checked_leaf_rows_gives_prime`.
  Supplying them is part of the unformalized case tree.
* The **count-type integers** (`C`, `NH`, `E`, `ng`, `n2`, `final`) are checked by mpmath only.
* The case tree and zero location, the family bounds [R], the exterior regimes and the
  literature inputs, as before (STATE).
