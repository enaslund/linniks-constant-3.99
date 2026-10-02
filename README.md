# Linnik's constant is at most 3.99

This repository contains the paper *Linnik's constant is at most 3.99*
([`paper/linnik399.pdf`](paper/linnik399.pdf); its source and a single-file version are in
[`paper/`](paper/README.md)) and a Lean 4 / Mathlib (`v4.35.0-rc3`) formalization of parts of
its proof. It is the repository submitted to the [Palomar registry](https://submit.palomar-registry.org).

The [adversarial review reports from October 1–2, 2026](paper/README.md#adversarial-reviews)
record the objections examined, the correction to Example 8.9(i), and the scope and
limitations of the additional checks.

**What is formally verified, and what is not.** The paper proves that for every sufficiently
large modulus `q`, every reduced residue class modulo `q` contains a prime below `q^3.99`. That
bound is **not** formally verified here. The Palomar submission (`comparator.json`) consists of
18 theorems: the paper's graded near-density lemma (Theorem 8.4), a weighted version of
Heath-Brown's near-density estimate (his Lemma 12.1 of 1992), with its zero form; and the
soundness of the exact checker for the certificates of the leaf programs (paper §10). Their
analytic part is conditional on four published estimates, stated as hypotheses no stronger than
their printed sources. The repository proves more than it submits (items 3–6 below). The
zero-location arguments, the case analysis and the exterior regimes of the paper have
conventional proofs and computer checks only (see "What is not formalized").

References of the form "paper §8.2" or "paper Theorem 8.4" are to
[`paper/linnik399.pdf`](paper/linnik399.pdf). Paths beginning with `research/` or
`computations/` refer to the research repository in which this work was developed,
<https://github.com/enaslund/linniks-constant> (private at the time of submission). The
certificates, the programs that generate and check them and the full verification reports are
there. The records of the native Lean runs are in [`runs/`](runs/).

The formalization covers six parts of the proof:

1. **The graded near lemma and its zero form** (paper §§8–9). This is the weighted,
   Selberg-sieve-majorized Gram inequality for zeros of Dirichlet L-functions, the response
   lemma, the threshold form (T), and the entry bounds of the rows.
2. **The leaf LPs and their exact certificates** (paper §10). This is the checker, a proof that it is
   sound, the bridge from (T) to the LP rows, and seven certificates checked by the kernel: six
   leaves of the 3.99 corpus and the program of the large first-zero range. A copy of the checker without Mathlib, proved equal to it, runs natively on the
   whole corpus.
3. **What a certified leaf proves** (paper §§4–6, 10). From Xylouris's prime criterion (3.57), stated as
   printed, a certified leaf with valid data gives a prime `q^{L−2T} < p < q^L` in every reduced
   class. This holds for every modulus whose zeros satisfy the leaf's zero-level hypotheses.
4. **Verified numerics for the leaf data** (paper §§5–6). This part has three pieces: interval
   arithmetic with proved inclusion (including `exp`), enclosures of every leaf function, and a
   numeric checker. The checker is proved to imply that a leaf's integers are valid for its
   metadata.
5. **The concrete tests** (paper §9.1). The rows use the normalized parabolic autocorrelation as
   detector and Gram test. It satisfies Heath-Brown's Conditions 1 and 2, the hypotheses of the
   near lemma on its tests. Condition 2 comes from a general criterion, Heath-Brown's maximum
   principle argument, proved with the Phragmén–Lindelöf principle.
6. **Verified near rows** (paper §§8.6, 9, 10). Each near row of a leaf is a concrete instance of the
   near lemma, built from the row's rational parameters and sieve heights. A native row checker,
   proved sound, verifies that the row's stored integers (radius, features, diagonals) are valid
   for that instance. For a checked row, the stored integers satisfy (T) and the row of the leaf
   LP holds at the configuration's masses, under zero-level hypotheses only. This covers every
   column and every family term, including the three that keep a second zero: the `rc` pair, the
   first family's second zero and the shifted `rc` term with its `C_Z`. Their bounds come from
   enclosures of the transform at complex points, interpolation on grids, closed-form tails and a
   minimum principle, all proved. Only the two-test row (paper §9.6) is not checked.

**Status.** Every proof is complete. There is no `sorry`, no `native_decide` and no new axiom;
`#print axioms` reports only `propext`, `Classical.choice` and `Quot.sound` for every theorem
below. The native runs are compiled Lean programs. Their results transfer to the proved
statements through equality and soundness proofs, but a run is not a kernel check.

Every source file is a module of Lean's module system, as Palomar requires
(`scripts/port_modules.py` converted them; `scripts/palomar_check.py` checks the static
requirements).

This does not prove Linnik's constant 3.99. The remaining parts of the argument are listed
under "What is not formalized".

## The theorems

**1. The near lemma and the zero form.**

| Theorem | Statement | File |
| --- | --- | --- |
| `GradedNear.graded_near_lemma` | The quadratic-form inequality `(Σ a_j R_j)_+² ≤ (1+η) I_B [Σ (D(δ_j) - d₁ + e_j) a_j² + (d₁+η)(Σ a_j)²]` for the prime-sum responses `R_j` | `Statement.lean` |
| `GradedNear.response_lemma` | A response is at least the terms of the zeros it keeps, minus `f(0)/6 + η`, when the other disc zeros left of the anchor are `M`-separated and at most `K₀` | `Response.lean` |
| `GradedNear.graded_near_threshold` | The zero form: the entries satisfy (T), `∃ τ ∈ [0, √d], Σ_j (v_j - τ)_+²/D_j ≤ 1 - τ²/d`, with `v_j` computed from the kept zeros | `ZeroForm.lean` |
| `GradedNear.keptBound_single`, `keptBound_pair`, `keptBound_double`, `keptBound_pair_neg`, `zeroTerm_conj` | Entry bounds (paper §9.4). A kept zero at the entry's height with `λ ≤ hi` gives `F(hi - s_j)`. A second kept zero adds its term, which is nonnegative when it lies at or left of the test point and `≥ -C` for the shifted `rc` entry. A double zero counts twice, and conjugate entries have equal terms | `Entry.lean` |
| `GradedNear.keptBound_pair_neg_real`, `zmult_conj` | For a real character, conjugate zeros have equal multiplicity (`L(s̄, χ) = conj L(s, χ)`, `LFunction_conj`). The shifted `rc` entry bound therefore needs no multiplicity hypothesis | `Conj.lean` |
| `GradedNear.single_zero_threshold` | (T) with the features `(F(hi_j - s_j) - f(0)/6 - η)/N`, for rows whose entries each keep one zero | `Entry.lean` |
| `GradedNear.builder_threshold` | (T) in the leaf builders' normalization: features `r_j/√(I_u D_u) - η`, diagonals `(1+η)D_j⁺/D_u`, radius `(1+η)(d₁/D_u + η)`, with no numerical side conditions | `Builder.lean` |
| `GradedNear.pairExcess_eq_zero` | Same-character pairs at separated normalized heights carry no pair excess | `Builder.lean` |
| `GradedNear.burgessBound_of_primitive` | Burgess's bound for every non-principal character and `N ≥ 0`, from the printed statement for primitive characters and `N ≥ 1` | `BurgessReduction.lean` |

**2. The certificates.**

| Theorem | Statement | File |
| --- | --- | --- |
| `GradedNear.Cert.near_row_of_bins` | Binning the entries of a row conservatively into the columns and family terms of a leaf turns (T) into that row of the leaf LP (`Cert.Feasible`), at a column vector shared by all rows | `Cert/Bins.lean` |
| `GradedNear.Cert.checkLeaf_sound`, `checkLeaf_lt`, `certified` | If `Cert.checkLeaf L T = some v`, every feasible point of the leaf LP has objective `≤ v < S` (`S = 10¹⁶`, so the objective is below 1) | `Cert/Sound.lean` |
| `GradedNear.Cert.checkLeaf_ofCore` | The Mathlib-free checker computes the same value: `CertCore.checkLeaf L T = Cert.checkLeaf (Leaf.ofCore L) (Tree.ofCore T)` | `Cert/FastEq.lean` |
| `GradedNear.Cert.Samples.bound_*` (six leaves, and `bound_large_3_99`) | The LPs of six leaves of the 3.99 corpus, and the LP of the large first-zero range `λ₁ ≥ 3/2` (paper Theorem 12.6), have objective below 1 at every feasible point; `checkLeaf` is evaluated by the kernel (`decide +kernel`) | `Cert/Samples/*.lean` |

**3. What a certified leaf proves.**

| Theorem | Statement | File |
| --- | --- | --- |
| `GradedNear.exists_prime_of_criterion` | From (3.57): for an admissible triangle kernel supported in `[A, L]`, if the zero sum plus `ε` is below `H(0)`, every reduced class has a prime `q^A < p < q^L` | `Prime.lean` |
| `GradedNear.Kernel.exists_prime` | The same for the 3.99 step kernel (31 triangles, `T = .416829`), admissible for `L > 3 + 2T` | `Kernel.lean` |
| `GradedNear.Cert.leaf_relaxation`, `leaf_interpretation` | A certified leaf bounds the total cost below 1 for characters placed in columns with a meaning (`ColSem`). Bins are charged at their ends and tails carry mass `w(λ)`. The column data must be valid and the objectives monotone | `Cert/Relaxation.lean`, `Cert/Semantics.lean` |
| `GradedNear.certified_leaf_gives_prime` | Composes the two: a certified leaf plus the zero-level hypotheses gives primes | `LeafPrime.lean` |
| `GradedNear.Cert.valid_leaf_gives_prime` | For a leaf whose data are valid for its metadata (`MetaValid`), with a corpus far profile, `φ ≥ 0` and `L ≥ 3.99`, the hypotheses on the columns' objective and far data, the far budget and the first-family charge are discharged. The count, hidden-count, second-family, `final` and near-row integers still enter as they are. Monotonicity comes from `ColumnMono`, `H(0) = H₀` from `KernelFacts`, and `w > 0` decreasing from `FarFacts` | `LeafTheorem.lean` |
| `GradedNear.Cert.checked_leaf_gives_prime` | The same for a leaf accepted by the two native checks (`CertCore.checkLeaf`, `LeafCheckCore.checkNum`) | `LeafChecked.lean` |
| `GradedNear.envelope_column`, `far_from_lemma` | Adapters from the inputs to the zero-level hypotheses. The envelope bounds an ordinary column's zero sum. X Lemma 5.1, applied with `η/2`, bounds the far weights, including the inside first family's `n·w(b)` | `Adapters.lean` |
| `GradedNear.Kernel.FarProfile.far_bound_corpus` | Both corpus far profiles satisfy the printed conditions of X Lemma 5.1, and `Σ_χ w(λ_χ) ≤ (1+η)V` for `q ≥ q₀` | `FarFacts.lean` |

**4. Verified numerics.**

| Theorem | Statement | File |
| --- | --- | --- |
| `IntervalCore.Ival.mem_add`, `mem_mul`, `mem_div`, `mem_exp`, … | Inclusion for every operation of the interval library (`IntervalCore.lean`, precision `2⁻¹²⁸`), including `Real.exp` (argument reduction, Taylor bounds, squaring) | `Interval/Sound.lean` |
| `LeafNumCore.gphi_sound`, `cpa_sound`, `jold_sound`, `jnew_sound`, `winv_sound`, `V_le_vUpper`, … | Each enclosure of `LeafNumCore.lean` contains the value of the real function in `Functions.lean`: `B_φ`, `G_φ`, `h`, `C(p,a)`, `J_old`, `J_new`, `w⁻¹`, `w`, `V`. The far weight's integral is done by substitution and a Taylor series with a proved remainder | `LeafNumSound.lean` |
| `GradedNear.Cert.checkNum_sound` | `LeafCheckCore.checkNum m L = true → MetaValid m (Leaf.ofCore L)`: each column is valid for its meaning, and so are the far budget and the first-family charge | `Cert/NumericsSound.lean` |

**5. The concrete tests.**

| Theorem | Statement | File |
| --- | --- | --- |
| `GradedNear.Admissible.laplace_differentiable` | For `f` satisfying Condition 1, the Laplace transform `F` is entire (differentiation under the integral on `[0, x₀]`) | `Admissible.lean` |
| `GradedNear.condition2_of_imag_axis` | Condition 1, `f ≥ 0` on `[0, ∞)` and `Re F(iy) ≥ 0` for all real `y` give Condition 2. This is Heath-Brown's argument [HB, §7, p. 36], by Phragmén–Lindelöf in the right half-plane applied to `exp(−F)` | `Admissible.lean` |
| `GradedNear.Parabolic.fpar_condition1`, `fpar_condition2` | The parabolic test `f(t) = P(t/c)` on `[0, c]` (`c = 2γ`, `P(u) = (1−u)³(1+3u+u²)`, `f(0) = 1`) satisfies Condition 1 with `B = 10/c²`, and Condition 2 | `Parabolic.lean` |
| `GradedNear.Parabolic.integral_P_cos`, `cos_numerator_eq` | `∫₀¹ P(s) cos(ws) ds = 60 (w cos(w/2) − 2 sin(w/2))² / w⁶` for `w ≠ 0`, the closed form of `Re F(iy) ≥ 0` | `Parabolic.lean` |

**6. Verified near rows.**

| Theorem | Statement | File |
| --- | --- | --- |
| `GradedNear.Parabolic.laplace_fpar_real`, `Phi_eq_closed`, `Phi_sub_taylor` | At a real point the transform is `F(x) = c Φ(cx)`, `Φ(u) = ∫₀¹ P(s) e^{−us} ds`. `Φ` has a closed form for `u ≠ 0` (five integrations by parts) and a Taylor polynomial with remainder for `\|u\| ≤ 1` | `Parabolic.lean` |
| `GradedNear.Row.Params.valid`, `IB_le`, `IB_pos`, `Dδ_eq`, `Dδ_anti` | The `NearData` of a row, built from its rational parameters, is valid. `I_B` is at most the builders' upper Riemann sum (2,000 short cells and the sieve cells), and `I_B > 0`. `D(δ) = 2g₁ Φ(2g₁(2δ − s₁)) + Σ_k c_k e^{−2δ t_k}`, which decreases in `δ` | `Row.lean` |
| `GradedNear.Row.phiI_sound`, `fI_sound`, `ibUpper_sound`, `dI_sound` | The enclosures of the Mathlib-free row checker `RowCheckCore` contain the true values | `Row/CheckSound.lean` |
| `GradedNear.Parabolic.laplace_fpar_eq`, `PhiC_eq_closed`, `PhiC_sub_taylor`, `E2_eq_closed`, `E2_sub_taylor` | At a complex point `F(z) = c ΦC(cz)`; `ΦC` has a closed form for `u ≠ 0` and a Taylor polynomial with remainder for `‖u‖ ≤ 1`, and so has the exponential moment `E₂(α) = ∫₀¹ s² P(s) e^{αs} ds` (eight integrations by parts) | `ParabolicComplex.lean`, `Moments.lean` |
| `GradedNear.Row.cosSinI_sound`, `rePhiCI_sound`, `reFI_sound`, `e2I_sound` | The checker's enclosures of `cos`, `sin` (Taylor at `q/2^k`, then `k` angle doublings), `Re ΦC`, `Re F(x + iy)` and `E₂` contain the true values | `Row/SpecialSound.lean` |
| `GradedNear.Parabolic.vert_grid_lower`, `vert_grid_upper`, `vert_cell_upper`, `horiz_lipschitz` | `Re F` on a vertical line from grid values, with the second-derivative bound `∫ t² f e^{−xt}` (`interp_lower`: a concavity argument); `\|Re F(x + iy) − Re F(x₀ + iy)\| ≤ c² m₁ \|x − x₀\|` for `x, x₀ ≥ 0` | `Row/SpecialBounds.lean`, `Interp.lean`, `Vertical.lean` |
| `GradedNear.Parabolic.tail_re_le`, `tail_neg_re_le`, `re_ge_of_line` | On `Re z = −d`, `\|Im z\| ≥ U`: `Re F` and `−Re F` are bounded by the closed form's tail. The minimum principle: `Re F ≥ −C` on the line `Re z = −d` gives it on the half-plane `Re z ≥ −d` (Phragmén–Lindelöf for `exp(−F(w − d))`) | `Row/SpecialBounds.lean` |
| `GradedNear.Row.specVals_sound`, `twoVals_sound`, `czC_sound` | The values `(add, exc)` the checker computes for an entry's semantics mean what `SpecSem` says: for a second zero left of the test point (the `rc` pair, `y = 2μ₁`, and the first family's second zero), `add ≤ Re F(x + iy)` and `Re G(−s₁ + iy) − 1/6 ≤ exc` on the entry's range of `(x, \|y\|)`; for the shifted `rc` entry, `add = −C_Z ≤ Re F(z)` on `Re z ≥ a − s` | `Row/SpecSound.lean` |
| `GradedNear.Row.rowCheck_sound`, `checkRow_sound`, `checkRows_sound` | An accepted row is valid (`RowNum`). There are `I_u ≥ I_B` and `D_u > 0` such that the stored radius is at least `(1+η)(1/6/D_u + η)`. Each checked entry (feature at `hi` from the anchor `anc`, values `(add, exc)` of its semantics) has stored feature at most `(F(hi − anc) + add − 1/6)/√(I_u D_u) − η`, a diagonal numerator `D(s − anc) − 1/6 > 0`, and a stored diagonal at least `(1+η)D⁺/D_u` for some `D⁺ ≥ D(s − anc) − 1/6 + exc`. Every column and family term with a positive feature has a checked entry | `Row/RowSound.lean` |
| `GradedNear.Row.row_threshold` | For a checked row, the stored integers satisfy (T) for every configuration of entries satisfying the zero-level conditions of `builder_threshold`, when each entry's kept zeros give at least `F(hi − anc) + add − 1/6` (or that is `≤ 0`) and its pair excess is at most `exc`, for the values of its semantics (`keptBound_single`, `keptBound_pair`, `keptBound_pair_neg_real` give these from `SpecSem`) | `Row/Threshold.lean` |
| `GradedNear.Row.row_at_masses` | With `near_row_of_bins`: a checked row of the leaf LP holds at the configuration's masses. This is `Cert.valid_leaf_gives_prime`'s hypothesis `hrows` for that row, from zero-level facts only | `Row/Masses.lean` |
| `GradedNear.Row.checked_leaf_rows_gives_prime` | **A leaf whose certificate, numerics and near rows pass the native checks** (`CertCore.checkLeaf`, `LeafCheckCore.checkNum`, `RowCheckCore.checkRows`) **gives primes** `q^{L−2T} < p < q^L` in every reduced class. It composes `checked_leaf_gives_prime` with `row_at_masses`: each checked row enters through its zero-level configuration (`RowZero`), and only a row without metadata (the inherited two-test row) enters as the row itself | `Row/LeafRows.lean` |

## Hypotheses

The analytic part is **conditional** on printed results, each stated as a hypothesis no stronger
than its source, and on one derived statement:

| Hypothesis | Source | Used by |
| --- | --- | --- |
| `XylourisLemma31` | Xylouris 2011, Lemma 3.1 = Heath-Brown 1992, Lemma 5.3 (principal prime sums) | near lemma |
| `XylourisLemma32` | Xylouris 2011, Lemma 3.2 = Heath-Brown 1992, Lemma 5.2 (local explicit formula), with φ ≤ 1/3 | near lemma, response lemma |
| `BurgessPrimitive` | Heath-Brown 1992, Lemma 2.1, `k = 3`, as printed (primitive characters) | near lemma |
| `GrahamEstimate` | Graham 1978; Heath-Brown 1992, (11.13) with U = 1 | near lemma |
| `XylourisCriterion357` | Xylouris 2011, (3.57)–(3.58), pp. 34–35 (finite combinations of triangles) | prime extraction |
| `XylourisLemma51` | Xylouris 2011, Lemma 5.1, (5.19), p. 66 | far budget |
| `OrdinaryEnvelope` (derived, not printed) | paper §5 (Proposition 5.5): X Lemma 3.10 with the local formula | `envelope_column` |

Everything else is proved here, including:
* Mertens' first theorem with explicit constants, and the Riemann-sum limit of the first
  Cauchy–Schwarz factor;
* the Selberg majorant of Λ, partial summation against Graham's estimate, and Abel summation
  against the pointwise Burgess bound, whose non-primitive form comes by Möbius inversion;
* the decay of the Laplace transform `F(x + iY)` in `Y` (integration by parts), the finiteness
  of the zeros of `L(s, χ)` in a disc, and the positivity and conjugation symmetry of zero
  multiplicities;
* the threshold identity (T);
* the row relaxations of the certificates: the first-order relaxation, the tangent pair by
  convexity, and the safe direction of every integer rounding; weak duality with the free dual
  of the second-family equality; exclusions; the bisection trees and the root box;
* the prime extraction from (3.57), the admissibility and normalization of the step kernel, the
  printed conditions of X Lemma 5.1 for both far profiles, and the monotonicity of every column
  meaning;
* interval arithmetic and the enclosures of the leaf functions.

## What is not formalized

The formal statements are tied to the rest of the 3.99 argument by these unformalized links:
* **The case tree and zero location** (paper §§7, 11). This is the map from a modulus to a
  leaf and its columns: which zeros exist where, the kept sets `S_j`, the separation `M`, and the
  count `K₀` (paper §6.3). It also includes the count, hidden-count and second-family constraints.
  `valid_leaf_gives_prime` takes these as zero-level hypotheses.
* **The family bounds** [R] (the rest of the zero sum, charged in `first`) and the derivation of
  `OrdinaryEnvelope` from X Lemma 3.10.
* **The exterior regimes** (paper §12). The small exceptional-zero range is not formalized. The program
  of the large first-zero range `λ₁ ≥ 3/2` is a leaf in the format above
  (`computations/graded/graded_large.py` in the research repository). Its certificate (natively and in the kernel), numeric
  data and near row pass the three checkers, so `checked_leaf_rows_gives_prime` applies to it. What
  is not formalized there is that every modulus with `λ₁ ≥ 3/2` satisfies its zero-level
  hypotheses.
* **The literature inputs** listed above, and X Lemma 3.3 (used to derive `SafeAnchor`).
* **The count-type integers, and the near rows in the leaf theorem.** `MetaValid` constrains each
  column's `G` and `W`, the far budget `F` and the first-family charge `first`. The integers `C`,
  `NH`, `E`, `ng`, `n2` and `final` enter the hypotheses of `valid_leaf_gives_prime` as they are;
  an mpmath reproduction checked `C`, `NH`, `E` and `final` on 154 leaves
  ([`runs/numerics_check_3.99.json`](runs/numerics_check_3.99.json)). The near rows (`v`, `D`, `d`) also
  enter as the hypothesis `hrows` of `valid_leaf_gives_prime`; `checked_leaf_rows_gives_prime`
  discharges it for every row that `rowcheck` accepts, from each row's zero-level configuration.
  The two-test row (paper §9.6) has no row checker and still enters as it is. It is compared
  exactly with the earlier implementation of the same inequality (paper §14, item 5).
* **The metadata.** The numeric checker proves that `G`, `W`, `F` and `first` are valid for the
  leaf's metadata (spans, objectives, profile). Whether that metadata describes the leaf's case is
  part of the case tree.

## Layout

| File | Content |
| --- | --- |
| `GradedNear/Defs.lean` | Every definition the compared theorems use, with the literature hypotheses of the near lemma (imports only Mathlib): the near lemma's data, the zero form, and the certificate checker (mirrors the acceptance test of `computations/graded/graded_cert.py`) with the leaf LP semantics |
| `GradedNear/Statement.lean`, `Main.lean` | `graded_near_lemma` and its assembly |
| `GradedNear/Basic.lean`, `Expansion.lean`, `Gram.lean`, `Entries.lean`, `Bookkeeping.lean`, `GramForm.lean` | Finite-sum identities, weighted Cauchy–Schwarz, the Gram part |
| `GradedNear/FirstFactor.lean`, `FirstPart.lean` | Mertens and the upper Riemann sum |
| `GradedNear/Sieve*.lean`, `BurgessReduction.lean` | Sieve part: majorant, Graham diagonal, Burgess off-diagonal, cells, errors; Burgess from the primitive form |
| `GradedNear/LaplaceDecay.lean`, `ZeroFinite.lean`, `Response.lean`, `Conj.lean` | The response lemma; conjugation of `L`-functions and multiplicities |
| `GradedNear/Threshold.lean`, `ZeroForm.lean`, `Entry.lean`, `Builder.lean` | (T), the zero form, the entry bounds, the builders' normalization, the pair excess |
| `GradedNear/Cert/Relax.lean`, `Sound.lean`, `Bins.lean` | Row relaxations, checker soundness, binning |
| `GradedNear/Cert/Samples/*.lean` | Seven kernel-checked certificates, one module per leaf: six leaves of the corpus (generated by `computations/graded/graded_lean_export.py --split-dir` in the research repository) and the large first-zero range (`Large.lean`, generated by `computations/graded/graded_large.py --lean-module`) |
| `CertCore.lean`, `GradedNear/Cert/FastEq.lean`, `CertRunNative.lean` | The checker without Mathlib, its equality with `Cert.checkLeaf`, and the native runner `certrun` |
| `GradedNear/Prime.lean`, `Kernel.lean`, `KernelFacts.lean` | (3.57) as printed and prime extraction; the step kernel and its facts |
| `GradedNear/Functions.lean`, `Far.lean`, `FarFacts.lean`, `Envelope.lean` | The leaf functions and far profiles; X Lemma 5.1 as printed and the far bound; the envelope hypothesis |
| `GradedNear/Cert/Relaxation.lean`, `Semantics.lean`, `LeafPrime.lean`, `ColumnMono.lean`, `LeafTheorem.lean`, `LeafChecked.lean`, `Adapters.lean` | What a certified leaf proves, down to the zero-level hypotheses |
| `IntervalCore.lean`, `GradedNear/Interval/Sound.lean` | Interval arithmetic without Mathlib, and its soundness |
| `LeafNumCore.lean`, `GradedNear/LeafNumSound.lean` | Enclosures of the leaf functions without Mathlib, and their soundness |
| `LeafMetaCore.lean`, `GradedNear/Cert/NumericsSpec.lean` | Leaf metadata, and what a leaf's numbers must satisfy (`MetaValid`) |
| `LeafCheckCore.lean`, `GradedNear/Cert/NumericsSound.lean`, `LeafCheckNative.lean` | The numeric checker, its soundness, and the native runner `leafcheck` (certificates and numerics) |
| `GradedNear/Admissible.lean`, `GradedNear/Parabolic.lean` | The criterion for Condition 2; Conditions 1–2 for the parabolic tests, and their transform at real points |
| `GradedNear/ParabolicComplex.lean`, `Moments.lean`, `Interp.lean`, `Vertical.lean` | The transform at complex points; moments and the exponential moment `E₂`; interpolation with a second-derivative bound; derivatives along vertical and horizontal lines |
| `GradedNear/Row.lean`, `GradedNear/Row/*.lean` | The near row as a concrete `NearData` (`Row.lean`); the soundness of the row checker's enclosures (`CheckSound`, `SpecialSound`), the analytic bounds of the special entries (`SpecialBounds`), their values (`SpecSound`) and the row check (`RowSound`); (T) for the stored integers and the row at the masses (`Threshold`, `Masses`) |
| `RowCheckCore.lean`, `RowCheckNative.lean` | The row checker without Mathlib, with the enclosures at complex points for the special entries, and its native runner `rowcheck` (`graded_lean_export.py --rows`) |
| `Challenge.lean` | Palomar Challenge, generated by `scripts/make_challenge.py` (`Defs.lean` verbatim plus the eighteen statements) |
| `Solution.lean`, `comparator.json`, `Audit.lean` | Palomar Solution, Comparator configuration, axiom audit |
| `scripts/Compare.lean` | Local stand-in for Palomar's Comparator (same algorithm) |
| `scripts/CertRun.lean` | Runs the checker in the Lean interpreter on leaves streamed as JSON lines |
| `formalization.yaml` | Palomar metadata (formalization.yaml v0.4) |
| `scripts/palomar_check.py` | Local check of Palomar's static requirements: modules, line limits, the Challenge's size and imports, pins, toolchain, `comparator.json`, licence, metadata shapes |
| `scripts/palomar_emulate.sh` | Local emulation of Palomar's mechanical run on a machine the size of its hosted profile (4 CPUs, 15 GiB cap): the Challenge and Solution builds and exports, then `lake comparator` with the toolchain's nanoda and con-ron kernels, reporting time and peak memory per step. It is not Palomar's preflight, which must be run through Palomar's reusable workflow |
| `scripts/port_modules.py` | The one-time conversion of the sources to modules (`--check` reports files that are not modules) |

## Build and verify

```bash
lake exe cache get          # Mathlib v4.35.0-rc3 oleans
lake build                  # the library, Challenge and Solution
lake build Samples          # the kernel-checked certificates (7-16 GB of memory per leaf)
lake build certrun leafcheck rowcheck  # the native runners (no Mathlib compiled)
scripts/verify.sh           # all of the above, plus Palomar's static checks, Challenge
                            # regeneration, comparison, axiom audit and leanchecker replay
python3 scripts/palomar_check.py   # Palomar's static requirements only
```

The whole corpus is checked natively by streaming leaves from the replay. The corpora and the
replay are in the research repository, not here; from its root (with this package in
`lean-graded/`), rebuild the packed corpora and stream them:

```bash
computations/graded/corpora/assemble.sh
python3 computations/graded/graded_lean_export.py --kind outside --roots all --full \
    --workers 6 --out outside.json
python3 computations/graded/graded_lean_export.py --kind inside --roots all --full \
    --workers 6 --out inside.json
python3 computations/graded/graded_lean_export.py --kind inside --roots all --rows \
    --workers 6 --out rows_inside.json     # the near rows (rowcheck); likewise --kind outside
```

The Lean FRO Comparator can be run locally from its source (`leanprover/comparator`) with a
pass-through `landrun`. See the verification record.

## Verification record (2026-09-30 and 2026-10-01)

| Check | Result |
| --- | --- |
| `scripts/verify.sh` | **PASS** (2026-10-01, in this repository; 14 min with Mathlib prebuilt, peak 43.4 GB): Palomar's static checks (1 warning: the Challenge's advisory size), Challenge regeneration unchanged, every build including the seven kernel-checked samples and `certrun`, `leafcheck`, `rowcheck`, the comparison (18 theorems, 53,995 reachable constants, 0 problems), the axiom audit (96 declarations, all `[propext, Classical.choice, Quot.sound]`), and `leanchecker` on all 78 modules (the six Mathlib-free cores, every `GradedNear` module, `Solution`) |
| Axioms (`Audit.lean`) | `[propext, Classical.choice, Quot.sound]` for all 96 audited declarations: the compared theorems, the leaf-level theorems, the seven sample bounds, and the near-row theorems (`specVals_sound`, `rowCheck_sound`, `row_at_masses`, `checked_leaf_rows_gives_prime`, …) |
| Large first-zero range | `computations/graded/graded_large.py --lean` in the research repository (2026-09-30): `certrun`, `leafcheck` (numerics `ok`) and `rowcheck` (150 entries) accept the leaf of `λ₁ ≥ 3/2`, value 9966813270344512/10¹⁶ on 36 boxes; `lake build GradedNear.Cert.Samples.Large` checks the same certificate in the kernel (12 s, 3.8 GB). Record: [`runs/large_3.99.json`](runs/large_3.99.json) |
| Stand-in comparison (`scripts/Compare.lean`) | 18 statements equal; 0 problems |
| **Lean FRO Comparator** (`leanprover/comparator`, built from source) | **"nanoda kernel accepts the solution. Lean default kernel accepts the solution. Your solution is okay!"** (2026-09-30, 9 min, `comparator.json` as committed, with `enable_nanoda: true` and the machine's `nanoda_bin` 0.4.17). Run locally with a pass-through `landrun` (no sandbox, which is only needed for untrusted solutions); Palomar runs the sandbox on submission |
| Kernel-checked certificates | Six leaves: outside roots 1193, 1202, 2455; inside roots 2766, 1155 (two leaves); 122 boxes. Each value equals `graded_cert`'s |
| The native checker (`certrun`) on the outside corpus | All 1,685 roots, 1,642 leaves, 87,424 boxes in 660 s: every value and box count equals `graded_cert`'s ([`runs/certrun_native_outside_3.99.json`](runs/certrun_native_outside_3.99.json)) |
| The native checker on the inside corpus | **PASS**, in `leafcheck` (next row), which runs this checker and the numeric checker in one pass |
| Certificates and numerics (`leafcheck`) | **Outside: PASS.** All 1,685 roots, 1,642 leaves, 87,424 boxes and 1,303,174 columns in 3,113 s. Every value and box count equals `graded_cert`'s, and every leaf passes `checkNum` ([`runs/leafcheck_full_outside_3.99.json`](runs/leafcheck_full_outside_3.99.json)). **Inside: PASS.** All 2,768 roots, 3,949 certificate trees and 4,109,455 boxes in 10,169 s (12 workers), maximum numerator 9999998223456687. The trees are the parts of the corpus's 3,146 leaf records (2,913 leaves and 233 identities nodes); a split leaf (the `rc` pair's `μ` split, the second zero's `y` pieces) has one tree per part, and the per-root tree counts equal the corpus's. Every value and box count equals `graded_cert`'s, and every tree's leaf passes `checkNum` ([`runs/leafcheck_full_inside_3.99.json`](runs/leafcheck_full_inside_3.99.json)) |
| The near rows (`rowcheck`) | **Outside: PASS.** All 1,685 roots and 1,642 leaves: 3,314 rows, all with metadata, and 2,021,521 checked entries in 395 s (12 workers) ([`runs/rowcheck_outside_3.99.json`](runs/rowcheck_outside_3.99.json)). The outside rows have no special terms. **Inside: PASS.** All 2,768 roots and 3,949 certificate trees: 13,565 rows, of which the 13,528 with metadata pass (the other 37 are the inherited two-test rows), and 9,113,802 checked entries, 1,706 of them special (the `rc` pair, the first family's second zero, the shifted `rc` entry), in 3,665 s ([`runs/rowcheck_inside_3.99.json`](runs/rowcheck_inside_3.99.json)) |
| The interpreted checker (`scripts/CertRun.lean`) | The outside corpus, and 48 inside roots (85 leaves, 65,422 boxes, including the tightest leaves), all equal to `graded_cert` (`runs/certrun_*`) |
| Independent review of the statements | Near lemma and certificates: no soundness problem; its scope findings are addressed. Leaf level: no unsound statement; its two scope findings (the envelope's radius, the coverage claims) are fixed (`research/notes/leaf-formalization-2026-09-29.md` §5, in the research repository) |

**Findings of the formalization.**
* **Family counts.** Both row relaxations of the checker need nonnegative family counts. Without
  them there are counterexamples, which the soundness proof found and which were checked in exact
  arithmetic. `graded_cert.Leaf` already asserts the condition, and `Cert.wellFormed` requires it.
* **Auxiliary constants.** Lean abstracts proofs inside definitions (here, numeral instances such
  as `Nat.AtLeastTwo 6`) into auxiliary constants and shares them only within a module. Running
  the Comparator showed that definitions split over several modules therefore differ from their
  copies in the single-file Challenge. All definitions now live in `Defs.lean`, which the Challenge
  copies verbatim.
* **Burgess.** The printed Lemma 2.1 is for primitive characters. The near lemma's form, for all
  non-principal characters and `N ≥ 0`, is now derived from it rather than assumed.
* **The far budget has slack.** The stored `F` is `⌈S(1+η)V⌉ − n⌊S w(b)⌋`. X Lemma 5.1 holds for
  every tolerance, so the leaf theorem applies it with `η/2`.
* **Diagonal positivity at the true offset.** The row builders test `D(δ) − d₁ > 0` at the offset
  rounded down to the grid `1/200`, where `D` is larger; the near lemma needs it at the true offset
  `s − anc`. The row checker verifies it at the grid point above (`delHi`), where `D` is smaller.
  No corpus entry was affected: the smallest margin is 0.0805.

**Limits.**
* The kernel evaluates `checkLeaf` at about 2 s and 1–2 GB per box. A 70-box inside leaf needed
  more than 22 GB and was dropped from the samples.
* The native runs trust the Lean compiler and runtime, and the runners' JSON parsing, which is
  not verified. The runners compare the parsed values with the replay's own.
* The leaf-level and near-row statements are not part of the Palomar Challenge. The Challenge has
  989 of its 1,000 allowed lines, and these statements need their own definitions.
* All reviews so far are by AI agents. No human has reviewed the statements.

## Authorship and the use of AI

The paper and this formalization were produced by AI systems under the direction of Eric
Naslund; the note after the paper's abstract describes how. The Lean code was written with
Claude Code (Anthropic's Claude Opus 5.5). The formal statements were reviewed against the
printed sources by AI agents. No human has yet reviewed the formal statements or refereed the
underlying mathematics.

## Licence

The contents of this repository are released under the Apache License 2.0
([`LICENSE`](LICENSE)).
