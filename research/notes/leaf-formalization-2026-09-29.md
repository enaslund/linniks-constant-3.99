# The leaf level in Lean: native checking, the leaf theorem and verified numerics

Date: 2026-09-29. This round extends [`lean-graded/`](../../README.md) in three
directions:
1. three quick wins: a native certificate checker with an equality proof, Burgess from its
   printed primitive form, and conjugate multiplicity;
2. a theorem saying what a certified leaf proves about primes;
3. verified numerics for the leaf data.

Everything below compiles with standard axioms only, with no `sorry` and no `native_decide`.
The native runs are compiled Lean programs. Their soundness transfers through equality proofs
(below), but a run result is not a kernel-checked theorem.

## 1. Quick wins

**The native checker.** `CertCore.lean` copies the certificate checker without Mathlib, so it
compiles to native code. `GradedNear/Cert/FastEq.lean` proves the two checkers equal:
`checkLeaf_ofCore : CertCore.checkLeaf L T = Cert.checkLeaf (Leaf.ofCore L) (Tree.ofCore T)`.
`Cert.checkLeaf_sound` therefore applies to every leaf that the native program `certrun`
accepts.
* **Outside corpus:** all 1,685 roots, 1,642 leaves and 87,424 boxes, in 660 s. Every value and
  box count equals `graded_cert`'s (`computations/graded/lean_runs/certrun_native_outside_3.99.json`).
* **Inside corpus (with the identities nodes):** the native `leafcheck` (§3), which runs this
  checker together with the numeric checker, accepts every certificate: all 2,768 roots, 3,949
  certificate trees (the parts of the corpus's 3,146 leaf records: 2,913 leaves and 233
  identities nodes; a split leaf has one tree per part) and 4,109,455 boxes, maximum numerator
  9999998223456687. Every value and box count equals `graded_cert`'s
  (`computations/graded/lean_runs/leafcheck_full_inside_3.99.json`, 2026-09-29/30; see the
  [near-row note](near-rows-formalization-2026-09-30.md) §1).

The interpreted checker needed 40–180 ms per box, which is about 1,000 times slower.

**Burgess from the printed statement.** `BurgessPrimitive` is [HB, Lemma 2.1] with `k = 3`, as
printed: primitive `χ`, `N ≥ 1`, `1 ≤ H ≤ q`. `burgessBound_of_primitive` derives the form the near
lemma uses (every non-principal character, `N ≥ 0`), in the following steps:
* Möbius inversion over the primes of `q` not dividing the conductor;
* removal of complete periods;
* a shift by `q*`;
* `τ(q) ≪_ε q^ε` (`card_divisors_le_rpow`, also proved).

The headline theorems now take `BurgessPrimitive`.

**Conjugate multiplicity.** For a real non-principal character, `L(s, χ)` commutes with complex
conjugation (`LFunction_conj`). Conjugate zeros therefore have equal multiplicity (`zmult_conj`).
`keptBound_pair_neg_real` is the shifted `rc` entry bound without its multiplicity hypothesis.

The Challenge has 18 compared theorems in 984 lines (the limit is 1,000).

## 2. What a certified leaf proves

The chain, each step compiled:

| Theorem | Content |
| --- | --- |
| `exists_prime_of_criterion` (`Prime.lean`) | Xylouris (3.57), stated as printed (`XylourisCriterion357`), gives a prime `q^A < p < q^L` in every reduced class when the zero sum plus `ε` is below `H(0)`, for any admissible triangle kernel supported in `[A, L]`. |
| `Kernel.exists_prime` (`Kernel.lean`) | The same for the 3.99 step kernel `h = Σ c_k h_{A+(k+2)κ, κ}` (31 triangles; `T = .416829`, `κ = T/16`), admissible for `L > 3 + 2T`. |
| `leaf_relaxation` (`Cert/Relaxation.lean`) | A certified leaf bounds the cost of any mass vector satisfying the per-column bounds and the LP rows. |
| `leaf_interpretation` (`Cert/Semantics.lean`) | The same for characters placed in columns with a meaning (`ColSem`: bins charged at `lo`/`hi`, tails with mass `w(λ)`), valid integer data and monotone objectives. |
| `certified_leaf_gives_prime` (`LeafPrime.lean`) | Composes the two: a certified leaf plus the zero-level hypotheses gives primes. |
| `valid_leaf_gives_prime` (`LeafTheorem.lean`) | For a leaf whose data are valid for its metadata (`MetaValid`), with a corpus far profile, `φ ≥ 0` and `L ≥ 3.99`, the hypotheses on the columns' objective and far data (`G`, `W`), the far budget `F` and the first-family charge `first` are discharged. |
| `envelope_column`, `far_from_lemma` (`Adapters.lean`) | The envelope gives the zero-sum bound of an ordinary column. X Lemma 5.1 (with `η/2`) gives the far hypothesis, including the inside first family's `n·w(b)`. |

**Proved facts used by the chain.**
* `KernelFacts`: `H(0) = H₀` for the step kernel, `B_φ` and `G_φ` decrease, and the closed forms
  of `hRatio` and `C(p, a)`.
* `FarFacts`: both corpus profiles satisfy the printed conditions of X Lemma 5.1; `w > 0`, `w`
  decreases, and the far bound `Σ w(λ_χ) ≤ (1+η)V` holds for `q ≥ q₀`.
* `ColumnMono`: every column meaning in the corpus is monotone. For bins `g` decreases; for tails
  `g/w` decreases.

**Hypotheses.**
* Two printed results, stated as printed: `XylourisCriterion357` ([X, (3.57)–(3.58), pp. 34–35])
  and `XylourisLemma51` ([X, Lemma 5.1, (5.19), p. 66]).
* `OrdinaryEnvelope`, which is derived, not printed. It is PROOF.md §3's form of the envelope
  (X Lemma 3.10 with the local formula).

**What `valid_leaf_gives_prime` still assumes.** These are statements about the zeros of the
characters mod `q`. Some of them involve leaf integers that `MetaValid` does not constrain and
that enter as they are: the count, hidden-count and second-family coefficients `C`, `NH`, `E` with
`ng`, `n2`, the error budget `final`, and the near-row integers `v`, `D`, `d`. The statements are:
* a zero-sum bound for each placed character, which the envelope gives for ordinary columns;
* the rest covered by the first-family charge plus an extra term (PROOF.md's first- and
  second-family bounds [R]);
* the far weights within `(1+η/2)V`, which `far_from_lemma` gives for chosen zeros in
  X's far region;
* the count, hidden-count and second-family constraints;
* the near rows at the masses. `builder_threshold` and `near_row_of_bins` give these, given the
  zero-location facts.

The case tree (§8), which decides which leaf a modulus falls in and where its characters go, is
not formalized. Neither are the exterior regimes (§9).

## 3. Verified numerics

**Specification.** [What the graded-leaf LP data mean](leaf-data-semantics-2026-09-29.md) traced
each stored integer to its formula. The exporter's `--numerics` mode writes each leaf's metadata:
* the exponent `L` and `η`;
* the far profile;
* each column's span and objective;
* the inside first family and a reserved family.

`leaf_numerics_check.py` recomputed the column and budget integers from the metadata alone, in
mpmath at 50 digits: `G`, `W`, `C`, `NH` and `E` for every column, and `F`, `first` and `final`
for every leaf. All 530,942 integers matched exactly (154 leaves, 117 roots, all seven leaf
types). The near-row integers were not part of this check. The
closest any `S·x` came to an integer is `4.95·10⁻⁷`, far above the Lean enclosures' width.

**Lean.**
* `IntervalCore` implements rational interval arithmetic without Mathlib: outward rounding at
  `2⁻¹²⁸`, and `exp` by argument reduction, Taylor series and squaring.
* `GradedNear/Interval/Sound.lean` proves every operation's inclusion theorem, including `Real.exp`.
* `LeafNumCore` builds enclosures of the leaf functions without Mathlib: `B_φ`, `G_φ`, the `h`
  ratio, `C(p, a)`, `J_old`, `J_new`, `w⁻¹`, `w` and `V`.
* `GradedNear/LeafNumSound.lean` proves each enclosure sound against the definitions in
  `Functions.lean`. That includes the quadratures behind `C(p, a)` and `w⁻¹`, done in closed form
  or as a series with a proved remainder.
* `Cert/NumericsSpec.lean` states what the data must satisfy (`MetaValid`):
  * each column valid for its meaning;
  * the far budget `F ≥ S·[(1+η/2)V − reserved]`;
  * the first-family charge `first ≥ S·[J + n₂ G_{φ₂}(lo₂)]`.
* `LeafCheckCore.checkNum m L` checks a leaf's integers against its metadata with these
  enclosures, without Mathlib. It computes each distinct `G_φ`, `B_φ` and `w⁻¹` point once per leaf.
  `checkNum_sound` proves that acceptance implies `MetaValid m (Leaf.ofCore L)`. `checkNum_profile`,
  `checkNum_phi`, `checkNum_L`, `checkNum_eta` and `checkNum_jnew` prove the side conditions:
  * a corpus profile, `φ ≥ 0`, `L ≥ 3.99` and `η > 0`;
  * `J_new` is used only when `p ≥ b`, for the family whose `n·w(b)` leaves the far budget.
* `checked_leaf_gives_prime` joins the two native checks to the leaf theorem. If
  `CertCore.checkLeaf L T = some v` and `checkNum m L = true`, the conclusion of
  `valid_leaf_gives_prime` holds for the leaf.
* **The native runner `leafcheck`** runs both checks on leaves streamed by
  `graded_lean_export.py --full`. The runner parses the metadata; this parsing is unverified glue.
  It then compares the metadata's copies of the stored integers (each column's `G` and `W`, `F`
  and `first`) with the leaf's.
  * **Tests.** On 67 leaves the runner agreed with `graded_cert` on every value and box count,
    and every numeric check passed. The leaves cover 12 named and 40 random roots and every leaf
    type, including `J_new` and reserved columns. The numeric check takes 0.4–0.7 s per leaf,
    about 1 ms per column; the certificate check takes 0.15–12.5 s.
  * **Mutations.** 160 errors were planted in six leaves. 145 were rejected with the right
    reason. The other 15 are still valid data, all moves in the safe direction: the mpmath
    reference gives a positive margin for each. An example is `F − 10¹²` on a retuned leaf, whose
    `η/2` slack is `1.22·10¹²`. `first − 1` is rejected even where the true margin is `−0.04/S`.
  * **Corpus run.** The whole outside corpus passes both checks: 1,685 roots, 1,642 leaves,
    87,424 boxes and 1,303,174 columns in 3,113 s, with every value and box count equal to
    `graded_cert`'s (`computations/graded/lean_runs/leafcheck_full_outside_3.99.json`). The
    numeric check took 0.69 s per leaf on average. The inside corpus passes both checks in one
    run: all 2,768 roots, 3,949 certificate trees (the parts of 3,146 leaf records) and
    4,109,455 boxes, with every value and box count equal to `graded_cert`'s and 0 numeric
    failures, in 10,169 s with 12 workers
    (`computations/graded/lean_runs/leafcheck_full_inside_3.99.json`).

## 4. Findings

* **The far budget has slack.** The stored `F` is `⌈S(1+η)V⌉ − n⌊S w(b)⌋`. X Lemma 5.1 holds for
  every tolerance, so the Lean statement applies it with `η/2` and leaves half of `η` unused.
* **One path is untested.** No corpus leaf charges a reserved family without columns (`J₂` in
  `first`). The metadata and `MetaValid` cover that path, but no real data exercise it.
* **Positivity is needed.** `φ ≥ 0` and `L ≥ 3.99` are needed for the monotonicity of every
  column meaning. Both are checked from the metadata.
* **`J_new` was not tied to its condition.** The metadata recorded that `J_new` applies, but not
  why. `checkNum` now requires `p ≥ b` for the charged family and identifies that family with the
  far budget's inside family (`checkNum_jnew`).

## 5. Independent review of the leaf level

An independent agent reviewed the statements of this round against the printed pages, the
builders' code and the semantics note. It found **no unsound statement**.

**Checked and found correct.**
* `XylourisCriterion357` against X pp. 33–35 and H Lemma 13.2: the triangles (3.51), admissibility
  `L > 2K + 3`, the quantifier order `∀k ∀ε ∃C₀ ∃q₀`, the weight `log p/p · h(log p/𝓛)`, the factor
  `𝓛/φ(q)`, the rectangle (3.58) and multiplicities.
* `XylourisLemma51` and `ProfileCondition` against X p. 66 and pp. 25–26, including the index
  shift and `(M² + ε)/(c₁c₂²)`.
* `BurgessPrimitive` against H Lemma 2.1.
* The functions and kernel against the code. `V` (175.2664…, 243.3209…), `w(0)`, `2x` and `H₀`
  were recomputed from the Lean formulas. `B_φ` and `C(p, a)` agree with the code's enclosures to
  `10⁻⁸`.
* The leaf chain. There is no reachable trivialization (`tsum`, `finsum`, division by zero,
  `getD` defaults), and every rounding direction of `MetaValid` matches the builders.
* `FastEq`. The conversions are bijections that map every field in order.

**Findings, all fixed.**
1. *Scope.* `OrdinaryEnvelope` put no upper bound on the disc radius `δ`. A provider could take a
   huge `δ`, and the per-character premise would then constrain zeros that the `T*`
   representative does not control. The hypothesis now requires `δ < 1/2`, as PROOF.md §3 does.
   H's proof gives `δ ≤ 1/6`.
2. *Scope.* The docs claimed that every hypothesis about the leaf's numbers was discharged.
   `MetaValid` covers `G`, `W`, `F` and `first` only. The docs now list the integers that enter
   as they are: `C`, `NH`, `E`, `ng`, `n2`, `final` and the near rows. They also say what the
   mpmath reproduction covered.
3. *Scope, minor.* `far_from_lemma` handled only the inside family. It now takes a bound `b_k`
   for each character charged without columns, which covers both terms of `farReserved`.
4. *Cosmetic.* PROOF.md §3 stated the envelope error as `ε`, while E2 and the Lean statement use
   `εe^{−Aλ}`. PROOF.md now states that form and derives it from Lemma 3.10.
5. *Cosmetic.* A docstring named the wrong predicate.
6. *Cosmetic.* `XylourisLemma51` allowed the principal character. It now requires `χ ≠ 1`, which
   only weakens it. `L(s, χ₀)` has no zero in the region anyway.

## 6. Not formalized

* The case tree and zero location (PROOF.md §§5, 8). This is the map from an actual modulus to a
  leaf and its columns, with the count rules and the kept sets.
* The count-type and near-row integers of each leaf: `C`, `NH`, `E`, `ng`, `n2`, `final`, and the
  rows' `v`, `D`, `d`. They enter the leaf theorem as they are. Their checks are mpmath only:
  the reproduction covered `C`, `NH`, `E` and `final` on 154 leaves, and the earlier audit covered
  the near rows of 38 leaves. Verifying the near rows in Lean would need enclosures of `I_B`,
  `D(δ)`, `F` and the family terms (rc pair, dz, `C_Z`). That is a larger project than the column
  data.
* The exterior regimes (§9).
* The first- and second-family bounds [R], and the derivation of `OrdinaryEnvelope` from
  X Lemma 3.10.
* Four more printed inputs, stated as hypotheses: X Lemmas 3.1–3.2, Burgess and Graham, which
  feed the near lemma.
