# Closing the literature interfaces of the graded-near proof

Date: 2026-09-29. The graded-near proof ([PROOF.md](../PROOF.md)) shares its
literature-interface items with the 4.30 candidate.

* **Arguments.** An independent review (R3) supplied an argument for each
  item.
* **Checked against the printed text:** items 1, 7c and 7e. The constant
  `K_far` of item 6 was recomputed with the rigorous weight enclosures.
* **Not yet re-checked:** the other items are arguments from that one review.

**Result.** Every listed interface closes, and no certificate number changes.
Two text repairs follow:
* the definition of `K₀` (item 5);
* the explicit split of the error allowance (item 6).

X = Xylouris's dissertation (printed pages); H = Heath-Brown 1992 (retained copy).

## 1. Xylouris's criterion for the step mixture: printed (verified)

X p. 34, between (3.56) and (3.57), states (3.56) and then (3.57) for any
finite linear combination `h=Σ_{i≤M} α_i h_{L_i,K_i}`, with `α_i` real, under
`L_i>2K_i+3`: "Offensichtlich gilt (3.56) auch für dieses neue h und H", and
(3.57) follows for fixed `ε` with `C₀(ε)`, `q₀(ε)`.

The proof's kernel is such a combination.
* `1_{[iκ,(i+1)κ)} * 1_{[jκ,(j+1)κ)}` is the (3.51) triangle with `K=κ` on
  `[(i+j)κ,(i+j+2)κ]`.
* Hence `h(t)=(ψ*ψ)(t-A)=Σ_{k=0}^{30} c_k h_{A+(k+2)κ,κ}(t)` with
  `c_k=Σ_{i+j=k}β_iβ_j>0`.
* Every left endpoint `L_i-2K_i=A+kκ≥A=3.156342>3`.

So (3.57) applies as printed. Any `C_P≥C₀` works, since enlarging the square
only adds nonnegative terms.

Xylouris's own kernel (6.2) is a six-triangle combination, and his (6.31)
uses (3.57) in exactly this way. The signed-formula route of
SOURCE_INTERFACES is not needed.

## 2. Occurrence form

Each cost in PROOF.md §3 bounds a single zero occurrence:
* **Ordinary and reserved-family envelopes.**
  `|H((1-ρ)ℓ)|=e^{-Aλ_ρ}|Ψ(λ_ρ-iμ_ρ)|²≤e^{-Aλ_ρ}Re F_σ((λ_ρ-σ)-iμ_ρ)` for
  `λ_ρ≥σ`, by (3.59) and X Lemma 3.5. The right side is `ρ`'s own term in
  X Lemma 3.2's zero sum, which counts multiplicity. Lemma 3.10 is stated for
  `Σ'|H₂|` (p. 35).
* **First family.** `J_old`/`J_new` treat the distinguished zeros through a
  nonnegative integrand (4.33 §2). `α=2` counts `ρ₁` and `\barρ₁`, and `n=2`
  uses the conjugation symmetry of `R_P`.
* **Hidden columns** are bounded the same way.

So the LP objective bounds the occurrence sum `W_occ`. The grouped route
(3.56) belongs only to the 4.30 corpus's collective envelope and Lean
population interface, which the graded-near proof does not use.

## 3. The empty rectangle

For large `q`, `R_P⊂R(l)`, since `C_P≤log log ℓ/3` (X (6.30), p. 81). If no
nonprincipal `L(s,χ)` vanishes in `R(l)`, the zero sum is empty and
`Σ≥(ℓ/φ(q))(H₀-ε)>0`.

Xylouris states this case himself (p. 36, Bemerkung; p. 81 after (6.31)). The
principal `L`-function has no zeros in `R(l)` for large `q` (X p. 21,
footnote 4).

## 4. Actual-zero row realization

For every configuration with `.1≤λ₁<1.5`, the actual zeros give a feasible
point of the leaf that contains the configuration:
* `x_i`: the number of ordinary characters whose `T*` representative lies in
  bin `i`;
* `x_tail=Σ_{λ_χ≥R}w(λ_χ)`;
* `y_h`: the first-family characters by hidden bin;
* `z_j=n₂·1[ν₂∈` column `j]`;
* characters without an `R_P` zero are dropped, which only weakens the
  constraints.

Each constraint then holds.
* **Far:** X Lemma 5.1 applied to the chosen zeros. X §3.2.2 allows an
  arbitrary choice of zero, and `w` is decreasing.
* **Count:** the global second-family argument of 4.33 §3.
* **Near rows:** the graded lemma gives (T) at some `τ`. Each actual feature
  is at least the column feature, since the feature is taken at the bin's
  right end.
* **Objective:** item 2.
* **Coverage:** the splits are exhaustive, and the replay checks this.

No theorem is missing here. What remains is a line-by-line check that the
generated rows (`make_endgame`, `first_out_input`, `graded_leaves`) are the
instances of PROOF.md §§6.5 and 7. Review 6 audited this once; the
independent checker and review R2 continue it.

## 5. Order of the constants (repairs PROOF.md §§4 and 10)

| Stage | Fixed | Depends on |
| --- | --- | --- |
| S0 | `L`; kernels, far weights, tests, anchors, grids, trees and certificates; `η′=η=10⁻⁶`; `u₀=1/η_{HB}(1/2)` | nothing |
| S1 | `ε_c=ηH₀`; `C_P≥max(C₀(ε_c),3)` | S0 |
| S2 | `K₀` = a uniform bound on the zeros (all characters, with multiplicity) with `λ≤s_max` and **`|γ|≤2`**; `M` such that `|F(x+iY)|≤η′/(2K₀)` and `|G₁(-σ+iY)|≤η′/4` for `|Y|≥M` | S0 |
| S3 | `C_B>max(C_P+M,1.5)` with `4c_out/(H₀C_B²)≤η` | S1, S2 |
| S4 | The source `o(1)` tolerances (X Lemmas 3.1, 3.2, 3.10, 5.1, Graham/Burgess, PNT, table `ε`, small-branch errors) | S0–S3 |
| S5 | `q₀`, the maximum of finitely many thresholds, including `ℓ>4M(K₀+1)` for the `T*` pigeonhole | all |

**Repair.** PROOF.md §4 counted zeros to height `1+δ`. There `δ` is Lemma
3.2's disc radius, which depends on the S4 tolerance, while `M` (S2) depends
on `K₀`. Counting to height 2 removes this circularity, since `δ<1` always.

## 6. The split of the error allowance `final=5η`

| Term | Content | Bound |
| --- | --- | --- |
| E1 | The criterion's `ε`: `ε_c/H₀` | `η` |
| E2 | The envelope errors. Each character contributes `e^{-Aλ_χ}ε₁/H₀`. Since `A>2x`, `e^{-Aλ}/w(λ)≤1/w(0)`, so `Σ_χe^{-Aλ_χ}≤(1+η)V/w(0)=K_far`, at most 16.372 (inherited weight) or 18.472 (retuned); recomputed 2026-09-29. The summation is as in H §14 and X (6.32) | `η`, with `ε₁=ηH₀/19` |
| E3 | At most four outside distinguished terms, each `≤c_out/C_B²` | `η`, by the choice in S3 |

The total is at most `3η<5η`.

These are already inside other bounds and are not charged here:
* prime powers (inside (3.57));
* the far lemma's `ε` (inside `(1+η)V`);
* the near-lemma errors (inside `η′`);
* enclosure errors (outward rounding).

If the auxiliary smoothing of §10 is kept, its error
`K_far·[N(C_P)·2‖ψ-ψ_δ‖₁/‖ψ‖₁+sup|B_δ-B|]` can also be made at most `η`.

## 7. Further interfaces found by the review

* **(a) Lemma 5.1's selection:** closed. X §3.2.2 allows an arbitrary choice
  of zero per character, and `q₀` depends only on the chosen parameters.
* **(b) One common height `l` for the H and X tables:** derived from the
  proofs, low risk. H Lemma 6.1 proves that some `l=10^k` works. Later proofs
  use `l` only through `1≤l≤ℓ/10` and the zero-free annulus, and Xylouris
  applies Heath-Brown's lemmas inside his own `R(l)`. The residual is a
  written confirmation for each table.
* **(c) The localized envelope at `T*` representatives:** needs Lemma 3.2's
  disc radius `δ<T*`. H's proof of Lemma 3.1 (p. 14) takes
  `δ=min(1/(2k),ε₀/(3c₀k²))` with `k≥3`, so `δ≤1/6<1/2≤T*`. The proof works
  for every smaller `δ`, and H remarks after Lemma 5.2 (p. 24) that
  `δ=1/log 𝓛` may be taken. **Checked against the printed text
  (2026-09-29).** It is now stated in PROOF.md §3.
* **(d) Smoothing is optional.** The step kernel's `f_λ` can be written as 16
  Condition-1 pieces, with a `C²` rebalancing term so that every piece but one
  vanishes at 0. X Lemma 3.10 then applies to the exact step kernel, which
  would remove §10's step 3 and its error. The printed Lemma 3.10 omits the
  hypothesis `f_{1i}(0)≥0`, which its proof uses; the rebalanced decomposition
  satisfies it. **Not adopted**: the proof keeps its reviewed smoothing route,
  and this is recorded as an alternative.
* **(e) X (4.34) is printed (verified).** X pp. 58–59 show that the term in
  (4.34) is at most 0 on `λ₁∈[.44,.80]`, `λ₂∈[.44,1.176]` with `γ=1.04`. So
  (4.31) holds as printed for real `χ₁`, `ρ₁`.
  `computations/sieve_near/third_refine.py` uses exactly `γ=26/25`. The refined
  `rr` third bound therefore rests on a printed inequality; the repository's
  floating recheck is confirmatory only.
* **(f) Uniformity of Lemmas 3.1, 3.2 and 3.10 over a family:** the printed
  dependence paragraph, X p. 36.
