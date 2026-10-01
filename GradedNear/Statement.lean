module

public import GradedNear.Main
public import GradedNear.BurgessReduction

/-!
# The graded near lemma: statement

Paper §8.2 (Theorem 8.4). For fixed data, every `η > 0` and
all large `q`: for every finite family of entries of height at most `T ≤ (log q)/3` under the
safe-anchor hypothesis at height `2T + 1`, and every `a ≥ 0`,
`(Σ a_j R_j)_+² ≤ (1 + η) I_B [Σ_j (D(δ_j) - d₁ + e_j) a_j² + (d₁ + η)(Σ_j a_j)²]`.
Entries of the same character are allowed only when the sieve weight vanishes.
-/

@[expose] public section

namespace GradedNear

open NearData

/-- **The graded near lemma** (paper Theorem 8.4, slightly generalized). Assumes the four printed
inputs (`XylourisLemma31`, `XylourisLemma32`, `BurgessPrimitive`, `GrahamEstimate`), data `D` with
`D.Valid`, and, for the modulus `q`, the zero-free case hypothesis `SafeAnchor q D.s₁ (2T + 1)`
(not a printed result; it is provable when `s₁ ≤ 0`, and in the application it is the case
hypothesis `s₁ ≤ λ₁` together with [X, Lemma 3.3]). Then for `q ≥ q₀`, all non-principal entries
of height `≤ T ≤ (log q)/3` with offsets in `D.Δ` (distinct characters when the sieve weight is
nonzero) and all `a ≥ 0`:
`(Σ a_j R_j)_+² ≤ (1+η) I_B [Σ_j (D(δ_j) - d₁ + e_j) a_j² + (d₁+η)(Σ_j a_j)²]`. -/
theorem graded_near_lemma
    (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessPrimitive)
    (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid) {η : ℝ} (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
          (max 0 (∑ j, a j * response D E j)) ^ 2 ≤
            (1 + η) * D.IB *
              (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
                (D.d₁ + η) * (∑ j, a j) ^ 2) :=
  graded_near_lemma' hX31 hX32 (burgessBound_of_primitive hBur) hGr D hD hη

end GradedNear
