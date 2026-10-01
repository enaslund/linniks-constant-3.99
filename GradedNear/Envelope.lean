module

public import GradedNear.FarFacts
public import GradedNear.LeafPrime

/-!
# Ordinary characters: the envelope and the error sum (paper §§4–6)

**The envelope** (`OrdinaryEnvelope`) is the per-character cost bound of paper §5 (Proposition 5.5, Corollary 5.7). It is
[X, Lemma 3.10, (3.60)] in the localized form that the paper uses (Remark 5.6). The step kernel violates
Xylouris's Condition 1, so the bound comes from smoothings of the kernel (paper §5.2). It is a
derived input (proved in paper §5, not formalized here), stated here as a hypothesis. It says: if `χ ≠ 1` has no
zero with parameter below `λ` in the disc `|1 − ρ| ≤ δ`, then its zero sum over the prime window
is at most `H₀ G(λ) + ε e^{−Aλ}`.

**The error sum** (paper §5.8). The errors `ε e^{−Aλ_j}` are summed through the far
weight: `e^{−Aλ}/w(λ)` decreases when `A ≥ 2x`, so `Σ_j e^{−Aλ_j} ≤ Σ_j w(λ_j)/w(0)`
(`sum_exp_le`). The far lemma bounds the right side by `(1+η)V/w(0)`.
-/

@[expose] public section

noncomputable section

namespace GradedNear

open Kernel

/-- **The ordinary envelope** (paper §5; derived from [X, Lemma 3.10, (3.60)]). For every
prime window `C > 0`, every `ε > 0` and every `λ_min > 0` there are `δ ∈ (0, 1/2)` and `q₀` such
that the following holds for `q ≥ q₀`, a non-principal `χ` mod `q` and `λ ≥ λ_min`. If `L(s, χ)`
has no zero `ρ` with `|1 − ρ| ≤ δ` and `(1 − Re ρ) log q < λ`, then its zero sum over the window
is at most `H₀ G(λ) + ε e^{−Aλ}`, with `A = L − 2T`.

The bound `δ < 1/2` is what the application needs. An ordinary character's representative is
its rightmost zero with `|γ| ≤ T*`, and `T* ≥ 1/2`. So every zero in the disc lies below height
`T*`, and none has a parameter below the representative's. The radius of X Lemma 3.2 comes
from [HB, Lemma 3.1], whose proof takes `δ ≤ 1/6`. The error `ε e^{−Aλ}` is what the error sum
needs (paper §5.8). For `λ ≤ C` it is X Lemma 3.10 with `ε e^{−AC}`. For `λ > C` and large
`q` the window has no zero, since a zero in it has `|1 − ρ| ≤ √2 C/log q ≤ δ` and parameter
`≤ C < λ`. -/
def OrdinaryEnvelope (Lx : ℝ) : Prop :=
  ∀ C : ℝ, 0 < C → ∀ ε : ℝ, 0 < ε → ∀ lamMin : ℝ, 0 < lamMin →
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ lam : ℝ, lamMin ≤ lam →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖1 - ρ‖ ≤ δ →
        lam ≤ (1 - ρ.re) * Real.log q) →
      rectZeroSum χ (primeKernel Lx).H C ≤
        H0 * G Lx lam + ε * Real.exp (-((Lx - 2 * T) * lam))

/-- **The error sum** (paper §5.8): for parameters `λ_j ≥ 0` and `A ≥ 2x`,
`Σ_j e^{−Aλ_j} ≤ Σ_j w(λ_j) / w(0)`. -/
lemma sum_exp_le (P : FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) {A : ℝ}
    (hA : 2 * P.x ≤ A) {ι : Type*} [Fintype ι] (lam : ι → ℝ) (hlam : ∀ j, 0 ≤ lam j) :
    ∑ j, Real.exp (-(A * lam j)) ≤ (∑ j, P.w (lam j)) / P.w 0 := by
  have hw0 := P.w_pos hc₁ hc₂ 0
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  have hwj := P.w_pos hc₁ hc₂ (lam j)
  have hmono := P.tail_antitone' hc₁ hc₂ hA (hlam j)
  simp only [mul_zero, neg_zero, Real.exp_zero] at hmono
  -- e^{−Aλ}/w(λ) ≤ 1/w(0)
  rw [div_le_div_iff₀ hwj hw0] at hmono
  rw [le_div_iff₀ hw0]
  linarith

end GradedNear
