module

public import Mathlib

/-!
# The threshold form (paper Proposition 8.8)

If `(Σ a_j v_j)_+² ≤ Σ D_j a_j² + d (Σ a_j)²` for all `a ≥ 0`, with every `D_j > 0` and `d > 0`,
then some `τ ∈ [0, √d]` satisfies `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ² / d`.
(Ported from `Linnik430.Near.common_threshold_iff` of the 4.30 library.)

The helpers in `GradedNear.ThresholdAux` are a port of the direction
"quadratic ⇒ threshold" (`Linnik430.Near.exists_common_threshold`). The threshold
is a zero of the continuous scalar function `t ↦ d Σ_j (v_j - t)_+ / D_j - t` on
`[0, b]`, found by the intermediate value theorem; the test vector
`a_j = (v_j - t)_+ / D_j` then turns the quadratic hypothesis into the threshold bound.
-/

@[expose] public section

namespace GradedNear

namespace ThresholdAux

open Finset

noncomputable section

/-- The positive part, with the order of arguments fixed for the formulas below. -/
def pos (x : ℝ) : ℝ := max x 0

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_right _ _

lemma pos_mul (x : ℝ) : pos x * x = (pos x) ^ 2 := by
  rcases le_total x 0 with hx | hx
  · simp [pos, max_eq_right hx]
  · simp [pos, max_eq_left hx, pow_two]

lemma pos_mono {x y : ℝ} (hxy : x ≤ y) : pos x ≤ pos y :=
  max_le_max hxy le_rfl

/-- The resource quadratic form in the scalar two-test inequality. -/
def resource {ι : Type*} [Fintype ι] (D : ι → ℝ) (d : ℝ) (a : ι → ℝ) : ℝ :=
  (∑ i, D i * (a i) ^ 2) + d * (∑ i, a i) ^ 2

lemma resource_nonneg {ι : Type*} [Fintype ι] (D : ι → ℝ) (d : ℝ) (a : ι → ℝ)
    (hD : ∀ i, 0 < D i) (hd : 0 < d) : 0 ≤ resource D d a :=
  add_nonneg
    (Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hD i)) (sq_nonneg _)))
    (mul_nonneg (le_of_lt hd) (sq_nonneg _))

/-- The common-threshold scalar cost. -/
def thresholdCost {ι : Type*} [Fintype ι]
    (v D : ι → ℝ) (d t : ℝ) : ℝ :=
  t ^ 2 / d + ∑ i, (pos (v i - t)) ^ 2 / D i

/-- Existence of the common threshold, by a continuous scalar fixed-point equation. -/
theorem exists_common_threshold {ι : Type*} [Fintype ι]
    (v D : ι → ℝ) (d : ℝ) (hD : ∀ i, 0 < D i) (hd : 0 < d)
    (hquad : ∀ a : ι → ℝ, (∀ i, 0 ≤ a i) →
      (pos (∑ i, a i * v i)) ^ 2 ≤ resource D d a) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ Real.sqrt d ∧ thresholdCost v D d t ≤ 1 := by
  let b : ℝ := d * ∑ i, pos (v i) / D i
  let f : ℝ → ℝ := fun t => d * (∑ i, pos (v i - t) / D i) - t
  have hb : 0 ≤ b := by
    dsimp [b]
    exact mul_nonneg (le_of_lt hd)
      (Finset.sum_nonneg (fun i _ => div_nonneg (pos_nonneg _) (le_of_lt (hD i))))
  have hf : Continuous f := by
    dsimp [f, pos]
    fun_prop
  have hf₀ : 0 ≤ f 0 := by simpa [f, b] using hb
  have hfb : f b ≤ 0 := by
    have hp : (∑ i, pos (v i - b) / D i) ≤ ∑ i, pos (v i) / D i := by
      apply Finset.sum_le_sum
      intro i _
      exact div_le_div_of_nonneg_right (pos_mono (by linarith)) (le_of_lt (hD i))
    have hm := mul_le_mul_of_nonneg_left hp (le_of_lt hd)
    dsimp [f, b] at *
    linarith
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' hb hf.continuousOn ⟨hfb, hf₀⟩
  let a : ι → ℝ := fun i => pos (v i - t) / D i
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    exact div_nonneg (pos_nonneg _) (le_of_lt (hD i))
  have htfix : t = d * ∑ i, a i := by
    change d * (∑ i, a i) - t = 0 at hft
    linarith
  have hcoord : ∀ i, a i * v i = D i * (a i) ^ 2 + t * a i := by
    intro i
    have hi := ne_of_gt (hD i)
    have hp := pos_mul (v i - t)
    dsimp [a]
    field_simp
    nlinarith
  have hdot : (∑ i, a i * v i) = resource D d a := by
    simp_rw [hcoord]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    dsimp [resource]
    rw [htfix]
    ring
  have hres : 0 ≤ resource D d a := resource_nonneg D d a hD hd
  have hres₁ : resource D d a ≤ 1 := by
    have hq := hquad a ha
    rw [hdot, pos, max_eq_left hres] at hq
    nlinarith
  have hcost : thresholdCost v D d t = resource D d a := by
    unfold thresholdCost resource
    have he : ∀ i, (pos (v i - t)) ^ 2 / D i = D i * (a i) ^ 2 := by
      intro i
      dsimp [a]
      field_simp
    simp_rw [he]
    rw [htfix]
    field_simp
    ring
  have ht₂ : t ^ 2 ≤ d := by
    have hsum : 0 ≤ ∑ i, (pos (v i - t)) ^ 2 / D i :=
      Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (le_of_lt (hD i)))
    have hdiv : t ^ 2 / d ≤ 1 := by
      rw [← hcost] at hres₁
      dsimp [thresholdCost] at hres₁
      linarith
    exact (div_le_one hd).1 hdiv
  refine ⟨t, ht.1, ?_, hcost ▸ hres₁⟩
  exact Real.le_sqrt_of_sq_le ht₂

end

end ThresholdAux

theorem threshold_of_quadratic {ι : Type*} [Fintype ι] (v D : ι → ℝ) (d : ℝ)
    (hD : ∀ j, 0 < D j) (hd : 0 < d)
    (hq : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (max 0 (∑ j, a j * v j)) ^ 2 ≤ ∑ j, D j * a j ^ 2 + d * (∑ j, a j) ^ 2) :
    ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt d ∧
      ∑ j, (max 0 (v j - τ)) ^ 2 / D j ≤ 1 - τ ^ 2 / d := by
  have hquad : ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
      (ThresholdAux.pos (∑ j, a j * v j)) ^ 2 ≤ ThresholdAux.resource D d a := by
    intro a ha
    have h := hq a ha
    rw [ThresholdAux.pos, max_comm]
    exact h
  obtain ⟨τ, hτ0, hτd, hcost⟩ := ThresholdAux.exists_common_threshold v D d hD hd hquad
  refine ⟨τ, hτ0, hτd, ?_⟩
  have hmax : ∀ j, max 0 (v j - τ) = ThresholdAux.pos (v j - τ) := fun j => max_comm _ _
  simp only [hmax]
  unfold ThresholdAux.thresholdCost at hcost
  linarith

end GradedNear
