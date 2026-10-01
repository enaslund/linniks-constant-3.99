module

public import GradedNear.Entries
public import GradedNear.Bookkeeping

/-!
# The Gram form bound

For all large `q`, entries of height `≤ T ≤ (log q)/3`, the safe anchor at height `2T + 1`
and `a ≥ 0`:
`𝓛⁻¹ Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk}) ≤
  Σ_j (∫ g e^{(s₁ - 2δ_j)u} - d₁ + e_j) a_j² + (d₁ + ε)(Σ a)²` (paper §8.5).
-/

@[expose] public section

open Complex MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

/-- The Laplace transform of a real function commutes with conjugation. -/
lemma laplace_conj (g : ℝ → ℝ) (z : ℂ) :
    laplace g ((starRingEnd ℂ) z) = (starRingEnd ℂ) (laplace g z) := by
  unfold laplace
  rw [← integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg]

lemma laplace_re_conj (g : ℝ → ℝ) (z : ℂ) :
    (laplace g ((starRingEnd ℂ) z)).re = (laplace g z).re := by
  rw [laplace_conj, Complex.conj_re]

/-- At a real argument `-x`, `Re G(-x) = ∫₀^∞ g(u) e^{x u} du`. -/
lemma laplace_re_neg_real (g : ℝ → ℝ) (x : ℝ) :
    (laplace g (((-x : ℝ)) : ℂ)).re = ∫ u in Set.Ioi (0 : ℝ), g u * Real.exp (x * u) := by
  unfold laplace
  have : ∀ u : ℝ, (g u : ℂ) * cexp (-((((-x : ℝ)) : ℂ) * u)) = ((g u * Real.exp (x * u) : ℝ) : ℂ) := by
    intro u
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 2
    push_cast; ring
  simp_rw [this]
  rw [integral_complex_ofReal, Complex.ofReal_re]

/-- The diagonal Gram value `∫ g(u) e^{(s₁ - 2δ) u} du`. -/
def gramDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∫ u in Set.Ioi (0 : ℝ), D.g u * Real.exp ((D.s₁ - 2 * δ) * u)

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- The value `R_{jk} = Re G(-σ_{jk} + i y_{jk})` of a same-character Gram entry. -/
def pairValue (D : NearData) (E : Entries q ι) (j k : ι) : ℝ :=
  (laplace D.g (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) +
    (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)).re

omit [Fintype ι] in
lemma pairValue_symm (D : NearData) (E : Entries q ι) (j k : ι) :
    pairValue D E j k = pairValue D E k j := by
  unfold pairValue
  rw [← laplace_re_conj]
  congr 2
  rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

omit [Fintype ι] in
lemma pairValue_self (D : NearData) (E : Entries q ι) (j : ι) :
    pairValue D E j j = gramDiag D (E.δ j) := by
  unfold pairValue gramDiag
  have : (((-(D.s₁ - E.δ j - E.δ j)) : ℝ) : ℂ) + (((E.γ j - E.γ j) * Real.log q : ℝ) : ℂ) * I =
      (((-(D.s₁ - 2 * E.δ j)) : ℝ) : ℂ) := by
    rw [sub_self, zero_mul, Complex.ofReal_zero, zero_mul, add_zero]
    congr 1; ring
  rw [this, laplace_re_neg_real]

omit [Fintype ι] in
/-- `(s_{jk} - 1) log q = -σ_{jk} + i y_{jk}`. -/
lemma sjk_arg (D : NearData) (E : Entries q ι) (j k : ι) (hℓ : Real.log q ≠ 0) :
    (sjk D E j k - 1) * (Real.log q : ℂ) =
      (((-(D.s₁ - E.δ j - E.δ k)) : ℝ) : ℂ) + (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I := by
  unfold sjk
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re,
      Complex.sub_im, Complex.add_im, Complex.one_im]
    ring

omit [Fintype ι] in
lemma sjk_re (D : NearData) (E : Entries q ι) (j k : ι) :
    (sjk D E j k).re = 1 - (D.s₁ - E.δ j - E.δ k) / Real.log q := by
  simp only [sjk, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]

omit [Fintype ι] in
lemma sjk_im (D : NearData) (E : Entries q ι) (j k : ι) :
    (sjk D E j k).im = E.γ j - E.γ k := by
  simp only [sjk, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]

/-- `|σ_{jk}| ≤ |s₁| + 2 Σ_{δ ∈ Δ} δ` for offsets in `Δ`. -/
lemma sigma_bound (D : NearData) (hD : D.Valid) {δj δk : ℝ} (hj : δj ∈ D.Δ) (hk : δk ∈ D.Δ) :
    |D.s₁ - δj - δk| ≤ |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ := by
  have hnn : ∀ δ ∈ D.Δ, 0 ≤ δ := hD.Δ_nonneg
  have h1 : δj ≤ ∑ δ ∈ D.Δ, δ := Finset.single_le_sum hnn hj
  have h2 : δk ≤ ∑ δ ∈ D.Δ, δ := Finset.single_le_sum hnn hk
  have h3 := hnn δj hj
  have h4 := hnn δk hk
  calc |D.s₁ - δj - δk| ≤ |D.s₁| + |δj| + |δk| := by
        have := abs_sub (D.s₁ - δj) δk
        have := abs_sub D.s₁ δj
        linarith
    _ ≤ _ := by rw [abs_of_nonneg h3, abs_of_nonneg h4]; linarith

/-- **The Gram form bound.** -/
theorem gram_form_bound (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) →
        (∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re) /
            Real.log q ≤
          ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
            (D.d₁ + ε) * (∑ j, a j) ^ 2 := by
  set K : ℝ := |D.s₁| + 2 * ∑ δ ∈ D.Δ, δ with hK
  obtain ⟨q₁, hq₁⟩ := principal_entry hX31 hD.g_cond1 K hε
  obtain ⟨δ, hδ0, hδ1, q₂, hq₂⟩ := nonprincipal_entry hX32 hD.g_cond1 hD.g_cond2 K hε
  refine ⟨max (max q₁ q₂) 2, fun q _ hq T hT hTq hsafe ι _ E hγ hΔ a ha => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hq2' : q₂ ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hℓ := log_q_pos hq2
  classical
  -- bounds on the Gram point
  have hre : ∀ j k, |(sjk D E j k).re - 1| ≤ K / Real.log q := by
    intro j k
    rw [sjk_re, show 1 - (D.s₁ - E.δ j - E.δ k) / Real.log q - 1 =
      -((D.s₁ - E.δ j - E.δ k) / Real.log q) by ring, abs_neg, abs_div, abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right (sigma_bound D hD (hΔ j) (hΔ k)) hℓ.le
  have him : ∀ j k, |(sjk D E j k).im| ≤ 2 * T := by
    intro j k
    rw [sjk_im]
    have := abs_sub (E.γ j) (E.γ k)
    linarith [hγ j, hγ k]
  have him' : ∀ j k, |(sjk D E j k).im| ≤ Real.log q := fun j k => by
    linarith [him j k]
  -- the bookkeeping
  have key := gram_bookkeeping (fun j k => E.χ j = E.χ k) (fun j k h => h.symm)
    (fun j => rfl) (fun j k => (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re / Real.log q)
    (pairValue D E) (pairValue_symm D E) a ha D.d₁ ε ?_ ?_
  · rw [Finset.sum_div]
    simp_rw [Finset.sum_div, mul_div_assoc]
    refine key.trans (le_of_eq ?_)
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pairValue_self]
    unfold pairExcess sameCharOthers pairValue
    congr 2
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext k
    simp only [Finset.mem_filter]
  · -- same character: principal entries
    intro j k hjk
    have h1 : E.χ j * (E.χ k)⁻¹ = 1 := by rw [hjk, mul_inv_cancel]
    rw [h1]
    have := hq₁ q hq1 (sjk D E j k) (hre j k) (him' j k)
    rw [sjk_arg D E j k hℓ.ne'] at this
    exact this
  · -- distinct characters: non-principal entries
    intro j k hjk
    have h1 : E.χ j * (E.χ k)⁻¹ ≠ 1 := by
      intro h; exact hjk (mul_inv_eq_one.1 h)
    refine hq₂ q hq2' _ h1 (sjk D E j k) (hre j k) (him' j k) ?_
    intro ρ hρ hdist
    have hρim : |ρ.im| ≤ 2 * T + 1 := by
      have h2 : |ρ.im - (sjk D E j k).im| ≤ δ := by
        have := Complex.abs_im_le_norm ((1 + ((sjk D E j k).im : ℂ) * I) - ρ)
        rw [show ((1 + ((sjk D E j k).im : ℂ) * I) - ρ).im = (sjk D E j k).im - ρ.im by
          simp] at this
        rw [abs_sub_comm]; linarith
      have := abs_sub_abs_le_abs_sub ρ.im (sjk D E j k).im
      linarith [him j k]
    have hsafe' := hsafe _ h1 ρ hρ hρim
    rw [sjk_re]
    have hδs : D.s₁ - E.δ j - E.δ k ≤ D.s₁ := by
      linarith [hD.Δ_nonneg _ (hΔ j), hD.Δ_nonneg _ (hΔ k)]
    have : (D.s₁ - E.δ j - E.δ k) / Real.log q ≤ D.s₁ / Real.log q :=
      div_le_div_of_nonneg_right hδs hℓ.le
    linarith

end GradedNear
