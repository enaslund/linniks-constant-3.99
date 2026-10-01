module

public import GradedNear.FirstPart
public import GradedNear.SievePart

/-!
# Proof of the graded near lemma

Assembly (paper §8.5): the responses as one sum over `n`, Cauchy–Schwarz with the weight
`ω = g e^{s₁ t} + H`, the first factor by `first_factor_bound`, and the second factor split into
the Gram part (`gram_part_eq`, `gram_form_bound`) and the sieve part (`sieve_part_bound`).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData

/-- `ω ≥ 0` on `[0, ∞)`. -/
lemma omega_nonneg (D : NearData) (hD : D.Valid) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ D.omega u := by
  unfold NearData.omega NearData.sieveH
  refine add_nonneg (mul_nonneg (hD.g_cond2.nonneg u hu) (Real.exp_pos _).le) ?_
  refine Finset.sum_nonneg fun k hk => ?_
  split_ifs
  · exact hD.h_nonneg k (Finset.mem_range.1 hk)
  · exact le_rfl

/-- `(Re Σ c_n Y_n)² ≤ (Σ |c_n| ‖Y_n‖)²`. -/
lemma re_sum_sq_le {β : Type*} (S : Finset β) (c : β → ℝ) (Y : β → ℂ) :
    ((∑ n ∈ S, (c n : ℂ) * Y n).re) ^ 2 ≤ (∑ n ∈ S, |c n| * ‖Y n‖) ^ 2 := by
  have h1 : |(∑ n ∈ S, (c n : ℂ) * Y n).re| ≤ ∑ n ∈ S, |c n| * ‖Y n‖ := by
    refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (le_of_eq ?_))
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h2 : 0 ≤ ∑ n ∈ S, |c n| * ‖Y n‖ :=
    Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  calc ((∑ n ∈ S, (c n : ℂ) * Y n).re) ^ 2 = |(∑ n ∈ S, (c n : ℂ) * Y n).re| ^ 2 :=
        (sq_abs _).symm
    _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h1 2

theorem graded_near_lemma'
    (hX31 : XylourisLemma31) (hX32 : XylourisLemma32) (hBur : BurgessBound)
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
                (D.d₁ + η) * (∑ j, a j) ^ 2) := by
  have hIB := hD.IB_pos
  obtain ⟨qF, hqF⟩ := first_factor_bound D hD (ε := η * D.IB) (mul_pos hη hIB)
  obtain ⟨qG, hqG⟩ := gram_form_bound hX31 hX32 D hD (ε := η / 2) (half_pos hη)
  obtain ⟨qS, hqS⟩ := sieve_part_bound hGr hBur D hD (ε := η / 2) (half_pos hη)
  obtain ⟨c, hc, hωc⟩ := hD.omega_lb
  refine ⟨max (max qF qG) (max qS 2), fun q _ hq T hT hTq hsafe ι _ E _ hγ hΔ hinj a ha => ?_⟩
  have hqF' : qF ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hq
  have hqG' : qG ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hq
  have hqS' : qS ≤ q := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hq
  have hq2 : 2 ≤ q := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hq
  have hℓ := log_q_pos hq2
  set Sf := Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊ with hSf
  set N := max ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊ with hN
  set w : ℕ → ℝ := fun n => Λ n / n * D.omega (tn q n) with hw
  have hw0 : ∀ n, 0 ≤ w n := fun n =>
    mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
      (omega_nonneg D hD (tn_nonneg q n hq2))
  -- Step 1: the responses as one sum
  have hresp := sum_response D E a hq2 hD.f_cond.vanish
  -- Step 2: Cauchy–Schwarz
  have hcw : ∀ n ∈ Sf, cWeight D q n ≠ 0 → 0 < w n := by
    intro n hn hne
    have hn1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    unfold cWeight at hne
    have hΛ : Λ n ≠ 0 := fun h => hne (by rw [h]; simp)
    have hf : D.f (tn q n) ≠ 0 := fun h => hne (by rw [h]; simp)
    have hΛpos : 0 < Λ n := lt_of_le_of_ne ArithmeticFunction.vonMangoldt_nonneg (Ne.symm hΛ)
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    exact mul_pos (div_pos hΛpos hnpos) (lt_of_lt_of_le hc (hωc _ (tn_nonneg q n hq2) hf))
  have hcs := weighted_cs Sf (cWeight D q) w (fun n => ‖Yn E a n‖) (fun n _ => hw0 n) hcw
  -- the first factor
  have hfirst_eq : ∑ n ∈ Sf, cWeight D q n ^ 2 / w n = ∑ n ∈ Sf, Λ n / n *
      (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n)) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    unfold cWeight
    simp only [hw]
    by_cases hΛ : Λ n = 0
    · simp [hΛ]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.1 hn).1
      by_cases hω : D.omega (tn q n) = 0
      · simp [hω]
      · have he : Real.exp (2 * D.s * tn q n) = Real.exp (D.s * tn q n) ^ 2 := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        rw [he]
        field_simp
  have hfirst : (∑ n ∈ Sf, cWeight D q n ^ 2 / w n) / Real.log q ≤ (1 + η) * D.IB := by
    rw [hfirst_eq]
    have := hqF q hqF'
    linarith
  -- the second factor, enlarged to `Icc 1 N`
  have hsecond_mono : ∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, w n * ‖Yn E a n‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n => w n * ‖Yn E a n‖ ^ 2)
      (Finset.Icc_subset_Icc (le_refl 1)
        (le_max_left ⌊(q : ℝ) ^ D.xf⌋₊ ⌊(q : ℝ) ^ D.xg⌋₊))
      (fun n _ _ => mul_nonneg (hw0 n) (sq_nonneg _))
  have hsplit : ∑ n ∈ Finset.Icc 1 N, w n * ‖Yn E a n‖ ^ 2 =
      ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
          ‖Yn E a n‖ ^ 2 +
        ∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [hw, NearData.omega]
    ring
  have hgram := gram_part_eq D E a hq2 hD.g_cond1.vanish (N := N) (le_max_right _ _)
  have hG := hqG q hqG' T hT hTq hsafe ι E hγ hΔ a ha
  have hS := hqS q hqS' T hT hTq ι E hγ hΔ hinj a ha N
  have hsecond : (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q ≤
      ∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
        (D.d₁ + η) * (∑ j, a j) ^ 2 := by
    refine (div_le_div_of_nonneg_right hsecond_mono hℓ.le).trans ?_
    rw [hsplit, add_div, hgram]
    have hD' : ∀ j, D.Dδ (E.δ j) = gramDiag D (E.δ j) + sieveDiag D (E.δ j) := fun j => by
      rw [Dδ_eq]; rfl
    simp_rw [hD']
    have : ∑ j, (gramDiag D (E.δ j) + sieveDiag D (E.δ j) - D.d₁ + pairExcess D E j) *
        a j ^ 2 = ∑ j, (gramDiag D (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    linarith
  have hsecond0 : 0 ≤ (∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q :=
    div_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (hw0 n) (sq_nonneg _)) hℓ.le
  have hfirst0 : 0 ≤ (∑ n ∈ Sf, cWeight D q n ^ 2 / w n) / Real.log q :=
    div_nonneg (Finset.sum_nonneg fun n _ => div_nonneg (sq_nonneg _) (hw0 n)) hℓ.le
  -- combine
  have hsq : (∑ j, a j * response D E j) ^ 2 ≤
      ((∑ n ∈ Sf, cWeight D q n ^ 2 / w n) / Real.log q) *
        ((∑ n ∈ Sf, w n * ‖Yn E a n‖ ^ 2) / Real.log q) := by
    rw [hresp, neg_div, neg_sq, div_pow]
    have h1 := re_sum_sq_le Sf (cWeight D q) (Yn E a)
    have h2 := h1.trans hcs
    rw [div_mul_div_comm, ← sq]
    exact div_le_div_of_nonneg_right h2 (sq_nonneg _)
  calc (max 0 (∑ j, a j * response D E j)) ^ 2 ≤ (∑ j, a j * response D E j) ^ 2 := by
        rcases le_total 0 (∑ j, a j * response D E j) with h | h
        · rw [max_eq_right h]
        · rw [max_eq_left h, zero_pow two_ne_zero]; exact sq_nonneg _
    _ ≤ _ := hsq
    _ ≤ (1 + η) * D.IB * (∑ j, (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) * a j ^ 2 +
          (D.d₁ + η) * (∑ j, a j) ^ 2) :=
        mul_le_mul hfirst hsecond hsecond0 (by nlinarith)

end GradedNear
