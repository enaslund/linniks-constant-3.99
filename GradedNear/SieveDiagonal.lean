module

public import GradedNear.SieveBasic

/-!
# (B) The diagonal of the sieve part: Graham's estimate and partial summation

From `Σ_{n ≤ N} ν_V(n) = N / log V + O(N / log² V)` (`GrahamEstimate`), partial summation gives
`Σ_{A ≤ n ≤ B} (log n / n) ν_V(n) ≤ (log² B - log² A) / (2 log V) + O((log² B + 1) / log² V)`
for `V₀ ≤ V ≤ A ≤ B`.

## Proof outline

* Enlarge the range `[⌈A⌉, ⌊B⌋]` to `[⌊A⌋, ⌊B⌋] = {⌊A⌋} ∪ (⌊A⌋, ⌊B⌋]` (all terms are `≥ 0`).
* The single term `n = ⌊A⌋` is at most `(2 log A / A) · S(A) ≤ 2 log A (1/log V + C/log² V)`,
  where `S(N) = Σ_{1 ≤ n ≤ N} ν_V(n)`.
* On `(⌊A⌋, ⌊B⌋]` apply Abel summation (`sum_mul_eq_sub_sub_integral_mul`) with the weight
  `F(t) = log t / t`, whose derivative `(1 - log t)/t²` is `≤ 0` for `t ≥ e`, and bound
  `S(t)` from above and below by Graham's estimate.
* The main term is `(1 / log V) ∫_A^B log t / t dt = (log² B - log² A) / (2 log V)`; all other
  terms are `O((log² B + 1) / log² V)` because `1 ≤ log V ≤ log A ≤ log B`.
-/

@[expose] public section

namespace GradedNear

open Finset MeasureTheory

/-! ## Calculus of `log t / t` -/

private lemma hasDerivAt_log_div_self {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (fun t : ℝ => Real.log t / t) ((1 - Real.log t) / t ^ 2) t := by
  have h := (Real.hasDerivAt_log ht).div (hasDerivAt_id' (x := t)) ht
  convert h using 1
  field_simp

private lemma deriv_log_div_self {t : ℝ} (ht : t ≠ 0) :
    deriv (fun t : ℝ => Real.log t / t) t = (1 - Real.log t) / t ^ 2 :=
  (hasDerivAt_log_div_self ht).deriv

private lemma continuousOn_log_div_self {A B : ℝ} (hA : 0 < A) :
    ContinuousOn (fun t : ℝ => Real.log t / t) (Set.Icc A B) := by
  apply ContinuousOn.div
  · exact Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (hA.trans_le ht.1))
  · exact continuousOn_id
  · intro t ht
    exact ne_of_gt (hA.trans_le ht.1)

private lemma integrableOn_deriv_log_div_self {A B : ℝ} (hA : 0 < A) :
    IntegrableOn (deriv (fun t : ℝ => Real.log t / t)) (Set.Icc A B) := by
  have hcont : ContinuousOn (fun t : ℝ => (1 - Real.log t) / t ^ 2) (Set.Icc A B) := by
    apply ContinuousOn.div
    · exact continuousOn_const.sub (Real.continuousOn_log.mono (fun t ht => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact ne_of_gt (hA.trans_le ht.1)))
    · exact continuousOn_id.pow 2
    · intro t ht
      exact pow_ne_zero 2 (ne_of_gt (hA.trans_le ht.1))
  refine hcont.integrableOn_Icc.congr_fun (fun t ht => ?_) measurableSet_Icc
  exact (deriv_log_div_self (ne_of_gt (hA.trans_le ht.1))).symm

private lemma integral_log_div_self {A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    ∫ t in Set.Ioc A B, Real.log t / t = (Real.log B ^ 2 - Real.log A ^ 2) / 2 := by
  rw [← intervalIntegral.integral_of_le hAB]
  have hderiv : ∀ x ∈ Set.uIcc A B,
      HasDerivAt (fun t : ℝ => Real.log t ^ 2 / 2) (Real.log x / x) x := by
    intro x hx
    rw [Set.uIcc_of_le hAB] at hx
    have hx0 : x ≠ 0 := ne_of_gt (hA.trans_le hx.1)
    have h := ((Real.hasDerivAt_log hx0).pow 2).div_const 2
    convert h using 1
    field_simp
    ring
  have hint : IntervalIntegrable (fun t : ℝ => Real.log t / t) volume A B := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hAB]
    exact continuousOn_log_div_self hA
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- The pointwise bound for the integrand in Abel's formula. -/
private lemma neg_deriv_mul_le {t S K ℓ : ℝ} (ht : 0 < t) (hℓ : 1 ≤ ℓ) (hS0 : 0 ≤ S)
    (hSK : S ≤ t * K) : -((1 - ℓ) / t ^ 2 * S) ≤ K * (ℓ / t) := by
  have e1 : -((1 - ℓ) / t ^ 2 * S) = (ℓ - 1) * S / t ^ 2 := by ring
  have e2 : K * (ℓ / t) = ℓ * (t * K) / t ^ 2 := by
    field_simp
  rw [e1, e2]
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  exact mul_le_mul (by linarith) hSK hS0 (by linarith)

/-! ## Graham's estimate in terms of `sieveNu` -/

private lemma sieveNu_zero (V : ℝ) : sieveNu V 0 = 0 := by
  simp [sieveNu]

private lemma sum_Icc_zero_sieveNu (V : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 0 n, sieveNu V k = ∑ k ∈ Finset.Icc 1 n, sieveNu V k := by
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le n), Finset.sum_cons, sieveNu_zero, zero_add,
    ← Finset.Icc_add_one_left_eq_Ioc, zero_add]

private lemma graham_sieveNu {C₀ V₁ : ℝ}
    (hC₀ : ∀ V N : ℝ, V₁ ≤ V → V ≤ N →
      |∑ n ∈ Finset.Icc 1 ⌊N⌋₊, (∑ d ∈ n.divisors, grahamWeight V d) ^ 2 - N / Real.log V| ≤
        C₀ * N / Real.log V ^ 2)
    {V N : ℝ} (hV : V₁ ≤ V) (hVN : V ≤ N) (hV0 : 0 ≤ V) :
    N / Real.log V - max C₀ 0 * N / Real.log V ^ 2 ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ∧
      ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ≤ N / Real.log V + max C₀ 0 * N / Real.log V ^ 2 := by
  have h := hC₀ V N hV hVN
  have hN : 0 ≤ N := le_trans hV0 hVN
  have h' : C₀ * N / Real.log V ^ 2 ≤ max C₀ 0 * N / Real.log V ^ 2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hN) (sq_nonneg _)
  have h2 := abs_le.mp (h.trans h')
  simp only [sieveNu]
  constructor <;> linarith [h2.1, h2.2]

/-! ## The core estimate for a fixed level `V` -/

/-- The single term `n = ⌊A⌋`. -/
private lemma floor_term_le {V A K : ℝ} (hA2 : 2 ≤ A) (hK : 0 ≤ K)
    (hSA : ∑ n ∈ Finset.Icc 1 ⌊A⌋₊, sieveNu V n ≤ A * K) :
    Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * sieveNu V ⌊A⌋₊ ≤ 2 * Real.log A * K := by
  have hA0 : 0 ≤ A := by linarith
  have hm1 : 1 ≤ ⌊A⌋₊ := (Nat.one_le_floor_iff A).mpr (by linarith)
  have hm_pos : (0 : ℝ) < ⌊A⌋₊ := by exact_mod_cast hm1
  have hmA : (⌊A⌋₊ : ℝ) ≤ A := Nat.floor_le hA0
  have hAm : A < ⌊A⌋₊ + 1 := Nat.lt_floor_add_one A
  have hA2m : A ≤ 2 * ⌊A⌋₊ := by linarith
  have hlogm : Real.log ⌊A⌋₊ ≤ Real.log A := Real.log_le_log hm_pos hmA
  have hlogm0 : 0 ≤ Real.log ⌊A⌋₊ := Real.log_natCast_nonneg _
  have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hnu : sieveNu V ⌊A⌋₊ ≤ A * K := by
    refine le_trans ?_ hSA
    exact Finset.single_le_sum (f := fun n => sieveNu V n) (fun i _ => sieveNu_nonneg V i)
      (Finset.mem_Icc.mpr ⟨hm1, le_rfl⟩)
  calc Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * sieveNu V ⌊A⌋₊
      ≤ Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * (A * K) :=
        mul_le_mul_of_nonneg_left hnu (div_nonneg hlogm0 hm_pos.le)
    _ ≤ 2 * Real.log A * K := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hm_pos]
        have h1 : Real.log ⌊A⌋₊ * A ≤ Real.log A * (2 * ⌊A⌋₊) :=
          mul_le_mul hlogm hA2m hA0 hlogA0
        nlinarith [mul_le_mul_of_nonneg_right h1 hK]

/-- The final arithmetic. -/
private lemma final_arith {a b L C₁ : ℝ} (hL : 1 ≤ L) (hLa : L ≤ a) (hab : a ≤ b) (hC₁ : 0 ≤ C₁) :
    2 * a * (1 / L + C₁ / L ^ 2) + (b / L + C₁ * b / L ^ 2) - (a / L - C₁ * a / L ^ 2) +
        (1 / L + C₁ / L ^ 2) * ((b ^ 2 - a ^ 2) / 2) ≤
      (b ^ 2 - a ^ 2) / (2 * L) + (3 + 3 * C₁) * (b ^ 2 + 1) / L ^ 2 := by
  have hL0 : 0 < L := by linarith
  rw [← sub_nonneg]
  have e : (b ^ 2 - a ^ 2) / (2 * L) + (3 + 3 * C₁) * (b ^ 2 + 1) / L ^ 2 -
      (2 * a * (1 / L + C₁ / L ^ 2) + (b / L + C₁ * b / L ^ 2) - (a / L - C₁ * a / L ^ 2) +
        (1 / L + C₁ / L ^ 2) * ((b ^ 2 - a ^ 2) / 2)) =
      ((3 + 3 * C₁) * (b ^ 2 + 1) - (a + b) * L - C₁ * (3 * a + b) -
        C₁ * (b ^ 2 - a ^ 2) / 2) / L ^ 2 := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ (by positivity)
  nlinarith [mul_nonneg hC₁ (sq_nonneg (b - 1)), mul_nonneg hC₁ (sub_nonneg.2 hab),
    mul_nonneg hC₁ (sq_nonneg a), mul_nonneg (sub_nonneg.2 hLa) (sub_nonneg.2 hab),
    mul_nonneg (sub_nonneg.2 (hLa.trans hab)) (sub_nonneg.2 hab),
    mul_nonneg hC₁ (sub_nonneg.2 hL), mul_nonneg hC₁ (sub_nonneg.2 hLa)]

private lemma sieve_diagonal_core {V A B C₁ : ℝ} (hC₁ : 0 ≤ C₁) (hVe : Real.exp 1 ≤ V) (hVA : V ≤ A)
    (hAB : A ≤ B)
    (hS : ∀ N : ℝ, V ≤ N →
      N / Real.log V - C₁ * N / Real.log V ^ 2 ≤ ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ∧
      ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ≤ N / Real.log V + C₁ * N / Real.log V ^ 2) :
    ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
      (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
        (3 + 3 * C₁) * (Real.log B ^ 2 + 1) / Real.log V ^ 2 := by
  -- basic facts
  have h2e : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hV2 : 2 ≤ V := h2e.trans hVe
  have hA2 : 2 ≤ A := hV2.trans hVA
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hL1 : 1 ≤ Real.log V := by
    have := Real.log_le_log (Real.exp_pos 1) hVe
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log V := by linarith
  have hLA : Real.log V ≤ Real.log A := Real.log_le_log (by linarith) hVA
  have hlogAB : Real.log A ≤ Real.log B := Real.log_le_log hA0 hAB
  have hK0 : 0 ≤ 1 / Real.log V + C₁ / Real.log V ^ 2 := by positivity
  -- the upper bound in product form
  have hSup : ∀ N : ℝ, V ≤ N →
      ∑ n ∈ Finset.Icc 1 ⌊N⌋₊, sieveNu V n ≤ N * (1 / Real.log V + C₁ / Real.log V ^ 2) := by
    intro N hN
    calc _ ≤ _ := (hS N hN).2
      _ = N * (1 / Real.log V + C₁ / Real.log V ^ 2) := by ring
  -- Step 1: enlarge the range of summation
  have step1 : ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
      Real.log (⌊A⌋₊ : ℝ) / (⌊A⌋₊ : ℝ) * sieveNu V ⌊A⌋₊ +
        ∑ n ∈ Finset.Ioc ⌊A⌋₊ ⌊B⌋₊, Real.log n / n * sieveNu V n := by
    have hsub : Finset.Icc ⌈A⌉₊ ⌊B⌋₊ ⊆ Finset.Icc ⌊A⌋₊ ⌊B⌋₊ :=
      Finset.Icc_subset_Icc (Nat.floor_le_ceil A) le_rfl
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => ?_).trans_eq ?_
    · exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
        (sieveNu_nonneg V n)
    · rw [Finset.Icc_eq_cons_Ioc (Nat.floor_le_floor hAB), Finset.sum_cons]
  -- Step 2: Abel summation on `(A, B]`
  have hdiff : ∀ t ∈ Set.Icc A B, DifferentiableAt ℝ (fun t : ℝ => Real.log t / t) t :=
    fun t ht => (hasDerivAt_log_div_self (ne_of_gt (hA0.trans_le ht.1))).differentiableAt
  have hint := integrableOn_deriv_log_div_self (B := B) hA0
  have hAbel := sum_mul_eq_sub_sub_integral_mul (sieveNu V) hA0.le hAB hdiff hint
  -- Step 3: the boundary terms
  have hBt : Real.log B / B * ∑ k ∈ Finset.Icc 0 ⌊B⌋₊, sieveNu V k ≤
      Real.log B / Real.log V + C₁ * Real.log B / Real.log V ^ 2 := by
    rw [sum_Icc_zero_sieveNu]
    have h := (hS B (hVA.trans hAB)).2
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    calc Real.log B / B * ∑ k ∈ Finset.Icc 1 ⌊B⌋₊, sieveNu V k
        ≤ Real.log B / B * (B / Real.log V + C₁ * B / Real.log V ^ 2) :=
          mul_le_mul_of_nonneg_left h (div_nonneg hlogB0 hB0.le)
      _ = Real.log B / Real.log V + C₁ * Real.log B / Real.log V ^ 2 := by
          field_simp
  have hAt : Real.log A / Real.log V - C₁ * Real.log A / Real.log V ^ 2 ≤
      Real.log A / A * ∑ k ∈ Finset.Icc 0 ⌊A⌋₊, sieveNu V k := by
    rw [sum_Icc_zero_sieveNu]
    have h := (hS A hVA).1
    have hlogA0 : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
    calc Real.log A / Real.log V - C₁ * Real.log A / Real.log V ^ 2
        = Real.log A / A * (A / Real.log V - C₁ * A / Real.log V ^ 2) := by
          field_simp
      _ ≤ Real.log A / A * ∑ k ∈ Finset.Icc 1 ⌊A⌋₊, sieveNu V k :=
          mul_le_mul_of_nonneg_left h (div_nonneg hlogA0 hA0.le)
  -- Step 4: the integral
  have hI : -(∫ t in Set.Ioc A B, deriv (fun t : ℝ => Real.log t / t) t *
        ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, sieveNu V k) ≤
      (1 / Real.log V + C₁ / Real.log V ^ 2) * ((Real.log B ^ 2 - Real.log A ^ 2) / 2) := by
    rw [← integral_neg, ← integral_log_div_self hA0 hAB, ← integral_const_mul]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc ?_
    · exact ((integrableOn_mul_sum_Icc (m := 0) (sieveNu V) hA0.le hint).mono_set
        Set.Ioc_subset_Icc_self).neg
    · exact ((continuousOn_log_div_self hA0).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self).const_mul _
    · intro t ht
      have ht0 : 0 < t := hA0.trans ht.1
      have hVt : V ≤ t := hVA.trans ht.1.le
      have hlogt : 1 ≤ Real.log t := by
        have := Real.log_le_log (Real.exp_pos 1) (hVe.trans hVt)
        rwa [Real.log_exp] at this
      rw [deriv_log_div_self ht0.ne', sum_Icc_zero_sieveNu]
      exact neg_deriv_mul_le ht0 hlogt (Finset.sum_nonneg fun i _ => sieveNu_nonneg V i)
        (hSup t hVt)
  -- Step 5: the single term
  have hE := floor_term_le (V := V) hA2 hK0 (hSup A hVA)
  -- Step 6: combine
  have key := final_arith hL1 hLA hlogAB hC₁
  linarith [step1, hAbel, hBt, hAt, hI, hE, key]

theorem sieve_diagonal (hGr : GrahamEstimate) :
    ∃ C V₀ : ℝ, 1 < V₀ ∧ ∀ V A B : ℝ, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
        (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
          C * (Real.log B ^ 2 + 1) / Real.log V ^ 2 := by
  obtain ⟨C₀, V₁, hC₀⟩ := hGr
  refine ⟨3 + 3 * max C₀ 0, max V₁ (Real.exp 1), ?_, ?_⟩
  · exact lt_max_of_lt_right (Real.one_lt_exp_iff.mpr one_pos)
  · intro V A B hV hVA hAB
    have hV1 : V₁ ≤ V := le_trans (le_max_left _ _) hV
    have hVe : Real.exp 1 ≤ V := le_trans (le_max_right _ _) hV
    have hV0 : 0 ≤ V := le_trans (Real.exp_pos 1).le hVe
    exact sieve_diagonal_core (le_max_right C₀ 0) hVe hVA hAB
      (fun N hN => graham_sieveNu hC₀ hV1 hN hV0)

end GradedNear
