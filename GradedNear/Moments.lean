module

public import GradedNear.Parabolic

/-!
# Moments of the parabolic test

The slacks of the row builders' grids use moments of the test `f` of width `c`:

* `integral_pow_mul_fpar`: `∫₀^c t^k f(t) dt = c^{k+1} m_k`, and `moment_le`: for `x ≥ 0`,
  `∫₀^c t^k |f(t)| e^{-xt} dt ≤ c^{k+1} m_k`;
* `moment2_exp_eq`: `∫₀^c t² |f(t)| e^{dt} dt = c³ E₂(cd)` with `E₂(α) = ∫₀¹ s² P(s) e^{αs} ds`;
* `E2_eq_closed`: the closed form of `E₂(α)` for `α ≠ 0` (eight integrations by parts), and
  `E2_sub_taylor`: its Taylor polynomial `Σ_{j<N} αʲ m_{j+2}/j!` with the remainder for `|α| ≤ 1`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace GradedNear

namespace Parabolic

/-- `∫₀^c t^k f(t) dt = c^{k+1} m_k`. -/
lemma integral_pow_mul_fpar {c : ℝ} (hc : 0 < c) (k : ℕ) :
    ∫ t in (0 : ℝ)..c, t ^ k * fpar c t = c ^ (k + 1) * mom k := by
  have hcongr : ∫ t in (0 : ℝ)..c, t ^ k * fpar c t = ∫ t in (0 : ℝ)..c, t ^ k * P (t / c) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.le] at ht
    simp only [fpar_of_le ht.2]
  rw [hcongr]
  have hsub := intervalIntegral.integral_comp_mul_left (fun t => t ^ k * P (t / c))
    (a := 0) (b := 1) hc.ne'
  simp only [mul_zero, mul_one] at hsub
  have e : ∫ t in (0 : ℝ)..c, t ^ k * P (t / c) =
      c * ∫ s in (0 : ℝ)..1, (c * s) ^ k * P (c * s / c) := by
    rw [hsub, smul_eq_mul, mul_inv_cancel_left₀ hc.ne']
  rw [e, ← integral_pow_mul_P]
  have e2 : ∫ s in (0 : ℝ)..1, (c * s) ^ k * P (c * s / c) =
      c ^ k * ∫ s in (0 : ℝ)..1, s ^ k * P s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show (c * s) ^ k * P (c * s / c) = c ^ k * (s ^ k * P s)
    rw [mul_div_cancel_left₀ _ hc.ne', mul_pow]
    ring
  rw [e2]
  ring

/-- For `x ≥ 0`: `∫₀^c t^k |f(t)| e^{-xt} dt ≤ c^{k+1} m_k`. -/
lemma moment_le {c : ℝ} (hc : 0 < c) (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    ∫ t in (0 : ℝ)..c, t ^ k * |fpar c t| * Real.exp (-(x * t)) ≤ c ^ (k + 1) * mom k := by
  rw [← integral_pow_mul_fpar hc k]
  refine intervalIntegral.integral_mono_on hc.le
    (Continuous.intervalIntegrable (((continuous_pow k).mul (continuous_fpar hc).abs).mul
      (by fun_prop)) _ _)
    (Continuous.intervalIntegrable ((continuous_pow k).mul (continuous_fpar hc)) _ _)
    fun t ht => ?_
  rw [abs_of_nonneg (fpar_nonneg hc ht.1)]
  have h1 : Real.exp (-(x * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [ht.1])
  have h2 : 0 ≤ t ^ k * fpar c t := mul_nonneg (pow_nonneg ht.1 k) (fpar_nonneg hc ht.1)
  nlinarith

/-- `E₂(α) = ∫₀¹ s² P(s) e^{αs} ds`. -/
def E2 (α : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, s ^ 2 * P s * Real.exp (α * s)

/-- `∫₀^c t² |f(t)| e^{dt} dt = c³ E₂(cd)`. -/
lemma moment2_exp_eq {c : ℝ} (hc : 0 < c) (d : ℝ) :
    ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-((-d) * t)) = c ^ 3 * E2 (c * d) := by
  have hcongr : ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-((-d) * t)) =
      ∫ t in (0 : ℝ)..c, t ^ 2 * P (t / c) * Real.exp (d * t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.le] at ht
    rw [abs_of_nonneg (fpar_nonneg hc ht.1), fpar_of_le ht.2]
    ring_nf
  rw [hcongr]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun t => t ^ 2 * P (t / c) * Real.exp (d * t)) (a := 0) (b := 1) hc.ne'
  simp only [mul_zero, mul_one] at hsub
  have e : ∫ t in (0 : ℝ)..c, t ^ 2 * P (t / c) * Real.exp (d * t) =
      c * ∫ s in (0 : ℝ)..1, (c * s) ^ 2 * P (c * s / c) * Real.exp (d * (c * s)) := by
    rw [hsub, smul_eq_mul, mul_inv_cancel_left₀ hc.ne']
  rw [e]
  unfold E2
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun s _ => ?_
  show c * ((c * s) ^ 2 * P (c * s / c) * Real.exp (d * (c * s))) =
    c ^ 3 * (s ^ 2 * P s * Real.exp (c * d * s))
  rw [mul_div_cancel_left₀ _ hc.ne']
  ring_nf

/-! ## The closed form of `E₂` -/

/-- `Q(s) = s² P(s)` and its derivatives. -/
def Q0 (s : ℝ) : ℝ := s ^ 2 - 5 * s ^ 4 + 5 * s ^ 5 - s ^ 7
def Q1 (s : ℝ) : ℝ := 2 * s - 20 * s ^ 3 + 25 * s ^ 4 - 7 * s ^ 6
def Q2 (s : ℝ) : ℝ := 2 - 60 * s ^ 2 + 100 * s ^ 3 - 42 * s ^ 5
def Q3 (s : ℝ) : ℝ := -120 * s + 300 * s ^ 2 - 210 * s ^ 4
def Q4 (s : ℝ) : ℝ := -120 + 600 * s - 840 * s ^ 3
def Q5 (s : ℝ) : ℝ := 600 - 2520 * s ^ 2
def Q6 (s : ℝ) : ℝ := -5040 * s

lemma Q0_eq (s : ℝ) : Q0 s = s ^ 2 * P s := by unfold Q0 P; ring

lemma hasDerivAt_Q0 (s : ℝ) : HasDerivAt Q0 (Q1 s) s := by
  have h := (((hasDerivAt_pow 2 s).sub ((hasDerivAt_pow 4 s).const_mul 5)).add
    ((hasDerivAt_pow 5 s).const_mul 5)).sub (hasDerivAt_pow 7 s)
  exact h.congr_deriv (by unfold Q1; push_cast; ring)

lemma hasDerivAt_Q1 (s : ℝ) : HasDerivAt Q1 (Q2 s) s := by
  have h := ((((hasDerivAt_id' s).const_mul 2).sub ((hasDerivAt_pow 3 s).const_mul 20)).add
    ((hasDerivAt_pow 4 s).const_mul 25)).sub ((hasDerivAt_pow 6 s).const_mul 7)
  exact h.congr_deriv (by unfold Q2; push_cast; ring)

lemma hasDerivAt_Q2 (s : ℝ) : HasDerivAt Q2 (Q3 s) s := by
  have h := (((hasDerivAt_const s (2 : ℝ)).sub ((hasDerivAt_pow 2 s).const_mul 60)).add
    ((hasDerivAt_pow 3 s).const_mul 100)).sub ((hasDerivAt_pow 5 s).const_mul 42)
  exact h.congr_deriv (by unfold Q3; push_cast; ring)

lemma hasDerivAt_Q3 (s : ℝ) : HasDerivAt Q3 (Q4 s) s := by
  have h := ((((hasDerivAt_id' s).const_mul (-120 : ℝ)).add
    ((hasDerivAt_pow 2 s).const_mul 300)).sub ((hasDerivAt_pow 4 s).const_mul 210))
  exact h.congr_deriv (by unfold Q4; push_cast; ring)

lemma hasDerivAt_Q4 (s : ℝ) : HasDerivAt Q4 (Q5 s) s := by
  have h := ((hasDerivAt_const s (-120 : ℝ)).add ((hasDerivAt_id' s).const_mul 600)).sub
    ((hasDerivAt_pow 3 s).const_mul 840)
  exact h.congr_deriv (by unfold Q5; push_cast; ring)

lemma hasDerivAt_Q5 (s : ℝ) : HasDerivAt Q5 (Q6 s) s := by
  have h := (hasDerivAt_const s (600 : ℝ)).sub ((hasDerivAt_pow 2 s).const_mul 2520)
  exact h.congr_deriv (by unfold Q6; push_cast; ring)

lemma hasDerivAt_Q6 (s : ℝ) : HasDerivAt Q6 (-5040) s := by
  have h := (hasDerivAt_id' s).const_mul (-5040 : ℝ)
  exact h.congr_deriv (by ring)

/-- The antiderivative of `Q(s) e^{αs}` (`α ≠ 0`): `e^{αs} Σ_j (-1)ʲ Q⁽ʲ⁾(s)/α^{j+1}`. -/
def e2Prim (α s : ℝ) : ℝ :=
  Real.exp (α * s) * (Q0 s / α - Q1 s / α ^ 2 + Q2 s / α ^ 3 - Q3 s / α ^ 4 + Q4 s / α ^ 5 -
    Q5 s / α ^ 6 + Q6 s / α ^ 7 - (-5040) / α ^ 8)

lemma hasDerivAt_e2Prim {α : ℝ} (hα : α ≠ 0) (s : ℝ) :
    HasDerivAt (e2Prim α) (Q0 s * Real.exp (α * s)) s := by
  have hl : HasDerivAt (fun s => α * s) α s := by
    simpa using (hasDerivAt_id s).const_mul α
  have hA := (((((((((hasDerivAt_Q0 s).div_const α).sub ((hasDerivAt_Q1 s).div_const (α ^ 2))).add
    ((hasDerivAt_Q2 s).div_const (α ^ 3))).sub ((hasDerivAt_Q3 s).div_const (α ^ 4))).add
    ((hasDerivAt_Q4 s).div_const (α ^ 5))).sub ((hasDerivAt_Q5 s).div_const (α ^ 6))).add
    ((hasDerivAt_Q6 s).div_const (α ^ 7))).sub (hasDerivAt_const s ((-5040 : ℝ) / α ^ 8)))
  have h := hl.exp.mul hA
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, Pi.sub_apply]
  unfold Q0 Q1 Q2 Q3 Q4 Q5 Q6
  field_simp
  ring

/-- The closed form of `E₂(α)`, `α ≠ 0`. -/
def E2Closed (α : ℝ) : ℝ :=
  Real.exp α * (30 / α ^ 4 - 360 / α ^ 5 + 1920 / α ^ 6 - 5040 / α ^ 7 + 5040 / α ^ 8) -
    2 / α ^ 3 + 120 / α ^ 5 + 600 / α ^ 6 - 5040 / α ^ 8

lemma E2_eq_closed {α : ℝ} (hα : α ≠ 0) : E2 α = E2Closed α := by
  have e : E2 α = ∫ s in (0 : ℝ)..1, Q0 s * Real.exp (α * s) := by
    unfold E2
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [Q0_eq]
  rw [e, intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_e2Prim hα s)
    (Continuous.intervalIntegrable (by unfold Q0; fun_prop) _ _)]
  simp only [e2Prim, E2Closed, Q0, Q1, Q2, Q3, Q4, Q5, Q6, mul_one, mul_zero, Real.exp_zero]
  field_simp
  ring

/-- **The Taylor polynomial of `E₂`**: for `|α| ≤ 1` and `N ≥ 1`,
`|E₂(α) - Σ_{j<N} αʲ m_{j+2}/j!| ≤ m₂ |α|^N (N+1)/(N!·N)`. -/
lemma E2_sub_taylor {α : ℝ} (hα : |α| ≤ 1) {N : ℕ} (hN : 0 < N) :
    |E2 α - ∑ j ∈ Finset.range N, α ^ j / j.factorial * mom (j + 2)| ≤
      mom 2 * (|α| ^ N * (N.succ / (N.factorial * N))) := by
  set K := |α| ^ N * ((N.succ : ℝ) / (N.factorial * N)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : ∑ j ∈ Finset.range N, α ^ j / j.factorial * mom (j + 2) =
      ∫ s in (0 : ℝ)..1, s ^ 2 * P s * ∑ j ∈ Finset.range N, (α * s) ^ j / j.factorial := by
    have e1 : (fun s : ℝ => s ^ 2 * P s * ∑ j ∈ Finset.range N, (α * s) ^ j / j.factorial) =
        fun s => ∑ j ∈ Finset.range N, α ^ j / j.factorial * (s ^ (j + 2) * P s) := by
      funext s
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, pow_add]
      ring
    rw [e1, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow_mul_P]
    · intro j _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hdiff : E2 α - ∑ j ∈ Finset.range N, α ^ j / j.factorial * mom (j + 2) =
      ∫ s in (0 : ℝ)..1, s ^ 2 * P s * (Real.exp (α * s) -
        ∑ j ∈ Finset.range N, (α * s) ^ j / j.factorial) := by
    rw [hsum, E2, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hdiff]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  have hm2 : ∫ s in (0 : ℝ)..1, s ^ 2 * P s = mom 2 := integral_pow_mul_P 2
  calc ∫ s in (0 : ℝ)..1, |s ^ 2 * P s * (Real.exp (α * s) -
          ∑ j ∈ Finset.range N, (α * s) ^ j / j.factorial)|
      ≤ ∫ s in (0 : ℝ)..1, s ^ 2 * P s * K := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
        have hPs : 0 ≤ s ^ 2 * P s := mul_nonneg (sq_nonneg s) (P_nonneg hs.1 hs.2)
        have hus : |α * s| ≤ |α| := by
          rw [abs_mul, abs_of_nonneg hs.1]
          exact mul_le_of_le_one_right (abs_nonneg α) hs.2
        have hb := Real.exp_bound (hus.trans hα) hN
        rw [abs_mul, abs_of_nonneg hPs]
        refine mul_le_mul_of_nonneg_left (hb.trans ?_) hPs
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hus N) (by positivity)
    _ = mom 2 * K := by
        rw [intervalIntegral.integral_mul_const, hm2]

end Parabolic

end GradedNear

end
