module

public import GradedNear.Parabolic

/-!
# The transform of the parabolic test at complex points

For the family terms of the near rows that keep two zeros (the `rc` conjugate pair, the first
family's second zero) and for the shifted `rc` term, the row builders evaluate `Re F(x + iy)` at
complex points. With `ΦC(u) = ∫₀¹ P(s) e^{-us} ds` for complex `u`:

* `laplace_fpar_eq`: `F(z) = c ΦC(cz)` for the parabolic test of width `c`;
* `PhiC_eq_closed`: `ΦC(u) = 1/u - 10/u³ + 30/u⁴ - 120/u⁶ + e^{-u}(30/u⁴ + 120/u⁵ + 120/u⁶)` for
  `u ≠ 0` (five integrations by parts, as for real `u`);
* `PhiC_sub_taylor`: the Taylor polynomial of `ΦC` with its remainder for `‖u‖ ≤ 1`.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set
open scoped Interval

namespace GradedNear

namespace Parabolic

/-- `ΦC(u) = ∫₀¹ P(s) e^{-us} ds` for complex `u`. -/
def PhiC (u : ℂ) : ℂ := ∫ s in (0 : ℝ)..1, (P s : ℂ) * cexp (-(u * s))

/-- The closed form of `ΦC(u)` for `u ≠ 0`. -/
def PhiClosedC (u : ℂ) : ℂ :=
  1 / u - 10 / u ^ 3 + 30 / u ^ 4 - 120 / u ^ 6 + cexp (-u) * (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6)

/-- The antiderivative of `P(s) e^{-us}` (`u ≠ 0`). -/
def expPrimC (u : ℂ) (s : ℝ) : ℂ :=
  -cexp (-(u * s)) * ((P s : ℂ) / u + (P1 s : ℂ) / u ^ 2 + (P2 s : ℂ) / u ^ 3 + (P3 s : ℂ) / u ^ 4 +
    (P4 s : ℂ) / u ^ 5 - 120 / u ^ 6)

lemma hasDerivAt_expPrimC {u : ℂ} (hu : u ≠ 0) (s : ℝ) :
    HasDerivAt (expPrimC u) ((P s : ℂ) * cexp (-(u * s))) s := by
  have hl : HasDerivAt (fun s : ℝ => -(u * (s : ℂ))) (-u) s := by
    have := ((hasDerivAt_id s).ofReal_comp).const_mul u
    exact this.neg.congr_deriv (by simp)
  have hP := (hasDerivAt_P s).ofReal_comp
  have hP1 := (hasDerivAt_P1 s).ofReal_comp
  have hP2 := (hasDerivAt_P2 s).ofReal_comp
  have hP3 := (hasDerivAt_P3 s).ofReal_comp
  have hP4 := (hasDerivAt_P4 s).ofReal_comp
  have hA := ((((((hP.div_const u).add (hP1.div_const (u ^ 2))).add
    (hP2.div_const (u ^ 3))).add (hP3.div_const (u ^ 4))).add (hP4.div_const (u ^ 5))).sub
    (hasDerivAt_const s (120 / u ^ 6 : ℂ)))
  have h := hl.cexp.neg.mul hA
  refine h.congr_deriv ?_
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply]
  unfold P P1 P2 P3 P4
  push_cast
  field_simp
  ring

/-- **The closed form of `ΦC`.** -/
lemma PhiC_eq_closed {u : ℂ} (hu : u ≠ 0) : PhiC u = PhiClosedC u := by
  unfold PhiC
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_expPrimC hu s)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [expPrimC, PhiClosedC, P, P1, P2, P3, P4]
  push_cast
  simp only [mul_one, mul_zero, neg_zero, Complex.exp_zero]
  field_simp
  ring

/-- **The Taylor polynomial of `ΦC`**: for `‖u‖ ≤ 1` and `N ≥ 1`,
`‖ΦC(u) - Σ_{n<N} (-u)ⁿ m_n / n!‖ ≤ (5/12) ‖u‖^N (N+1)/(N!·N)`. -/
lemma PhiC_sub_taylor {u : ℂ} (hu : ‖u‖ ≤ 1) {N : ℕ} (hN : 0 < N) :
    ‖PhiC u - ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * (mom n : ℂ)‖ ≤
      5 / 12 * (‖u‖ ^ N * ((N.succ : ℝ) * ((N.factorial : ℝ) * N)⁻¹)) := by
  set K := ‖u‖ ^ N * ((N.succ : ℝ) * ((N.factorial : ℝ) * N)⁻¹) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * (mom n : ℂ) =
      ∫ s in (0 : ℝ)..1, (P s : ℂ) * ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial := by
    have e1 : (fun s : ℝ => (P s : ℂ) * ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial) =
        fun s => ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * (((s ^ n * P s : ℝ)) : ℂ) := by
      funext s
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show -(u * s) = -u * s by ring, mul_pow]
      push_cast
      ring
    rw [e1, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, integral_pow_mul_P]
    · intro n _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hdiff : PhiC u - ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * (mom n : ℂ) =
      ∫ s in (0 : ℝ)..1, (P s : ℂ) * (cexp (-(u * s)) -
        ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial) := by
    rw [hsum, PhiC, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hdiff]
  calc ‖∫ s in (0 : ℝ)..1, (P s : ℂ) * (cexp (-(u * s)) -
          ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial)‖
      ≤ ∫ s in (0 : ℝ)..1, P s * K := by
        refine intervalIntegral.norm_integral_le_of_norm_le zero_le_one
          (Filter.Eventually.of_forall fun s hs => ?_)
          (Continuous.intervalIntegrable (by fun_prop) _ _)
        have hs' : s ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self hs
        have hPs : 0 ≤ P s := P_nonneg hs'.1 hs'.2
        have hus : ‖-(u * (s : ℂ))‖ ≤ ‖u‖ := by
          rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs'.1]
          exact mul_le_of_le_one_right (norm_nonneg u) hs'.2
        have hb := Complex.exp_bound (hus.trans hu) hN
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hPs]
        refine mul_le_mul_of_nonneg_left (hb.trans ?_) hPs
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hus N) (by positivity)
    _ = 5 / 12 * K := by
        rw [intervalIntegral.integral_mul_const, integral_P]

/-- **The transform at a complex point**: `F(z) = ∫₀^c f(t) e^{-zt} dt = c ΦC(c z)`. -/
lemma laplace_fpar_eq {c : ℝ} (hc : 0 < c) (z : ℂ) :
    laplace (fpar c) z = c * PhiC (c * z) := by
  rw [Decay.laplace_eq_intervalIntegral (fpar_condition1 hc)]
  have hcongr : ∫ t in (0 : ℝ)..c, (fpar c t : ℂ) * cexp (-(z * t)) =
      ∫ t in (0 : ℝ)..c, (P (t / c) : ℂ) * cexp (-(z * t)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.le] at ht
    simp only [fpar_of_le ht.2]
  rw [hcongr]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun t : ℝ => (P (t / c) : ℂ) * cexp (-(z * t))) (a := 0) (b := 1) hc.ne'
  simp only [mul_zero, mul_one] at hsub
  have hint : ∫ t in (0 : ℝ)..c, (P (t / c) : ℂ) * cexp (-(z * t)) =
      c • ∫ s in (0 : ℝ)..1, (P (c * s / c) : ℂ) * cexp (-(z * ((c * s : ℝ) : ℂ))) := by
    rw [hsub, smul_inv_smul₀ hc.ne']
  rw [hint]
  unfold PhiC
  rw [Complex.real_smul]
  congr 1
  refine intervalIntegral.integral_congr fun s _ => ?_
  show (P (c * s / c) : ℂ) * cexp (-(z * ((c * s : ℝ) : ℂ))) = (P s : ℂ) * cexp (-((c : ℂ) * z * s))
  rw [mul_div_cancel_left₀ _ hc.ne']
  push_cast
  ring_nf

end Parabolic

end GradedNear

end
