module

public import GradedNear.LaplaceDecay

/-!
# A criterion for Condition 2

Heath-Brown checks Condition 2 for his autocorrelation tests by a maximum principle [HB, §7,
p. 36, using his Lemma 4.1]: the Laplace transform `F` of a test supported in `[0, x₀]` is entire
and bounded on the closed right half-plane, so `Re F ≥ 0` there as soon as `Re F ≥ 0` on the
imaginary axis. This file proves that criterion.

* `laplace_hasDerivAt`, `laplace_differentiable`: for `f` satisfying Condition 1, `F` is entire
  (differentiation under the integral sign on `[0, x₀]`);
* `norm_laplace_le`: `‖F(z)‖ ≤ ∫₀^{x₀} |f|` for `Re z ≥ 0`;
* `condition2_of_imag_axis`: Condition 1, `f ≥ 0` on `[0, ∞)` and `Re F(iy) ≥ 0` for every real
  `y` give Condition 2. The proof applies the Phragmén–Lindelöf principle in the right half-plane
  (`PhragmenLindelof.right_half_plane_of_bounded_on_real`) to `exp(-F)`, whose norm is
  `exp(-Re F)`.
-/

@[expose] public section

open Complex MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Admissible

variable {f : ℝ → ℝ} {x₀ B : ℝ}

/-- A `Condition1` function is bounded on `[0, x₀]`. -/
lemma exists_abs_le (hf : Condition1 f x₀ B) : ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ Icc 0 x₀, |f t| ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hf.cont.mono (Icc_subset_Ici_self : Icc (0 : ℝ) x₀ ⊆ Ici 0))
  refine ⟨max M 0, le_max_right _ _, fun t ht => ?_⟩
  have := hM t ht
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

/-- The Laplace transform of a `Condition1` function has a complex derivative everywhere:
`F'(z) = -∫₀^{x₀} t f(t) e^{-zt} dt`. -/
theorem laplace_hasDerivAt (hf : Condition1 f x₀ B) (z₀ : ℂ) :
    HasDerivAt (laplace f)
      (∫ t in (0 : ℝ)..x₀, (f t : ℂ) * (-(t : ℂ)) * Complex.exp (-(z₀ * t))) z₀ := by
  have hx₀ := hf.pos
  obtain ⟨M, hM0, hM⟩ := exists_abs_le hf
  have heq : laplace f = fun z => ∫ t in (0 : ℝ)..x₀, (f t : ℂ) * Complex.exp (-(z * t)) := by
    funext z; exact Decay.laplace_eq_intervalIntegral hf z
  rw [heq]
  have hcont : ContinuousOn (fun t : ℝ => (f t : ℂ)) (Icc 0 x₀) :=
    Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self)
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => (f t : ℂ) * Complex.exp (-(z * t)))
      (volume.restrict (Ι (0 : ℝ) x₀)) := by
    intro z
    rw [uIoc_of_le hx₀.le]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (hcont.mono Ioc_subset_Icc_self).mul (by fun_prop)
  set K := M * x₀ * Real.exp ((‖z₀‖ + 1) * x₀) with hK
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := x₀)
    (F := fun z t => (f t : ℂ) * Complex.exp (-(z * t)))
    (F' := fun z t => (f t : ℂ) * (-(t : ℂ)) * Complex.exp (-(z * t)))
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun _ => K)
    (Metric.ball_mem_nhds z₀ one_pos) (Eventually.of_forall hmeasF) ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact key.2
  · -- integrability at z₀
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hx₀.le]
    exact hcont.mul (by fun_prop)
  · -- measurability of the derivative
    rw [uIoc_of_le hx₀.le]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact ((hcont.mono Ioc_subset_Icc_self).mul (by fun_prop)).mul (by fun_prop)
  · -- the bound
    refine Eventually.of_forall fun t ht z hz => ?_
    rw [uIoc_of_le hx₀.le] at ht
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos ht.1, Complex.norm_exp]
    have h1 : |f t| ≤ M := hM t (Ioc_subset_Icc_self ht)
    have h2 : (-(z * (t : ℂ))).re ≤ (‖z₀‖ + 1) * x₀ := by
      have : (-(z * (t : ℂ))).re = -(z.re * t) := by simp
      rw [this]
      have hre : -z.re ≤ ‖z‖ := by
        have := Complex.abs_re_le_norm z
        rw [abs_le] at this
        linarith
      have := mul_le_mul_of_nonneg_right hre ht.1.le
      have h3 : ‖z‖ * t ≤ (‖z₀‖ + 1) * x₀ :=
        mul_le_mul hzn ht.2 ht.1.le (by positivity)
      linarith
    have h3 := Real.exp_le_exp.2 h2
    calc |f t| * t * Real.exp (-(z * (t : ℂ))).re
        ≤ M * x₀ * Real.exp ((‖z₀‖ + 1) * x₀) := by
          apply mul_le_mul (mul_le_mul h1 ht.2 ht.1.le hM0) h3 (Real.exp_pos _).le
          positivity
      _ = K := rfl
  · -- the derivative in z
    refine Eventually.of_forall fun t _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) z :=
      (hasDerivAt_mul_const (t : ℂ)).neg
    have h2 := h1.cexp.const_mul (f t : ℂ)
    convert h2 using 1
    ring

/-- The Laplace transform of a `Condition1` function is entire. -/
theorem laplace_differentiable (hf : Condition1 f x₀ B) : Differentiable ℂ (laplace f) :=
  fun z => (laplace_hasDerivAt hf z).differentiableAt

/-- `‖F(z)‖ ≤ ∫₀^{x₀} |f|` on the closed right half-plane. -/
lemma norm_laplace_le (hf : Condition1 f x₀ B) {z : ℂ} (hz : 0 ≤ z.re) :
    ‖laplace f z‖ ≤ ∫ t in (0 : ℝ)..x₀, |f t| := by
  have hx₀ := hf.pos
  rw [Decay.laplace_eq_intervalIntegral hf]
  refine intervalIntegral.norm_integral_le_of_norm_le hx₀.le
    (Eventually.of_forall fun t ht => ?_) ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    have : (-(z * (t : ℂ))).re ≤ 0 := by
      have : (-(z * (t : ℂ))).re = -(z.re * t) := by simp
      rw [this]
      nlinarith [ht.1]
    calc |f t| * Real.exp (-(z * (t : ℂ))).re ≤ |f t| * 1 :=
          mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.2 this) (abs_nonneg _)
      _ = |f t| := mul_one _
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hx₀.le]
    exact (hf.cont.mono Icc_subset_Ici_self).abs

/-! ## Derivatives of transforms of compactly supported functions -/

/-- The transform of a function vanishing on `[x₀, ∞)` is an interval integral over `[0, x₀]`. -/
lemma laplace_eq_intervalIntegral_of {g : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (z : ℂ) :
    laplace g z = ∫ t in (0 : ℝ)..x₀, (g t : ℂ) * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hx₀.le, laplace]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self fun t ht => ?_
  have ht' : x₀ ≤ t := by
    by_contra h
    exact ht.2 ⟨ht.1, (not_le.1 h).le⟩
  simp [hvan t ht']

/-- **The derivative of a transform**: for `g` continuous on `[0, x₀]` and vanishing on
`[x₀, ∞)`, `laplace g` has the complex derivative `laplace (t ↦ -t g(t))` everywhere. -/
theorem laplace_hasDerivAt_of {g : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀)
    (hcont : ContinuousOn g (Icc 0 x₀)) (hvan : ∀ t, x₀ ≤ t → g t = 0) (z₀ : ℂ) :
    HasDerivAt (laplace g) (laplace (fun t => -t * g t) z₀) z₀ := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hM' : ∀ t ∈ Icc 0 x₀, |g t| ≤ max M 0 := fun t ht => by
    have := hM t ht; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have heq : laplace g = fun z => ∫ t in (0 : ℝ)..x₀, (g t : ℂ) * Complex.exp (-(z * t)) := by
    funext z; exact laplace_eq_intervalIntegral_of hx₀ hvan z
  have hvan' : ∀ t, x₀ ≤ t → -t * g t = 0 := fun t ht => by rw [hvan t ht, mul_zero]
  rw [heq, laplace_eq_intervalIntegral_of hx₀ hvan' z₀]
  have hcontC : ContinuousOn (fun t : ℝ => (g t : ℂ)) (Icc 0 x₀) :=
    Complex.continuous_ofReal.comp_continuousOn hcont
  have hmeasF : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => (g t : ℂ) * Complex.exp (-(z * t)))
      (volume.restrict (Ι (0 : ℝ) x₀)) := by
    intro z
    rw [uIoc_of_le hx₀.le]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (hcontC.mono Ioc_subset_Icc_self).mul (by fun_prop)
  set K := max M 0 * x₀ * Real.exp ((‖z₀‖ + 1) * x₀) with hK
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := x₀)
    (F := fun z t => (g t : ℂ) * Complex.exp (-(z * t)))
    (F' := fun z t => (((-t * g t : ℝ)) : ℂ) * Complex.exp (-(z * t)))
    (x₀ := z₀) (s := Metric.ball z₀ 1) (bound := fun _ => K)
    (Metric.ball_mem_nhds z₀ one_pos) (Filter.Eventually.of_forall hmeasF) ?_ ?_ ?_
    intervalIntegrable_const ?_
  · exact key.2
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hx₀.le]
    exact hcontC.mul (by fun_prop)
  · rw [uIoc_of_le hx₀.le]
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    refine ContinuousOn.mul ?_ (by fun_prop)
    exact Complex.continuous_ofReal.comp_continuousOn
      ((continuous_neg.continuousOn.mul hcont).mono Ioc_subset_Icc_self)
  · refine Filter.Eventually.of_forall fun t ht z hz => ?_
    rw [uIoc_of_le hx₀.le] at ht
    have hzn : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [Metric.mem_ball, dist_eq_norm] at hz
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, abs_mul, abs_neg,
      abs_of_pos ht.1]
    have h1 : |g t| ≤ max M 0 := hM' t (Ioc_subset_Icc_self ht)
    have h2 : (-(z * (t : ℂ))).re ≤ (‖z₀‖ + 1) * x₀ := by
      have : (-(z * (t : ℂ))).re = -(z.re * t) := by simp
      rw [this]
      have hre : -z.re ≤ ‖z‖ := by
        have := Complex.abs_re_le_norm z
        rw [abs_le] at this
        linarith
      have := mul_le_mul_of_nonneg_right hre ht.1.le
      have h3 : ‖z‖ * t ≤ (‖z₀‖ + 1) * x₀ := mul_le_mul hzn ht.2 ht.1.le (by positivity)
      linarith
    calc t * |g t| * Real.exp (-(z * (t : ℂ))).re
        ≤ x₀ * max M 0 * Real.exp ((‖z₀‖ + 1) * x₀) :=
          mul_le_mul (mul_le_mul ht.2 h1 (abs_nonneg _) hx₀.le) (Real.exp_le_exp.2 h2)
            (Real.exp_pos _).le (by positivity)
      _ = K := by rw [hK]; ring
  · refine Filter.Eventually.of_forall fun t _ z _ => ?_
    have h1 : HasDerivAt (fun z : ℂ => -(z * (t : ℂ))) (-(t : ℂ)) z :=
      (hasDerivAt_mul_const (t : ℂ)).neg
    have h2 := h1.cexp.const_mul (g t : ℂ)
    convert h2 using 1
    push_cast
    ring

/-- `‖laplace g z‖ ≤ ∫₀^{x₀} |g(t)| e^{-t Re z} dt`. -/
lemma norm_laplace_le_of {g : ℝ → ℝ} {x₀ : ℝ} (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (z : ℂ) :
    ‖laplace g z‖ ≤ ∫ t in (0 : ℝ)..x₀, |g t| * Real.exp (-(z.re * t)) := by
  rw [laplace_eq_intervalIntegral_of hx₀ hvan]
  refine intervalIntegral.norm_integral_le_of_norm_le hx₀.le
    (Filter.Eventually.of_forall fun t _ => ?_) ?_
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
    simp
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hx₀.le]
    exact hcont.abs.mul (by fun_prop)

end Admissible

open Admissible in
/-- **A criterion for Condition 2** (Heath-Brown's argument, [HB, §7, p. 36]). If `f` satisfies
Condition 1, is nonnegative on `[0, ∞)`, and its Laplace transform has nonnegative real part on the
imaginary axis, then `Re F(z) ≥ 0` whenever `Re z ≥ 0`. -/
theorem condition2_of_imag_axis {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hnn : ∀ t, 0 ≤ t → 0 ≤ f t) (him : ∀ y : ℝ, 0 ≤ (laplace f ((y : ℂ) * I)).re) :
    Condition2 f := by
  refine ⟨hnn, fun z hz => ?_⟩
  set A := ∫ t in (0 : ℝ)..x₀, |f t|
  set g : ℂ → ℂ := fun z => Complex.exp (-laplace f z) with hg
  have hgd : Differentiable ℂ g := (laplace_differentiable hf).neg.cexp
  have hgn : ∀ w, ‖g w‖ = Real.exp (-(laplace f w).re) := fun w => by
    simp [g, Complex.norm_exp]
  -- `g` is bounded by `exp A` on the closed right half-plane
  have hgb : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ Real.exp A := fun w hw => by
    rw [hgn]
    refine Real.exp_le_exp.2 ?_
    have h1 := norm_laplace_le hf hw
    have h2 : -(laplace f w).re ≤ ‖laplace f w‖ := by
      have := Complex.abs_re_le_norm (laplace f w)
      rw [abs_le] at this
      linarith
    linarith
  have hPL := PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) (C := 1)
    hgd.diffContOnCl ?_ ?_ ?_ hz
  · rw [hgn] at hPL
    have := Real.exp_le_one_iff.1 hPL
    linarith
  · -- growth: `g` is bounded on the right half-plane
    refine ⟨0, by norm_num, 0, ?_⟩
    refine Asymptotics.IsBigO.of_bound (Real.exp A) ?_
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    have hw' : 0 ≤ w.re := le_of_lt hw
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hgb w hw'
  · -- `g` is bounded on the positive real axis
    refine ⟨Real.exp A, Filter.eventually_map.2 ?_⟩
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact hgb (x : ℂ) (by simpa using hx)
  · -- on the imaginary axis `‖g‖ = exp(-Re F) ≤ 1`
    intro y
    rw [hgn]
    exact Real.exp_le_one_iff.2 (by linarith [him y])

end GradedNear
