module

public import GradedNear.Defs

/-!
# Decay of the Laplace transform

For `f` satisfying Condition 1, `F(x + iY) → 0` as `|Y| → ∞`, uniformly for `x` in a compact
interval.

The proof is by integration by parts on `[0, x₀]` (`f` vanishes on `[x₀, ∞)`):
`z F(z) = f(0) + ∫₀^{x₀} f'(t) e^{-zt} dt`. The derivative `f'` is bounded on `(0, x₀]`, because
`|f''| ≤ B` makes it Lipschitz on `(0, x₀)`. Hence `|F(x + iY)| ≤ C / |Y|` with
`C = |f(0)| + K x₀ e^{X x₀}`, uniformly for `x ∈ [-X, X]`, where `K` bounds `|f'|`.
-/

@[expose] public section

namespace GradedNear

namespace Decay

open MeasureTheory Set

/-- The derivative of a `Condition1` function is bounded on `(0, x₀]`. -/
lemma exists_abs_deriv_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t ∈ Ioc 0 x₀, |deriv f t| ≤ K := by
  have hopen : IsOpen (Ioo (0 : ℝ) x₀) := isOpen_Ioo
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Ioo 0 x₀) :=
    hf.smooth.deriv_of_isOpen hopen (by norm_num)
  have hdiff : ∀ t ∈ Ioo (0 : ℝ) x₀, DifferentiableAt ℝ (deriv f) t := fun t ht =>
    (hd1.differentiableOn (by norm_num) t ht).differentiableAt (hopen.mem_nhds ht)
  have hbd : ∀ t ∈ Ioo (0 : ℝ) x₀, ‖deriv (deriv f) t‖ ≤ B := fun t ht => by
    rw [Real.norm_eq_abs]; exact hf.bound t ht
  have hx₀ := hf.pos
  have hmid : x₀ / 2 ∈ Ioo (0 : ℝ) x₀ := ⟨by linarith, by linarith⟩
  have hB : 0 ≤ B := (abs_nonneg _).trans (hf.bound _ hmid)
  refine ⟨max (|deriv f (x₀ / 2)| + B * x₀) |deriv f x₀|,
    (abs_nonneg _).trans (le_max_right _ _), fun t ht => ?_⟩
  rcases eq_or_lt_of_le ht.2 with h | h
  · rw [h]; exact le_max_right _ _
  · have htm : t ∈ Ioo (0 : ℝ) x₀ := ⟨ht.1, h⟩
    have hmv := (convex_Ioo (0 : ℝ) x₀).norm_image_sub_le_of_norm_deriv_le hdiff hbd hmid htm
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmv
    have h2 : |t - x₀ / 2| ≤ x₀ := by
      rw [abs_le]; constructor <;> linarith [htm.1, htm.2]
    have h3 : |deriv f t| - |deriv f (x₀ / 2)| ≤ |deriv f t - deriv f (x₀ / 2)| :=
      abs_sub_abs_le_abs_sub _ _
    have h4 : B * |t - x₀ / 2| ≤ B * x₀ := mul_le_mul_of_nonneg_left h2 hB
    exact le_trans (by linarith) (le_max_left _ _)

/-- Since `f` vanishes on `[x₀, ∞)`, the Laplace transform is an integral over `[0, x₀]`. -/
lemma laplace_eq_intervalIntegral {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (z : ℂ) :
    laplace f z = ∫ t in (0 : ℝ)..x₀, (f t : ℂ) * Complex.exp (-(z * t)) := by
  rw [intervalIntegral.integral_of_le hf.pos.le, laplace]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Ioc_subset_Ioi_self fun t ht => ?_
  have ht' : x₀ ≤ t := by
    by_contra h
    exact ht.2 ⟨ht.1, (not_le.1 h).le⟩
  simp [hf.vanish t ht']

/-- Integration by parts: `z F(z) = f(0) + ∫₀^{x₀} f'(t) e^{-zt} dt`. -/
lemma mul_laplace_eq {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) {K : ℝ}
    (hK : ∀ t ∈ Ioc 0 x₀, |deriv f t| ≤ K) (z : ℂ) :
    z * laplace f z =
      (f 0 : ℂ) + ∫ t in (0 : ℝ)..x₀, ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t)) := by
  have hx₀ := hf.pos
  have hmin : min 0 x₀ = 0 := min_eq_left hx₀.le
  have hmax : max 0 x₀ = x₀ := max_eq_right hx₀.le
  have hu : ContinuousOn (fun t : ℝ => (f t : ℂ)) (uIcc 0 x₀) := by
    rw [uIcc_of_le hx₀.le]
    exact Complex.continuous_ofReal.comp_continuousOn (hf.cont.mono Icc_subset_Ici_self)
  have hv : ContinuousOn (fun t : ℝ => Complex.exp (-(z * t))) (uIcc 0 x₀) :=
    (by fun_prop : Continuous fun t : ℝ => Complex.exp (-(z * t))).continuousOn
  have huu' : ∀ t ∈ Ioo (min 0 x₀) (max 0 x₀),
      HasDerivAt (fun t : ℝ => (f t : ℂ)) ((deriv f t : ℝ) : ℂ) t := by
    intro t ht
    rw [hmin, hmax] at ht
    exact ((hf.smooth.differentiableOn (by norm_num) t ht).differentiableAt
      (isOpen_Ioo.mem_nhds ht)).hasDerivAt.ofReal_comp
  have hvv' : ∀ t ∈ Ioo (min 0 x₀) (max 0 x₀),
      HasDerivAt (fun t : ℝ => Complex.exp (-(z * t))) (-z * Complex.exp (-(z * t))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(z * (t : ℂ))) (-z) t := by
      convert ((hasDerivAt_id' t).ofReal_comp).const_mul (-z) using 1
      · ext y; ring
      · simp
    exact h1.cexp.congr_deriv (mul_comm _ _)
  have hu' : IntervalIntegrable (fun t : ℝ => ((deriv f t : ℝ) : ℂ)) volume 0 x₀ := by
    refine (intervalIntegrable_const (c := K)).mono_fun' ?_ ?_
    · exact (Complex.measurable_ofReal.comp (measurable_deriv f)).aestronglyMeasurable
    · rw [uIoc_of_le hx₀.le]
      refine ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_
      simpa using hK t ht
  have hv' : IntervalIntegrable (fun t : ℝ => -z * Complex.exp (-(z * t))) volume 0 x₀ :=
    (by fun_prop : Continuous fun t : ℝ => -z * Complex.exp (-(z * t))).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv huu' hvv'
    hu' hv'
  have hlhs : (∫ t in (0 : ℝ)..x₀, (f t : ℂ) * (-z * Complex.exp (-(z * t)))) =
      -z * laplace f z := by
    rw [laplace_eq_intervalIntegral hf, ← intervalIntegral.integral_const_mul]
    congr 1
    ext t
    ring
  rw [hlhs, hf.vanish x₀ le_rfl] at hibp
  simp only [Complex.ofReal_zero, zero_mul, mul_zero, neg_zero, Complex.exp_zero, mul_one,
    zero_sub] at hibp
  linear_combination -hibp

/-- The bound `‖z F(z)‖ ≤ |f(0)| + K e^{X x₀} x₀` for `Re z ≥ -X`. -/
lemma norm_mul_laplace_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) {K : ℝ}
    (hK : ∀ t ∈ Ioc 0 x₀, |deriv f t| ≤ K) (hK0 : 0 ≤ K) {X : ℝ} (hX : 0 ≤ X) (z : ℂ)
    (hz : -X ≤ z.re) :
    ‖z * laplace f z‖ ≤ |f 0| + K * Real.exp (X * x₀) * x₀ := by
  have hx₀ := hf.pos
  rw [mul_laplace_eq hf hK z]
  refine (norm_add_le _ _).trans (add_le_add (by simp) ?_)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := x₀)
    (C := K * Real.exp (X * x₀))
    (f := fun t : ℝ => ((deriv f t : ℝ) : ℂ) * Complex.exp (-(z * t))) ?_
  · rwa [sub_zero, abs_of_pos hx₀] at h
  intro t ht
  rw [uIoc_of_le hx₀.le] at ht
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul (hK t ht) ?_ (Real.exp_pos _).le hK0
  refine Real.exp_le_exp.2 ?_
  simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero]
  nlinarith [ht.1, ht.2]

end Decay

theorem laplace_decay {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (X : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (-X) X, ∀ Y : ℝ, M ≤ |Y| →
      ‖laplace f ((x : ℂ) + (Y : ℂ) * Complex.I)‖ ≤ ε := by
  obtain ⟨K, hK0, hK⟩ := Decay.exists_abs_deriv_le hf
  have hx₀ := hf.pos
  set C := |f 0| + K * Real.exp (X * x₀) * x₀
  have hC0 : 0 ≤ C := by positivity
  refine ⟨C / ε + 1, by positivity, fun x hx Y hY => ?_⟩
  set z : ℂ := (x : ℂ) + (Y : ℂ) * Complex.I
  have hzre : z.re = x := by simp [z]
  have hzim : z.im = Y := by simp [z]
  have hX : 0 ≤ X := by linarith [hx.1, hx.2]
  have hbound := Decay.norm_mul_laplace_le hf hK hK0 hX z (by rw [hzre]; exact hx.1)
  rw [norm_mul] at hbound
  have hYz : |Y| ≤ ‖z‖ := hzim ▸ Complex.abs_im_le_norm z
  have hMz : C / ε + 1 ≤ ‖z‖ := hY.trans hYz
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hMz
  have hCε : C ≤ ε * ‖z‖ := by
    have h1 : ε * (C / ε + 1) = C + ε := by field_simp
    have h2 := mul_le_mul_of_nonneg_left hMz hε.le
    linarith
  exact le_of_mul_le_mul_left (hbound.trans (hCε.trans_eq (mul_comm _ _))) hzpos

end GradedNear
