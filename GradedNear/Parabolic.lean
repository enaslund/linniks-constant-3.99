module

public import GradedNear.Admissible
public import GradedNear.Entry

/-!
# The parabolic autocorrelation tests

The near rows of the leaves use, as detector `f` and as short Gram test `g₁`, the normalized
autocorrelation of the parabola `(γ² - y²)₊` ([HB, §7]; `computations/sieve_near/sieve_inputs.py` in the research repository,
`fnorm`): with `c = 2γ`,
`f(t) = P(t/c)` for `t ≤ c` and `f(t) = 0` for `t > c`, where
`P(u) = (1 - u)³(1 + 3u + u²) = 1 - 5u² + 5u³ - u⁵`, so that `f(0) = 1`.

* `fpar_condition1`: Condition 1 with `x₀ = c` and `B = 10 / c²`;
* `integral_P_cos`: `∫₀¹ P(s) cos(ws) ds = 60 (w cos(w/2) - 2 sin(w/2))² / w⁶` for `w ≠ 0`, which is
  `≥ 0` (the autocorrelation identity `Re F(iy) = (15/(8γ⁵)) (∫₀^γ (γ² - s²) cos(sy) ds)²` in closed
  form);
* `fpar_condition2`: Condition 2, by the criterion `condition2_of_imag_axis`;
* `fpar_anti`, `fpar_pos`: `f` decreases on `[0, ∞)` and is positive on `[0, c)`;
* `laplace_fpar_real`: at a real point, `Re F(x) = c Φ(c x)` with `Φ(u) = ∫₀¹ P(s) e^{-us} ds`;
  `Phi_eq_closed`: the closed form of `Φ(u)` for `u ≠ 0` (five integrations by parts);
  `Phi_sub_taylor`: the Taylor polynomial of `Φ` with its remainder for `|u| ≤ 1`.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Parabolic

/-- `P(u) = (1 - u)³(1 + 3u + u²) = 1 - 5u² + 5u³ - u⁵`. -/
def P (u : ℝ) : ℝ := 1 - 5 * u ^ 2 + 5 * u ^ 3 - u ^ 5
/-- `P'`. -/
def P1 (u : ℝ) : ℝ := -10 * u + 15 * u ^ 2 - 5 * u ^ 4
/-- `P''`. -/
def P2 (u : ℝ) : ℝ := -10 + 30 * u - 20 * u ^ 3
/-- `P'''`. -/
def P3 (u : ℝ) : ℝ := 30 - 60 * u ^ 2
/-- `P''''` (and `P⁽⁵⁾ = -120`). -/
def P4 (u : ℝ) : ℝ := -120 * u

lemma P_eq (u : ℝ) : P u = (1 - u) ^ 3 * (1 + 3 * u + u ^ 2) := by unfold P; ring

lemma P_one : P 1 = 0 := by norm_num [P]

lemma P_nonneg {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : 0 ≤ P u := by
  rw [P_eq]
  exact mul_nonneg (pow_nonneg (by linarith) 3) (by positivity)

lemma P_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : P u ≤ 1 := by
  unfold P
  nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg (mul_nonneg h0 h0)
    (sub_nonneg.2 h1), pow_le_one₀ h0 h1 (n := 2), pow_le_one₀ h0 h1 (n := 3)]

lemma hasDerivAt_P (u : ℝ) : HasDerivAt P (P1 u) u := by
  have h := ((((hasDerivAt_const u (1 : ℝ)).sub ((hasDerivAt_pow 2 u).const_mul 5)).add
    ((hasDerivAt_pow 3 u).const_mul 5)).sub (hasDerivAt_pow 5 u))
  exact h.congr_deriv (by unfold P1; push_cast; ring)

lemma hasDerivAt_P1 (u : ℝ) : HasDerivAt P1 (P2 u) u := by
  have h := ((((hasDerivAt_id' u).const_mul (-10 : ℝ)).add
    ((hasDerivAt_pow 2 u).const_mul 15)).sub ((hasDerivAt_pow 4 u).const_mul 5))
  exact h.congr_deriv (by unfold P2; push_cast; ring)

lemma hasDerivAt_P2 (u : ℝ) : HasDerivAt P2 (P3 u) u := by
  have h := (((hasDerivAt_const u (-10 : ℝ)).add ((hasDerivAt_id' u).const_mul 30)).sub
    ((hasDerivAt_pow 3 u).const_mul 20))
  exact h.congr_deriv (by unfold P3; push_cast; ring)

lemma hasDerivAt_P3 (u : ℝ) : HasDerivAt P3 (P4 u) u := by
  have h := ((hasDerivAt_const u (30 : ℝ)).sub ((hasDerivAt_pow 2 u).const_mul 60))
  exact h.congr_deriv (by unfold P4; push_cast; ring)

lemma hasDerivAt_P4 (u : ℝ) : HasDerivAt P4 (-120) u := by
  have h := (hasDerivAt_id' u).const_mul (-120 : ℝ)
  exact h.congr_deriv (by ring)

@[fun_prop] lemma continuous_P : Continuous P := by unfold P; fun_prop

lemma contDiff_P : ContDiff ℝ 2 P := by unfold P; fun_prop

lemma abs_P2_le {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) : |P2 u| ≤ 10 := by
  unfold P2
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg h0 (mul_nonneg h0 h0), mul_nonneg h0 (sub_nonneg.2 h1),
      mul_nonneg (mul_nonneg h0 h0) (sub_nonneg.2 h1)]
  · nlinarith [mul_nonneg h0 (mul_nonneg h0 h0), sq_nonneg (u - 1 / 2), sq_nonneg (2 * u - 1),
      mul_nonneg (sq_nonneg (2 * u - 1)) h0]

/-- The normalized parabolic autocorrelation of width `c = 2γ`. -/
def fpar (c t : ℝ) : ℝ := if t ≤ c then P (t / c) else 0

lemma fpar_of_le {c t : ℝ} (h : t ≤ c) : fpar c t = P (t / c) := by simp [fpar, h]

lemma fpar_of_lt {c t : ℝ} (h : c < t) : fpar c t = 0 := by simp [fpar, not_le.2 h]

lemma fpar_zero {c : ℝ} (hc : 0 < c) : fpar c 0 = 1 := by
  rw [fpar_of_le hc.le, zero_div]; norm_num [P]

lemma continuous_fpar {c : ℝ} (hc : 0 < c) : Continuous (fpar c) := by
  have h := Continuous.if_le (f' := fun t => P (t / c)) (g' := fun _ => (0 : ℝ))
    (f := fun t => t) (g := fun _ => c)
    (continuous_P.comp (continuous_id.div_const c)) continuous_const continuous_id
    continuous_const (fun t ht => by rw [ht, div_self hc.ne', P_one])
  exact h

lemma fpar_nonneg {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) : 0 ≤ fpar c t := by
  unfold fpar
  split_ifs with h
  · exact P_nonneg (div_nonneg ht hc.le) ((div_le_one hc).2 h)
  · exact le_rfl

lemma fpar_le_one {c t : ℝ} (hc : 0 < c) (ht : 0 ≤ t) : fpar c t ≤ 1 := by
  unfold fpar
  split_ifs with h
  · exact P_le_one (div_nonneg ht hc.le) ((div_le_one hc).2 h)
  · norm_num

/-- On `(0, c)` the second derivative of `f` is `P''(t/c)/c²`. -/
lemma deriv_deriv_fpar {c t : ℝ} (hc : 0 < c) (ht : t < c) :
    deriv (deriv (fpar c)) t = P2 (t / c) / c ^ 2 := by
  have hloc : fpar c =ᶠ[nhds t] fun x => P (x / c) := by
    filter_upwards [eventually_lt_nhds ht] with x hx
    exact fpar_of_le hx.le
  have hd1 : ∀ x, HasDerivAt (fun x => P (x / c)) (P1 (x / c) / c) x := fun x => by
    have := (hasDerivAt_P (x / c)).comp x ((hasDerivAt_id' x).div_const c)
    exact this.congr_deriv (by ring)
  have hd2 : ∀ x, HasDerivAt (fun x => P1 (x / c) / c) (P2 (x / c) / c ^ 2) x := fun x => by
    have := ((hasDerivAt_P1 (x / c)).comp x ((hasDerivAt_id' x).div_const c)).div_const c
    exact this.congr_deriv (by field_simp)
  have heq : deriv (fpar c) =ᶠ[nhds t] fun x => P1 (x / c) / c := by
    filter_upwards [hloc.eventuallyEq_nhds] with x hx
    rw [hx.deriv_eq]
    exact (hd1 x).deriv
  rw [heq.deriv_eq]
  exact (hd2 t).deriv

/-- **Condition 1** for the parabolic test of width `c`. -/
theorem fpar_condition1 {c : ℝ} (hc : 0 < c) : Condition1 (fpar c) c (10 / c ^ 2) where
  pos := hc
  cont := (continuous_fpar hc).continuousOn
  vanish := fun t ht => by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h, fpar_of_le le_rfl, div_self hc.ne', P_one]
    · exact fpar_of_lt h
  smooth := by
    refine (contDiff_P.comp (contDiff_id.div_const c)).contDiffOn.congr fun t ht => ?_
    exact fpar_of_le ht.2.le
  bound := fun t ht => by
    rw [deriv_deriv_fpar hc ht.2, abs_div, abs_of_pos (by positivity : (0 : ℝ) < c ^ 2)]
    exact div_le_div_of_nonneg_right (abs_P2_le (div_nonneg ht.1.le hc.le)
      ((div_le_one hc).2 ht.2.le)) (by positivity)

/-! ## Condition 2 -/

/-- The antiderivative of `P(s) cos(ws)` (`w ≠ 0`), by five integrations by parts. -/
def cosPrim (w s : ℝ) : ℝ :=
  Real.sin (w * s) * (P s / w - P2 s / w ^ 3 + P4 s / w ^ 5) +
    Real.cos (w * s) * (P1 s / w ^ 2 - P3 s / w ^ 4 - 120 / w ^ 6)

lemma hasDerivAt_cosPrim {w : ℝ} (hw : w ≠ 0) (s : ℝ) :
    HasDerivAt (cosPrim w) (P s * Real.cos (w * s)) s := by
  have hws : HasDerivAt (fun s => w * s) w s := by simpa using (hasDerivAt_id s).const_mul w
  have hsin := (Real.hasDerivAt_sin (w * s)).comp s hws
  have hcos := (Real.hasDerivAt_cos (w * s)).comp s hws
  have hA : HasDerivAt (fun s => P s / w - P2 s / w ^ 3 + P4 s / w ^ 5)
      (P1 s / w - P3 s / w ^ 3 + (-120) / w ^ 5) s :=
    (((hasDerivAt_P s).div_const w).sub ((hasDerivAt_P2 s).div_const (w ^ 3))).add
      ((hasDerivAt_P4 s).div_const (w ^ 5))
  have hB : HasDerivAt (fun s => P1 s / w ^ 2 - P3 s / w ^ 4 - 120 / w ^ 6)
      (P2 s / w ^ 2 - P4 s / w ^ 4 - 0) s :=
    (((hasDerivAt_P1 s).div_const (w ^ 2)).sub ((hasDerivAt_P3 s).div_const (w ^ 4))).sub
      (hasDerivAt_const s _)
  have h := (hsin.mul hA).add (hcos.mul hB)
  exact h.congr_deriv (by simp only [Function.comp_apply]; unfold P P1 P2 P3 P4; field_simp; ring)

/-- `∫₀¹ P(s) cos(ws) ds` in closed form. -/
lemma integral_P_cos {w : ℝ} (hw : w ≠ 0) :
    ∫ s in (0 : ℝ)..1, P s * Real.cos (w * s) =
      (30 * w ^ 2 * (1 + Real.cos w) - 120 * w * Real.sin w + 120 * (1 - Real.cos w)) / w ^ 6 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_cosPrim hw s)
    ((continuous_P.mul (by fun_prop)).intervalIntegrable _ _)]
  simp only [cosPrim, P, P1, P2, P3, P4, mul_one, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring

/-- The half-angle form: `30w²(1 + cos w) - 120 w sin w + 120(1 - cos w) = 60(w cos(w/2) - 2 sin(w/2))²`. -/
lemma cos_numerator_eq (w : ℝ) :
    30 * w ^ 2 * (1 + Real.cos w) - 120 * w * Real.sin w + 120 * (1 - Real.cos w) =
      60 * (w * Real.cos (w / 2) - 2 * Real.sin (w / 2)) ^ 2 := by
  have hs : Real.sin w = 2 * Real.sin (w / 2) * Real.cos (w / 2) := by
    rw [← Real.sin_two_mul]; ring_nf
  have hc : Real.cos w = 2 * Real.cos (w / 2) ^ 2 - 1 := by
    rw [← Real.cos_two_mul]; ring_nf
  have hsc := Real.sin_sq_add_cos_sq (w / 2)
  rw [hs, hc]
  linear_combination (-240) * hsc

lemma integral_P_cos_nonneg (w : ℝ) : 0 ≤ ∫ s in (0 : ℝ)..1, P s * Real.cos (w * s) := by
  rcases eq_or_ne w 0 with hw | hw
  · subst hw
    simp only [zero_mul, Real.cos_zero, mul_one]
    exact intervalIntegral.integral_nonneg zero_le_one fun s hs => P_nonneg hs.1 hs.2
  · rw [integral_P_cos hw, cos_numerator_eq]
    positivity

/-- On the imaginary axis `Re F(iy) = ∫₀^c f(t) cos(yt) dt = c ∫₀¹ P(s) cos(cys) ds ≥ 0`. -/
lemma laplace_fpar_imag_re_nonneg {c : ℝ} (hc : 0 < c) (y : ℝ) :
    0 ≤ (laplace (fpar c) ((y : ℂ) * I)).re := by
  have hf := fpar_condition1 hc
  rw [Decay.laplace_eq_intervalIntegral hf]
  have hint : IntervalIntegrable (fun t : ℝ => (fpar c t : ℂ) * Complex.exp (-((y : ℂ) * I * t)))
      volume 0 c :=
    ((Complex.continuous_ofReal.comp (continuous_fpar hc)).mul (by fun_prop)).intervalIntegrable _ _
  have hre : (∫ t in (0 : ℝ)..c, (fpar c t : ℂ) * Complex.exp (-((y : ℂ) * I * t))).re =
      ∫ t in (0 : ℝ)..c, fpar c t * Real.cos (y * t) := by
    rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hint]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Complex.reCLM_apply]
    have hexp : Complex.exp (-((y : ℂ) * I * t)) =
        (Real.cos (y * t) : ℂ) - (Real.sin (y * t) : ℂ) * I := by
      have : -((y : ℂ) * I * t) = ((-(y * t) : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg,
        Real.sin_neg]
      push_cast; ring
    rw [hexp]
    simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  have hcongr : ∫ t in (0 : ℝ)..c, fpar c t * Real.cos (y * t) =
      ∫ t in (0 : ℝ)..c, P (t / c) * Real.cos (y * t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.le] at ht
    simp only [fpar_of_le ht.2]
  rw [hcongr]
  -- the substitution `t = c s`
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun t => P (t / c) * Real.cos (y * t)) (a := 0) (b := 1) hc.ne'
  simp only [mul_zero, mul_one] at hsub
  have hs : ∫ t in (0 : ℝ)..c, P (t / c) * Real.cos (y * t) =
      c * ∫ s in (0 : ℝ)..1, P s * Real.cos ((c * y) * s) := by
    rw [← smul_eq_mul, ← inv_smul_eq_iff₀ hc.ne', ← hsub]
    refine intervalIntegral.integral_congr fun s _ => ?_
    show P (c * s / c) * Real.cos (y * (c * s)) = P s * Real.cos (c * y * s)
    rw [mul_div_cancel_left₀ _ hc.ne']
    ring_nf
  rw [hs]
  exact mul_nonneg hc.le (integral_P_cos_nonneg _)

/-- **Condition 2** for the parabolic test of width `c`. -/
theorem fpar_condition2 {c : ℝ} (hc : 0 < c) : Condition2 (fpar c) :=
  condition2_of_imag_axis (fpar_condition1 hc) (fun _ ht => fpar_nonneg hc ht)
    (laplace_fpar_imag_re_nonneg hc)

/-! ## Monotonicity -/

lemma P1_eq (u : ℝ) : P1 u = -5 * u * (u - 1) ^ 2 * (u + 2) := by unfold P1; ring

lemma P1_nonpos {u : ℝ} (hu : 0 ≤ u) : P1 u ≤ 0 := by
  rw [P1_eq]
  have : 0 ≤ u * (u - 1) ^ 2 * (u + 2) := by positivity
  nlinarith

lemma P_antitoneOn : AntitoneOn P (Ici 0) :=
  antitoneOn_of_deriv_nonpos (convex_Ici 0) continuous_P.continuousOn
    (fun x _ => (hasDerivAt_P x).differentiableAt.differentiableWithinAt)
    (fun x hx => by
      rw [interior_Ici] at hx
      rw [(hasDerivAt_P x).deriv]
      exact P1_nonpos (le_of_lt hx))

lemma P_pos {u : ℝ} (h0 : 0 ≤ u) (h1 : u < 1) : 0 < P u := by
  rw [P_eq]
  exact mul_pos (pow_pos (by linarith) 3) (by positivity)

/-- `f` decreases on `[0, ∞)`. -/
lemma fpar_anti {c : ℝ} (hc : 0 < c) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    fpar c t ≤ fpar c s := by
  rcases le_or_gt t c with htc | htc
  · rw [fpar_of_le htc, fpar_of_le (hst.trans htc)]
    exact P_antitoneOn (show (0 : ℝ) ≤ s / c from div_nonneg hs hc.le)
      (show (0 : ℝ) ≤ t / c from div_nonneg (hs.trans hst) hc.le)
      (div_le_div_of_nonneg_right hst hc.le)
  · rw [fpar_of_lt htc]
    exact fpar_nonneg hc hs

lemma fpar_pos {c t : ℝ} (hc : 0 < c) (h0 : 0 ≤ t) (ht : t < c) : 0 < fpar c t := by
  rw [fpar_of_le ht.le]
  exact P_pos (div_nonneg h0 hc.le) ((div_lt_one hc).2 ht)

/-! ## The transform at real points -/

/-- `Φ(u) = ∫₀¹ P(s) e^{-us} ds`, so that `Re F(x) = c Φ(c x)` (`laplace_fpar_real`). -/
def Phi (u : ℝ) : ℝ := ∫ s in (0 : ℝ)..1, P s * Real.exp (-(u * s))

/-- `Φ` decreases. -/
lemma Phi_anti {u u' : ℝ} (h : u ≤ u') : Phi u' ≤ Phi u := by
  unfold Phi
  refine intervalIntegral.integral_mono_on zero_le_one
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith [hs.1]))
    (P_nonneg hs.1 hs.2)

/-- The closed form of `Φ(u)` for `u ≠ 0`:
`1/u - 10/u³ + 30/u⁴ - 120/u⁶ + e^{-u} (30/u⁴ + 120/u⁵ + 120/u⁶)`. -/
def PhiClosed (u : ℝ) : ℝ :=
  1 / u - 10 / u ^ 3 + 30 / u ^ 4 - 120 / u ^ 6 +
    Real.exp (-u) * (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6)

/-- The antiderivative of `P(s) e^{-us}` (`u ≠ 0`): `-e^{-us} Σ_k P⁽ᵏ⁾(s)/u^{k+1}`. -/
def expPrim (u s : ℝ) : ℝ :=
  -Real.exp (-(u * s)) *
    (P s / u + P1 s / u ^ 2 + P2 s / u ^ 3 + P3 s / u ^ 4 + P4 s / u ^ 5 - 120 / u ^ 6)

lemma hasDerivAt_expPrim {u : ℝ} (hu : u ≠ 0) (s : ℝ) :
    HasDerivAt (expPrim u) (P s * Real.exp (-(u * s))) s := by
  have hl : HasDerivAt (fun s => -(u * s)) (-u) s :=
    ((hasDerivAt_id' s).const_mul u).neg.congr_deriv (by ring)
  have hA : HasDerivAt
      (fun s => P s / u + P1 s / u ^ 2 + P2 s / u ^ 3 + P3 s / u ^ 4 + P4 s / u ^ 5 - 120 / u ^ 6)
      (P1 s / u + P2 s / u ^ 2 + P3 s / u ^ 3 + P4 s / u ^ 4 + (-120) / u ^ 5 - 0) s :=
    (((((((hasDerivAt_P s).div_const u).add ((hasDerivAt_P1 s).div_const _)).add
      ((hasDerivAt_P2 s).div_const _)).add ((hasDerivAt_P3 s).div_const _)).add
      ((hasDerivAt_P4 s).div_const _)).sub (hasDerivAt_const s _))
  have h := hl.exp.neg.mul hA
  exact h.congr_deriv (by simp only [Pi.neg_apply]; unfold P P1 P2 P3 P4; field_simp; ring)

/-- **The closed form of `Φ`.** -/
lemma Phi_eq_closed {u : ℝ} (hu : u ≠ 0) : Phi u = PhiClosed u := by
  unfold Phi
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hasDerivAt_expPrim hu s)
    ((continuous_P.mul (by fun_prop)).intervalIntegrable _ _)]
  simp only [expPrim, PhiClosed, P, P1, P2, P3, P4, mul_one, mul_zero, neg_zero, Real.exp_zero]
  field_simp
  ring

/-- The moments `m_n = ∫₀¹ sⁿ P(s) ds = 1/(n+1) - 5/(n+3) + 5/(n+4) - 1/(n+6)`. -/
def mom (n : ℕ) : ℝ := 1 / (n + 1) - 5 / (n + 3) + 5 / (n + 4) - 1 / (n + 6)

lemma integral_pow_mul_P (n : ℕ) : ∫ s in (0 : ℝ)..1, s ^ n * P s = mom n := by
  have hQ : ∀ s : ℝ, HasDerivAt
      (fun s : ℝ => s ^ (n + 1) / (n + 1) - 5 * s ^ (n + 3) / (n + 3) +
        5 * s ^ (n + 4) / (n + 4) - s ^ (n + 6) / (n + 6)) (s ^ n * P s) s := by
    intro s
    have h1 := (hasDerivAt_pow (n + 1) s).div_const ((n : ℝ) + 1)
    have h3 := ((hasDerivAt_pow (n + 3) s).const_mul 5).div_const ((n : ℝ) + 3)
    have h4 := ((hasDerivAt_pow (n + 4) s).const_mul 5).div_const ((n : ℝ) + 4)
    have h6 := (hasDerivAt_pow (n + 6) s).div_const ((n : ℝ) + 6)
    have h := ((h1.sub h3).add h4).sub h6
    refine h.congr_deriv ?_
    simp only [Nat.add_sub_cancel, show n + 3 - 1 = n + 2 by omega, show n + 4 - 1 = n + 3 by omega,
      show n + 6 - 1 = n + 5 by omega]
    unfold P
    push_cast
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hQ s)
    (((continuous_pow n).mul continuous_P).intervalIntegrable _ _)]
  unfold mom
  simp only [one_pow, ne_eq, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    zero_pow, zero_div, mul_one]
  ring

lemma mom_zero : mom 0 = 5 / 12 := by norm_num [mom]

lemma integral_P : ∫ s in (0 : ℝ)..1, P s = 5 / 12 := by
  have := integral_pow_mul_P 0
  simp only [pow_zero, one_mul] at this
  rw [this, mom_zero]

/-- **The Taylor polynomial of `Φ`**: for `|u| ≤ 1` and `N ≥ 1`,
`|Φ(u) - Σ_{n<N} (-u)ⁿ m_n / n!| ≤ (5/12) |u|^N (N+1)/(N!·N)`. -/
lemma Phi_sub_taylor {u : ℝ} (hu : |u| ≤ 1) {N : ℕ} (hN : 0 < N) :
    |Phi u - ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * mom n| ≤
      5 / 12 * (|u| ^ N * (N.succ / (N.factorial * N))) := by
  set K := |u| ^ N * ((N.succ : ℝ) / (N.factorial * N)) with hK
  have hK0 : 0 ≤ K := by positivity
  have hsum : ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * mom n =
      ∫ s in (0 : ℝ)..1, P s * ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial := by
    have e1 : (fun s : ℝ => P s * ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial) =
        fun s => ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * (s ^ n * P s) := by
      funext s
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show -(u * s) = -u * s by ring, mul_pow]
      ring
    rw [e1, intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [intervalIntegral.integral_const_mul, integral_pow_mul_P]
    · intro n _
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hdiff : Phi u - ∑ n ∈ Finset.range N, (-u) ^ n / n.factorial * mom n =
      ∫ s in (0 : ℝ)..1, P s * (Real.exp (-(u * s)) -
        ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial) := by
    rw [hsum, Phi, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun s _ => ?_
      ring
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
    · exact Continuous.intervalIntegrable (by fun_prop) _ _
  rw [hdiff]
  refine (intervalIntegral.abs_integral_le_integral_abs zero_le_one).trans ?_
  calc ∫ s in (0 : ℝ)..1, |P s * (Real.exp (-(u * s)) -
          ∑ n ∈ Finset.range N, (-(u * s)) ^ n / n.factorial)|
      ≤ ∫ s in (0 : ℝ)..1, P s * K := by
        refine intervalIntegral.integral_mono_on zero_le_one
          (Continuous.intervalIntegrable (by fun_prop) _ _)
          (Continuous.intervalIntegrable (by fun_prop) _ _) fun s hs => ?_
        have hPs : 0 ≤ P s := P_nonneg hs.1 hs.2
        have hus : |-(u * s)| ≤ |u| := by
          rw [abs_neg, abs_mul, abs_of_nonneg hs.1]
          exact mul_le_of_le_one_right (abs_nonneg u) hs.2
        have hb := Real.exp_bound (hus.trans hu) hN
        rw [abs_mul, abs_of_nonneg hPs]
        refine mul_le_mul_of_nonneg_left (hb.trans ?_) hPs
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hus N) (by positivity)
    _ = 5 / 12 * K := by
        rw [intervalIntegral.integral_mul_const, integral_P]

/-- **The transform at real points**: `Re F(x) = ∫₀^c f(t) e^{-xt} dt = c Φ(c x)`. -/
lemma laplace_fpar_real {c : ℝ} (hc : 0 < c) (x : ℝ) :
    (laplace (fpar c) (x : ℂ)).re = c * Phi (c * x) := by
  rw [laplace_re_real (fpar_condition1 hc) x]
  have hcongr : ∫ t in (0 : ℝ)..c, fpar c t * Real.exp (-(x * t)) =
      ∫ t in (0 : ℝ)..c, P (t / c) * Real.exp (-(x * t)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hc.le] at ht
    simp only [fpar_of_le ht.2]
  rw [hcongr]
  have hsub := intervalIntegral.integral_comp_mul_left
    (fun t => P (t / c) * Real.exp (-(x * t))) (a := 0) (b := 1) hc.ne'
  simp only [mul_zero, mul_one] at hsub
  rw [← smul_eq_mul, ← inv_smul_eq_iff₀ hc.ne', ← hsub]
  unfold Phi
  refine intervalIntegral.integral_congr fun s _ => ?_
  show P (c * s / c) * Real.exp (-(x * (c * s))) = P s * Real.exp (-(c * x * s))
  rw [mul_div_cancel_left₀ _ hc.ne']
  ring_nf

end Parabolic

end GradedNear

end
