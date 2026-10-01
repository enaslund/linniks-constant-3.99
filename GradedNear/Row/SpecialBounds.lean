module

public import GradedNear.Vertical
public import GradedNear.Interp
public import GradedNear.Moments
public import GradedNear.ParabolicComplex
public import GradedNear.GramForm

/-!
# Bounds for the transform of the parabolic test off the real axis

For the parabolic test `f = fpar c` of width `c > 0` and its transform `F`:

* `vert_grid_lower`, `vert_grid_upper`: from values on a uniform grid of a vertical line
  `Re z = x`, with the second-derivative bound `∫₀^c t² f(t) e^{-xt} dt ≤ M`;
* `vert_cell_upper`: the same for `-Re F` on one cell;
* `horiz_lipschitz`: `|Re F(x + iy) - Re F(x₀ + iy)| ≤ c² m₁ |x - x₀|` for `x, x₀ ≥ 0`;
* `tail_re_le`, `tail_neg_re_le`: on `Re z = -d` (`d ≥ 0`) with `|Im z| ≥ U > 0`, from the closed
  form of `ΦC`: `Re F ≤ c R(cU, E)` and `-Re F ≤ d/U² + c R(cU, E)`, where
  `R(u, E) = 10/u³ + 30/u⁴ + 120/u⁶ + E (30/u⁴ + 120/u⁵ + 120/u⁶)` and `E ≥ e^{cd}`;
* `re_ge_of_line`: the minimum principle: `Re F ≥ -C` on the line `Re z = -d` gives `Re F ≥ -C`
  on the half-plane `Re z ≥ -d` (Phragmén–Lindelöf for `exp(-F(w - d))` on `Re w ≥ 0`).
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Parabolic

variable {c : ℝ}

lemma fpar_contOn (hc : 0 < c) : ContinuousOn (fpar c) (Icc 0 c) :=
  (continuous_fpar hc).continuousOn

lemma fpar_van (hc : 0 < c) : ∀ t, c ≤ t → fpar c t = 0 := fun t ht => by
  rcases eq_or_lt_of_le ht with h | h
  · subst h; rw [fpar_of_le le_rfl, div_self hc.ne', P_one]
  · exact fpar_of_lt h

/-- The point `x + iy`. -/
abbrev pt (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * I

lemma integral_sq_nonneg (hc : 0 < c) (x : ℝ) :
    0 ≤ ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-(x * t)) :=
  intervalIntegral.integral_nonneg hc.le fun t _ => by positivity

/-- `Re F` along the vertical line `Re z = x` has second derivative at most
`∫₀^c t² |f| e^{-xt}` in absolute value. -/
lemma vert_second (hc : 0 < c) (x : ℝ) :
    (∀ y, HasDerivAt (fun y : ℝ => (laplace (fpar c) (pt x y)).re)
      ((laplace (Vertical.mulT (fpar c)) (pt x y) * I).re) y) ∧
    (∀ y, HasDerivAt (fun y : ℝ => (laplace (Vertical.mulT (fpar c)) (pt x y) * I).re)
      (-(laplace (Vertical.mulT (Vertical.mulT (fpar c))) (pt x y)).re) y) ∧
    (∀ y, |-(laplace (Vertical.mulT (Vertical.mulT (fpar c))) (pt x y)).re| ≤
      ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-(x * t))) :=
  ⟨fun y => Vertical.hasDerivAt_vert hc (fpar_contOn hc) (fpar_van hc) x y,
    fun y => Vertical.hasDerivAt_vert' hc (fpar_contOn hc) (fpar_van hc) x y,
    fun y => Vertical.abs_vert''_le hc (fpar_contOn hc) (fpar_van hc) x y⟩

/-- **Lower bound on a vertical line from a uniform grid.** -/
theorem vert_grid_lower (hc : 0 < c) {x lo h M m : ℝ} (hh : 0 < h) {n : ℕ}
    (hM : ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-(x * t)) ≤ M)
    (hm : ∀ k ≤ n, m ≤ (laplace (fpar c) (pt x (lo + k * h))).re) :
    ∀ y ∈ Icc lo (lo + n * h), m - M * h ^ 2 / 8 ≤ (laplace (fpar c) (pt x y)).re := by
  obtain ⟨h1, h2, h3⟩ := vert_second hc x
  have hM0 := (integral_sq_nonneg hc x).trans hM
  exact grid_lower hh hM0 h1 h2 (fun y _ => (le_abs_self _).trans ((h3 y).trans hM)) hm

/-- **Upper bound on a vertical line from a uniform grid.** -/
theorem vert_grid_upper (hc : 0 < c) {x lo h M m : ℝ} (hh : 0 < h) {n : ℕ}
    (hM : ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-(x * t)) ≤ M)
    (hm : ∀ k ≤ n, (laplace (fpar c) (pt x (lo + k * h))).re ≤ m) :
    ∀ y ∈ Icc lo (lo + n * h), (laplace (fpar c) (pt x y)).re ≤ m + M * h ^ 2 / 8 := by
  obtain ⟨h1, h2, h3⟩ := vert_second hc x
  have hM0 := (integral_sq_nonneg hc x).trans hM
  exact grid_upper hh hM0 h1 h2 (fun y _ => neg_le_of_abs_le ((h3 y).trans hM)) hm

/-- **An upper bound for `-Re F` on one cell** `[a, b]` of a vertical line. -/
theorem vert_cell_upper (hc : 0 < c) {x a b M m : ℝ} (hab : a ≤ b)
    (hM : ∫ t in (0 : ℝ)..c, t ^ 2 * |fpar c t| * Real.exp (-(x * t)) ≤ M)
    (ha : -(laplace (fpar c) (pt x a)).re ≤ m) (hb : -(laplace (fpar c) (pt x b)).re ≤ m) :
    ∀ y ∈ Icc a b, -(laplace (fpar c) (pt x y)).re ≤ m + M * (b - a) ^ 2 / 8 := by
  obtain ⟨h1, h2, h3⟩ := vert_second hc x
  have hM0 := (integral_sq_nonneg hc x).trans hM
  intro y hy
  have := interp_lower hab hM0 h1 h2 (fun y _ => (le_abs_self _).trans ((h3 y).trans hM)) y hy
  have hmin : -m ≤ min (laplace (fpar c) (pt x a)).re (laplace (fpar c) (pt x b)).re :=
    le_min (by linarith) (by linarith)
  linarith

/-- **Lipschitz bound in the real part** on the closed right half-plane:
`|Re F(x + iy) - Re F(x₀ + iy)| ≤ c² m₁ |x - x₀|` for `x, x₀ ≥ 0`. -/
theorem horiz_lipschitz (hc : 0 < c) {x x₀ : ℝ} (hx : 0 ≤ x) (hx₀ : 0 ≤ x₀) (y : ℝ) :
    |(laplace (fpar c) (pt x y)).re - (laplace (fpar c) (pt x₀ y)).re| ≤
      c ^ 2 * mom 1 * |x - x₀| := by
  have hd : ∀ x' ∈ Ici (0 : ℝ), HasDerivWithinAt (fun x : ℝ => (laplace (fpar c) (pt x y)).re)
      ((laplace (Vertical.mulT (fpar c)) (pt x' y)).re) (Ici 0) x' := fun x' _ =>
    (Vertical.hasDerivAt_horiz hc (fpar_contOn hc) (fpar_van hc) x' y).hasDerivWithinAt
  have hb : ∀ x' ∈ Ici (0 : ℝ), ‖(laplace (Vertical.mulT (fpar c)) (pt x' y)).re‖ ≤
      c ^ 2 * mom 1 := fun x' hx' => by
    rw [Real.norm_eq_abs]
    refine (Vertical.abs_horiz'_le hc (fpar_contOn hc) (fpar_van hc) x' y).trans ?_
    have h := moment_le hc 1 (x := x') hx'
    simp only [pow_one] at h
    exact h.trans_eq (by ring)
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb (convex_Ici 0) hx₀ hx
  simpa [Real.norm_eq_abs] using this

/-! ## Tails from the closed form -/

/-- `R(u, E) = 10/u³ + 30/u⁴ + 120/u⁶ + E (30/u⁴ + 120/u⁵ + 120/u⁶)`. -/
def tailR (u E : ℝ) : ℝ :=
  10 / u ^ 3 + 30 / u ^ 4 + 120 / u ^ 6 + E * (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6)

lemma norm_div_pow_le {u : ℂ} {U k : ℝ} (hU : 0 < U) (hu : U ≤ ‖u‖) (hk : 0 ≤ k) (n : ℕ) :
    ‖(k : ℂ) / u ^ n‖ ≤ k / U ^ n := by
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hk]
  exact div_le_div_of_nonneg_left hk (pow_pos hU n) (pow_le_pow_left₀ hU.le hu n)

/-- The closed form of `ΦC` minus its leading term `1/u`, bounded in norm. -/
lemma norm_rest_le {u : ℂ} {U E : ℝ} (hU : 0 < U) (hu : U ≤ ‖u‖) (hE : ‖cexp (-u)‖ ≤ E) :
    ‖PhiClosedC u - 1 / u‖ ≤ tailR U E := by
  have e : PhiClosedC u - 1 / u = -((10 : ℝ) / u ^ 3) + (30 : ℝ) / u ^ 4 - (120 : ℝ) / u ^ 6 +
      cexp (-u) * ((30 : ℝ) / u ^ 4 + (120 : ℝ) / u ^ 5 + (120 : ℝ) / u ^ 6) := by
    unfold PhiClosedC; push_cast; ring
  rw [e]
  have h3 := norm_div_pow_le hU hu (by norm_num : (0 : ℝ) ≤ 10) 3
  have h4 := norm_div_pow_le hU hu (by norm_num : (0 : ℝ) ≤ 30) 4
  have h5 := norm_div_pow_le hU hu (by norm_num : (0 : ℝ) ≤ 120) 5
  have h6 := norm_div_pow_le hU hu (by norm_num : (0 : ℝ) ≤ 120) 6
  have hE0 : 0 ≤ E := (norm_nonneg _).trans hE
  have hB : ‖(30 : ℝ) / u ^ 4 + (120 : ℝ) / u ^ 5 + ((120 : ℝ) : ℂ) / u ^ 6‖ ≤
      30 / U ^ 4 + 120 / U ^ 5 + 120 / U ^ 6 :=
    (norm_add₃_le).trans (by linarith)
  have hB0 : 0 ≤ 30 / U ^ 4 + 120 / U ^ 5 + 120 / U ^ 6 := by positivity
  calc ‖-((10 : ℝ) / u ^ 3) + (30 : ℝ) / u ^ 4 - (120 : ℝ) / u ^ 6 +
        cexp (-u) * ((30 : ℝ) / u ^ 4 + (120 : ℝ) / u ^ 5 + (120 : ℝ) / u ^ 6)‖
      ≤ ‖-((10 : ℝ) / u ^ 3) + (30 : ℝ) / u ^ 4 - (120 : ℝ) / u ^ 6‖ +
          ‖cexp (-u) * ((30 : ℝ) / u ^ 4 + (120 : ℝ) / u ^ 5 + (120 : ℝ) / u ^ 6)‖ :=
        norm_add_le _ _
    _ ≤ (10 / U ^ 3 + 30 / U ^ 4 + 120 / U ^ 6) +
          E * (30 / U ^ 4 + 120 / U ^ 5 + 120 / U ^ 6) := by
        gcongr
        · refine (norm_sub_le _ _).trans ?_
          refine add_le_add ((norm_add_le _ _).trans ?_) h6
          rw [norm_neg]
          exact add_le_add h3 h4
        · rw [norm_mul]
          exact mul_le_mul hE hB (norm_nonneg _) hE0
    _ = tailR U E := by unfold tailR; ring

/-- On the line `Re z = -d` with `|Im z| ≥ U > 0`: `Re F(z) = -d/|z|² + c Re(ΦC(cz) - 1/(cz))`. -/
lemma re_F_line (hc : 0 < c) {d y : ℝ} (hy : y ≠ 0) :
    (laplace (fpar c) (pt (-d) y)).re = -d / (d ^ 2 + y ^ 2) +
      c * (PhiClosedC ((c : ℂ) * pt (-d) y) - 1 / ((c : ℂ) * pt (-d) y)).re := by
  have hz : pt (-d) y ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp [pt] at this
    exact hy this
  have hcz : (c : ℂ) * pt (-d) y ≠ 0 := mul_ne_zero (by exact_mod_cast hc.ne') hz
  rw [laplace_fpar_eq hc, PhiC_eq_closed hcz]
  have hre : ((c : ℂ) * PhiClosedC ((c : ℂ) * pt (-d) y)).re =
      ((c : ℂ) * (1 / ((c : ℂ) * pt (-d) y))).re +
        c * (PhiClosedC ((c : ℂ) * pt (-d) y) - 1 / ((c : ℂ) * pt (-d) y)).re := by
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.sub_re]; ring
  rw [hre]
  congr 1
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have e : (c : ℂ) * (1 / ((c : ℂ) * pt (-d) y)) = 1 / pt (-d) y := by field_simp
  rw [e, one_div, Complex.inv_re, Complex.normSq_apply]
  simp only [pt, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  ring

lemma tail_common (hc : 0 < c) {d y U E : ℝ} (hU : 0 < U) (hy : U ≤ |y|)
    (hE : Real.exp (c * d) ≤ E) :
    |(PhiClosedC ((c : ℂ) * pt (-d) y) - 1 / ((c : ℂ) * pt (-d) y)).re| ≤ tailR (c * U) E := by
  refine (Complex.abs_re_le_norm _).trans (norm_rest_le (mul_pos hc hU) ?_ ?_)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    refine mul_le_mul_of_nonneg_left (hy.trans ?_) hc.le
    have : |((pt (-d) y)).im| ≤ ‖pt (-d) y‖ := Complex.abs_im_le_norm _
    simpa [pt] using this
  · rw [Complex.norm_exp]
    refine le_trans (le_of_eq ?_) hE
    congr 1
    simp [pt]

lemma tailR_nonneg {u E : ℝ} (hu : 0 < u) (hE : 0 ≤ E) : 0 ≤ tailR u E := by
  unfold tailR; positivity

/-- **The tail of `Re F`** on the line `Re z = -d`, `d ≥ 0`, for `|y| ≥ U > 0`. -/
theorem tail_re_le (hc : 0 < c) {d y U E : ℝ} (hd : 0 ≤ d) (hU : 0 < U) (hy : U ≤ |y|)
    (hE : Real.exp (c * d) ≤ E) :
    (laplace (fpar c) (pt (-d) y)).re ≤ c * tailR (c * U) E := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, abs_zero] at hy; linarith
  rw [re_F_line hc hy0]
  have h1 := tail_common hc hU hy hE
  have h2 : -d / (d ^ 2 + y ^ 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h3 := (le_abs_self _).trans h1
  nlinarith

/-- **The tail of `-Re F`** on the line `Re z = -d`, `d ≥ 0`, for `|y| ≥ U > 0`. -/
theorem tail_neg_re_le (hc : 0 < c) {d y U E : ℝ} (hd : 0 ≤ d) (hU : 0 < U) (hy : U ≤ |y|)
    (hE : Real.exp (c * d) ≤ E) :
    -(laplace (fpar c) (pt (-d) y)).re ≤ d / U ^ 2 + c * tailR (c * U) E := by
  have hy0 : y ≠ 0 := by
    intro h; rw [h, abs_zero] at hy; linarith
  rw [re_F_line hc hy0]
  have h1 := tail_common hc hU hy hE
  have h4 : d / (d ^ 2 + y ^ 2) ≤ d / U ^ 2 := by
    have hU2 : U ^ 2 ≤ d ^ 2 + y ^ 2 := by
      have : U ^ 2 ≤ y ^ 2 := by
        rw [← sq_abs y]; exact pow_le_pow_left₀ hU.le hy 2
      nlinarith [sq_nonneg d]
    exact div_le_div_of_nonneg_left hd (by positivity) hU2
  have h5 := neg_abs_le ((PhiClosedC ((c : ℂ) * pt (-d) y) - 1 / ((c : ℂ) * pt (-d) y)).re)
  have h6 : -(c * tailR (c * U) E) ≤
      c * (PhiClosedC ((c : ℂ) * pt (-d) y) - 1 / ((c : ℂ) * pt (-d) y)).re := by
    have := mul_le_mul_of_nonneg_left (h5.trans' (neg_le_neg h1)) hc.le
    linarith
  have e : -(-d / (d ^ 2 + y ^ 2)) = d / (d ^ 2 + y ^ 2) := by ring
  linarith

/-! ## The minimum principle on a half-plane -/

/-- **The minimum principle**: `Re F ≥ -C` on the line `Re z = -d` gives `Re F ≥ -C`
on the half-plane `Re z ≥ -d`. -/
theorem re_ge_of_line (hc : 0 < c) {d C : ℝ}
    (hline : ∀ y : ℝ, -C ≤ (laplace (fpar c) (pt (-d) y)).re) :
    ∀ z : ℂ, -d ≤ z.re → -C ≤ (laplace (fpar c) z).re := by
  intro z hz
  set A := ∫ t in (0 : ℝ)..c, |fpar c t| * Real.exp (-((-d) * t)) with hA
  set g : ℂ → ℂ := fun w => cexp (-laplace (fpar c) (w - d)) with hg
  have hF := Admissible.laplace_differentiable (fpar_condition1 hc)
  have hgd : Differentiable ℂ g := ((hF.comp (differentiable_id.sub_const _))).neg.cexp
  have hgn : ∀ w, ‖g w‖ = Real.exp (-(laplace (fpar c) (w - d)).re) := fun w => by
    simp [g, Complex.norm_exp]
  -- `F(w - d)` is bounded by `A` on the closed right half-plane
  have hFb : ∀ w : ℂ, 0 ≤ w.re → ‖laplace (fpar c) (w - d)‖ ≤ A := fun w hw => by
    refine (Admissible.norm_laplace_le_of hc (fpar_contOn hc) (fpar_van hc) _).trans ?_
    refine intervalIntegral.integral_mono_on hc.le ?_ ?_ fun t ht => ?_
    · exact Continuous.intervalIntegrable ((continuous_fpar hc).abs.mul (by fun_prop)) _ _
    · exact Continuous.intervalIntegrable ((continuous_fpar hc).abs.mul (by fun_prop)) _ _
    · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (abs_nonneg _)
      have : (w - d).re = w.re - d := by simp
      rw [this]
      nlinarith [ht.1]
  have hgb : ∀ w : ℂ, 0 ≤ w.re → ‖g w‖ ≤ Real.exp A := fun w hw => by
    rw [hgn]
    refine Real.exp_le_exp.2 ?_
    have h1 := hFb w hw
    have h2 := neg_abs_le (laplace (fpar c) (w - d)).re
    have h3 := Complex.abs_re_le_norm (laplace (fpar c) (w - d))
    linarith
  have hw : 0 ≤ (z + d).re := by simp; linarith
  have hPL := PhragmenLindelof.right_half_plane_of_bounded_on_real (f := g) (C := Real.exp C)
    hgd.diffContOnCl ?_ ?_ ?_ hw
  · rw [hgn, show z + (d : ℂ) - d = z by ring] at hPL
    have := Real.exp_le_exp.1 hPL
    linarith
  · refine ⟨0, by norm_num, 0, ?_⟩
    refine Asymptotics.IsBigO.of_bound (Real.exp A) ?_
    refine eventually_inf_principal.2 (Eventually.of_forall fun w hw => ?_)
    have hw' : 0 ≤ w.re := le_of_lt hw
    simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hgb w hw'
  · refine ⟨Real.exp A, Filter.eventually_map.2 ?_⟩
    filter_upwards [eventually_ge_atTop 0] with x hx
    exact hgb (x : ℂ) (by simpa using hx)
  · intro y
    rw [hgn]
    refine Real.exp_le_exp.2 ?_
    have h := hline y
    have e : (y : ℂ) * I - d = pt (-d) y := by simp [pt]; ring
    rw [e]
    linarith

end Parabolic

end GradedNear

end
