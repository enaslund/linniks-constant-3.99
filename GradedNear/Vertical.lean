module

public import GradedNear.Admissible

/-!
# The transform along vertical and horizontal lines

For `g` continuous on `[0, x₀]` and vanishing on `[x₀, ∞)` (so that its transform is entire,
`Admissible.laplace_hasDerivAt_of`):

* `hasDerivAt_vert`, `hasDerivAt_vert'`: `y ↦ Re G(x + iy)` is twice differentiable, with first
  derivative `Re(G₁(x + iy) i)` and second derivative `-Re G₂(x + iy)`, where `G₁` and `G₂` are the
  transforms of `-t g(t)` and `t² g(t)`;
* `abs_vert''_le`: `|-Re G₂(x + iy)| ≤ ∫₀^{x₀} t² |g(t)| e^{-xt} dt`;
* `hasDerivAt_horiz`, `abs_horiz'_le`: `x ↦ Re G(x + iy)` has derivative `Re G₁(x + iy)`, bounded by
  `∫₀^{x₀} t |g(t)| e^{-xt} dt`.
-/

@[expose] public section

noncomputable section

open Complex MeasureTheory Set

namespace GradedNear

namespace Vertical

open Admissible

variable {g : ℝ → ℝ} {x₀ : ℝ}

/-- `-t g(t)`. -/
def mulT (g : ℝ → ℝ) (t : ℝ) : ℝ := -t * g t

lemma mulT_cont (hcont : ContinuousOn g (Icc 0 x₀)) : ContinuousOn (mulT g) (Icc 0 x₀) :=
  continuous_neg.continuousOn.mul hcont

lemma mulT_van (hvan : ∀ t, x₀ ≤ t → g t = 0) : ∀ t, x₀ ≤ t → mulT g t = 0 := fun t ht => by
  simp [mulT, hvan t ht]

lemma hasDerivAt_line (x y : ℝ) :
    HasDerivAt (fun y : ℝ => (x : ℂ) + (y : ℂ) * I) I y := by
  have := ((hasDerivAt_id y).ofReal_comp.mul_const I).const_add (x : ℂ)
  simpa using this

lemma hasDerivAt_hline (x y : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + (y : ℂ) * I) 1 x := by
  have := ((hasDerivAt_id x).ofReal_comp).add_const ((y : ℂ) * I)
  simpa using this

/-- The complex function `y ↦ G(x + iy)` has derivative `G₁(x + iy) i`. -/
lemma hasDerivAt_vertC (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => laplace g ((x : ℂ) + (y : ℂ) * I))
      (laplace (mulT g) ((x : ℂ) + (y : ℂ) * I) * I) y := by
  have h := (laplace_hasDerivAt_of hx₀ hcont hvan ((x : ℂ) + (y : ℂ) * I)).comp y
    (hasDerivAt_line x y)
  exact h

/-- **First derivative along a vertical line.** -/
lemma hasDerivAt_vert (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => (laplace g ((x : ℂ) + (y : ℂ) * I)).re)
      ((laplace (mulT g) ((x : ℂ) + (y : ℂ) * I) * I).re) y :=
  (Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hasDerivAt_vertC hx₀ hcont hvan x y))

/-- **Second derivative along a vertical line.** -/
lemma hasDerivAt_vert' (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    HasDerivAt (fun y : ℝ => (laplace (mulT g) ((x : ℂ) + (y : ℂ) * I) * I).re)
      (-(laplace (mulT (mulT g)) ((x : ℂ) + (y : ℂ) * I)).re) y := by
  have h := (hasDerivAt_vertC hx₀ (mulT_cont hcont) (mulT_van hvan) x y).mul_const I
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y h
  refine h2.congr_deriv ?_
  simp only [Complex.reCLM_apply]
  rw [mul_assoc, Complex.I_mul_I]
  simp

lemma mulT_mulT (g : ℝ → ℝ) (t : ℝ) : mulT (mulT g) t = t ^ 2 * g t := by
  simp only [mulT]; ring

/-- `|-Re G₂(x + iy)| ≤ ∫₀^{x₀} t² |g(t)| e^{-xt} dt`. -/
lemma abs_vert''_le (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    |-(laplace (mulT (mulT g)) ((x : ℂ) + (y : ℂ) * I)).re| ≤
      ∫ t in (0 : ℝ)..x₀, t ^ 2 * |g t| * Real.exp (-(x * t)) := by
  rw [abs_neg]
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_laplace_le_of hx₀ (mulT_cont (mulT_cont hcont)) (mulT_van (mulT_van hvan)) _).trans
    (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun t ht => ?_
  simp only [mulT_mulT, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [abs_mul, abs_of_nonneg (sq_nonneg t)]

/-- **The derivative along a horizontal line.** -/
lemma hasDerivAt_horiz (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    HasDerivAt (fun x : ℝ => (laplace g ((x : ℂ) + (y : ℂ) * I)).re)
      ((laplace (mulT g) ((x : ℂ) + (y : ℂ) * I)).re) x := by
  have h := (laplace_hasDerivAt_of hx₀ hcont hvan ((x : ℂ) + (y : ℂ) * I)).comp x
    (hasDerivAt_hline x y)
  have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x h
  refine h2.congr_deriv ?_
  simp only [Complex.reCLM_apply, mul_one]
  rfl

/-- `|Re G₁(x + iy)| ≤ ∫₀^{x₀} t |g(t)| e^{-xt} dt`. -/
lemma abs_horiz'_le (hx₀ : 0 < x₀) (hcont : ContinuousOn g (Icc 0 x₀))
    (hvan : ∀ t, x₀ ≤ t → g t = 0) (x y : ℝ) :
    |(laplace (mulT g) ((x : ℂ) + (y : ℂ) * I)).re| ≤
      ∫ t in (0 : ℝ)..x₀, t * |g t| * Real.exp (-(x * t)) := by
  refine (Complex.abs_re_le_norm _).trans ?_
  refine (norm_laplace_le_of hx₀ (mulT_cont hcont) (mulT_van hvan) _).trans (le_of_eq ?_)
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hx₀.le] at ht
  simp only [mulT, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  rw [abs_mul, abs_neg, abs_of_nonneg ht.1]

end Vertical

end GradedNear

end
