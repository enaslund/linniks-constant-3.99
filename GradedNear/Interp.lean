module

public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.Convex.Segment

/-!
# Interpolation with a second-derivative bound

The row builders bound a function of the height on an interval from its values at the ends of
the grid cells: for `g` twice differentiable with `g'' ≤ M` on `[a, b]` (`M ≥ 0`),
`g(y) ≥ min(g(a), g(b)) - M (b - a)²/8`, and for `g'' ≥ -M`, `g(y) ≤ max(g(a), g(b)) + M (b-a)²/8`
(`interp_lower`, `interp_upper`). The proof: `g - ℓ + (M/2)(y - a)(b - y)`, with `ℓ` the chord,
is concave and vanishes at both ends. `grid_lower` and `grid_upper` apply this on every cell of a
uniform grid.
-/

@[expose] public section

open Set

namespace GradedNear

/-- **Lower bound from the ends of a cell**, for `g'' ≤ M`, `M ≥ 0`. -/
theorem interp_lower {g g' g'' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hM0 : 0 ≤ M)
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Icc a b, g'' y ≤ M) :
    ∀ y ∈ Icc a b, min (g a) (g b) - M * (b - a) ^ 2 / 8 ≤ g y := by
  intro y hy
  rcases eq_or_lt_of_le hab with hab' | hab'
  · subst hab'
    have : y = a := le_antisymm hy.2 hy.1
    subst this
    have : 0 ≤ M * (y - y) ^ 2 / 8 := by positivity
    linarith [min_le_left (g y) (g y)]
  set k := (g b - g a) / (b - a) with hk
  -- ψ = g - chord + (M/2)(y - a)(b - y)
  set ψ : ℝ → ℝ := fun y => g y - (g a + k * (y - a)) + M / 2 * ((y - a) * (b - y)) with hψ
  have hψ' : ∀ y, HasDerivAt ψ (g' y - k + M / 2 * (a + b - 2 * y)) y := fun y => by
    have h1 := ((hg y).sub (((hasDerivAt_id' y).sub_const a).const_mul k |>.const_add (g a))).add
      ((((hasDerivAt_id' y).sub_const a).mul ((hasDerivAt_const y b).sub (hasDerivAt_id' y))).const_mul
        (M / 2))
    refine h1.congr_deriv ?_
    simp only [Pi.sub_apply]
    ring
  have hψ'' : ∀ y, HasDerivAt (fun y => g' y - k + M / 2 * (a + b - 2 * y))
      (g'' y - M) y := fun y => by
    have h1 := ((hg' y).sub_const k).add
      ((((hasDerivAt_const y (a + b)).sub ((hasDerivAt_id' y).const_mul 2))).const_mul (M / 2))
    refine h1.congr_deriv ?_
    ring
  have hconc : ConcaveOn ℝ (Icc a b) ψ := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc a b)
      (fun y _ => (hψ' y).continuousAt.continuousWithinAt)
      (fun y _ => (hψ' y).hasDerivWithinAt) (fun y _ => (hψ'' y).hasDerivWithinAt) ?_
    intro y hy
    rw [interior_Icc] at hy
    have := hM y (Ioo_subset_Icc_self hy)
    linarith
  have ha : ψ a = 0 := by simp [hψ]
  have hb : ψ b = 0 := by
    simp only [hψ, hk]
    field_simp
    ring
  have hψy := hconc.ge_on_segment (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
    (by rw [segment_eq_Icc hab]; exact hy)
  rw [ha, hb, min_self] at hψy
  simp only [hψ] at hψy
  -- the chord is at least the smaller end value, and (y - a)(b - y) ≤ (b - a)²/4
  have hchord : min (g a) (g b) ≤ g a + k * (y - a) := by
    have hba : 0 < b - a := by linarith
    have ht : 0 ≤ (y - a) / (b - a) ∧ (y - a) / (b - a) ≤ 1 :=
      ⟨div_nonneg (by linarith [hy.1]) hba.le, (div_le_one hba).2 (by linarith [hy.2])⟩
    have e : g a + k * (y - a) = (1 - (y - a) / (b - a)) * g a + ((y - a) / (b - a)) * g b := by
      rw [hk]; field_simp; ring
    rw [e]
    have h1 := min_le_left (g a) (g b)
    have h2 := min_le_right (g a) (g b)
    nlinarith [ht.1, ht.2]
  have hsq : (y - a) * (b - y) ≤ (b - a) ^ 2 / 4 := by nlinarith [sq_nonneg (2 * y - a - b)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hM0]

/-- **Upper bound from the ends of a cell**, for `g'' ≥ -M`, `M ≥ 0`. -/
theorem interp_upper {g g' g'' : ℝ → ℝ} {a b M : ℝ} (hab : a ≤ b) (hM0 : 0 ≤ M)
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y)
    (hM : ∀ y ∈ Icc a b, -M ≤ g'' y) :
    ∀ y ∈ Icc a b, g y ≤ max (g a) (g b) + M * (b - a) ^ 2 / 8 := by
  intro y hy
  have h := interp_lower (g := fun y => -g y) (g' := fun y => -g' y) (g'' := fun y => -g'' y)
    hab hM0 (fun y => (hg y).neg) (fun y => (hg' y).neg) (fun y hy => by linarith [hM y hy]) y hy
  simp only [min_neg_neg] at h
  linarith

/-- **A uniform grid**: with `y_k = lo + k h`, `k ≤ n`, and `g'' ≤ M` on `[lo, lo + n h]`, every value
on `[lo, lo + n h]` is at least `m - M h²/8` when every grid value is at least `m`. -/
theorem grid_lower {g g' g'' : ℝ → ℝ} {lo h M : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y) {n : ℕ}
    (hM : ∀ y ∈ Icc lo (lo + n * h), g'' y ≤ M) {m : ℝ}
    (hm : ∀ k ≤ n, m ≤ g (lo + k * h)) :
    ∀ y ∈ Icc lo (lo + n * h), m - M * h ^ 2 / 8 ≤ g y := by
  intro y hy
  have hMh : 0 ≤ M * h ^ 2 / 8 := by positivity
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Nat.cast_zero, zero_mul, add_zero] at hy
    have hyl : y = lo := le_antisymm hy.2 hy.1
    subst hyl
    have := hm 0 le_rfl
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    linarith
  set j := min (⌊(y - lo) / h⌋₊) (n - 1) with hj
  have hjn : j + 1 ≤ n := by omega
  have hq0 : 0 ≤ (y - lo) / h := div_nonneg (by linarith [hy.1]) hh.le
  have hlo : lo + j * h ≤ y := by
    have h1 : (j : ℝ) ≤ (y - lo) / h := by
      have : (j : ℝ) ≤ (⌊(y - lo) / h⌋₊ : ℝ) := by exact_mod_cast min_le_left _ _
      exact this.trans (Nat.floor_le hq0)
    rw [le_div_iff₀ hh] at h1
    linarith
  have hhi : y ≤ lo + ((j + 1 : ℕ) : ℝ) * h := by
    rcases le_or_gt (⌊(y - lo) / h⌋₊) (n - 1) with hle | hgt
    · have hjeq : j = ⌊(y - lo) / h⌋₊ := min_eq_left hle
      have h1 : (y - lo) / h < (j : ℝ) + 1 := by rw [hjeq]; exact Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hh] at h1
      push_cast
      linarith
    · have hjeq : j = n - 1 := min_eq_right hgt.le
      have hj1 : ((j + 1 : ℕ) : ℝ) = n := by rw [hjeq]; exact_mod_cast Nat.sub_add_cancel hn
      rw [hj1]
      exact hy.2
  have hsub : Icc (lo + j * h) (lo + ((j + 1 : ℕ) : ℝ) * h) ⊆ Icc lo (lo + n * h) := by
    have h0 : (0 : ℝ) ≤ j * h := by positivity
    refine Icc_subset_Icc (by linarith) ?_
    have : ((j + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hjn
    nlinarith
  have hcell := interp_lower (a := lo + j * h) (b := lo + ((j + 1 : ℕ) : ℝ) * h) (M := M)
    (by push_cast; nlinarith) hM0 hg hg' (fun z hz => hM z (hsub hz)) y ⟨hlo, hhi⟩
  have hw : (lo + ((j + 1 : ℕ) : ℝ) * h) - (lo + j * h) = h := by push_cast; ring
  rw [hw] at hcell
  have h1 := hm j (by omega)
  have h2 := hm (j + 1) hjn
  have : m ≤ min (g (lo + j * h)) (g (lo + ((j + 1 : ℕ) : ℝ) * h)) := le_min h1 h2
  linarith

/-- **A uniform grid**, upper bound: for `g'' ≥ -M` and every grid value at most `m`, every value
on `[lo, lo + n h]` is at most `m + M h²/8`. -/
theorem grid_upper {g g' g'' : ℝ → ℝ} {lo h M : ℝ} (hh : 0 < h) (hM0 : 0 ≤ M)
    (hg : ∀ y, HasDerivAt g (g' y) y) (hg' : ∀ y, HasDerivAt g' (g'' y) y) {n : ℕ}
    (hM : ∀ y ∈ Icc lo (lo + n * h), -M ≤ g'' y) {m : ℝ}
    (hm : ∀ k ≤ n, g (lo + k * h) ≤ m) :
    ∀ y ∈ Icc lo (lo + n * h), g y ≤ m + M * h ^ 2 / 8 := by
  intro y hy
  have := grid_lower (g := fun y => -g y) (g' := fun y => -g' y) (g'' := fun y => -g'' y)
    hh hM0 (fun y => (hg y).neg) (fun y => (hg' y).neg) (fun y hy => by linarith [hM y hy])
    (m := -m) (fun k hk => by linarith [hm k hk]) y hy
  linarith

end GradedNear
