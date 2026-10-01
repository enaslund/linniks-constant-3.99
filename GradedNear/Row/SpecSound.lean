module

public import GradedNear.Row.SpecialSound
public import GradedNear.Row.SpecialBounds

/-!
# The values of the special entries are sound (`RowCheckCore.specVals`)

`SpecSem q sp add exc` states what the values `(add, exc)` of an entry's semantics `sp` mean for
the row parameters `q` (paper §9.2). `F` and `G` are the transforms of the detector `fpar(2γ)`
and of the Gram test `fpar(2g₁)`:
* `one`: `add = exc = 0`;
* `two xa xb ylo yhi`: `exc ≥ 0`, and for `x ∈ [xa, xb]` and `|y| ∈ [ylo, yhi]`, `add ≤ Re F(x + iy)`
  and `Re G(-s₁ + iy) - 1/6 ≤ exc`. This is the second zero's term and the pair excess of the `rc`
  pair (`y = ±2μ₁`) and of the first family's second zero;
* `cz d`: `add ≤ Re F(z)` on the half-plane `Re z ≥ -d`, and `exc = 0`. This is the shifted `rc`
  entry's conjugate zero (`add = -C_Z`).

`specVals_sound`: the checker's values satisfy `SpecSem`. The grids use `vert_grid_lower`,
`vert_grid_upper` and `horiz_lipschitz`, the tails `tail_re_le` and `tail_neg_re_le`, and the
half-plane the minimum principle `re_ge_of_line`.
-/

@[expose] public section

noncomputable section

open IntervalCore LeafNumCore Complex Set

namespace GradedNear.Row

open Parabolic

/-- **The meaning of an entry's values** `(add, exc)` (see the module docstring). -/
def SpecSem (q : Params) : RowCheckCore.Spec → ℝ → ℝ → Prop
  | .one, add, exc => add = 0 ∧ exc = 0
  | .two xa xb ylo yhi _ _, add, exc => 0 ≤ exc ∧
      ∀ x y : ℝ, (xa : ℝ) ≤ x → x ≤ xb → (ylo : ℝ) ≤ |y| → (∀ v, yhi = some v → |y| ≤ v) →
        add ≤ (laplace (fpar (2 * (q.γ : ℝ))) (pt x y)).re ∧
        (laplace (fpar (2 * (q.g1 : ℝ))) (pt (-(q.s1 : ℝ)) y)).re - 1 / 6 ≤ exc
  | .cz d _, add, exc => exc = 0 ∧
      ∀ z : ℂ, -(d : ℝ) ≤ z.re → add ≤ (laplace (fpar (2 * (q.γ : ℝ))) z).re

lemma SpecSem.exc_nonneg {q : Params} {sp : RowCheckCore.Spec} {add exc : ℝ}
    (h : SpecSem q sp add exc) : 0 ≤ exc := by
  cases sp with
  | one => exact h.2.symm ▸ le_rfl
  | two => exact h.1
  | cz => exact h.1.symm ▸ le_rfl

/-! ## Points, grids and tails -/

lemma reFI_pt {c : ℚ} (hc : 0 < c) (x y : ℚ) (prec : ℕ) :
    (laplace (fpar (c : ℝ)) (pt (x : ℝ) (y : ℝ))).re ∈ₗ RowCheckCore.reFI c x y prec := by
  have e : pt (x : ℝ) (y : ℝ) = (x : ℂ) + (y : ℂ) * I := by simp [pt]
  rw [e]
  exact reFI_sound hc x y prec

/-- `Re` of a real function's transform is even in the height. -/
lemma re_pt_abs (g : ℝ → ℝ) (x y : ℝ) : (laplace g (pt x y)).re = (laplace g (pt x |y|)).re := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy, ← laplace_re_conj g (pt x (-y))]
    congr 2
    apply Complex.ext <;> simp [pt]

lemma gridMin_le (c x lo h : ℚ) (prec : ℕ) : ∀ n k : ℕ, k ≤ n →
    (RowCheckCore.gridMin c x lo h prec n : ℝ) ≤
      ((RowCheckCore.reFI c x (lo + (k : ℚ) * h) prec).lo : ℝ)
  | 0, k, hk => by
    obtain rfl : k = 0 := by omega
    simp [RowCheckCore.gridMin]
  | n + 1, k, hk => by
    simp only [RowCheckCore.gridMin]
    rw [cast_rmin]
    rcases Nat.lt_or_ge k (n + 1) with h1 | h1
    · exact (min_le_left _ _).trans (gridMin_le c x lo h prec n k (by omega))
    · obtain rfl : k = n + 1 := by omega
      exact min_le_right _ _

lemma le_gridMax (c x lo h : ℚ) (prec : ℕ) : ∀ n k : ℕ, k ≤ n →
    ((RowCheckCore.reFI c x (lo + (k : ℚ) * h) prec).hi : ℝ) ≤
      (RowCheckCore.gridMax c x lo h prec n : ℝ)
  | 0, k, hk => by
    obtain rfl : k = 0 := by omega
    simp [RowCheckCore.gridMax]
  | n + 1, k, hk => by
    simp only [RowCheckCore.gridMax]
    rw [cast_rmax]
    rcases Nat.lt_or_ge k (n + 1) with h1 | h1
    · exact (le_gridMax c x lo h prec n k (by omega)).trans (le_max_left _ _)
    · obtain rfl : k = n + 1 := by omega
      exact le_max_right _ _

lemma cast_tailRQ (u E : ℚ) : ((RowCheckCore.tailRQ u E : ℚ) : ℝ) = tailR (u : ℝ) (E : ℝ) := by
  simp only [RowCheckCore.tailRQ, tailR]; push_cast; ring

lemma exp_le_expI_hi (q : ℚ) (prec : ℕ) :
    Real.exp (q : ℝ) ≤ ((expI q prec).hi : ℝ) := (mem_expI q prec).2

/-- The second moment `∫ t² |f| e^{dt}` of the test of width `c` is at most `c³ (e2I (cd)).hi`. -/
lemma moment2_le_e2I {c : ℚ} (hc : (0 : ℝ) < c) (d : ℚ) (prec : ℕ) :
    ∫ t in (0 : ℝ)..(c : ℝ), t ^ 2 * |fpar (c : ℝ) t| * Real.exp (-((-(d : ℝ)) * t)) ≤
      ((c ^ 3 * (RowCheckCore.e2I (c * d) prec).hi : ℚ) : ℝ) := by
  rw [moment2_exp_eq hc]
  have h := (e2I_sound (c * d) prec).2
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-! ## `two` entries -/

section Two

variable {p : RowCheckCore.RowP} (hg : (ofCore p).Good)
include hg

lemma hγ2 : (0 : ℝ) < 2 * (p.γ : ℝ) := by
  have := hg.γ_pos; simp only [ofCore_γ] at this
  have : (0 : ℝ) < p.γ := by exact_mod_cast this
  linarith

lemma hg12 : (0 : ℝ) < 2 * (p.g1 : ℝ) := by
  have := hg.g1_pos; simp only [ofCore_g1] at this
  have : (0 : ℝ) < p.g1 := by exact_mod_cast this
  linarith

lemma hs1 : (0 : ℝ) ≤ p.s1 := by
  have := hg.s1_nonneg; simp only [ofCore_s1] at this; exact_mod_cast this

/-- **The grid part of a `two` entry.** -/
lemma twoGrid_sound {xa xb lo top : ℚ} {n prec : ℕ} (hxa : 0 ≤ xa) (hxab : xa ≤ xb)
    (hlt : lo < top) (hn : 0 < n) {x Y : ℝ} (hx1 : (xa : ℝ) ≤ x) (hx2 : x ≤ xb)
    (hY1 : (lo : ℝ) ≤ Y) (hY2 : Y ≤ top) :
    ((RowCheckCore.twoGrid p xa xb lo top n prec).1 : ℝ) ≤
        (laplace (fpar (2 * (p.γ : ℝ))) (pt x Y)).re ∧
      (laplace (fpar (2 * (p.g1 : ℝ))) (pt (-(p.s1 : ℝ)) Y)).re ≤
        ((RowCheckCore.twoGrid p xa xb lo top n prec).2 : ℝ) := by
  unfold RowCheckCore.twoGrid
  simp only []
  have hγ := hγ2 hg
  have hg1 := hg12 hg
  have hn' : (0 : ℚ) < n := by exact_mod_cast hn
  set h : ℚ := (top - lo) / n with hh
  have hh0 : (0 : ℚ) < h := div_pos (by linarith) hn'
  have hh0' : (0 : ℝ) < h := by exact_mod_cast hh0
  have htop : (lo : ℝ) + (n : ℝ) * (h : ℝ) = top := by
    have : (lo : ℚ) + (n : ℚ) * h = top := by rw [hh]; field_simp; ring
    exact_mod_cast this
  have hYI : Y ∈ Icc (lo : ℝ) ((lo : ℝ) + (n : ℝ) * (h : ℝ)) := ⟨hY1, by rw [htop]; exact hY2⟩
  set x₀ : ℚ := (xa + xb) / 2 with hx₀
  have hx₀0 : (0 : ℝ) ≤ x₀ := by
    have : (0 : ℚ) ≤ x₀ := by rw [hx₀]; linarith
    exact_mod_cast this
  have hcγ : ((2 * p.γ : ℚ) : ℝ) = 2 * (p.γ : ℝ) := by push_cast; ring
  have hcg : ((2 * p.g1 : ℚ) : ℝ) = 2 * (p.g1 : ℝ) := by push_cast; ring
  have hγq : (0 : ℚ) < 2 * p.γ := by exact_mod_cast (hcγ ▸ hγ)
  have hgq : (0 : ℚ) < 2 * p.g1 := by exact_mod_cast (hcg ▸ hg1)
  constructor
  · -- `Re F` at the midpoint from the grid, then the Lipschitz bound in `x`
    have hM := moment_le hγ 2 hx₀0
    have hgrid := vert_grid_lower hγ (x := (x₀ : ℝ)) (lo := (lo : ℝ)) (h := (h : ℝ))
      (M := (2 * (p.γ : ℝ)) ^ 3 * Parabolic.mom 2)
      (m := (RowCheckCore.gridMin (2 * p.γ) x₀ lo h prec n : ℝ)) hh0' (n := n)
      (by simpa using hM)
      (fun k hk => by
        have h1 := gridMin_le (2 * p.γ) x₀ lo h prec n k hk
        have h2 := (reFI_pt hγq x₀ (lo + (k : ℚ) * h) prec).1
        rw [hcγ] at h2
        push_cast at h2
        exact h1.trans h2) Y hYI
    have hlip := horiz_lipschitz hγ (le_trans (by exact_mod_cast hxa) hx1) hx₀0 Y
    have hdist : |x - x₀| ≤ ((xb : ℝ) - xa) / 2 := by
      rw [abs_le]; push_cast [hx₀]; constructor <;> linarith
    have hm1 : 0 ≤ (2 * (p.γ : ℝ)) ^ 2 * Parabolic.mom 1 := by
      have : 0 ≤ Parabolic.mom 1 := by norm_num [Parabolic.mom]
      positivity
    have hlip' := (abs_le.1 hlip).1
    have := mul_le_mul_of_nonneg_left hdist hm1
    push_cast [cast_mom]
    nlinarith
  · -- `Re G` on the line `Re z = -s₁` from the grid
    have hM := moment2_le_e2I (c := 2 * p.g1) (by rw [hcg]; exact hg1) p.s1 prec
    rw [hcg] at hM
    have hgrid := vert_grid_upper hg1 (x := -(p.s1 : ℝ)) (lo := (lo : ℝ)) (h := (h : ℝ))
      (M := (((2 * p.g1) ^ 3 * (RowCheckCore.e2I (2 * p.g1 * p.s1) prec).hi : ℚ) : ℝ))
      (m := (RowCheckCore.gridMax (2 * p.g1) (-p.s1) lo h prec n : ℝ)) hh0' (n := n)
      hM
      (fun k hk => by
        have h1 := le_gridMax (2 * p.g1) (-p.s1) lo h prec n k hk
        have h2 := (reFI_pt hgq (-p.s1) (lo + (k : ℚ) * h) prec).2
        rw [hcg] at h2
        push_cast at h2
        exact h2.trans h1) Y hYI
    push_cast at hgrid ⊢
    linarith

/-- **The tail of a `two` entry**: `Re F ≥ 0` for `x ≥ 0`, and `Re G(-s₁ + iY) ≤ gramTail` for
`Y ≥ ytop > 0`. -/
lemma twoTail_sound {ytop : ℚ} {prec : ℕ} (hytop : 0 < ytop) {x Y : ℝ} (hx : 0 ≤ x)
    (hY : (ytop : ℝ) ≤ Y) :
    0 ≤ (laplace (fpar (2 * (p.γ : ℝ))) (pt x Y)).re ∧
      (laplace (fpar (2 * (p.g1 : ℝ))) (pt (-(p.s1 : ℝ)) Y)).re ≤
        ((RowCheckCore.gramTail p ytop prec : ℚ) : ℝ) := by
  have hγ := hγ2 hg
  have hg1 := hg12 hg
  refine ⟨(fpar_condition2 hγ).re_nonneg _ (by simp [pt]; exact hx), ?_⟩
  have hU : (0 : ℝ) < ytop := by exact_mod_cast hytop
  have hY' : (ytop : ℝ) ≤ |Y| := hY.trans (le_abs_self Y)
  have h := tail_re_le hg1 (hs1 hg) hU hY'
    (exp_le_expI_hi (2 * p.g1 * p.s1) prec |>.trans_eq' (by push_cast; ring_nf))
  unfold RowCheckCore.gramTail
  push_cast [cast_tailRQ]
  exact h

omit hg in
/-- The range of a `two` entry is covered by its grid and its tail. -/
lemma two_cover {ylo ytop : ℚ} {yhi : Option ℚ}
    (hsome : ylo < RowCheckCore.twoTop yhi ytop ∨ RowCheckCore.twoTail yhi ytop = true)
    {Y : ℝ} (hY1 : (ylo : ℝ) ≤ Y) (hY2 : ∀ v, yhi = some v → Y ≤ v) :
    (ylo < RowCheckCore.twoTop yhi ytop ∧ Y ≤ (RowCheckCore.twoTop yhi ytop : ℝ)) ∨
      (RowCheckCore.twoTail yhi ytop = true ∧ (ytop : ℝ) ≤ Y) := by
  cases yhi with
  | none =>
    simp only [RowCheckCore.twoTop, RowCheckCore.twoTail, true_and] at hsome ⊢
    by_cases h : ylo < ytop ∧ Y ≤ (ytop : ℝ)
    · exact Or.inl h
    · right
      rcases not_and_or.1 h with h1 | h1
      · have : (ytop : ℝ) ≤ ylo := by exact_mod_cast not_lt.1 h1
        linarith
      · linarith [not_le.1 h1]
  | some v =>
    have hv := hY2 v rfl
    simp only [RowCheckCore.twoTop, RowCheckCore.twoTail, decide_eq_true_eq] at hsome ⊢
    rw [cast_rmin] at *
    by_cases h : ylo < rmin v ytop ∧ Y ≤ min (v : ℝ) (ytop : ℝ)
    · exact Or.inl h
    · right
      rcases not_and_or.1 h with h1 | h1
      · -- `ylo ≥ top`: the tail must be used, and `Y ≥ ylo ≥ top = ytop`
        have htail : ytop < v := hsome.resolve_left h1
        have hmin : rmin v ytop = ytop := by
          unfold rmin; split_ifs with h2
          · exact absurd h2 (not_le.2 htail)
          · rfl
        rw [hmin] at h1
        have : (ytop : ℝ) ≤ ylo := by exact_mod_cast not_lt.1 h1
        exact ⟨htail, by linarith⟩
      · -- `Y > top`: then `top = ytop < Y ≤ v`
        have hlt := not_le.1 h1
        rcases le_total (v : ℝ) (ytop : ℝ) with hvt | hvt
        · rw [min_eq_left hvt] at hlt; linarith
        · rw [min_eq_right hvt] at hlt
          refine ⟨?_, hlt.le⟩
          have : (ytop : ℝ) < v := lt_of_lt_of_le hlt hv
          exact_mod_cast this

/-- **The bounds `(R, C)` of a `two` entry.** -/
lemma twoRC_sound {xa xb ylo ytop : ℚ} {yhi : Option ℚ} {n prec : ℕ} {R C : ℚ}
    (hxa : 0 ≤ xa) (hxab : xa ≤ xb) (hytop : 0 < ytop) (hn : 0 < n)
    (h : RowCheckCore.twoRC p xa xb ylo yhi ytop n prec = some (R, C))
    {x Y : ℝ} (hx1 : (xa : ℝ) ≤ x) (hx2 : x ≤ xb) (hY1 : (ylo : ℝ) ≤ Y)
    (hY2 : ∀ v, yhi = some v → Y ≤ v) :
    (R : ℝ) ≤ (laplace (fpar (2 * (p.γ : ℝ))) (pt x Y)).re ∧
      (laplace (fpar (2 * (p.g1 : ℝ))) (pt (-(p.s1 : ℝ)) Y)).re ≤ C := by
  have hx0 : (0 : ℝ) ≤ x := le_trans (by exact_mod_cast hxa) hx1
  have hgrid := fun (hlt : ylo < RowCheckCore.twoTop yhi ytop)
    (hY : Y ≤ (RowCheckCore.twoTop yhi ytop : ℝ)) =>
    twoGrid_sound hg (prec := prec) hxa hxab hlt hn hx1 hx2 hY1 hY
  have htail := fun (hY : (ytop : ℝ) ≤ Y) => twoTail_sound hg (prec := prec) hytop hx0 hY
  unfold RowCheckCore.twoRC at h
  split_ifs at h with hlt htl htl'
  · -- grid and tail
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [cast_rmin, cast_rmax]
    rcases two_cover (Or.inl hlt) hY1 hY2 with ⟨_, hY⟩ | ⟨_, hY⟩
    · obtain ⟨h1, h2⟩ := hgrid hlt hY
      exact ⟨(min_le_left _ _).trans h1, h2.trans (le_max_left _ _)⟩
    · obtain ⟨h1, h2⟩ := htail hY
      push_cast
      exact ⟨(min_le_right _ _).trans h1, h2.trans (le_max_right _ _)⟩
  · -- grid only
    simp only [Option.some.injEq] at h
    rcases two_cover (Or.inl hlt) hY1 hY2 with ⟨_, hY⟩ | ⟨h', _⟩
    · have hg' := hgrid hlt hY
      rw [h] at hg'
      exact hg'
    · exact absurd h' htl
  · -- tail only
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases two_cover (Or.inr htl') hY1 hY2 with ⟨h', _⟩ | ⟨_, hY⟩
    · exact absurd h' hlt
    · obtain ⟨h1, h2⟩ := htail hY
      push_cast
      exact ⟨h1, h2⟩

/-- **The values of a `two` entry.** -/
theorem twoVals_sound {xa xb ylo ytop : ℚ} {yhi : Option ℚ} {n prec : ℕ} {a e : ℚ}
    (h : RowCheckCore.twoVals p xa xb ylo yhi ytop n prec = some (a, e)) :
    SpecSem (ofCore p) (.two xa xb ylo yhi ytop n) a e := by
  unfold RowCheckCore.twoVals at h
  split_ifs at h with hc
  obtain ⟨hxa, hxab, hylo, hytop, hn⟩ := hc
  rw [Option.map_eq_some_iff] at h
  obtain ⟨⟨R, C⟩, hRC, hae⟩ := h
  simp only [Prod.mk.injEq] at hae
  obtain ⟨rfl, rfl⟩ := hae
  refine ⟨by rw [cast_rmax]; push_cast; exact le_max_right _ _, ?_⟩
  intro x y hx1 hx2 hy1 hy2
  have hY0 : (0 : ℝ) ≤ |y| := abs_nonneg y
  obtain ⟨h1, h2⟩ := twoRC_sound hg hxa hxab hytop hn hRC hx1 hx2 hy1 hy2
  simp only [ofCore_γ, ofCore_g1, ofCore_s1]
  rw [re_pt_abs, re_pt_abs (fpar (2 * (p.g1 : ℝ)))]
  rw [cast_rmax, cast_rmax]
  push_cast
  constructor
  · exact max_le h1 (by
      have := (fpar_condition2 (hγ2 hg)).re_nonneg (pt x |y|)
        (by simp [pt]; exact le_trans (by exact_mod_cast hxa) hx1)
      exact this)
  · exact (by linarith : _ - 1 / 6 ≤ (C : ℝ) - 1 / 6).trans (le_max_left _ _)

/-! ## `cz` entries -/

omit hg in
/-- **The cells of the line `Re z = -d`.** -/
lemma cellsMax_sound {c d M : ℚ} (hc : 0 < c) {prec : ℕ}
    (hM : ∫ t in (0 : ℝ)..(c : ℝ), t ^ 2 * |fpar (c : ℝ) t| * Real.exp (-((-(d : ℝ)) * t)) ≤ M) :
    ∀ (rest : List ℚ) (a m : ℚ), RowCheckCore.cellsMax c d M prec a rest = some m →
      ∀ y : ℝ, (a : ℝ) ≤ y → y ≤ (RowCheckCore.lastPt a rest : ℝ) →
        -(laplace (fpar (c : ℝ)) (pt (-(d : ℝ)) y)).re ≤ m
  | [], a, m, h, y, hy1, hy2 => by
    simp only [RowCheckCore.cellsMax, Option.some.injEq] at h
    subst h
    simp only [RowCheckCore.lastPt] at hy2
    have hy : y = a := le_antisymm hy2 hy1
    subst hy
    have := (reFI_pt hc (-d) a prec).1
    push_cast at this ⊢
    linarith
  | b :: rest, a, m, h, y, hy1, hy2 => by
    have hc' : (0 : ℝ) < c := by exact_mod_cast hc
    simp only [RowCheckCore.cellsMax] at h
    split_ifs at h with hab
    rw [Option.map_eq_some_iff] at h
    obtain ⟨m', hm', rfl⟩ := h
    simp only [RowCheckCore.lastPt] at hy2
    rw [cast_rmax]
    rcases le_or_gt y b with hyb | hyb
    · -- the cell `[a, b]`
      refine le_trans ?_ (le_max_right _ _)
      have ha := (reFI_pt hc (-d) a prec).1
      have hb := (reFI_pt hc (-d) b prec).1
      push_cast at ha hb
      set A : ℝ := ((RowCheckCore.reFI c (-d) a prec).lo : ℝ) with hA
      set B : ℝ := ((RowCheckCore.reFI c (-d) b prec).lo : ℝ) with hB
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab.le
      have hma : -(laplace (fpar (c : ℝ)) (pt (-(d : ℝ)) a)).re ≤ max (-A) (-B) := by
        have := le_max_left (-A) (-B); linarith
      have hmb : -(laplace (fpar (c : ℝ)) (pt (-(d : ℝ)) b)).re ≤ max (-A) (-B) := by
        have := le_max_right (-A) (-B); linarith
      have hcell := vert_cell_upper hc' hab' hM hma hmb y ⟨hy1, hyb⟩
      push_cast [cast_rmax]
      exact hcell
    · -- the later cells
      exact (cellsMax_sound hc hM rest b m' hm' y hyb.le hy2).trans (le_max_left _ _)

/-- **The bound `C` of a `cz` entry**: `Re F ≥ -C` on the half-plane `Re z ≥ -d`. -/
theorem czC_sound {d : ℚ} {ys : List ℚ} {prec : ℕ} {C : ℚ}
    (h : RowCheckCore.czC p d ys prec = some C) :
    ∀ z : ℂ, -(d : ℝ) ≤ z.re → -(C : ℝ) ≤ (laplace (fpar (2 * (p.γ : ℝ))) z).re := by
  have hγ := hγ2 hg
  have hcγ : ((2 * p.γ : ℚ) : ℝ) = 2 * (p.γ : ℝ) := by push_cast; ring
  have hγq : (0 : ℚ) < 2 * p.γ := by exact_mod_cast (hcγ ▸ hγ)
  unfold RowCheckCore.czC at h
  cases ys with
  | nil => simp at h
  | cons y0 rest =>
    simp only [] at h
    split_ifs at h with hc
    obtain ⟨rfl, hd, hY⟩ := hc
    rw [Option.map_eq_some_iff] at h
    obtain ⟨m, hm, rfl⟩ := h
    have hd' : (0 : ℝ) ≤ d := by exact_mod_cast hd
    set Y := RowCheckCore.lastPt 0 rest with hYdef
    have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
    have hM := moment2_le_e2I (c := 2 * p.γ) (by rw [hcγ]; exact hγ) d prec
    have hcells := cellsMax_sound hγq hM rest 0 m hm
    rw [hcγ] at hcells
    refine re_ge_of_line hγ ?_
    intro y
    rw [re_pt_abs, cast_rmax]
    rcases le_or_gt |y| (Y : ℝ) with hy | hy
    · have := hcells |y| (by simp) hy
      linarith [le_max_left (m : ℝ) (((d / Y ^ 2 + 2 * p.γ * RowCheckCore.tailRQ (2 * p.γ * Y)
        (expI (2 * p.γ * d) prec).hi : ℚ)) : ℝ)]
    · have ht := tail_neg_re_le hγ hd' hY' (y := |y|) (by rw [abs_abs]; exact hy.le)
        (exp_le_expI_hi (2 * p.γ * d) prec |>.trans_eq' (by push_cast; ring_nf))
      have e : (((d / Y ^ 2 + 2 * p.γ * RowCheckCore.tailRQ (2 * p.γ * Y)
          (expI (2 * p.γ * d) prec).hi : ℚ)) : ℝ) = (d : ℝ) / (Y : ℝ) ^ 2 +
          2 * (p.γ : ℝ) * tailR (2 * (p.γ : ℝ) * Y) ((expI (2 * p.γ * d) prec).hi) := by
        push_cast [cast_tailRQ]; ring_nf
      linarith [le_max_right (m : ℝ) (((d / Y ^ 2 + 2 * p.γ * RowCheckCore.tailRQ (2 * p.γ * Y)
        (expI (2 * p.γ * d) prec).hi : ℚ)) : ℝ)]

/-- **The values of an entry's semantics are sound.** -/
theorem specVals_sound {sp : RowCheckCore.Spec} {prec : ℕ} {a e : ℚ}
    (h : RowCheckCore.specVals p sp prec = some (a, e)) : SpecSem (ofCore p) sp a e := by
  cases sp with
  | one =>
    simp only [RowCheckCore.specVals, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [SpecSem]
  | two xa xb ylo yhi ytop n => exact twoVals_sound hg h
  | cz d ys =>
    simp only [RowCheckCore.specVals] at h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨C, hC, hae⟩ := h
    simp only [Prod.mk.injEq] at hae
    obtain ⟨rfl, rfl⟩ := hae
    refine ⟨by simp, fun z hz => ?_⟩
    have := czC_sound hg hC z hz
    simp only [ofCore_γ]
    push_cast
    exact this

end Two

end GradedNear.Row

end
