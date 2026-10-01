module

public import IntervalCore
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Nat.Cast.Order.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Soundness of the interval library `IntervalCore`

`x ∈ₗ I` means `(I.lo : ℝ) ≤ x ≤ (I.hi : ℝ)`. For every operation of `IntervalCore` we prove the
inclusion property: if the arguments are members of the argument intervals, the value is a member
of the result (`Ival.mem_add`, `mem_sub`, `mem_neg`, `mem_mul`, `mem_div`, `mem_inv`, `mem_sqr`,
`mem_pow`, `mem_addRat`, `mem_mulRat`, `mem_divRat`, `mem_ofRat`, `mem_join_left`,
`mem_join_right`, `mem_round`, `mem_exp`), and the checks (`Ival.le_of_le`, `le_of_leRat`, …) are sound. The
rounding lemmas are `roundDown_le` and `le_roundUp` (in `ℚ`) and their casts to `ℝ`.

For the exponential (`expLo_le`, `le_expHi`, `Ival.mem_exp`): the fixed-point Taylor sum is a lower
bound by `Real.sum_le_exp_of_nonneg` (`taylor_fst_le`); its error bound gives an upper bound by
`Real.exp_bound` for the tail after `m ≥ 1` terms, `|Y|^m (m+1)/(m!·m) ≤ 2 Y^m/m!` for `|Y| ≤ 1`
(`le_taylor_add`), and `Real.abs_exp_sub_one_le` covers the rounding of the reduced argument. The
squarings use `Real.exp_add`, negative arguments `Real.exp_neg`, and `q ≤ -p` the bound
`2 ≤ exp 1`.
-/

@[expose] public section

namespace IntervalCore

open Finset

/-- Membership of a real number in an interval with rational ends. -/
def Mem (x : ℝ) (I : Ival) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

@[inherit_doc] infix:50 " ∈ₗ " => Mem

theorem mem_def {x : ℝ} {I : Ival} : x ∈ₗ I ↔ (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ) := Iff.rfl

/-! ## Rounding -/

theorem cast_mkRat_two_pow (m : ℤ) (p : ℕ) :
    ((mkRat m (2 ^ p) : ℚ) : ℝ) = (m : ℝ) / 2 ^ p := by
  rw [Rat.mkRat_eq_div]; push_cast; rfl

theorem divDown_le (p : ℕ) (n : ℤ) {d : ℕ} (hd : 0 < d) : divDown p n d ≤ (n : ℚ) / d := by
  unfold divDown
  rw [Rat.mkRat_eq_div]
  have h2 : (0 : ℚ) < ((2 ^ p : ℕ) : ℚ) := by positivity
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ h2 hd']
  have key := Int.ediv_mul_le (n * ((2 ^ p : ℕ) : ℤ)) (b := (d : ℤ)) (by exact_mod_cast hd.ne')
  have key' : (((n * ((2 ^ p : ℕ) : ℤ) / (d : ℤ) : ℤ) : ℚ)) * ((d : ℤ) : ℚ) ≤
      ((n * ((2 ^ p : ℕ) : ℤ) : ℤ) : ℚ) := by exact_mod_cast key
  simpa using key'

theorem le_divUp (p : ℕ) (n : ℤ) {d : ℕ} (hd : 0 < d) : (n : ℚ) / d ≤ divUp p n d := by
  unfold divUp
  rw [Rat.mkRat_eq_div]
  have h2 : (0 : ℚ) < ((2 ^ p : ℕ) : ℚ) := by positivity
  have hd' : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  rw [div_le_div_iff₀ hd' h2]
  have key := Int.ediv_mul_le (-n * ((2 ^ p : ℕ) : ℤ)) (b := (d : ℤ)) (by exact_mod_cast hd.ne')
  have key' : (((-n * ((2 ^ p : ℕ) : ℤ) / (d : ℤ) : ℤ) : ℚ)) * ((d : ℤ) : ℚ) ≤
      ((-n * ((2 ^ p : ℕ) : ℤ) : ℤ) : ℚ) := by exact_mod_cast key
  push_cast at key' ⊢
  linarith

theorem roundDown_le (p : ℕ) (q : ℚ) : roundDown p q ≤ q := by
  unfold roundDown
  split_ifs
  · exact le_rfl
  · calc divDown p q.num q.den ≤ (q.num : ℚ) / q.den := divDown_le p q.num q.den_pos
      _ = q := Rat.num_div_den q

theorem le_roundUp (p : ℕ) (q : ℚ) : q ≤ roundUp p q := by
  unfold roundUp
  split_ifs
  · exact le_rfl
  · calc q = (q.num : ℚ) / q.den := (Rat.num_div_den q).symm
      _ ≤ divUp p q.num q.den := le_divUp p q.num q.den_pos

theorem roundDown_le_real (p : ℕ) (q : ℚ) : ((roundDown p q : ℚ) : ℝ) ≤ (q : ℝ) := by
  exact_mod_cast roundDown_le p q

theorem le_roundUp_real (p : ℕ) (q : ℚ) : (q : ℝ) ≤ ((roundUp p q : ℚ) : ℝ) := by
  exact_mod_cast le_roundUp p q

theorem cast_rmin (a b : ℚ) : ((rmin a b : ℚ) : ℝ) = min (a : ℝ) (b : ℝ) := by
  unfold rmin
  split_ifs with h
  · rw [min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right (by exact_mod_cast (le_of_lt (not_le.mp h)))]

theorem cast_rmax (a b : ℚ) : ((rmax a b : ℚ) : ℝ) = max (a : ℝ) (b : ℝ) := by
  unfold rmax
  split_ifs with h
  · rw [max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left (by exact_mod_cast (le_of_lt (not_le.mp h)))]

/-! ## Checks -/

theorem ratLe_iff (a b : ℚ) : ratLe a b = true ↔ (a : ℝ) ≤ (b : ℝ) := by
  simp [ratLe, Rat.cast_le]

theorem ratLt_iff (a b : ℚ) : ratLt a b = true ↔ (a : ℝ) < (b : ℝ) := by
  simp [ratLt, Rat.cast_lt]

namespace Ival

theorem valid_of_mem {x : ℝ} {I : Ival} (hx : x ∈ₗ I) : I.valid = true := by
  have : (I.lo : ℝ) ≤ I.hi := hx.1.trans hx.2
  simpa [valid] using (show I.lo ≤ I.hi by exact_mod_cast this)

theorem mem_of_contains {I : Ival} {q : ℚ} (h : I.contains q = true) : (q : ℝ) ∈ₗ I := by
  simp only [contains, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩

theorem mem_of_subset {x : ℝ} {I J : Ival} (h : I.subset J = true) (hx : x ∈ₗ I) : x ∈ₗ J := by
  simp only [subset, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨le_trans (by exact_mod_cast h.1) hx.1, le_trans hx.2 (by exact_mod_cast h.2)⟩

theorem le_of_le {x y : ℝ} {I J : Ival} (h : I.le J = true) (hx : x ∈ₗ I) (hy : y ∈ₗ J) :
    x ≤ y := by
  simp only [le, decide_eq_true_eq] at h
  exact hx.2.trans ((show (I.hi : ℝ) ≤ J.lo by exact_mod_cast h).trans hy.1)

theorem lt_of_lt {x y : ℝ} {I J : Ival} (h : I.lt J = true) (hx : x ∈ₗ I) (hy : y ∈ₗ J) :
    x < y := by
  simp only [lt, decide_eq_true_eq] at h
  exact lt_of_le_of_lt hx.2 ((show (I.hi : ℝ) < J.lo by exact_mod_cast h).trans_le hy.1)

theorem le_of_leRat {x : ℝ} {I : Ival} {q : ℚ} (h : I.leRat q = true) (hx : x ∈ₗ I) :
    x ≤ q := by
  simp only [leRat, decide_eq_true_eq] at h
  exact hx.2.trans (by exact_mod_cast h)

theorem lt_of_ltRat {x : ℝ} {I : Ival} {q : ℚ} (h : I.ltRat q = true) (hx : x ∈ₗ I) :
    x < q := by
  simp only [ltRat, decide_eq_true_eq] at h
  exact hx.2.trans_lt (by exact_mod_cast h)

theorem ge_of_geRat {x : ℝ} {I : Ival} {q : ℚ} (h : I.geRat q = true) (hx : x ∈ₗ I) :
    (q : ℝ) ≤ x := by
  simp only [geRat, decide_eq_true_eq] at h
  exact (show (q : ℝ) ≤ I.lo by exact_mod_cast h).trans hx.1

theorem gt_of_gtRat {x : ℝ} {I : Ival} {q : ℚ} (h : I.gtRat q = true) (hx : x ∈ₗ I) :
    (q : ℝ) < x := by
  simp only [gtRat, decide_eq_true_eq] at h
  exact (show (q : ℝ) < I.lo by exact_mod_cast h).trans_le hx.1

/-! ## Arithmetic -/

theorem mem_ofRat (q : ℚ) : (q : ℝ) ∈ₗ ofRat q := ⟨le_rfl, le_rfl⟩

theorem mem_join_left {x : ℝ} {I : Ival} (J : Ival) (hx : x ∈ₗ I) : x ∈ₗ join I J := by
  refine ⟨?_, ?_⟩
  · simp only [join, cast_rmin]; exact min_le_of_left_le hx.1
  · simp only [join, cast_rmax]; exact le_max_of_le_left hx.2

theorem mem_join_right {x : ℝ} (I : Ival) {J : Ival} (hx : x ∈ₗ J) : x ∈ₗ join I J := by
  refine ⟨?_, ?_⟩
  · simp only [join, cast_rmin]; exact min_le_of_right_le hx.1
  · simp only [join, cast_rmax]; exact le_max_of_le_right hx.2

theorem mem_round {x : ℝ} {I : Ival} (p : ℕ) (hx : x ∈ₗ I) : x ∈ₗ I.round p :=
  ⟨(roundDown_le_real p _).trans hx.1, hx.2.trans (le_roundUp_real p _)⟩

theorem mem_neg {x : ℝ} {I : Ival} (hx : x ∈ₗ I) : -x ∈ₗ I.neg := by
  refine ⟨?_, ?_⟩
  · simp only [neg, Rat.cast_neg]; linarith [hx.2]
  · simp only [neg, Rat.cast_neg]; linarith [hx.1]

theorem mem_add {x y : ℝ} {I J : Ival} (p : ℕ) (hx : x ∈ₗ I) (hy : y ∈ₗ J) :
    x + y ∈ₗ I.add J p := by
  refine ⟨?_, ?_⟩
  · refine (roundDown_le_real p _).trans ?_
    push_cast; linarith [hx.1, hy.1]
  · refine le_trans ?_ (le_roundUp_real p _)
    push_cast; linarith [hx.2, hy.2]

theorem mem_sub {x y : ℝ} {I J : Ival} (p : ℕ) (hx : x ∈ₗ I) (hy : y ∈ₗ J) :
    x - y ∈ₗ I.sub J p := by
  refine ⟨?_, ?_⟩
  · refine (roundDown_le_real p _).trans ?_
    push_cast; linarith [hx.1, hy.2]
  · refine le_trans ?_ (le_roundUp_real p _)
    push_cast; linarith [hx.2, hy.1]

theorem mem_addRat {x : ℝ} {I : Ival} (q : ℚ) (p : ℕ) (hx : x ∈ₗ I) :
    x + q ∈ₗ I.addRat q p := by
  refine ⟨?_, ?_⟩
  · refine (roundDown_le_real p _).trans ?_
    push_cast; linarith [hx.1]
  · refine le_trans ?_ (le_roundUp_real p _)
    push_cast; linarith [hx.2]

theorem mem_mulRat {x : ℝ} {I : Ival} (q : ℚ) (p : ℕ) (hx : x ∈ₗ I) :
    x * q ∈ₗ I.mulRat q p := by
  unfold mulRat
  split_ifs with hq
  · have hq' : (0 : ℝ) ≤ q := by exact_mod_cast hq
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast; exact mul_le_mul_of_nonneg_right hx.1 hq'
    · push_cast; exact mul_le_mul_of_nonneg_right hx.2 hq'
  · have hq' : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp hq))
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast; exact mul_le_mul_of_nonpos_right hx.2 hq'
    · push_cast; exact mul_le_mul_of_nonpos_right hx.1 hq'

theorem mem_divRat {x : ℝ} {I : Ival} (q : ℚ) (p : ℕ) (hx : x ∈ₗ I) :
    x / q ∈ₗ I.divRat q p := by
  have := mem_mulRat q⁻¹ p hx
  rw [div_eq_mul_inv]
  simpa [divRat] using this

/-! ### Products -/

theorem min_mul_le {a b x : ℝ} (y : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    min (a * y) (b * y) ≤ x * y := by
  rcases le_total 0 y with hy | hy
  · exact min_le_of_left_le (mul_le_mul_of_nonneg_right ha hy)
  · exact min_le_of_right_le (mul_le_mul_of_nonpos_right hb hy)

theorem le_max_mul {a b x : ℝ} (y : ℝ) (ha : a ≤ x) (hb : x ≤ b) :
    x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_right hb hy)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_right ha hy)

/-- A product lies above the least product of ends. -/
theorem min4_le_mul {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have h1 : min (a * c) (a * d) ≤ a * y := by
    have := min_mul_le a hc hd
    rwa [mul_comm c a, mul_comm d a, mul_comm y a] at this
  have h2 : min (b * c) (b * d) ≤ b * y := by
    have := min_mul_le b hc hd
    rwa [mul_comm c b, mul_comm d b, mul_comm y b] at this
  exact (min_le_min h1 h2).trans (min_mul_le y ha hb)

/-- A product lies below the greatest product of ends. -/
theorem mul_le_max4 {a b c d x y : ℝ} (ha : a ≤ x) (hb : x ≤ b) (hc : c ≤ y) (hd : y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h1 : a * y ≤ max (a * c) (a * d) := by
    have := le_max_mul a hc hd
    rwa [mul_comm c a, mul_comm d a, mul_comm y a] at this
  have h2 : b * y ≤ max (b * c) (b * d) := by
    have := le_max_mul b hc hd
    rwa [mul_comm c b, mul_comm d b, mul_comm y b] at this
  exact (le_max_mul y ha hb).trans (max_le_max h1 h2)

theorem mem_mul {x y : ℝ} {I J : Ival} (p : ℕ) (hx : x ∈ₗ I) (hy : y ∈ₗ J) :
    x * y ∈ₗ I.mul J p := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  unfold mul
  split_ifs with h
  · have h1 : (0 : ℝ) ≤ I.lo := by exact_mod_cast h.1
    have h2 : (0 : ℝ) ≤ J.lo := by exact_mod_cast h.2
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast; exact mul_le_mul hx1 hy1 h2 (h1.trans hx1)
    · push_cast; exact mul_le_mul hx2 hy2 (h2.trans hy1) ((h1.trans hx1).trans hx2)
  · refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · simp only [cast_rmin, Rat.cast_mul]; exact min4_le_mul hx1 hx2 hy1 hy2
    · simp only [cast_rmax, Rat.cast_mul]; exact mul_le_max4 hx1 hx2 hy1 hy2

theorem mem_sqr {x : ℝ} {I : Ival} (p : ℕ) (hx : x ∈ₗ I) : x ^ 2 ∈ₗ I.sqr p := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold sqr
  split_ifs with h h'
  · have h0 : (0 : ℝ) ≤ I.lo := by exact_mod_cast h
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast; nlinarith
    · push_cast; nlinarith
  · have h0 : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h'
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast; nlinarith
    · push_cast; nlinarith
  · refine ⟨by simpa using sq_nonneg x, le_trans ?_ (le_roundUp_real p _)⟩
    simp only [cast_rmax, Rat.cast_mul]
    rcases le_total 0 x with h0 | h0
    · exact le_max_of_le_right (by nlinarith)
    · exact le_max_of_le_left (by nlinarith)

theorem mem_pow {x : ℝ} {I : Ival} (n : ℕ) (p : ℕ) (hx : x ∈ₗ I) : x ^ n ∈ₗ I.pow n p := by
  obtain ⟨hx1, hx2⟩ := hx
  unfold pow
  split_ifs with hn h h'
  · subst hn; simpa using mem_ofRat 1
  · refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast
      rcases h with h | h
      · exact (Nat.odd_iff.mpr h).pow_le_pow.mpr hx1
      · exact pow_le_pow_left₀ (by exact_mod_cast h) hx1 n
    · push_cast
      rcases h with h | h
      · exact (Nat.odd_iff.mpr h).pow_le_pow.mpr hx2
      · exact pow_le_pow_left₀ ((show (0 : ℝ) ≤ I.lo by exact_mod_cast h).trans hx1) hx2 n
  · have he : Even n := Nat.even_iff.mpr (by have := (not_or.mp h).1; omega)
    have h0 : (I.hi : ℝ) ≤ 0 := by exact_mod_cast h'
    refine ⟨(roundDown_le_real p _).trans ?_, le_trans ?_ (le_roundUp_real p _)⟩
    · push_cast
      rw [← he.neg_pow (I.hi : ℝ), ← he.neg_pow x]
      exact pow_le_pow_left₀ (by linarith) (by linarith) n
    · push_cast
      rw [← he.neg_pow (I.lo : ℝ), ← he.neg_pow x]
      exact pow_le_pow_left₀ (by linarith) (by linarith) n
  · have he : Even n := Nat.even_iff.mpr (by have := (not_or.mp h).1; omega)
    refine ⟨by simpa using he.pow_nonneg x, le_trans ?_ (le_roundUp_real p _)⟩
    simp only [cast_rmax, Rat.cast_pow]
    rcases le_total 0 x with h0 | h0
    · exact le_max_of_le_right (pow_le_pow_left₀ h0 hx2 n)
    · refine le_max_of_le_left ?_
      rw [← he.neg_pow (I.lo : ℝ), ← he.neg_pow x]
      exact pow_le_pow_left₀ (by linarith) (by linarith) n

/-- The reciprocals of the members of an interval that does not contain `0`. -/
theorem inv_mem_recip {y : ℝ} {J : Ival} (hJ : 0 < J.lo ∨ J.hi < 0) (hy : y ∈ₗ J) :
    y⁻¹ ∈ₗ (⟨J.hi⁻¹, J.lo⁻¹⟩ : Ival) := by
  obtain ⟨hy1, hy2⟩ := hy
  simp only [Mem, Rat.cast_inv]
  rcases hJ with h | h
  · have h' : (0 : ℝ) < J.lo := by exact_mod_cast h
    exact ⟨inv_anti₀ (h'.trans_le hy1) hy2, inv_anti₀ h' hy1⟩
  · have h' : (J.hi : ℝ) < 0 := by exact_mod_cast h
    have hyn : y < 0 := hy2.trans_lt h'
    refine ⟨?_, ?_⟩
    · rw [inv_le_inv_of_neg h' hyn]; exact hy2
    · rw [inv_le_inv_of_neg hyn (hy1.trans_lt hyn)]; exact hy1

theorem mem_inv {y : ℝ} {J K : Ival} {p : ℕ} (h : J.inv p = some K) (hy : y ∈ₗ J) :
    y⁻¹ ∈ₗ K := by
  unfold inv at h
  split_ifs at h with hJ
  cases h
  obtain ⟨h1, h2⟩ := inv_mem_recip hJ hy
  exact ⟨(roundDown_le_real p _).trans h1, h2.trans (le_roundUp_real p _)⟩

theorem mem_div {x y : ℝ} {I J K : Ival} {p : ℕ} (h : I.div J p = some K) (hx : x ∈ₗ I)
    (hy : y ∈ₗ J) : x / y ∈ₗ K := by
  unfold div at h
  split_ifs at h with hJ
  cases h
  rw [div_eq_mul_inv]
  exact mem_mul p hx (inv_mem_recip hJ hy)

theorem div_isSome {I J : Ival} (p : ℕ) (hJ : 0 < J.lo ∨ J.hi < 0) : (I.div J p).isSome := by
  simp [div, hJ]

theorem inv_isSome {J : Ival} (p : ℕ) (hJ : 0 < J.lo ∨ J.hi < 0) : (J.inv p).isSome := by
  simp [inv, hJ]

/-! ### Notation -/

theorem mem_neg' {x : ℝ} {I : Ival} (hx : x ∈ₗ I) : -x ∈ₗ -I := mem_neg hx

theorem mem_add' {x y : ℝ} {I J : Ival} (hx : x ∈ₗ I) (hy : y ∈ₗ J) : x + y ∈ₗ I + J :=
  mem_add defaultPrec hx hy

theorem mem_sub' {x y : ℝ} {I J : Ival} (hx : x ∈ₗ I) (hy : y ∈ₗ J) : x - y ∈ₗ I - J :=
  mem_sub defaultPrec hx hy

theorem mem_mul' {x y : ℝ} {I J : Ival} (hx : x ∈ₗ I) (hy : y ∈ₗ J) : x * y ∈ₗ I * J :=
  mem_mul defaultPrec hx hy

end Ival

/-! ## Fixed point -/

theorem shr_le (a w : ℕ) : ((a >>> w : ℕ) : ℝ) ≤ (a : ℝ) / 2 ^ w := by
  rw [Nat.shiftRight_eq_div_pow]
  have := Nat.cast_div_le (α := ℝ) (m := a) (n := 2 ^ w)
  simpa using this

theorem lt_div_add_one (a : ℕ) {b : ℕ} (hb : 0 < b) : (a : ℝ) / b < ((a / b : ℕ) : ℝ) + 1 := by
  have h := Nat.lt_div_mul_add (a := a) hb
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have h' : (a : ℝ) < ((a / b : ℕ) : ℝ) * b + b := by exact_mod_cast h
  rw [div_lt_iff₀ hb']
  linarith

theorem lt_shr_add_one (a w : ℕ) : (a : ℝ) / 2 ^ w < ((a >>> w : ℕ) : ℝ) + 1 := by
  rw [Nat.shiftRight_eq_div_pow]
  have := lt_div_add_one a (Nat.two_pow_pos w)
  simpa using this

theorem le_shrUp (a w : ℕ) : (a : ℝ) / 2 ^ w ≤ ((shrUp a w : ℕ) : ℝ) := by
  unfold shrUp
  push_cast
  exact (lt_shr_add_one a w).le

/-! ## Taylor sums -/

theorem term_succ (Y : ℝ) (m : ℕ) :
    Y ^ m / m.factorial * Y / (m + 1 : ℝ) = Y ^ (m + 1) / (m + 1).factorial := by
  rw [Nat.factorial_succ]
  push_cast
  field_simp
  ring

theorem init_term (w y : ℕ) :
    2 ^ w * (((y : ℝ) / 2 ^ w) ^ 1 / (Nat.factorial 1 : ℕ)) = (y : ℝ) := by
  rw [pow_one, Nat.factorial_one, Nat.cast_one, div_one, mul_div_cancel₀ _ (by positivity)]

theorem init_sum (w y : ℕ) :
    2 ^ w * ∑ j ∈ range 1, ((y : ℝ) / 2 ^ w) ^ j / j.factorial = ((2 ^ w : ℕ) : ℝ) := by
  simp

/-- Lower bound: the Taylor sum with rounded-down terms is at most `2^w exp Y`. -/
theorem taylor_fst_le (w y : ℕ) : ∀ (fuel m t s e : ℕ),
    (t : ℝ) ≤ 2 ^ w * (((y : ℝ) / 2 ^ w) ^ m / m.factorial) →
    (s : ℝ) ≤ 2 ^ w * ∑ j ∈ range m, ((y : ℝ) / 2 ^ w) ^ j / j.factorial →
    ((taylor w y fuel m t s e).1 : ℝ) ≤ 2 ^ w * Real.exp ((y : ℝ) / 2 ^ w)
  | 0, m, t, s, e, _, hs => by
    simp only [taylor]
    exact hs.trans (by gcongr; exact Real.sum_le_exp_of_nonneg (by positivity) m)
  | fuel + 1, m, t, s, e, ht, hs => by
    simp only [taylor]
    split_ifs with h0
    · exact hs.trans (by gcongr; exact Real.sum_le_exp_of_nonneg (by positivity) m)
    · refine taylor_fst_le w y fuel (m + 1) _ (s + t) (e + 3) ?_ ?_
      · have hY : (0 : ℝ) ≤ (y : ℝ) / 2 ^ w := by positivity
        calc ((((t * y) >>> w) / (m + 1) : ℕ) : ℝ)
            ≤ (((t * y) >>> w : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := Nat.cast_div_le
          _ ≤ ((t * y : ℕ) : ℝ) / 2 ^ w / ((m + 1 : ℕ) : ℝ) := by
              gcongr; exact shr_le _ _
          _ = (t : ℝ) * ((y : ℝ) / 2 ^ w) / (m + 1 : ℝ) := by push_cast; ring
          _ ≤ 2 ^ w * (((y : ℝ) / 2 ^ w) ^ m / m.factorial) * ((y : ℝ) / 2 ^ w) / (m + 1 : ℝ) := by
              gcongr
          _ = 2 ^ w * (((y : ℝ) / 2 ^ w) ^ (m + 1) / (m + 1).factorial) := by
              rw [← term_succ]; ring
      · push_cast
        rw [sum_range_succ, mul_add]
        exact add_le_add hs ht

/-- One step of the error bound for a rounded-down term: if `T ≤ t + 3`, the next exact term
`T Y / c` is at most the next rounded term `B` plus `3`. -/
theorem step_bound {T t A B Y c : ℝ} (hc : 2 ≤ c) (hY0 : 0 ≤ Y) (hY1 : Y ≤ 1)
    (hT : T ≤ t + 3) (h1 : A / c < B + 1) (h2 : t * Y < A + 1) : T * Y / c ≤ B + 3 := by
  have hc0 : 0 < c := by linarith
  rw [div_lt_iff₀ hc0] at h1
  rw [div_le_iff₀ hc0]
  have h3 : T * Y ≤ (t + 3) * Y := mul_le_mul_of_nonneg_right hT hY0
  nlinarith

/-- Upper bound: `2^w exp Y ≤ s + e` for the result `(s, e)` of the Taylor sum, when `Y ≤ 1`
(`Real.exp_bound` for the tail). -/
theorem le_taylor_add (w y : ℕ) (hY1 : (y : ℝ) / 2 ^ w ≤ 1) : ∀ (fuel m t s e : ℕ), 1 ≤ m →
    2 ^ w * (((y : ℝ) / 2 ^ w) ^ m / m.factorial) ≤ (t : ℝ) + 3 →
    2 ^ w * ∑ j ∈ range m, ((y : ℝ) / 2 ^ w) ^ j / j.factorial ≤ (s : ℝ) + e →
    2 ^ w * Real.exp ((y : ℝ) / 2 ^ w) ≤
      ((taylor w y fuel m t s e).1 : ℝ) + ((taylor w y fuel m t s e).2 : ℝ) := by
  have hY : (0 : ℝ) ≤ (y : ℝ) / 2 ^ w := by positivity
  -- the tail bound
  have tail : ∀ (m t s e : ℕ), 1 ≤ m →
      2 ^ w * (((y : ℝ) / 2 ^ w) ^ m / m.factorial) ≤ (t : ℝ) + 3 →
      2 ^ w * ∑ j ∈ range m, ((y : ℝ) / 2 ^ w) ^ j / j.factorial ≤ (s : ℝ) + e →
      2 ^ w * Real.exp ((y : ℝ) / 2 ^ w) ≤ (s : ℝ) + ((e + 2 * t + 6 : ℕ) : ℝ) := by
    intro m t s e hm ht hs
    set Y := (y : ℝ) / 2 ^ w with hYdef
    have hb := Real.exp_bound (x := Y) (by rw [abs_of_nonneg hY]; exact hY1) (n := m) hm
    rw [abs_of_nonneg hY] at hb
    have h1 := (abs_sub_le_iff.1 hb).1
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    have h2 : Y ^ m * ((m.succ : ℝ) / (m.factorial * m)) ≤ 2 * (Y ^ m / m.factorial) := by
      have hYm : 0 ≤ Y ^ m := pow_nonneg hY m
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      have : (m.succ : ℝ) ≤ 2 * m := by push_cast; linarith
      calc Y ^ m * (m.succ : ℝ) ≤ Y ^ m * (2 * m) := by gcongr
        _ = 2 * (Y ^ m / m.factorial) * (m.factorial * m) := by field_simp
    have h3 : Real.exp Y ≤ ∑ j ∈ range m, Y ^ j / j.factorial + 2 * (Y ^ m / m.factorial) := by
      linarith
    push_cast
    calc 2 ^ w * Real.exp Y
        ≤ 2 ^ w * (∑ j ∈ range m, Y ^ j / j.factorial + 2 * (Y ^ m / m.factorial)) := by gcongr
      _ = 2 ^ w * ∑ j ∈ range m, Y ^ j / j.factorial + 2 * (2 ^ w * (Y ^ m / m.factorial)) := by
          ring
      _ ≤ s + (e + 2 * t + 6) := by linarith
  intro fuel
  induction fuel with
  | zero =>
    intro m t s e hm ht hs
    simp only [taylor]
    exact tail m t s e hm ht hs
  | succ fuel ih =>
    intro m t s e hm ht hs
    simp only [taylor]
    split_ifs with h0
    · have := tail m t s e hm ht hs
      rw [h0] at this
      simpa using this
    · refine ih (m + 1) _ (s + t) (e + 3) (by omega) ?_ ?_
      · set Y := (y : ℝ) / 2 ^ w with hYdef
        have hc : (2 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + 1 by omega)
        have h1 := lt_div_add_one ((t * y) >>> w) (show 0 < m + 1 by omega)
        have h2 : (t : ℝ) * Y < (((t * y) >>> w : ℕ) : ℝ) + 1 := by
          calc (t : ℝ) * Y = ((t * y : ℕ) : ℝ) / 2 ^ w := by push_cast; ring
            _ < _ := lt_shr_add_one _ _
        have hT : 2 ^ w * (Y ^ (m + 1) / (m + 1).factorial) =
            2 ^ w * (Y ^ m / m.factorial) * Y / ((m + 1 : ℕ) : ℝ) := by
          rw [← term_succ]; push_cast; ring
        rw [hT]
        exact step_bound hc hY hY1 ht h1 h2
      · push_cast
        rw [sum_range_succ, mul_add]
        linarith

/-! ## Squarings -/

theorem sqrLo_le (w : ℕ) : ∀ (k a : ℕ) (z : ℝ), (a : ℝ) ≤ 2 ^ w * Real.exp z →
    (sqrLo w k a : ℝ) ≤ 2 ^ w * Real.exp (2 ^ k * z)
  | 0, a, z, h => by simpa [sqrLo] using h
  | k + 1, a, z, h => by
    simp only [sqrLo]
    have h' : (((a * a) >>> w : ℕ) : ℝ) ≤ 2 ^ w * Real.exp (2 * z) := by
      have h2w : (0 : ℝ) < 2 ^ w := by positivity
      calc (((a * a) >>> w : ℕ) : ℝ) ≤ ((a * a : ℕ) : ℝ) / 2 ^ w := shr_le _ _
        _ = (a : ℝ) * a / 2 ^ w := by push_cast; ring
        _ ≤ (2 ^ w * Real.exp z) * (2 ^ w * Real.exp z) / 2 ^ w := by gcongr
        _ = 2 ^ w * Real.exp (2 * z) := by
            rw [two_mul, Real.exp_add]; field_simp
    have := sqrLo_le w k _ (2 * z) h'
    rw [pow_succ, mul_assoc]
    exact this

theorem le_sqrHi (w : ℕ) : ∀ (k a : ℕ) (z : ℝ), 2 ^ w * Real.exp z ≤ (a : ℝ) →
    2 ^ w * Real.exp (2 ^ k * z) ≤ (sqrHi w k a : ℝ)
  | 0, a, z, h => by simpa [sqrHi] using h
  | k + 1, a, z, h => by
    simp only [sqrHi]
    have h' : 2 ^ w * Real.exp (2 * z) ≤ ((shrUp (a * a) w : ℕ) : ℝ) := by
      have h2w : (0 : ℝ) < 2 ^ w := by positivity
      have h0 : (0 : ℝ) ≤ 2 ^ w * Real.exp z := by positivity
      calc 2 ^ w * Real.exp (2 * z) = (2 ^ w * Real.exp z) * (2 ^ w * Real.exp z) / 2 ^ w := by
            rw [two_mul, Real.exp_add]; field_simp
        _ ≤ (a : ℝ) * a / 2 ^ w := by gcongr
        _ = ((a * a : ℕ) : ℝ) / 2 ^ w := by push_cast; ring
        _ ≤ ((shrUp (a * a) w : ℕ) : ℝ) := le_shrUp _ _
    have := le_sqrHi w k _ (2 * z) h'
    rw [pow_succ, mul_assoc]
    exact this

/-! ## Exponential of `n / d ≥ 0` -/

theorem expShift_spec (n : ℕ) {d : ℕ} (hd : 0 < d) : n ≤ d * 2 ^ expShift n d := by
  unfold expShift
  split_ifs with hn
  · subst hn; exact Nat.zero_le _
  · have h1 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ d.log2 ≤ d := Nat.log2_self_le (by omega)
    have h3 : n.log2 + 1 ≤ d.log2 + ((n.log2 + 1 + expRed) - d.log2) := by omega
    calc n ≤ 2 ^ (n.log2 + 1) := h1.le
      _ ≤ 2 ^ (d.log2 + ((n.log2 + 1 + expRed) - d.log2)) := Nat.pow_le_pow_right (by norm_num) h3
      _ = 2 ^ d.log2 * 2 ^ ((n.log2 + 1 + expRed) - d.log2) := by rw [Nat.pow_add]
      _ ≤ d * 2 ^ ((n.log2 + 1 + expRed) - d.log2) := Nat.mul_le_mul_right _ h2

/-- The reduced argument `y = ⌊2^w n/(d 2^k)⌋` satisfies `y / 2^w ≤ n/d/2^k < (y + 1) / 2^w`. -/
theorem reduce_bounds (w k n : ℕ) {d : ℕ} (hd : 0 < d) :
    (((n <<< w) / (d <<< k) : ℕ) : ℝ) / 2 ^ w ≤ (n : ℝ) / d / 2 ^ k ∧
      (n : ℝ) / d / 2 ^ k ≤ (((n <<< w) / (d <<< k) : ℕ) : ℝ) / 2 ^ w + 1 / 2 ^ w := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hD : 0 < d <<< k := by rw [Nat.shiftLeft_eq]; positivity
  have e1 : ((n <<< w : ℕ) : ℝ) / ((d <<< k : ℕ) : ℝ) = (n : ℝ) / d / 2 ^ k * 2 ^ w := by
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]; push_cast; field_simp
  constructor
  · have h1 : ((((n <<< w) / (d <<< k) : ℕ)) : ℝ) ≤ ((n <<< w : ℕ) : ℝ) / ((d <<< k : ℕ) : ℝ) :=
      Nat.cast_div_le
    rw [e1] at h1
    rw [div_le_iff₀ (by positivity)]
    exact h1
  · have h1 := lt_div_add_one (n <<< w) hD
    rw [e1] at h1
    rw [← add_div, le_div_iff₀ (by positivity)]
    exact h1.le

theorem expMantLo_le (w k n : ℕ) {d : ℕ} (hd : 0 < d) :
    (expMantLo w k n d : ℝ) ≤ 2 ^ w * Real.exp ((n : ℝ) / d) := by
  unfold expMantLo
  simp only
  set y := (n <<< w) / (d <<< k) with hydef
  have hy := (reduce_bounds w k n hd).1
  have h0 := taylor_fst_le w y (w + 2) 1 y (2 ^ w) 0 (init_term w y).ge (init_sum w y).ge
  have h1 := sqrLo_le w k _ _ h0
  refine h1.trans ?_
  gcongr
  calc (2 : ℝ) ^ k * ((y : ℝ) / 2 ^ w) ≤ 2 ^ k * ((n : ℝ) / d / 2 ^ k) := by gcongr
    _ = (n : ℝ) / d := by field_simp

theorem le_expMantHi (w k n : ℕ) {d : ℕ} (hd : 0 < d) (hk : n ≤ d * 2 ^ k) :
    2 ^ w * Real.exp ((n : ℝ) / d) ≤ (expMantHi w k n d : ℝ) := by
  unfold expMantHi
  simp only
  set y := (n <<< w) / (d <<< k) with hydef
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨hyL, hyU⟩ := reduce_bounds w k n hd
  have hy1 : (y : ℝ) / 2 ^ w ≤ 1 := by
    have hk' : (n : ℝ) ≤ d * 2 ^ k := by exact_mod_cast hk
    refine hyL.trans ?_
    rw [div_div, div_le_one (by positivity)]
    exact hk'
  set r := taylor w y (w + 2) 1 y (2 ^ w) 0 with hr
  have h0 : 2 ^ w * Real.exp ((y : ℝ) / 2 ^ w) ≤ (r.1 : ℝ) + r.2 :=
    le_taylor_add w y hy1 (w + 2) 1 y (2 ^ w) 0 le_rfl (by rw [init_term]; linarith)
      (by rw [init_sum]; simp)
  -- the rounding of `y`: `exp (n/d/2^k) ≤ exp (y / 2^w) · exp (2^-w)`, `exp h ≤ 1 + 2 h`
  have hcorr : 2 ^ w * Real.exp ((n : ℝ) / d / 2 ^ k) ≤
      ((r.1 + r.2 + 2 * shrUp (r.1 + r.2) w : ℕ) : ℝ) := by
    set v := r.1 + r.2 with hv
    have hv' : 2 ^ w * Real.exp ((y : ℝ) / 2 ^ w) ≤ (v : ℝ) := by rw [hv]; push_cast; exact h0
    have hh : (0 : ℝ) ≤ 1 / 2 ^ w := by positivity
    have hh1 : (1 : ℝ) / 2 ^ w ≤ 1 := by
      rw [div_le_one (by positivity)]; exact one_le_pow₀ (by norm_num)
    have he : Real.exp (1 / 2 ^ w) ≤ 1 + 2 * (1 / 2 ^ w) := by
      have := Real.abs_exp_sub_one_le (x := 1 / 2 ^ w) (by rw [abs_of_nonneg hh]; exact hh1)
      rw [abs_of_nonneg hh] at this
      linarith [(abs_le.mp this).2]
    have hs := le_shrUp v w
    calc 2 ^ w * Real.exp ((n : ℝ) / d / 2 ^ k)
        ≤ 2 ^ w * Real.exp ((y : ℝ) / 2 ^ w + 1 / 2 ^ w) := by gcongr
      _ = 2 ^ w * Real.exp ((y : ℝ) / 2 ^ w) * Real.exp (1 / 2 ^ w) := by
          rw [Real.exp_add]; ring
      _ ≤ (v : ℝ) * (1 + 2 * (1 / 2 ^ w)) := by gcongr
      _ = v + 2 * ((v : ℝ) / 2 ^ w) := by ring
      _ ≤ v + 2 * ((shrUp v w : ℕ) : ℝ) := by gcongr
      _ = ((v + 2 * shrUp v w : ℕ) : ℝ) := by push_cast; ring
  have h1 := le_sqrHi w k _ _ hcorr
  have e2 : (2 : ℝ) ^ k * ((n : ℝ) / d / 2 ^ k) = (n : ℝ) / d := by field_simp
  rw [e2] at h1
  exact h1

theorem expMantBoth_eq (w k n d : ℕ) :
    expMantBoth w k n d = (expMantLo w k n d, expMantHi w k n d) := rfl

/-! ## Exponential of a rational -/

theorem cast_eq_of_nonneg {q : ℚ} (hq : 0 ≤ q) :
    (q : ℝ) = ((q.num.toNat : ℕ) : ℝ) / (q.den : ℝ) := by
  have h1 : (0 : ℤ) ≤ q.num := Rat.num_nonneg.mpr hq
  have h2 : ((q.num.toNat : ℕ) : ℝ) = (q.num : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg h1
  rw [h2, Rat.cast_def]

theorem cast_eq_of_neg {q : ℚ} (hq : q < 0) :
    (q : ℝ) = -(((q.num.natAbs : ℕ) : ℝ) / (q.den : ℝ)) := by
  have h1 : q.num ≤ 0 := (Rat.num_neg.mpr hq).le
  have h2 : ((q.num.natAbs : ℕ) : ℝ) = -(q.num : ℝ) := by
    rw [← Int.cast_natCast, Int.ofNat_natAbs_of_nonpos h1, Int.cast_neg]
  rw [h2, Rat.cast_def, neg_div, neg_neg]

theorem expLo_le (p : ℕ) (q : ℚ) : (expLo p q : ℝ) ≤ Real.exp q := by
  unfold expLo
  split_ifs with h0 h1
  · -- `q ≥ 0`
    simp only
    set n := q.num.toNat
    set k := expShift n q.den
    set L := expMantLo (p + k + expGuard) k n q.den
    have hL := expMantLo_le (p + k + expGuard) k n q.den_pos
    rw [cast_mkRat_two_pow, cast_eq_of_nonneg h0]
    have hs := shr_le L (k + expGuard)
    have h2 : (0 : ℝ) < 2 ^ p := by positivity
    rw [div_le_iff₀ h2]
    push_cast
    calc ((L >>> (k + expGuard) : ℕ) : ℝ) ≤ (L : ℝ) / 2 ^ (k + expGuard) := hs
      _ ≤ 2 ^ (p + k + expGuard) * Real.exp ((n : ℝ) / q.den) / 2 ^ (k + expGuard) := by gcongr
      _ = Real.exp ((n : ℝ) / q.den) * 2 ^ p := by
          rw [show p + k + expGuard = p + (k + expGuard) by ring, pow_add]; field_simp
  · -- `q ≤ -p`
    simp only [Rat.cast_zero]; exact (Real.exp_pos _).le
  · -- `-p < q < 0`
    simp only
    have hq : q < 0 := lt_of_not_ge h0
    set n := q.num.natAbs
    set k := expShift n q.den
    set w := p + k + expGuard
    set U := expMantHi w k n q.den
    have hU := le_expMantHi w k n q.den_pos (expShift_spec n q.den_pos)
    have hE : (0 : ℝ) < 2 ^ w * Real.exp ((n : ℝ) / q.den) := by positivity
    have hU0 : (0 : ℝ) < U := hE.trans_le hU
    rw [cast_mkRat_two_pow, cast_eq_of_neg hq, Real.exp_neg]
    have h2 : (0 : ℝ) < 2 ^ p := by positivity
    rw [div_le_iff₀ h2]
    push_cast
    calc (((2 ^ (w + p) / U : ℕ) : ℝ)) ≤ ((2 ^ (w + p) : ℕ) : ℝ) / (U : ℝ) := Nat.cast_div_le
      _ = 2 ^ w * 2 ^ p / (U : ℝ) := by rw [Nat.cast_pow, Nat.cast_ofNat, pow_add (2 : ℝ) w p]
      _ ≤ 2 ^ w * 2 ^ p / (2 ^ w * Real.exp ((n : ℝ) / q.den)) := by gcongr
      _ = (Real.exp ((n : ℝ) / q.den))⁻¹ * 2 ^ p := by field_simp

theorem le_expHi (p : ℕ) (q : ℚ) : Real.exp q ≤ (expHi p q : ℝ) := by
  unfold expHi
  split_ifs with h0 h1
  · -- `q ≥ 0`
    simp only
    set n := q.num.toNat
    set k := expShift n q.den
    set U := expMantHi (p + k + expGuard) k n q.den
    have hU := le_expMantHi (p + k + expGuard) k n q.den_pos (expShift_spec n q.den_pos)
    rw [cast_mkRat_two_pow, cast_eq_of_nonneg h0]
    have hs := le_shrUp U (k + expGuard)
    have h2 : (0 : ℝ) < 2 ^ p := by positivity
    rw [le_div_iff₀ h2]
    push_cast
    calc Real.exp ((n : ℝ) / q.den) * 2 ^ p
        = 2 ^ (p + k + expGuard) * Real.exp ((n : ℝ) / q.den) / 2 ^ (k + expGuard) := by
          rw [show p + k + expGuard = p + (k + expGuard) by ring, pow_add]; field_simp
      _ ≤ (U : ℝ) / 2 ^ (k + expGuard) := by gcongr
      _ ≤ ((shrUp U (k + expGuard) : ℕ) : ℝ) := hs
  · -- `q ≤ -p`: `exp q ≤ exp (-p) ≤ 2^-p`
    have hq : (q : ℝ) ≤ -(p : ℝ) := by exact_mod_cast h1
    rw [cast_mkRat_two_pow]
    push_cast
    have he : (2 : ℝ) ^ p ≤ Real.exp p := by
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by
        have := Real.add_one_le_exp (1 : ℝ); norm_num at this; linarith
      calc (2 : ℝ) ^ p ≤ Real.exp 1 ^ p := pow_le_pow_left₀ (by norm_num) h2 p
        _ = Real.exp p := by rw [← Real.exp_nat_mul]; ring_nf
    calc Real.exp q ≤ Real.exp (-(p : ℝ)) := Real.exp_le_exp.mpr hq
      _ = (Real.exp p)⁻¹ := Real.exp_neg _
      _ ≤ ((2 : ℝ) ^ p)⁻¹ := inv_anti₀ (by positivity) he
      _ = 1 / 2 ^ p := by rw [one_div]
  · -- `-p < q < 0`
    simp only
    have hq : q < 0 := lt_of_not_ge h0
    set n := q.num.natAbs
    set k := expShift n q.den
    set w := p + k + expGuard
    set L := max (expMantLo w k n q.den) 1
    have hL : (L : ℝ) ≤ 2 ^ w * Real.exp ((n : ℝ) / q.den) := by
      have hL0 := expMantLo_le w k n q.den_pos
      have hone : (1 : ℝ) ≤ 2 ^ w * Real.exp ((n : ℝ) / q.den) := by
        have : (1 : ℝ) ≤ Real.exp ((n : ℝ) / q.den) := Real.one_le_exp (by positivity)
        have : (1 : ℝ) ≤ 2 ^ w := one_le_pow₀ (by norm_num)
        nlinarith
      simp only [L, Nat.cast_max, Nat.cast_one]
      exact max_le hL0 hone
    have hL0 : (0 : ℝ) < L := by
      have : 1 ≤ L := le_max_right _ _
      exact_mod_cast this
    rw [cast_mkRat_two_pow, cast_eq_of_neg hq, Real.exp_neg]
    have h2 : (0 : ℝ) < 2 ^ p := by positivity
    rw [le_div_iff₀ h2]
    push_cast
    have hLpos : 0 < L := by exact_mod_cast hL0
    calc (Real.exp ((n : ℝ) / q.den))⁻¹ * 2 ^ p
        = 2 ^ w * 2 ^ p / (2 ^ w * Real.exp ((n : ℝ) / q.den)) := by field_simp
      _ ≤ 2 ^ w * 2 ^ p / (L : ℝ) := by gcongr
      _ = ((2 ^ (w + p) : ℕ) : ℝ) / (L : ℝ) := by
          rw [Nat.cast_pow, Nat.cast_ofNat, pow_add (2 : ℝ) w p]
      _ ≤ ((2 ^ (w + p) / L : ℕ) : ℝ) + 1 := (lt_div_add_one _ hLpos).le

theorem expBoth_eq (p : ℕ) (q : ℚ) : expBoth p q = (expLo p q, expHi p q) := by
  unfold expBoth expLo expHi
  split_ifs <;> rfl

namespace Ival

theorem mem_exp {x : ℝ} {I : Ival} (p : ℕ) (hx : x ∈ₗ I) : Real.exp x ∈ₗ I.exp p := by
  have key : Real.exp x ∈ₗ (⟨expLo p I.lo, expHi p I.hi⟩ : Ival) :=
    ⟨(expLo_le p I.lo).trans (Real.exp_le_exp.mpr hx.1),
      (Real.exp_le_exp.mpr hx.2).trans (le_expHi p I.hi)⟩
  unfold exp
  split_ifs with h
  · simp only [expBoth_eq]
    rw [← h] at key
    exact key
  · exact key

end Ival

end IntervalCore
