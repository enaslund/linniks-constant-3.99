module

public import GradedNear.ParabolicComplex
public import GradedNear.Moments
public import GradedNear.Row.CheckSound

/-!
# Soundness of the enclosures at complex points (`RowCheckCore`)

* `cosSinI_sound`: `cos q ∈ (cosSinI q).1` and `sin q ∈ (cosSinI q).2`, from `Complex.exp_bound` at
  `iy` and the double-angle formulas;
* `rePhiCI_sound`: `Re ΦC(ur + i ui) ∈ rePhiCI ur ui` (closed form `PhiC_eq_closed`, or the Taylor
  polynomial `PhiC_sub_taylor`);
* `reFI_sound`: `Re F_c(x + iy) ∈ reFI c x y` for `c > 0` (`laplace_fpar_eq`);
* `e2I_sound`: `E₂(α) ∈ e2I α` (`E2_eq_closed`, `E2_sub_taylor`).
-/

@[expose] public section

noncomputable section

open IntervalCore LeafNumCore Complex

namespace GradedNear.Row

open Parabolic

/-! ## Complex rationals -/

/-- A complex rational as a complex number. -/
def toC (a : RowCheckCore.CQ) : ℂ := ⟨a.re, a.im⟩

lemma toC_re (a : RowCheckCore.CQ) : (toC a).re = a.re := rfl
lemma toC_im (a : RowCheckCore.CQ) : (toC a).im = a.im := rfl

lemma toC_add (a b : RowCheckCore.CQ) : toC (RowCheckCore.CQ.add a b) = toC a + toC b := by
  apply Complex.ext <;> simp [toC, RowCheckCore.CQ.add]

lemma toC_mul (a b : RowCheckCore.CQ) : toC (RowCheckCore.CQ.mul a b) = toC a * toC b := by
  apply Complex.ext <;> simp [toC, RowCheckCore.CQ.mul]

lemma toC_smul (q : ℚ) (a : RowCheckCore.CQ) : toC (RowCheckCore.CQ.smul q a) = (q : ℂ) * toC a := by
  apply Complex.ext <;> simp [toC, RowCheckCore.CQ.smul]

lemma toC_neg (a : RowCheckCore.CQ) : toC (RowCheckCore.CQ.neg a) = -toC a := by
  apply Complex.ext <;> simp [toC, RowCheckCore.CQ.neg]

lemma toC_inv (a : RowCheckCore.CQ) : toC (RowCheckCore.CQ.inv a) = (toC a)⁻¹ := by
  apply Complex.ext <;> simp [toC, RowCheckCore.CQ.inv, Complex.inv_re, Complex.inv_im, Complex.normSq_apply]

lemma toC_pow (a : RowCheckCore.CQ) : ∀ n, toC (a.pow n) = toC a ^ n
  | 0 => by apply Complex.ext <;> simp [toC, RowCheckCore.CQ.pow]
  | n + 1 => by rw [RowCheckCore.CQ.pow, toC_mul, toC_pow a n, pow_succ]

lemma normSq_toC (a : RowCheckCore.CQ) : Complex.normSq (toC a) = (a.normSq : ℝ) := by
  simp [toC, RowCheckCore.CQ.normSq, Complex.normSq_apply]

lemma toC_mk (x y : ℚ) : toC ⟨x, y⟩ = (x : ℂ) + (y : ℂ) * I := by
  apply Complex.ext <;> simp [toC]

/-! ## `cos` and `sin` -/

lemma expITaylorAux_eq (y : ℚ) : ∀ (fuel m : ℕ) (term sum : RowCheckCore.CQ),
    toC term = (((y : ℝ) : ℂ) * I) ^ m / m.factorial →
    toC (RowCheckCore.expITaylorAux y fuel m term sum) =
      toC sum + ∑ j ∈ Finset.range fuel, (((y : ℝ) : ℂ) * I) ^ (m + j) / (m + j).factorial
  | 0, m, term, sum, _ => by simp [RowCheckCore.expITaylorAux]
  | fuel + 1, m, term, sum, ht => by
    rw [RowCheckCore.expITaylorAux, expITaylorAux_eq y fuel (m + 1) _ _ ?_, toC_add, ht,
      Finset.sum_range_succ']
    · simp only [add_zero]
      have e : ∀ j, m + 1 + j = m + (j + 1) := fun j => by omega
      simp only [e]
      ring
    · have hy : toC ⟨0, y⟩ = ((y : ℝ) : ℂ) * I := by apply Complex.ext <;> simp [toC]
      rw [toC_smul, toC_mul, ht, hy, Nat.factorial_succ, pow_succ]
      have h0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos m).ne'
      have h1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      push_cast
      field_simp

lemma expITaylor_eq (y : ℚ) (N : ℕ) :
    toC (RowCheckCore.expITaylor y N) = ∑ j ∈ Finset.range N, (((y : ℝ) : ℂ) * I) ^ j / j.factorial := by
  have h1 : toC ⟨1, 0⟩ = (((y : ℝ) : ℂ) * I) ^ 0 / (Nat.factorial 0 : ℂ) := by
    apply Complex.ext <;> simp [toC]
  have h0 : toC ⟨0, 0⟩ = 0 := by apply Complex.ext <;> simp [toC]
  rw [RowCheckCore.expITaylor, expITaylorAux_eq y N 0 _ _ h1, h0, zero_add]
  simp only [zero_add]

lemma cast_trigRem (y : ℚ) (N : ℕ) :
    ((RowCheckCore.trigRem y N : ℚ) : ℝ) = |(y : ℝ)| ^ N * ((N.succ : ℝ) * ((N.factorial : ℝ) * N)⁻¹) := by
  simp only [RowCheckCore.trigRem]
  push_cast [cast_rabs, fact_eq]
  ring

lemma cosSin0_sound {y : ℚ} (hy : |(y : ℝ)| ≤ 1) (prec : ℕ) :
    Real.cos y ∈ₗ (RowCheckCore.cosSin0 y prec).1 ∧ Real.sin y ∈ₗ (RowCheckCore.cosSin0 y prec).2 := by
  have hn : ‖((y : ℝ) : ℂ) * I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hy
  have hb := Complex.exp_bound hn (n := RowCheckCore.trigN) (by norm_num [RowCheckCore.trigN])
  rw [← expITaylor_eq] at hb
  have hr : ‖((y : ℝ) : ℂ) * I‖ ^ RowCheckCore.trigN *
      ((RowCheckCore.trigN.succ : ℝ) * ((RowCheckCore.trigN.factorial : ℝ) * RowCheckCore.trigN)⁻¹) = ((RowCheckCore.trigRem y RowCheckCore.trigN : ℚ) : ℝ) := by
    rw [cast_trigRem, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [hr] at hb
  have hre := (Complex.abs_re_le_norm _).trans hb
  have him := (Complex.abs_im_le_norm _).trans hb
  rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, toC_re] at hre
  rw [Complex.sub_im, Complex.exp_ofReal_mul_I_im, toC_im] at him
  exact ⟨mem_widen (Ival.mem_ofRat _) hre le_rfl prec, mem_widen (Ival.mem_ofRat _) him le_rfl prec⟩

lemma doubling_sound (prec : ℕ) : ∀ (k : ℕ) {θ : ℝ} {cs : Ival × Ival},
    Real.cos θ ∈ₗ cs.1 → Real.sin θ ∈ₗ cs.2 →
    Real.cos (2 ^ k * θ) ∈ₗ (RowCheckCore.doubling prec k cs).1 ∧ Real.sin (2 ^ k * θ) ∈ₗ (RowCheckCore.doubling prec k cs).2
  | 0, θ, cs, hc, hs => by simpa [RowCheckCore.doubling] using And.intro hc hs
  | k + 1, θ, cs, hc, hs => by
    have hc2 : Real.cos (2 * θ) ∈ₗ (cs.1.sqr prec).sub (cs.2.sqr prec) prec := by
      rw [Real.cos_two_mul']
      exact Ival.mem_sub prec (Ival.mem_sqr prec hc) (Ival.mem_sqr prec hs)
    have hs2 : Real.sin (2 * θ) ∈ₗ (cs.1.mul cs.2 prec).mulRat 2 prec := by
      have h := Ival.mem_mulRat 2 prec (Ival.mem_mul prec hc hs)
      have e : Real.sin (2 * θ) = Real.cos θ * Real.sin θ * ((2 : ℚ) : ℝ) := by
        rw [Real.sin_two_mul]; push_cast; ring
      rw [e]; exact h
    have h := doubling_sound prec k (θ := 2 * θ)
      (cs := ((cs.1.sqr prec).sub (cs.2.sqr prec) prec, (cs.1.mul cs.2 prec).mulRat 2 prec)) hc2 hs2
    rw [show (2 : ℝ) ^ (k + 1) * θ = 2 ^ k * (2 * θ) by ring]
    exact h

lemma halvings_spec (q : ℚ) : |(q : ℝ)| / 2 ^ RowCheckCore.halvings q ≤ 1 / 2 := by
  set n := natCeil (rabs q) with hn
  have hq : |(q : ℝ)| < n := by
    rw [← cast_rabs]; exact lt_natCeil (rabs_nonneg q)
  have hlog : n < 2 ^ (n.log2 + 1) := by
    have := Nat.lt_log2_self (n := n)
    simpa [pow_succ] using this
  have hlog' : (n : ℝ) < 2 ^ (n.log2 + 1) := by exact_mod_cast hlog
  rw [div_le_iff₀ (by positivity)]
  unfold RowCheckCore.halvings
  rw [← hn, pow_succ]
  nlinarith [abs_nonneg (q : ℝ)]

/-- **Enclosures of `cos q` and `sin q`.** -/
theorem cosSinI_sound (q : ℚ) (prec : ℕ) :
    Real.cos q ∈ₗ (RowCheckCore.cosSinI q prec).1 ∧ Real.sin q ∈ₗ (RowCheckCore.cosSinI q prec).2 := by
  set k := RowCheckCore.halvings q
  have hy : |(((q / (2 ^ k : ℕ) : ℚ)) : ℝ)| ≤ 1 := by
    have := halvings_spec q
    push_cast
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ k)]
    linarith
  obtain ⟨hc, hs⟩ := cosSin0_sound hy prec
  have h := doubling_sound prec k hc hs
  have e : (2 : ℝ) ^ k * (((q / (2 ^ k : ℕ) : ℚ)) : ℝ) = q := by
    push_cast; field_simp
  rw [e] at h
  exact h

/-! ## `Re ΦC` and `Re F` -/

lemma phiTaylorAux_eq (u : RowCheckCore.CQ) : ∀ (fuel n : ℕ) (term sum : RowCheckCore.CQ),
    toC term = (-toC u) ^ n / n.factorial →
    toC (RowCheckCore.phiTaylorAux u fuel n term sum) =
      toC sum + ∑ j ∈ Finset.range fuel, (-toC u) ^ (n + j) / (n + j).factorial * (mom (n + j) : ℂ)
  | 0, n, term, sum, _ => by simp [RowCheckCore.phiTaylorAux]
  | fuel + 1, n, term, sum, ht => by
    rw [RowCheckCore.phiTaylorAux, phiTaylorAux_eq u fuel (n + 1) _ _ ?_, toC_add, toC_smul, ht,
      Finset.sum_range_succ']
    · simp only [add_zero]
      have e : ∀ j, n + 1 + j = n + (j + 1) := fun j => by omega
      simp only [e]
      rw [← cast_mom]
      push_cast
      ring
    · rw [toC_smul, toC_mul, ht, toC_neg, Nat.factorial_succ, pow_succ]
      have h0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
      have h1 : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      push_cast
      field_simp

/-- **The enclosure of `Re ΦC`.** -/
theorem rePhiCI_sound (ur ui : ℚ) (prec : ℕ) :
    (PhiC ((ur : ℂ) + (ui : ℂ) * I)).re ∈ₗ RowCheckCore.rePhiCI ur ui prec := by
  have hu : ((ur : ℂ) + (ui : ℂ) * I) = toC ⟨ur, ui⟩ := (toC_mk ur ui).symm
  dsimp only [RowCheckCore.rePhiCI]
  split_ifs with h
  · -- the closed form
    have hn : (1 : ℝ) ≤ Complex.normSq (toC ⟨ur, ui⟩) := by
      rw [normSq_toC]; exact_mod_cast h
    have hne : toC ⟨ur, ui⟩ ≠ 0 := by
      intro h0; rw [h0, map_zero] at hn; linarith
    rw [hu, PhiC_eq_closed hne]
    obtain ⟨hc, hs⟩ := cosSinI_sound ui prec
    set w := RowCheckCore.CQ.inv ⟨ur, ui⟩ with hw
    have hwC : toC w = (toC ⟨ur, ui⟩)⁻¹ := toC_inv _
    have hB := Ival.mem_add prec (Ival.mem_mulRat (30 * (w.pow 4).re + 120 * (w.pow 5).re +
      120 * (w.pow 6).re) prec hc) (Ival.mem_mulRat (30 * (w.pow 4).im + 120 * (w.pow 5).im +
      120 * (w.pow 6).im) prec hs)
    have hm := Ival.mem_addRat (w.re - 10 * (w.pow 3).re + 30 * (w.pow 4).re - 120 * (w.pow 6).re)
      prec (Ival.mem_mul prec (mem_expI (-ur) prec) hB)
    have hclosed : PhiClosedC (toC ⟨ur, ui⟩) = toC w - 10 * toC (w.pow 3) + 30 * toC (w.pow 4) -
        120 * toC (w.pow 6) + cexp (-toC ⟨ur, ui⟩) *
          (30 * toC (w.pow 4) + 120 * toC (w.pow 5) + 120 * toC (w.pow 6)) := by
      unfold PhiClosedC
      simp only [toC_pow, hwC, inv_pow]
      ring
    have hre : (PhiClosedC (toC ⟨ur, ui⟩)).re =
        Real.exp ((-ur : ℚ) : ℝ) * (Real.cos ui * ((30 * (w.pow 4).re + 120 * (w.pow 5).re +
          120 * (w.pow 6).re : ℚ) : ℝ) + Real.sin ui * ((30 * (w.pow 4).im + 120 * (w.pow 5).im +
          120 * (w.pow 6).im : ℚ) : ℝ)) +
        ((w.re - 10 * (w.pow 3).re + 30 * (w.pow 4).re - 120 * (w.pow 6).re : ℚ) : ℝ) := by
      rw [hclosed]
      simp only [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.add_im,
        Complex.exp_re, Complex.exp_im, Complex.neg_re, Complex.neg_im, toC_re,
        toC_im, Complex.re_ofNat, Complex.im_ofNat, Real.cos_neg, Real.sin_neg]
      push_cast
      ring
    rw [hre]
    exact hm
  · -- the Taylor polynomial
    have hn : Complex.normSq (toC ⟨ur, ui⟩) ≤ 1 := by
      rw [normSq_toC]; exact_mod_cast (le_of_lt (not_le.1 h))
    have hnorm : ‖toC ⟨ur, ui⟩‖ ≤ 1 := by
      rw [← Real.sqrt_one, Complex.norm_def]; exact Real.sqrt_le_sqrt hn
    have hT := PhiC_sub_taylor hnorm (N := RowCheckCore.taylorN)
      (by norm_num [RowCheckCore.taylorN])
    rw [hu]
    have ht := phiTaylorAux_eq ⟨ur, ui⟩ RowCheckCore.taylorN 0 ⟨1, 0⟩ ⟨0, 0⟩
      (by apply Complex.ext <;> simp [toC])
    rw [show toC ⟨0, 0⟩ = 0 by apply Complex.ext <;> simp [toC], zero_add] at ht
    simp only [zero_add] at ht
    rw [← ht] at hT
    have hre := (Complex.abs_re_le_norm _).trans hT
    rw [Complex.sub_re, toC_re] at hre
    refine mem_widen (Ival.mem_ofRat _) hre (le_of_eq ?_) prec
    rw [Complex.norm_def, normSq_toC]
    simp only [RowCheckCore.taylorN, RowCheckCore.CQ.normSq]
    push_cast [fact_eq]
    have hs : Real.sqrt ((ur : ℝ) * ur + ui * ui) ^ 40 = ((ur : ℝ) * ur + ui * ui) ^ 20 := by
      rw [show (40 : ℕ) = 2 * 20 by rfl, pow_mul, Real.sq_sqrt (add_nonneg (mul_self_nonneg _) (mul_self_nonneg _))]
    rw [hs]
    ring

/-- **The enclosure of `Re F_c(x + iy)`** for the parabolic test of width `c > 0`. -/
theorem reFI_sound {c : ℚ} (hc : 0 < c) (x y : ℚ) (prec : ℕ) :
    (laplace (fpar (c : ℝ)) ((x : ℂ) + (y : ℂ) * I)).re ∈ₗ RowCheckCore.reFI c x y prec := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [laplace_fpar_eq hc']
  have h := Ival.mem_mulRat c prec (rePhiCI_sound (c * x) (c * y) prec)
  unfold RowCheckCore.reFI
  convert h using 1
  have e : ((c : ℝ) : ℂ) * ((x : ℂ) + (y : ℂ) * I) =
      (((c * x : ℚ)) : ℂ) + (((c * y : ℚ)) : ℂ) * I := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

/-! ## The exponential moment -/

lemma e2TaylorAux_eq (α : ℚ) : ∀ (fuel j : ℕ) (term sum : ℚ),
    (term : ℝ) = (α : ℝ) ^ j / j.factorial →
    ((RowCheckCore.e2TaylorAux α fuel j term sum : ℚ) : ℝ) =
      sum + ∑ i ∈ Finset.range fuel, (α : ℝ) ^ (j + i) / (j + i).factorial * mom (j + i + 2)
  | 0, j, term, sum, _ => by simp [RowCheckCore.e2TaylorAux]
  | fuel + 1, j, term, sum, ht => by
    rw [RowCheckCore.e2TaylorAux, e2TaylorAux_eq α fuel (j + 1) _ _ ?_, Finset.sum_range_succ']
    · push_cast
      rw [ht, ← cast_mom]
      have e : ∀ i, j + 1 + i = j + (i + 1) := fun i => by omega
      simp only [e, add_zero]
      ring
    · push_cast
      rw [ht, Nat.factorial_succ]
      push_cast
      have h0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
      field_simp
      ring

/-- **The enclosure of `E₂`.** -/
theorem e2I_sound (α : ℚ) (prec : ℕ) : E2 α ∈ₗ RowCheckCore.e2I α prec := by
  dsimp only [RowCheckCore.e2I]
  split_ifs with h
  · have hα : (α : ℝ) ≠ 0 := by
      intro h0
      have : α = 0 := by exact_mod_cast h0
      rw [this] at h
      norm_num [rabs] at h
    rw [E2_eq_closed hα]
    have hm := Ival.mem_addRat (-2 / α ^ 3 + 120 / α ^ 5 + 600 / α ^ 6 - 5040 / α ^ 8) prec
      (Ival.mem_mulRat (30 / α ^ 4 - 360 / α ^ 5 + 1920 / α ^ 6 - 5040 / α ^ 7 + 5040 / α ^ 8)
        prec (mem_expI α prec))
    have e : E2Closed α = Real.exp α * ((30 / α ^ 4 - 360 / α ^ 5 + 1920 / α ^ 6 - 5040 / α ^ 7 +
        5040 / α ^ 8 : ℚ) : ℝ) + ((-2 / α ^ 3 + 120 / α ^ 5 + 600 / α ^ 6 - 5040 / α ^ 8 : ℚ) : ℝ) := by
      unfold E2Closed
      push_cast
      ring
    rw [e]
    exact hm
  · have hα : |(α : ℝ)| ≤ 1 := by
      rw [← cast_rabs]; exact_mod_cast (le_of_lt (not_le.1 h))
    have hT := E2_sub_taylor hα (N := RowCheckCore.taylorN) (by norm_num [RowCheckCore.taylorN])
    have ht := e2TaylorAux_eq α RowCheckCore.taylorN 0 1 0 (by simp)
    simp only [zero_add, Rat.cast_zero] at ht
    rw [← ht] at hT
    refine mem_widen (Ival.mem_ofRat _) hT (le_of_eq ?_) prec
    push_cast [cast_rabs, fact_eq, cast_mom]
    rfl

end GradedNear.Row

end
