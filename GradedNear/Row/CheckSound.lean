module

public import RowCheckCore
public import GradedNear.Row
public import GradedNear.LeafNumSound

/-!
# Soundness of the near-row checker `RowCheckCore`

* `phiI_sound`, `fI_sound`: the enclosures of `Φ(u)` and of the transform `F_c(x) = c Φ(cx)`
  (`Parabolic.laplace_fpar_real`) contain the true values;
* `good_sound`: `RowP.good` gives `Params.Good`;
* `shortSum_sound`, `longSum_sound`, `ibUpper_sound`: the checker's Riemann sum bounds the builders'
  `Params.riemann`, hence `I_B` (`Params.IB_le`), and every cell bound `L_k` is positive;
* `mem_hornerL`, `dI_sound`: the enclosure of `D(δ)` (`Params.Dδ_eq`) contains `D(δ)`.

The enclosures at complex points are proved sound in `GradedNear/Row/SpecialSound.lean`, the
special entries' values in `GradedNear/Row/SpecSound.lean`, and the row check in
`GradedNear/Row/RowSound.lean`.
-/

@[expose] public section

noncomputable section

open IntervalCore LeafNumCore MeasureTheory Set

namespace GradedNear.Row

open Parabolic

/-- The row parameters of the checker as `Params`. -/
def ofCore (p : RowCheckCore.RowP) : Params := ⟨p.γ, p.g1, p.t0, p.s, p.s1, p.h⟩

@[simp] lemma ofCore_m (p : RowCheckCore.RowP) : (ofCore p).m = p.m := rfl
@[simp] lemma ofCore_tk (p : RowCheckCore.RowP) (k : ℕ) : (ofCore p).tk k = p.tk k := rfl
@[simp] lemma ofCore_hk (p : RowCheckCore.RowP) (k : ℕ) : (ofCore p).hk k = p.hk k := rfl
@[simp] lemma ofCore_γ (p : RowCheckCore.RowP) : (ofCore p).γ = p.γ := rfl
@[simp] lemma ofCore_g1 (p : RowCheckCore.RowP) : (ofCore p).g1 = p.g1 := rfl
@[simp] lemma ofCore_t0 (p : RowCheckCore.RowP) : (ofCore p).t0 = p.t0 := rfl
@[simp] lemma ofCore_s (p : RowCheckCore.RowP) : (ofCore p).s = p.s := rfl
@[simp] lemma ofCore_s1 (p : RowCheckCore.RowP) : (ofCore p).s1 = p.s1 := rfl

/-! ## Casts -/

lemma cast_P (u : ℚ) : ((RowCheckCore.P u : ℚ) : ℝ) = P (u : ℝ) := by
  simp only [RowCheckCore.P, P]; push_cast; ring

lemma cast_fpar {c : ℚ} (t : ℚ) : ((RowCheckCore.fpar c t : ℚ) : ℝ) = fpar (c : ℝ) (t : ℝ) := by
  unfold RowCheckCore.fpar fpar
  by_cases h : t ≤ c
  · have h' : (t : ℝ) ≤ c := by exact_mod_cast h
    simp only [h, h', ite_true, cast_P]
    push_cast; rfl
  · have h' : ¬ (t : ℝ) ≤ c := by exact_mod_cast h
    simp [h, h']

lemma cast_mom (n : ℕ) : ((RowCheckCore.mom n : ℚ) : ℝ) = Parabolic.mom n := by
  simp only [RowCheckCore.mom, Parabolic.mom]; push_cast; ring

lemma cast_taylorQ (u : ℚ) : ∀ n, ((RowCheckCore.taylorQ u n : ℚ) : ℝ) =
    ∑ i ∈ Finset.range n, (-(u : ℝ)) ^ i / i.factorial * Parabolic.mom i
  | 0 => by simp [RowCheckCore.taylorQ]
  | n + 1 => by
    rw [RowCheckCore.taylorQ, Finset.sum_range_succ, Rat.cast_add, cast_taylorQ u n, Rat.cast_mul,
      cast_mom, Rat.cast_div, Rat.cast_pow, Rat.cast_neg, fact_eq, Rat.cast_natCast]

lemma cast_taylorRem (u : ℚ) (N : ℕ) : ((RowCheckCore.taylorRem u N : ℚ) : ℝ) =
    5 / 12 * (|(u : ℝ)| ^ N * ((N.succ : ℝ) / (N.factorial * N))) := by
  simp only [RowCheckCore.taylorRem]
  push_cast [cast_rabs, fact_eq]
  ring

/-! ## `Φ` and `F` -/

/-- **The enclosure of `Φ`.** -/
theorem phiI_sound (u : ℚ) (prec : ℕ) : Phi (u : ℝ) ∈ₗ RowCheckCore.phiI u prec := by
  unfold RowCheckCore.phiI
  split_ifs with h
  · have hu : (u : ℝ) ≠ 0 := by
      intro h0
      have : u = 0 := by exact_mod_cast h0
      rw [this] at h
      norm_num [rabs] at h
    rw [Phi_eq_closed hu]
    have h1 := Ival.mem_addRat (1 / u - 10 / u ^ 3 + 30 / u ^ 4 - 120 / u ^ 6) prec
      (Ival.mem_mulRat (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6) prec (mem_expI (-u) prec))
    convert h1 using 1
    unfold PhiClosed
    push_cast
    ring
  · have hu : |(u : ℝ)| ≤ 1 := by
      rw [← cast_rabs]
      exact_mod_cast (le_of_lt (not_le.1 h))
    have hT := Phi_sub_taylor hu (N := RowCheckCore.taylorN) (by norm_num [RowCheckCore.taylorN])
    rw [← cast_taylorQ] at hT
    exact mem_widen (Ival.mem_ofRat (RowCheckCore.taylorQ u RowCheckCore.taylorN)) hT
      (le_of_eq (cast_taylorRem u RowCheckCore.taylorN).symm) prec

/-- **The enclosure of the transform** `F_c(x) = c Φ(c x)` at a real point, `c > 0`. -/
theorem fI_sound {c : ℚ} (hc : 0 < c) (x : ℚ) (prec : ℕ) :
    (laplace (fpar (c : ℝ)) ((x : ℝ) : ℂ)).re ∈ₗ RowCheckCore.fI c x prec := by
  have hc' : (0 : ℝ) < c := by exact_mod_cast hc
  rw [laplace_fpar_real hc']
  have h := Ival.mem_mulRat c prec (phiI_sound (c * x) prec)
  unfold RowCheckCore.fI
  convert h using 1
  push_cast
  ring

/-! ## The parameters -/

theorem good_sound {p : RowCheckCore.RowP} (h : p.good = true) : (ofCore p).Good := by
  simp only [RowCheckCore.RowP.good, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, fun k hk => ?_⟩
  have hk' : k < p.h.length := hk
  show 0 ≤ p.h.getD k 0
  rw [List.getD_eq_getElem _ _ hk']
  exact h9 _ (List.getElem_mem hk')

/-! ## The Riemann sum -/

lemma cast_aj (p : RowCheckCore.RowP) (n j : ℕ) :
    (((p.t0 * j / n : ℚ)) : ℝ) = (ofCore p).aj n j := by
  simp only [Params.aj, ofCore_t0]; push_cast; ring

/-- The loop over the short cells. -/
theorem shortSum_sound {p : RowCheckCore.RowP} (hg : (ofCore p).Good) {n : ℕ} (hn : 0 < n)
    {R : Ival} {prec : ℕ} (hR : Real.exp (((2 * p.s - p.s1) * p.t0 / n : ℚ) : ℝ) ∈ₗ R) :
    ∀ (fuel j : ℕ) (E : Ival) (acc res : ℚ),
      Real.exp ((((2 * p.s - p.s1) * (p.t0 * (j + 1) / n) : ℚ)) : ℝ) ∈ₗ E →
      RowCheckCore.shortSum p n R prec fuel j E acc = some res →
      (acc : ℝ) + ∑ i ∈ Finset.range fuel, ((p.t0 : ℝ) / n) * (ofCore p).cS n (j + i) ≤ res
  | 0, j, E, acc, res, _, h => by
    simp only [RowCheckCore.shortSum, Option.some.injEq] at h
    simp [h]
  | fuel + 1, j, E, acc, res, hE, h => by
    simp only [RowCheckCore.shortSum] at h
    split_ifs at h with hgb
    have hE' : Real.exp ((((2 * p.s - p.s1) * (p.t0 * (((j + 1 : ℕ) : ℚ) + 1) / n) : ℚ)) : ℝ) ∈ₗ
        E.mul R prec := by
      have := Ival.mem_mul prec hE hR
      rw [← Real.exp_add] at this
      convert this using 2
      push_cast; ring
    have ih := shortSum_sound hg hn hR fuel (j + 1) (E.mul R prec) _ res hE' h
    rw [Finset.sum_range_succ']
    have hgb' : (0 : ℝ) < fpar (2 * (p.g1 : ℝ)) ((ofCore p).aj n (j + 1)) := by
      have h1 : (0 : ℚ) < RowCheckCore.fpar (2 * p.g1) (p.t0 * (j + 1) / n) := lt_of_not_ge hgb
      have h2 : (0 : ℝ) < ((RowCheckCore.fpar (2 * p.g1) (p.t0 * (j + 1) / n) : ℚ) : ℝ) := by
        exact_mod_cast h1
      rw [cast_fpar] at h2
      convert h2 using 2
      · push_cast; ring
      · rw [← cast_aj p n (j + 1)]; push_cast; ring
    have hf : ((RowCheckCore.fpar (2 * p.γ) (p.t0 * j / n) : ℚ) : ℝ) =
        fpar (2 * (p.γ : ℝ)) ((ofCore p).aj n j) := by
      rw [cast_fpar, cast_aj]; push_cast; rfl
    have hgb2 : ((RowCheckCore.fpar (2 * p.g1) (p.t0 * (j + 1) / n) : ℚ) : ℝ) =
        fpar (2 * (p.g1 : ℝ)) ((ofCore p).aj n (j + 1)) := by
      rw [cast_fpar, ← cast_aj p n (j + 1)]; push_cast; ring_nf
    have hexp : Real.exp ((2 * (p.s : ℝ) - p.s1) * (ofCore p).aj n (j + 1)) ≤ E.hi := by
      have := hE.2
      convert this using 2
      rw [← cast_aj p n (j + 1)]
      push_cast; ring
    have ht0 : (0 : ℝ) ≤ (p.t0 : ℝ) / n := by
      have := Params.t0_pos hg
      have : (0 : ℝ) < p.t0 := by exact_mod_cast this
      positivity
    have hterm : ((p.t0 : ℝ) / n) * (ofCore p).cS n j ≤
        ((roundUp prec (p.t0 / n * E.hi * (RowCheckCore.fpar (2 * p.γ) (p.t0 * j / n) *
          RowCheckCore.fpar (2 * p.γ) (p.t0 * j / n)) /
          RowCheckCore.fpar (2 * p.g1) (p.t0 * (j + 1) / n)) : ℚ) : ℝ) := by
      refine le_trans ?_ (le_roundUp_real prec _)
      unfold Params.cS
      push_cast
      rw [hf, hgb2]
      calc (p.t0 : ℝ) / n * (Real.exp ((2 * (p.s : ℝ) - p.s1) * (ofCore p).aj n (j + 1)) *
            fpar (2 * (p.γ : ℝ)) ((ofCore p).aj n j) ^ 2 /
              fpar (2 * (p.g1 : ℝ)) ((ofCore p).aj n (j + 1)))
          ≤ (p.t0 : ℝ) / n * ((E.hi : ℝ) * fpar (2 * (p.γ : ℝ)) ((ofCore p).aj n j) ^ 2 /
              fpar (2 * (p.g1 : ℝ)) ((ofCore p).aj n (j + 1))) := by
            gcongr
        _ = (p.t0 : ℝ) / n * (E.hi : ℝ) * (fpar (2 * (p.γ : ℝ)) ((ofCore p).aj n j) *
              fpar (2 * (p.γ : ℝ)) ((ofCore p).aj n j)) /
              fpar (2 * (p.g1 : ℝ)) ((ofCore p).aj n (j + 1)) := by ring
    have hacc := le_roundUp_real prec (acc + roundUp prec (p.t0 / n * E.hi *
      (RowCheckCore.fpar (2 * p.γ) (p.t0 * j / n) * RowCheckCore.fpar (2 * p.γ) (p.t0 * j / n)) /
      RowCheckCore.fpar (2 * p.g1) (p.t0 * (j + 1) / n)))
    push_cast at hacc
    have hre : ∑ i ∈ Finset.range fuel, ((p.t0 : ℝ) / n) * (ofCore p).cS n (j + (i + 1)) =
        ∑ i ∈ Finset.range fuel, ((p.t0 : ℝ) / n) * (ofCore p).cS n (j + 1 + i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show j + (i + 1) = j + 1 + i by omega]
    rw [hre]
    simp only [add_zero]
    linarith

lemma fpar_nonneg_q {c t : ℚ} (hc : 0 < c) (ht : 0 ≤ t) : 0 ≤ RowCheckCore.fpar c t := by
  have h := fpar_nonneg (c := (c : ℝ)) (by exact_mod_cast hc) (show (0 : ℝ) ≤ t by exact_mod_cast ht)
  rw [← cast_fpar] at h
  exact_mod_cast h

lemma tk_succ (p : RowCheckCore.RowP) (k : ℕ) : p.tk (k + 1) = p.tk k + p.dt := by
  simp only [RowCheckCore.RowP.tk, RowCheckCore.RowP.dt]; push_cast; ring

/-- The loop over the sieve cells. -/
theorem longSum_sound {p : RowCheckCore.RowP} (hg : (ofCore p).Good) {R1 R2 : Ival} {prec : ℕ}
    (hR1 : Real.exp (((2 * p.s * p.dt : ℚ)) : ℝ) ∈ₗ R1)
    (hR2 : Real.exp (((p.s1 * p.dt : ℚ)) : ℝ) ∈ₗ R2) :
    ∀ (fuel k : ℕ) (E1 E2 : Ival) (acc res : ℚ),
      Real.exp (((2 * p.s * p.tk (k + 1) : ℚ)) : ℝ) ∈ₗ E1 →
      Real.exp (((p.s1 * p.tk k : ℚ)) : ℝ) ∈ₗ E2 →
      RowCheckCore.longSum p R1 R2 prec fuel k E1 E2 acc = some res →
      (∀ i < fuel, 0 < (ofCore p).Lk (k + i)) ∧
        (acc : ℝ) + ∑ i ∈ Finset.range fuel,
          (((p.tk (k + i + 1) : ℚ) : ℝ) - (p.tk (k + i) : ℝ)) * (ofCore p).cL (k + i) ≤ res
  | 0, k, E1, E2, acc, res, _, _, h => by
    simp only [RowCheckCore.longSum, Option.some.injEq] at h
    simp [h]
  | fuel + 1, k, E1, E2, acc, res, hE1, hE2, h => by
    simp only [RowCheckCore.longSum] at h
    split_ifs at h with hlo
    have hE1' : Real.exp (((2 * p.s * p.tk (k + 1 + 1) : ℚ)) : ℝ) ∈ₗ E1.mul R1 prec := by
      have := Ival.mem_mul prec hE1 hR1
      rw [← Real.exp_add] at this
      convert this using 2
      rw [tk_succ p (k + 1)]; push_cast; ring
    have hE2' : Real.exp (((p.s1 * p.tk (k + 1) : ℚ)) : ℝ) ∈ₗ E2.mul R2 prec := by
      have := Ival.mem_mul prec hE2 hR2
      rw [← Real.exp_add] at this
      convert this using 2
      rw [tk_succ p k]; push_cast; ring
    obtain ⟨ihL, ih⟩ := longSum_sound hg hR1 hR2 fuel (k + 1) _ _ _ res hE1' hE2' h
    have hg1 : (0 : ℚ) < 2 * p.g1 := by have := hg.g1_pos; simp only [ofCore_g1] at this; linarith
    have hγ : (0 : ℚ) < 2 * p.γ := by have := hg.γ_pos; simp only [ofCore_γ] at this; linarith
    have htk : ∀ i, (0 : ℚ) ≤ p.tk i := fun i => by
      have h1 := Params.t0_le_tk hg i
      have h2 := Params.t0_pos hg
      simp only [ofCore_tk, ofCore_t0] at h1 h2
      linarith
    have hgq := fpar_nonneg_q hg1 (htk (k + 1))
    -- the cell bound `L_k` is at least the checked lower bound
    have hL : ((roundDown prec (RowCheckCore.fpar (2 * p.g1) (p.tk (k + 1)) * E2.lo + p.hk k) :
        ℚ) : ℝ) ≤ (ofCore p).Lk k := by
      refine (roundDown_le_real prec _).trans ?_
      unfold Params.Lk
      push_cast
      rw [cast_fpar]
      push_cast
      have h2 := hE2.1
      push_cast at h2
      have hgr : (0 : ℝ) ≤ fpar (2 * (p.g1 : ℝ)) (p.tk (k + 1)) := by
        have := cast_fpar (c := 2 * p.g1) (p.tk (k + 1))
        push_cast at this
        rw [← this]; exact_mod_cast hgq
      simp only [ofCore_tk, ofCore_hk, ofCore_s1, ofCore_g1]
      nlinarith [mul_le_mul_of_nonneg_left h2 hgr]
    have hlo' : (0 : ℝ) < ((roundDown prec (RowCheckCore.fpar (2 * p.g1) (p.tk (k + 1)) * E2.lo +
        p.hk k) : ℚ) : ℝ) := by exact_mod_cast lt_of_not_ge hlo
    have hLpos : 0 < (ofCore p).Lk k := lt_of_lt_of_le hlo' hL
    refine ⟨fun i hi => ?_, ?_⟩
    · rcases i with _ | i
      · simpa using hLpos
      · have := ihL i (by omega)
        rwa [show k + 1 + i = k + (i + 1) by omega] at this
    -- the first term
    have hdt : (0 : ℝ) ≤ ((p.tk (k + 1) : ℚ) : ℝ) - (p.tk k : ℝ) := by
      have := Params.tk_mono hg (Nat.le_succ k)
      simp only [ofCore_tk] at this
      have : ((p.tk k : ℚ) : ℝ) ≤ p.tk (k + 1) := by exact_mod_cast this
      linarith
    have hf : ((RowCheckCore.fpar (2 * p.γ) (p.tk k) : ℚ) : ℝ) =
        fpar (2 * (p.γ : ℝ)) (p.tk k) := by
      rw [cast_fpar]; push_cast; rfl
    have hterm : (((p.tk (k + 1) : ℚ) : ℝ) - (p.tk k : ℝ)) * (ofCore p).cL k ≤
        ((roundUp prec ((p.tk (k + 1) - p.tk k) * E1.hi * (RowCheckCore.fpar (2 * p.γ) (p.tk k) *
          RowCheckCore.fpar (2 * p.γ) (p.tk k)) / roundDown prec (RowCheckCore.fpar (2 * p.g1)
          (p.tk (k + 1)) * E2.lo + p.hk k)) : ℚ) : ℝ) := by
      refine le_trans ?_ (le_roundUp_real prec _)
      unfold Params.cL
      push_cast
      rw [hf]
      have hexp : Real.exp (2 * (p.s : ℝ) * p.tk (k + 1)) ≤ E1.hi := by
        have := hE1.2; push_cast at this; exact this
      simp only [ofCore_tk, ofCore_s]
      have hsq : 0 ≤ fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 := sq_nonneg _
      have hE1pos : (0 : ℝ) ≤ E1.hi := (Real.exp_pos _).le.trans hexp
      have hstep : Real.exp (2 * (p.s : ℝ) * p.tk (k + 1)) * fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 /
          (ofCore p).Lk k ≤ (E1.hi : ℝ) * fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 /
            ((roundDown prec (RowCheckCore.fpar (2 * p.g1) (p.tk (k + 1)) * E2.lo + p.hk k) :
              ℚ) : ℝ) :=
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hexp hsq) hLpos.le).trans
          (div_le_div_of_nonneg_left (mul_nonneg hE1pos hsq) hlo' hL)
      calc (((p.tk (k + 1) : ℚ) : ℝ) - (p.tk k : ℝ)) * (Real.exp (2 * (p.s : ℝ) * p.tk (k + 1)) *
            fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 / (ofCore p).Lk k)
          ≤ (((p.tk (k + 1) : ℚ) : ℝ) - (p.tk k : ℝ)) * ((E1.hi : ℝ) *
            fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 / ((roundDown prec (RowCheckCore.fpar (2 * p.g1)
              (p.tk (k + 1)) * E2.lo + p.hk k) : ℚ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hstep hdt
        _ = _ := by ring
    have hacc := le_roundUp_real prec (acc + roundUp prec ((p.tk (k + 1) - p.tk k) * E1.hi *
      (RowCheckCore.fpar (2 * p.γ) (p.tk k) * RowCheckCore.fpar (2 * p.γ) (p.tk k)) /
      roundDown prec (RowCheckCore.fpar (2 * p.g1) (p.tk (k + 1)) * E2.lo + p.hk k)))
    push_cast at hacc
    rw [Finset.sum_range_succ']
    have hre : ∑ i ∈ Finset.range fuel, (((p.tk (k + (i + 1) + 1) : ℚ) : ℝ) -
        (p.tk (k + (i + 1)) : ℝ)) * (ofCore p).cL (k + (i + 1)) =
        ∑ i ∈ Finset.range fuel, (((p.tk (k + 1 + i + 1) : ℚ) : ℝ) - (p.tk (k + 1 + i) : ℝ)) *
          (ofCore p).cL (k + 1 + i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show k + (i + 1) = k + 1 + i by omega]
    rw [hre]
    simp only [add_zero]
    linarith

/-- **The checker's Riemann sum**: every cell bound `L_k` is positive, and `ibUpper` bounds the
builders' Riemann sum (hence `I_B`, by `Params.IB_le`). -/
theorem ibUpper_sound {p : RowCheckCore.RowP} (hg : (ofCore p).Good) {prec : ℕ} {IL : ℚ}
    (h : RowCheckCore.ibUpper p prec = some IL) :
    (∀ k < p.m, 0 < (ofCore p).Lk k) ∧ (ofCore p).riemann RowCheckCore.nShort ≤ IL := by
  unfold RowCheckCore.ibUpper at h
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨sh, hsh, lg, hlg, h⟩ := h
  have hn : 0 < RowCheckCore.nShort := by norm_num [RowCheckCore.nShort]
  have hS := shortSum_sound hg hn (mem_expI _ prec) RowCheckCore.nShort 0 _ 0 sh
    (by convert mem_expI ((2 * p.s - p.s1) * p.t0 / RowCheckCore.nShort) prec using 2
        push_cast; ring) hsh
  obtain ⟨hLpos, hLg⟩ := longSum_sound hg (mem_expI _ prec) (mem_expI _ prec) p.m 0 _ _ 0 lg
    (by simpa using mem_expI (2 * p.s * p.tk 1) prec) (mem_expI (p.s1 * p.tk 0) prec) hlg
  refine ⟨fun k hk => by simpa using hLpos k hk, ?_⟩
  unfold Params.riemann
  rw [← h]
  refine le_trans ?_ (le_roundUp_real prec _)
  push_cast
  simp only [Rat.cast_zero, zero_add] at hS hLg
  have e : ∑ k ∈ Finset.range (ofCore p).m, (((ofCore p).tk (k + 1) : ℝ) - (ofCore p).tk k) *
      (ofCore p).cL k = ∑ i ∈ Finset.range p.m, (((p.tk (0 + i + 1) : ℚ) : ℝ) -
        (p.tk (0 + i) : ℝ)) * (ofCore p).cL (0 + i) := by
    simp
  have e2 : ∑ j ∈ Finset.range RowCheckCore.nShort, ((ofCore p).t0 / RowCheckCore.nShort : ℝ) *
      (ofCore p).cS RowCheckCore.nShort j = ∑ i ∈ Finset.range RowCheckCore.nShort,
        ((p.t0 : ℝ) / RowCheckCore.nShort) * (ofCore p).cS RowCheckCore.nShort (0 + i) := by
    simp
  rw [e, e2]
  simp only [zero_add]
  linarith

/-! ## `D(δ)` -/

/-- Horner's rule over a list of fixed-point coefficients. -/
theorem mem_hornerL {x : ℝ} {X : Fx} {w : ℕ} (hx : x ∈ₗ X.toIval w) (c : ℕ → ℝ) :
    ∀ (cs : List Fx) (k : ℕ), (∀ i < cs.length, c (k + i) ∈ₗ (cs.getD i ⟨0, 0⟩).toIval w) →
      (∑ i ∈ Finset.range cs.length, c (k + i) * x ^ i) ∈ₗ
        (RowCheckCore.hornerL X w cs).toIval w
  | [], k, _ => by simpa [RowCheckCore.hornerL] using Fx.mem_zero w
  | c0 :: cs, k, h => by
    show _ ∈ₗ ((X.mul (RowCheckCore.hornerL X w cs) w).add c0).toIval w
    have ih := mem_hornerL hx c cs (k + 1) fun i hi => by
      have := h (i + 1) (by simp; omega)
      simpa [show k + (i + 1) = k + 1 + i by omega] using this
    have h0 : c k ∈ₗ c0.toIval w := by simpa using h 0 (by simp)
    have hm := Fx.mem_add (Fx.mem_mul hx ih) h0
    convert hm using 1
    rw [List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k + (i + 1) = k + 1 + i by omega, pow_succ]
    ring

/-- `F_c(x) = c Φ(c x)` lies in `fI c x`, for any `c`. -/
theorem fI_mem (c x : ℚ) (prec : ℕ) :
    (c : ℝ) * Phi ((c : ℝ) * x) ∈ₗ RowCheckCore.fI c x prec := by
  have h := Ival.mem_mulRat c prec (phiI_sound (c * x) prec)
  unfold RowCheckCore.fI
  convert h using 1
  push_cast; ring

lemma cast_ck (p : RowCheckCore.RowP) (k : ℕ) :
    ((RowCheckCore.RowP.ck p k : ℚ) : ℝ) = (ofCore p).ck k := by
  simp only [RowCheckCore.RowP.ck, Params.ck, Params.lev, ofCore_tk, ofCore_hk,
    RowCheckCore.epsLev, epsLev]
  push_cast
  ring

/-- **The enclosure of `D(δ)`.** -/
theorem dI_sound {p : RowCheckCore.RowP} (hg : (ofCore p).Good) (Δ : Finset ℝ) (δ : ℚ)
    (prec : ℕ) :
    ((ofCore p).near Δ).Dδ δ ∈ₗ RowCheckCore.dI p (RowCheckCore.ckFx p (prec + 16)) δ prec := by
  rw [Params.Dδ_eq hg]
  unfold RowCheckCore.dI
  have hG := fI_mem (2 * p.g1) (2 * δ - p.s1) prec
  have hE0 := mem_expI (-(2 * δ * p.t0)) prec
  have hR := Fx.mem_ofIval (mem_expI (-(2 * δ * p.dt)) prec) (prec + 16)
  have hH := mem_hornerL hR (fun k => (ofCore p).ck k) (RowCheckCore.ckFx p (prec + 16)) 0
    (fun i hi => by
      simp only [RowCheckCore.ckFx, List.length_map, List.length_range] at hi
      simp only [RowCheckCore.ckFx, zero_add]
      rw [List.getD_eq_getElem _ _ (by simpa using hi)]
      simp only [List.getElem_map, List.getElem_range]
      rw [← cast_ck]
      exact Fx.mem_ofRat _ _)
  have hm := Ival.mem_add prec hG (Ival.mem_mul prec hE0 hH)
  convert hm using 1
  simp only [RowCheckCore.ckFx, List.length_map, List.length_range, zero_add, ofCore_g1,
    ofCore_s1]
  push_cast
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Real.exp_nat_mul, mul_left_comm, ← Real.exp_add]
  congr 2
  simp only [ofCore_tk, RowCheckCore.RowP.tk, RowCheckCore.RowP.dt]
  push_cast
  ring

/-! ## The constants -/

/-- `η = 10⁻⁶` as a real number. -/
def ηR : ℝ := ((RowCheckCore.eta : ℚ) : ℝ)

/-- `S = 10¹⁶` as a real number. -/
def SR : ℝ := ((RowCheckCore.S : ℤ) : ℝ)

lemma ηR_pos : 0 < ηR := by norm_num [ηR, RowCheckCore.eta]

lemma SR_pos : 0 < SR := by norm_num [SR, RowCheckCore.S]

end GradedNear.Row

end
