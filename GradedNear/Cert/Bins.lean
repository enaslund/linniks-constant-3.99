module

public import GradedNear.Defs

/-!
# Binning a near row (paper §§8.6, 10)

A near row of a leaf LP relaxes the threshold form (T) of the configuration's entries. Each
entry is assigned to a column (bin) of the leaf, to a fixed family term of the row, or to
nothing. The assignment must be conservative:

* the bin's feature is at most the entry's feature, or at most `0` (such a bin contributes
  nothing at `τ ≥ 0`);
* the bin's diagonal is at least the entry's diagonal;
* the row's radius is at least the configuration's radius;
* each family term has at least its count of entries.

Then (T) at a threshold `τ` implies row `k` of the leaf LP at `τ`, for column values shared by
all rows that do not exceed the bin counts on the columns with a positive feature in row `k`.
`near_row_of_bins` states this in the exact form of `GradedNear.Cert.Feasible`.
-/

@[expose] public section

namespace GradedNear.Cert

open Finset

/-- A threshold term `(v - τ)_+² / D` at `τ ≥ 0` increases with `v` and decreases with `D > 0`,
and it vanishes for `v ≤ 0`. -/
lemma term_le {v v' D D' τ : ℝ} (hv : v ≤ v' ∨ v ≤ 0) (hτ : 0 ≤ τ) (hD' : 0 < D')
    (hDD : D' ≤ D) : (max 0 (v - τ)) ^ 2 / D ≤ (max 0 (v' - τ)) ^ 2 / D' := by
  rcases hv with hv | hv
  · have h1 : (max 0 (v - τ)) ^ 2 ≤ (max 0 (v' - τ)) ^ 2 :=
      pow_le_pow_left₀ (le_max_left _ _) (max_le_max le_rfl (by linarith)) 2
    calc (max 0 (v - τ)) ^ 2 / D ≤ (max 0 (v' - τ)) ^ 2 / D :=
          div_le_div_of_nonneg_right h1 (hD'.le.trans hDD)
      _ ≤ (max 0 (v' - τ)) ^ 2 / D' :=
          div_le_div_of_nonneg_left (sq_nonneg _) hD' hDD
  · rw [max_eq_left (by linarith), sq, zero_mul, zero_div]
    exact div_nonneg (sq_nonneg _) hD'.le

/-- **A near row of the leaf LP from the threshold form.** Let the entries `j : ι` of row `k` satisfy
(T): `τ ∈ [0, √d]` and `Σ_j (v_j - τ)_+² / D_j ≤ 1 - τ²/d`, with `D_j > 0`. Assign each entry by
`bin` to a column of the leaf, to a family term of row `k`, or to nothing, conservatively:
* a binned entry's feature is at least its bin's feature, or the bin's feature is `≤ 0`;
* a binned entry's diagonal is at most its bin's diagonal;
* each family term `(n, v, D)` has `D > 0` and at least `n` entries;
* the row's radius is at least `d`.

Let `x ≥ 0` be column values shared by all rows (the LP point). If every column with a positive
feature in row `k` has `x_c` at most the number of entries of row `k` binned to it, then row `k`
of `Feasible` holds at `x` and `τ`. (Columns whose feature in row `k` is `≤ 0` contribute nothing,
so their `x_c` is free; with `x_c` equal to the bin counts this is the row at the counts.) -/
theorem near_row_of_bins (L : Leaf) (k : ℕ) {ι : Type*} [Fintype ι] (v Dg : ι → ℝ) (d τ : ℝ)
    (hDg : ∀ j, 0 < Dg j) (hd : 0 < d) (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d)
    (bin : ι → Option (Fin L.cols.length ⊕ Fin (L.rows.getD k ⟨1, []⟩).fam.length))
    (hcol : ∀ j c, bin j = some (Sum.inl c) →
      (((L.cols.get c).v.getD k 0 : ℝ) / S ≤ v j ∨ (L.cols.get c).v.getD k 0 ≤ 0) ∧
        Dg j ≤ ((L.cols.get c).D.getD k 1 : ℝ) / S)
    (hfam : ∀ j i, bin j = some (Sum.inr i) →
      (((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℤ) : ℝ) / S ≤ v j ∨
          ((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 ≤ 0) ∧
        Dg j ≤ ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℤ) : ℝ) / S)
    (hfamD : ∀ i, 0 < ((L.rows.getD k ⟨1, []⟩).fam.get i).2.2)
    (hn : ∀ i, ((((L.rows.getD k ⟨1, []⟩).fam.get i).1 : ℤ) : ℝ) ≤
      ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ))
    (hdrow : d ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)
    (x : Fin L.cols.length → ℝ) (hx0 : ∀ c, 0 ≤ x c)
    (hx : ∀ c, 0 < (L.cols.get c).v.getD k 0 →
      x c ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) :
    0 ≤ τ ∧ τ ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
      rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  have hS : (0 : ℝ) < (S : ℝ) := by norm_num [S]
  have hτ2 : τ ^ 2 ≤ d := by
    have := pow_le_pow_left₀ hτ0 hτd 2
    rwa [Real.sq_sqrt hd.le] at this
  refine ⟨hτ0, hτ2.trans hdrow, ?_⟩
  -- the entry terms
  set t : ι → ℝ := fun j => (max 0 (v j - τ)) ^ 2 / Dg j with ht
  have ht0 : ∀ j, 0 ≤ t j := fun j => div_nonneg (sq_nonneg _) (hDg j).le
  -- (T) with the row's radius
  have hTrow : ∑ j, t j ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
    refine hT.trans ?_
    have : τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) ≤ τ ^ 2 / d :=
      div_le_div_of_nonneg_left (sq_nonneg _) hd hdrow
    linarith
  -- split the entries by bin
  have hsplit : ∑ j, t j =
      ∑ j ∈ univ.filter (fun j => bin j = none), t j +
        (∑ c, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j +
          ∑ i, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inr i)), t j) := by
    rw [← Finset.sum_fiberwise univ bin t, Fintype.sum_option, Fintype.sum_sum_type]
  have hnone : 0 ≤ ∑ j ∈ univ.filter (fun j => bin j = none), t j :=
    Finset.sum_nonneg fun j _ => ht0 j
  -- the columns
  have hcols : ∑ c, x c * (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
          (((L.cols.get c).D.getD k 1 : ℝ) / S) ≤
      ∑ c, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j := by
    refine Finset.sum_le_sum fun c _ => ?_
    have hcount : ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ) *
          (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
            (((L.cols.get c).D.getD k 1 : ℝ) / S) ≤
        ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j := by
      rw [mul_div_assoc, ← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun j hj => ?_
      rw [Finset.mem_filter] at hj
      obtain ⟨hv, hD⟩ := hcol j c hj.2
      exact term_le (hv.imp_right fun h => div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast h)
        hS.le) hτ0 (hDg j) hD
    have hsum0 : 0 ≤ ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inl c)), t j :=
      Finset.sum_nonneg fun j _ => ht0 j
    by_cases hv : (L.cols.get c).v.getD k 0 ≤ 0
    · have h0 : max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ) = 0 := by
        apply max_eq_left
        have : ((L.cols.get c).v.getD k 0 : ℝ) / S ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by exact_mod_cast hv) hS.le
        linarith
      rw [h0, sq, zero_mul, mul_zero, zero_div]
      exact hsum0
    · have hxc := hx c (lt_of_not_ge hv)
      rcases Nat.eq_zero_or_pos (univ.filter fun j => bin j = some (Sum.inl c)).card with h0 | hpos
      · have hxz : x c = 0 := le_antisymm (by rw [h0] at hxc; exact_mod_cast hxc) (hx0 c)
        rw [hxz, zero_mul, zero_div]
        exact hsum0
      · obtain ⟨j, hj⟩ := Finset.card_pos.1 hpos
        rw [Finset.mem_filter] at hj
        have hDc : Dg j ≤ ((L.cols.get c).D.getD k 1 : ℝ) / S := (hcol j c hj.2).2
        have htc : 0 ≤ (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
            (((L.cols.get c).D.getD k 1 : ℝ) / S) :=
          div_nonneg (sq_nonneg _) ((hDg j).le.trans hDc)
        calc x c * (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
              (((L.cols.get c).D.getD k 1 : ℝ) / S)
            = x c * ((max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
              (((L.cols.get c).D.getD k 1 : ℝ) / S)) := mul_div_assoc _ _ _
          _ ≤ ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ) *
              ((max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
              (((L.cols.get c).D.getD k 1 : ℝ) / S)) := mul_le_mul_of_nonneg_right hxc htc
          _ = ((univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ) *
              (max 0 (((L.cols.get c).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
              (((L.cols.get c).D.getD k 1 : ℝ) / S) := (mul_div_assoc _ _ _).symm
          _ ≤ _ := hcount
  -- the family terms
  have hfams : (((L.rows.getD k ⟨1, []⟩).fam).map fun u =>
        (u.1 : ℝ) * (max 0 ((u.2.1 : ℝ) / S - τ)) ^ 2 / ((u.2.2 : ℝ) / S)).sum ≤
      ∑ i, ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inr i)), t j := by
    rw [← Fin.sum_univ_fun_getElem]
    refine Finset.sum_le_sum fun i _ => ?_
    have hDi : (0 : ℝ) < (((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℝ) / S :=
      div_pos (by exact_mod_cast hfamD i) hS
    have hti : 0 ≤ (max 0 ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℝ) / S - τ)) ^ 2 / ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℝ) / S) :=
      div_nonneg (sq_nonneg _) hDi.le
    have hget : (L.rows.getD k ⟨1, []⟩).fam[i.1] = (L.rows.getD k ⟨1, []⟩).fam.get i := rfl
    rw [hget, mul_div_assoc]
    calc (((L.rows.getD k ⟨1, []⟩).fam.get i).1 : ℝ) *
          ((max 0 ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℝ) / S - τ)) ^ 2 / ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℝ) / S))
        ≤ ((univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ) *
          ((max 0 ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.1 : ℝ) / S - τ)) ^ 2 / ((((L.rows.getD k ⟨1, []⟩).fam.get i).2.2 : ℝ) / S)) :=
          mul_le_mul_of_nonneg_right (hn i) hti
      _ ≤ ∑ j ∈ univ.filter (fun j => bin j = some (Sum.inr i)), t j := by
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          refine Finset.sum_le_sum fun j hj => ?_
          rw [Finset.mem_filter] at hj
          obtain ⟨hv, hD⟩ := hfam j i hj.2
          exact term_le (hv.imp_right fun h => div_nonpos_of_nonpos_of_nonneg
            (by exact_mod_cast h) hS.le) hτ0 (hDg j) hD
  unfold rowLHS
  linarith

end GradedNear.Cert
