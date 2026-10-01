module

public import GradedNear.Defs

/-!
# Soundness of the row relaxations

On a box interval `[a, b]` (ticks) containing `τ·TS`, a near row at the actual threshold `τ`
implies the first-order linear relaxation (case 2), and one of the two tangent relaxations
(cases 0, 1): the row's left side plus `τ²/(d/S)` is convex in `τ`, so its tangent line at the
midpoint is below it, and an affine function that is `≤ 1` somewhere on `[a, b]` is `≤ 1` at an
endpoint. Integer costs are floored and budgets ceiled, in the safe direction.

Both relaxations need the family counts `n ≥ 0` (part of `wellFormed`): the first-order budget
evaluates the family terms at the upper threshold `b`, and the tangent budget replaces each family
term by its tangent line. Without `n ≥ 0` both statements are false. The hypothesis
`k < L.rows.length` is not used: out-of-range rows default to `⟨1, []⟩`. Helpers are in
`GradedNear.Cert.RelaxAux`.
-/

@[expose] public section

namespace GradedNear.Cert

/-- The relaxed linear constraint of row `k` for case `c` on the box interval `[a, b]`. -/
def RelaxHolds (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (a b : ℤ) (c : ℕ) : Prop :=
  ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) *
      x j ≤ ((rowBudget (L.rows.getD k ⟨1, []⟩) a b c : ℤ) : ℝ)

namespace RelaxAux

/-! ### Constants and rounding -/

lemma S_pos_int : (0 : ℤ) < S := by unfold S; norm_num

lemma S_pos : (0 : ℝ) < S := by exact_mod_cast S_pos_int

lemma TS_pos : (0 : ℝ) < TS := by unfold TS; norm_num

/-- `S / TS` is exact. -/
lemma S_div_TS_mul : ((S / TS : ℤ) : ℝ) * TS = S := by norm_num [S, TS]

lemma S_div_TS_nonneg : (0 : ℝ) ≤ ((S / TS : ℤ) : ℝ) := by norm_num [S, TS]

/-- `HS = S / (2 TS)`. -/
lemma HS_mul : (HS : ℝ) * (2 * TS) = S := by norm_num [HS, S, TS]

/-- Floor division by a positive integer is at most real division. -/
lemma cast_ediv_le (a b : ℤ) (hb : 0 < b) : ((a / b : ℤ) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Int.ediv_mul_le a (ne_of_gt hb)

/-- A rational is at most its ceiling, in `ℝ`. -/
lemma cast_le_ceil (q : ℚ) : (q : ℝ) ≤ ((⌈q⌉ : ℤ) : ℝ) := by
  exact_mod_cast Int.le_ceil q

/-! ### Well-formedness -/

lemma wf_colD {L : Leaf} (hwf : wellFormed L = true) (j : Fin L.cols.length) (k : ℕ) :
    0 < (L.cols.get j).D.getD k 1 := by
  unfold wellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  have hD := (hwf.1 _ (List.get_mem L.cols j)).2
  rw [List.getD_eq_getElem?_getD]
  cases h : (L.cols.get j).D[k]? with
  | none => simp
  | some y => simpa using hD y (List.mem_of_getElem? h)

lemma wf_row {L : Leaf} (hwf : wellFormed L = true) (k : ℕ) :
    0 < (L.rows.getD k ⟨1, []⟩).d ∧ ∀ t ∈ (L.rows.getD k ⟨1, []⟩).fam, 0 ≤ t.1 ∧ 0 < t.2.2 := by
  unfold wellFormed at hwf
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  rw [List.getD_eq_getElem?_getD]
  cases h : L.rows[k]? with
  | none => simp
  | some r => simpa using hwf.2 r (List.mem_of_getElem? h)

/-! ### Sums -/

lemma list_sum_le {α : Type*} (l : List α) (f g : α → ℝ) (h : ∀ t ∈ l, f t ≤ g t) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a (by simp)) (ih fun t ht => h t (by simp [ht]))

lemma list_cast_sum_le {α : Type*} (l : List α) (f : α → ℤ) (g : α → ℝ) (c : ℝ)
    (h : ∀ t ∈ l, (f t : ℝ) ≤ c * g t) : (((l.map f).sum : ℤ) : ℝ) ≤ c * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, mul_add]
    exact add_le_add (h a (by simp)) (ih fun t ht => h t (by simp [ht]))

lemma list_cast_sum_eq {α : Type*} (l : List α) (f : α → ℚ) (g : α → ℝ)
    (h : ∀ t ∈ l, (f t : ℝ) = g t) : (((l.map f).sum : ℚ) : ℝ) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [h a (by simp), ih fun t ht => h t (by simp [ht])]

lemma list_affine {α : Type*} (l : List α) (g : α → ℝ → ℝ)
    (hg : ∀ i s, g i s = g i 0 + s * (g i 1 - g i 0)) (s : ℝ) :
    (l.map (fun i => g i s)).sum = (l.map (fun i => g i 0)).sum +
      s * ((l.map (fun i => g i 1)).sum - (l.map (fun i => g i 0)).sum) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih, hg a s]; ring

lemma finset_affine {ι : Type*} (u : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i s, g i s = g i 0 + s * (g i 1 - g i 0)) (s : ℝ) :
    ∑ i ∈ u, g i s = ∑ i ∈ u, g i 0 + s * (∑ i ∈ u, g i 1 - ∑ i ∈ u, g i 0) := by
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => hg i s

/-- An affine function that is `≤ 1` at a point of `[-h, h]` is `≤ 1` at an endpoint. -/
lemma endpoint {G : ℝ → ℝ} (hG : ∀ s, G s = G 0 + s * (G 1 - G 0)) {h s₀ : ℝ}
    (h1 : -h ≤ s₀) (h2 : s₀ ≤ h) (hle : G s₀ ≤ 1) : G (-h) ≤ 1 ∨ G h ≤ 1 := by
  rw [hG s₀] at hle
  rcases le_total 0 (G 1 - G 0) with hQ | hQ
  · left; rw [hG (-h)]; nlinarith
  · right; rw [hG h]; nlinarith

/-! ### First order -/

/-- The first-order bound for one term: with `Sτ ≤ sh` and `n ≥ 0`,
`⌊n (v - sh)₊² / D⌋ ≤ S · n (v/S - τ)₊² / (D/S)`. -/
lemma first_le (n v D sh : ℤ) (hn : 0 ≤ n) (hD : 0 < D) {τ : ℝ} (hsh : (S : ℝ) * τ ≤ sh) :
    (((n * (max (v - sh) 0) ^ 2) / D : ℤ) : ℝ) ≤
      S * ((n : ℝ) * (max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
  have hS := S_pos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hnr : (0 : ℝ) ≤ n := by exact_mod_cast hn
  refine (cast_ediv_le _ _ hD).trans ?_
  push_cast
  have hM : max ((v : ℝ) - sh) 0 ≤ S * max 0 ((v : ℝ) / S - τ) := by
    apply max_le
    · have e : (S : ℝ) * ((v : ℝ) / S - τ) = v - S * τ := by field_simp
      have := mul_le_mul_of_nonneg_left (le_max_right 0 ((v : ℝ) / S - τ)) hS.le
      linarith
    · exact mul_nonneg hS.le (le_max_left _ _)
  have hsq := pow_le_pow_left₀ (le_max_right _ _) hM 2
  calc (n : ℝ) * (max ((v : ℝ) - sh) 0) ^ 2 / D
      ≤ n * (S * max 0 ((v : ℝ) / S - τ)) ^ 2 / D :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hnr) hDr.le
    _ = S * ((n : ℝ) * (max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
        rw [div_div_eq_mul_div]; ring

lemma first_col_le (v D sh : ℤ) (hD : 0 < D) {τ : ℝ} (hsh : (S : ℝ) * τ ≤ sh) :
    (((max (v - sh) 0) ^ 2 / D : ℤ) : ℝ) ≤
      S * ((max 0 ((v : ℝ) / S - τ)) ^ 2 / ((D : ℝ) / S)) := by
  have h := first_le 1 v D sh zero_le_one hD hsh
  simp only [one_mul, Int.cast_one] at h
  exact h

/-! ### The tangent line -/

/-- The tangent line at `m` of `t ↦ (w - t)₊²`, evaluated at `t = m + s`. -/
noncomputable def tgt (w m s : ℝ) : ℝ := (max 0 (w - m)) ^ 2 - 2 * max 0 (w - m) * s

/-- `t ↦ (w - t)₊²` is convex: it lies above its tangent line at `m`. -/
lemma tangent_ineq (w m t : ℝ) : tgt w m (t - m) ≤ (max 0 (w - t)) ^ 2 := by
  unfold tgt
  have hY0 : 0 ≤ max 0 (w - t) := le_max_left _ _
  have hY1 : w - t ≤ max 0 (w - t) := le_max_right _ _
  rcases le_total (w - m) 0 with h1 | h1
  · rw [max_eq_left h1]; nlinarith [sq_nonneg (max 0 (w - t))]
  · rw [max_eq_right h1]
    nlinarith [sq_nonneg (max 0 (w - t) - (w - m)), mul_nonneg h1 (sub_nonneg.2 hY1)]

/-- Midpoint `(a + b)/(2 TS)` of the box interval, in threshold units. -/
noncomputable def mid (a b : ℤ) : ℝ := ((a : ℝ) + b) / (2 * TS)

/-- Half-width `(b - a)/(2 TS)` of the box interval, in threshold units. -/
noncomputable def hw (a b : ℤ) : ℝ := ((b : ℝ) - a) / (2 * TS)

/-- The endpoint offset of case `c`: `-h` for `c = 0`, `+h` for `c = 1`. -/
noncomputable def sgn (a b : ℤ) (c : ℕ) : ℝ := (2 * (c : ℝ) - 1) * hw a b

/-- Column part of the tangent line of row `k` at `m`, evaluated at `m + s`. -/
noncomputable def colT (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (m s : ℝ) : ℝ :=
  ∑ j, x j * tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) m s / (((L.cols.get j).D.getD k 1 : ℝ) / S)

/-- Family part of the tangent line. -/
noncomputable def famT (r : RowHead) (m s : ℝ) : ℝ :=
  (r.fam.map fun t => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m s / ((t.2.2 : ℝ) / S)).sum

/-- Tangent line of `τ ↦ τ²/(d/S)` at `m`, evaluated at `m + s`. -/
noncomputable def quadT (r : RowHead) (m s : ℝ) : ℝ := (m ^ 2 + 2 * m * s) / ((r.d : ℝ) / S)

/-- The tangent line at `m` of `τ ↦ rowLHS + τ²/(d/S)`, evaluated at `m + s`. -/
noncomputable def tline (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (m s : ℝ) : ℝ :=
  colT L x k m s + famT (L.rows.getD k ⟨1, []⟩) m s + quadT (L.rows.getD k ⟨1, []⟩) m s

lemma tline_affine (L : Leaf) (x : Fin L.cols.length → ℝ) (k : ℕ) (m s : ℝ) :
    tline L x k m s = tline L x k m 0 + s * (tline L x k m 1 - tline L x k m 0) := by
  have h1 : colT L x k m s = colT L x k m 0 + s * (colT L x k m 1 - colT L x k m 0) :=
    finset_affine Finset.univ
      (fun j s => x j * tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) m s /
        (((L.cols.get j).D.getD k 1 : ℝ) / S)) (fun j s => by simp only [tgt]; ring) s
  have h2 : famT (L.rows.getD k ⟨1, []⟩) m s = famT (L.rows.getD k ⟨1, []⟩) m 0 +
      s * (famT (L.rows.getD k ⟨1, []⟩) m 1 - famT (L.rows.getD k ⟨1, []⟩) m 0) :=
    list_affine _
      (fun (t : ℤ × ℤ × ℤ) s => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) m s / ((t.2.2 : ℝ) / S))
      (fun t s => by simp only [tgt]; ring) s
  have h3 : quadT (L.rows.getD k ⟨1, []⟩) m s = quadT (L.rows.getD k ⟨1, []⟩) m 0 +
      s * (quadT (L.rows.getD k ⟨1, []⟩) m 1 - quadT (L.rows.getD k ⟨1, []⟩) m 0) := by
    simp only [quadT]; ring
  unfold tline
  linear_combination h1 + h2 + h3

/-- The tangent line lies below the convex row function (needs `x ≥ 0` and `n ≥ 0`). -/
lemma tline_le (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) (k : ℕ) (m τ : ℝ) :
    tline L x k m (τ - m) ≤
      rowLHS L x k τ + τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  obtain ⟨hd, hfam⟩ := wf_row hwf k
  have hS := S_pos
  have h1 : colT L x k m (τ - m) ≤
      ∑ j, x j * (max 0 (((L.cols.get j).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
        (((L.cols.get j).D.getD k 1 : ℝ) / S) := by
    unfold colT
    refine Finset.sum_le_sum fun j _ => ?_
    have hD : (0 : ℝ) < ((L.cols.get j).D.getD k 1 : ℝ) / S :=
      div_pos (by exact_mod_cast wf_colD hwf j k) hS
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tangent_ineq _ _ _) (hx j)) hD.le
  have h2 : famT (L.rows.getD k ⟨1, []⟩) m (τ - m) ≤ ((L.rows.getD k ⟨1, []⟩).fam.map fun t =>
      (t.1 : ℝ) * (max 0 ((t.2.1 : ℝ) / S - τ)) ^ 2 / ((t.2.2 : ℝ) / S)).sum := by
    unfold famT
    refine list_sum_le _ _ _ fun t ht => ?_
    have hD : (0 : ℝ) < (t.2.2 : ℝ) / S := div_pos (by exact_mod_cast (hfam t ht).2) hS
    have hn : (0 : ℝ) ≤ t.1 := by exact_mod_cast (hfam t ht).1
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (tangent_ineq _ _ _) hn) hD.le
  have h3 : quadT (L.rows.getD k ⟨1, []⟩) m (τ - m) ≤
      τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
    have hdS : (0 : ℝ) < ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S :=
      div_pos (by exact_mod_cast hd) hS
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (τ - m)]) hdS.le
  unfold tline rowLHS
  linarith

/-! ### Tangent costs and budgets -/

/-- The integer tangent cost is at most `S` times the exact tangent value. -/
lemma tangentCost_le (v a b : ℤ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    ((tangentCost v (a + b) (b - a) c : ℤ) : ℝ) ≤ S * tgt ((v : ℝ) / S) (mid a b) (sgn a b c) := by
  have hS := S_pos
  have hT := TS_pos
  have hH := HS_mul
  unfold tangentCost
  dsimp only
  generalize hxi : v - (a + b) * HS = xi
  generalize hhs : (b - a) * HS = hS'
  have hxr : (xi : ℝ) = S * ((v : ℝ) / S - mid a b) := by
    rw [← hxi, mid]; simp only [S, TS, HS]; push_cast; ring
  have hhr : (hS' : ℝ) = S * hw a b := by
    rw [← hhs, hw]; simp only [S, TS, HS]; push_cast; ring
  split_ifs with hx hc0
  · have hX : (v : ℝ) / S - mid a b ≤ 0 := by
      have h0 : (xi : ℝ) ≤ 0 := by exact_mod_cast hx
      rw [hxr] at h0
      nlinarith
    simp [tgt, max_eq_left hX]
  · subst hc0
    have hX : 0 < (v : ℝ) / S - mid a b := by
      have h0 : (0 : ℝ) < xi := by exact_mod_cast (not_le.mp hx)
      rw [hxr] at h0
      exact pos_of_mul_pos_right h0 hS.le
    rw [tgt, max_eq_right hX.le]
    refine (cast_ediv_le _ _ S_pos_int).trans (le_of_eq ?_)
    push_cast
    rw [hxr, hhr, div_eq_iff hS.ne', sgn]
    push_cast
    ring
  · have hX : 0 < (v : ℝ) / S - mid a b := by
      have h0 : (0 : ℝ) < xi := by exact_mod_cast (not_le.mp hx)
      rw [hxr] at h0
      exact pos_of_mul_pos_right h0 hS.le
    obtain rfl : c = 1 := by omega
    rw [tgt, max_eq_right hX.le]
    refine (cast_ediv_le _ _ S_pos_int).trans (le_of_eq ?_)
    push_cast
    rw [hxr, hhr, div_eq_iff hS.ne', sgn]
    push_cast
    ring

/-- The tangent-case column cost is at most `S` times the exact tangent term. -/
lemma colCost_tangent_le (v D a b : ℤ) (hD : 0 < D) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    ((colCost v D a b c : ℤ) : ℝ) ≤
      S * (tgt ((v : ℝ) / S) (mid a b) (sgn a b c) / ((D : ℝ) / S)) := by
  have hS := S_pos
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  rw [colCost, ite_eq_right (by omega)]
  refine (cast_ediv_le _ _ hD).trans ?_
  rw [Int.cast_mul]
  calc ((tangentCost v (a + b) (b - a) c : ℤ) : ℝ) * S / D
      ≤ S * tgt ((v : ℝ) / S) (mid a b) (sgn a b c) * S / D :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (tangentCost_le v a b c hc) hS.le) hDr.le
    _ = S * (tgt ((v : ℝ) / S) (mid a b) (sgn a b c) / ((D : ℝ) / S)) := by
        rw [div_div_eq_mul_div]; ring

/-- The exact family term of `rowBudget`, cast to `ℝ`. -/
lemma tangentExact_cast {w m h : ℚ} {w' m' h' : ℝ} (hw' : (w : ℝ) = w') (hm' : (m : ℝ) = m')
    (hh' : (h : ℝ) = h') (c : ℕ) (hc : c = 0 ∨ c = 1) :
    ((tangentExact w m h c : ℚ) : ℝ) = tgt w' m' ((2 * (c : ℝ) - 1) * h') := by
  subst hw' hm' hh'
  unfold tangentExact tgt
  dsimp only
  rcases hc with rfl | rfl
  · rw [ite_eq_left rfl]
    push_cast
    rw [max_comm]
    ring
  · rw [ite_eq_right one_ne_zero]
    split_ifs with hpos
    · push_cast
      rw [max_comm]
      ring
    · have hwm : w - m ≤ 0 := by
        by_contra hcon
        exact hpos (lt_max_of_lt_left (not_le.mp hcon))
      have hwm' : (w : ℝ) - m ≤ 0 := by exact_mod_cast hwm
      rw [max_eq_left hwm']
      simp

/-- The tangent-case budget is at least `S` times the exact budget. -/
lemma rowBudget_tangent_ge (r : RowHead) (a b : ℤ) (c : ℕ) (hc : c = 0 ∨ c = 1) :
    S * (1 - famT r (mid a b) (sgn a b c) - quadT r (mid a b) (sgn a b c)) ≤
      ((rowBudget r a b c : ℤ) : ℝ) := by
  rw [rowBudget, ite_eq_right (by omega)]
  dsimp only
  refine le_trans (le_of_eq ?_) (cast_le_ceil _)
  rw [Rat.cast_mul, Rat.cast_sub, list_cast_sum_eq _ _
    (fun t => (t.1 : ℝ) * tgt ((t.2.1 : ℝ) / S) (mid a b) (sgn a b c) / ((t.2.2 : ℝ) / S))]
  · unfold famT quadT sgn mid hw
    rcases hc with rfl | rfl
    · rw [ite_eq_left rfl]
      push_cast
      ring
    · rw [ite_eq_right one_ne_zero]
      push_cast
      ring
  · intro t _
    rw [Rat.cast_div, Rat.cast_mul,
      tangentExact_cast (w' := (t.2.1 : ℝ) / S) (m' := mid a b) (h' := hw a b)
        (by simp) (by simp [mid]) (by simp [hw]) c hc]
    simp [sgn]

/-- One tangent case: if the tangent line is `≤ 1` at the case's endpoint, the case's linear
relaxation holds. -/
lemma relax_case (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) (k : ℕ) (a b : ℤ) (c : ℕ) (hc : c = 0 ∨ c = 1)
    (hG : tline L x k (mid a b) (sgn a b c) ≤ 1) : RelaxHolds L x k a b c := by
  have hS := S_pos
  have hcols : ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c :
      ℤ) : ℝ) * x j ≤ S * colT L x k (mid a b) (sgn a b c) := by
    unfold colT
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    calc ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b c : ℤ) : ℝ) * x j
        ≤ S * (tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) (mid a b) (sgn a b c) /
            (((L.cols.get j).D.getD k 1 : ℝ) / S)) * x j :=
          mul_le_mul_of_nonneg_right (colCost_tangent_le _ _ a b (wf_colD hwf j k) c hc) (hx j)
      _ = S * (x j * tgt (((L.cols.get j).v.getD k 0 : ℝ) / S) (mid a b) (sgn a b c) /
            (((L.cols.get j).D.getD k 1 : ℝ) / S)) := by ring
  have hbud := rowBudget_tangent_ge (L.rows.getD k ⟨1, []⟩) a b c hc
  unfold tline at hG
  unfold RelaxHolds
  calc _ ≤ S * colT L x k (mid a b) (sgn a b c) := hcols
    _ ≤ S * (1 - famT (L.rows.getD k ⟨1, []⟩) (mid a b) (sgn a b c) -
          quadT (L.rows.getD k ⟨1, []⟩) (mid a b) (sgn a b c)) :=
        mul_le_mul_of_nonneg_left (by linarith) hS.le
    _ ≤ _ := hbud

end RelaxAux

theorem relax_first (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} (_hk : k < L.rows.length) {a b : ℤ} (ha : 0 ≤ a) {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 2 := by
  obtain ⟨hd, hfam⟩ := RelaxAux.wf_row hwf k
  have hS := RelaxAux.S_pos
  have hT := RelaxAux.TS_pos
  -- the first-order shift `sh = b·(S/TS)` dominates `Sτ`
  have hsh : (S : ℝ) * τ ≤ ((b * (S / TS) : ℤ) : ℝ) := by
    calc (S : ℝ) * τ = ((S / TS : ℤ) : ℝ) * (τ * TS) := by rw [← RelaxAux.S_div_TS_mul]; ring
      _ ≤ ((S / TS : ℤ) : ℝ) * b := mul_le_mul_of_nonneg_left hτb RelaxAux.S_div_TS_nonneg
      _ = ((b * (S / TS) : ℤ) : ℝ) := by push_cast; ring
  have hcols : ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) a b 2 :
      ℤ) : ℝ) * x j ≤ S * ∑ j, x j * (max 0 (((L.cols.get j).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
        (((L.cols.get j).D.getD k 1 : ℝ) / S) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have h := RelaxAux.first_col_le ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1) _
      (RelaxAux.wf_colD hwf j k) hsh
    rw [colCost, ite_eq_left rfl]
    calc _ ≤ S * ((max 0 (((L.cols.get j).v.getD k 0 : ℝ) / S - τ)) ^ 2 /
          (((L.cols.get j).D.getD k 1 : ℝ) / S)) * x j := mul_le_mul_of_nonneg_right h (hx j)
      _ = _ := by ring
  have hfamb : ((((L.rows.getD k ⟨1, []⟩).fam.map fun t =>
      (t.1 * (max (t.2.1 - b * (S / TS)) 0) ^ 2) / t.2.2).sum : ℤ) : ℝ) ≤
      S * (((L.rows.getD k ⟨1, []⟩).fam.map fun t =>
        (t.1 : ℝ) * (max 0 ((t.2.1 : ℝ) / S - τ)) ^ 2 / ((t.2.2 : ℝ) / S)).sum) :=
    RelaxAux.list_cast_sum_le _ _ _ _ fun t ht =>
      RelaxAux.first_le t.1 t.2.1 t.2.2 _ (hfam t ht).1 (hfam t ht).2 hsh
  have hquad : (((S * S * a * a) / (TS * TS * (L.rows.getD k ⟨1, []⟩).d) : ℤ) : ℝ) ≤
      S * (τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) := by
    have hdr : (0 : ℝ) < (L.rows.getD k ⟨1, []⟩).d := by exact_mod_cast hd
    have hTi : (0 : ℤ) < TS := by unfold TS; norm_num
    refine (RelaxAux.cast_ediv_le _ _ (mul_pos (mul_pos hTi hTi) hd)).trans ?_
    have har : (0 : ℝ) ≤ a := by exact_mod_cast ha
    have h1 : (a : ℝ) * a ≤ (τ * TS) * (τ * TS) := mul_self_le_mul_self har hτa
    push_cast
    rw [div_le_iff₀ (mul_pos (mul_pos hT hT) hdr)]
    have hS0 : (S : ℝ) ≠ 0 := hS.ne'
    have hd0 : ((L.rows.getD k ⟨1, []⟩).d : ℝ) ≠ 0 := hdr.ne'
    have e : (S : ℝ) * (τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) *
        (TS * TS * (L.rows.getD k ⟨1, []⟩).d) = S * S * ((τ * TS) * (τ * TS)) := by
      field_simp
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left h1 (mul_nonneg hS.le hS.le)]
  have key := mul_le_mul_of_nonneg_left hrow hS.le
  unfold rowLHS at key
  rw [mul_add, mul_sub, mul_one] at key
  unfold RelaxHolds
  rw [rowBudget, ite_eq_left rfl, Int.cast_sub, Int.cast_sub]
  linarith

theorem relax_tangent (L : Leaf) (hwf : wellFormed L = true) (x : Fin L.cols.length → ℝ)
    (hx : ∀ j, 0 ≤ x j) {k : ℕ} (_hk : k < L.rows.length) {a b : ℤ} {τ : ℝ}
    (hτa : (a : ℝ) ≤ τ * TS) (hτb : τ * TS ≤ b)
    (hrow : rowLHS L x k τ ≤ 1 - τ ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    RelaxHolds L x k a b 0 ∨ RelaxHolds L x k a b 1 := by
  have hT := RelaxAux.TS_pos
  have hB := RelaxAux.tline_le L hwf x hx k (RelaxAux.mid a b) τ
  have hG : RelaxAux.tline L x k (RelaxAux.mid a b) (τ - RelaxAux.mid a b) ≤ 1 := by linarith
  have h1 : -RelaxAux.hw a b ≤ τ - RelaxAux.mid a b := by
    have : (a : ℝ) / TS ≤ τ := by rw [div_le_iff₀ hT]; linarith
    have e : RelaxAux.mid a b - RelaxAux.hw a b = a / TS := by
      unfold RelaxAux.mid RelaxAux.hw; ring
    linarith
  have h2 : τ - RelaxAux.mid a b ≤ RelaxAux.hw a b := by
    have : τ ≤ (b : ℝ) / TS := by rw [le_div_iff₀ hT]; linarith
    have e : RelaxAux.mid a b + RelaxAux.hw a b = b / TS := by
      unfold RelaxAux.mid RelaxAux.hw; ring
    linarith
  rcases RelaxAux.endpoint (RelaxAux.tline_affine L x k (RelaxAux.mid a b)) h1 h2 hG with h | h
  · left
    have e : RelaxAux.sgn a b 0 = -RelaxAux.hw a b := by unfold RelaxAux.sgn; push_cast; ring
    exact RelaxAux.relax_case L hwf x hx k a b 0 (Or.inl rfl) (by rw [e]; exact h)
  · right
    have e : RelaxAux.sgn a b 1 = RelaxAux.hw a b := by unfold RelaxAux.sgn; push_cast; ring
    exact RelaxAux.relax_case L hwf x hx k a b 1 (Or.inr rfl) (by rw [e]; exact h)

end GradedNear.Cert
