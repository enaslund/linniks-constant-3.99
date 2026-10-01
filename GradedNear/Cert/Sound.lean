module

public import GradedNear.Cert.Relax

/-!
# Soundness of the certificate checker

If `checkLeaf L T = some v`, then every feasible point of the leaf LP has objective at most `v`,
and `v < S`. Ingredients: the row relaxations (`Relax.lean`), weak duality with signed costs and
the free dual of the second-family equality, the exclusion rule (all costs `≥ 0`, negative
budget), the enumeration of case vectors, the bisection tree (children partition the parent
box), and the root box `[0, end_k]`, which contains every admissible `τ_k·TS` because
`end_k² > d_k TS²/S`.

The helpers live in `GradedNear.Cert.SoundAux`:
* list bookkeeping: the entries of `colCosts` and `budgets` are the per-row `colCost` and
  `rowBudget` terms of `RelaxHolds`, and `zipWith` sums are `Finset.range` sums
  (`colCosts_getD`, `budgets_getD`, `sum_zipWith`);
* `caseValue_sound`: weak duality for one case, given the relaxed constraint of every row;
* `not_excludable`: an excluded case contradicts the relaxed constraints at `x ≥ 0`;
* `exists_caseVector`: the actual case vector (`2` for order `≠ 1`, the tangent case supplied by
  `relax_tangent` for order `1`) is one of `caseVectors orders`;
* `checkBox_spec`, `checkBox_sound`: every case vector passes the fold, so the box value bounds
  the objective;
* `verifyTree_sound`, `verifyTree_lt`: induction over the bisection tree, with the box invariants
  (length `= rows.length`, lower ends `≥ 0`, `τ_k·TS` in the box);
* `le_rootEnd`: the root box contains `τ_k·TS`.
-/

@[expose] public section

namespace GradedNear.Cert

namespace SoundAux

/-! ### Generic list lemmas -/

theorem getD_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) (d : δ) (d1 : α) (d2 : β) (d3 : γ) :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ) (i : ℕ), i < l1.length → i < l2.length →
      i < l3.length →
      (List.zipWith3 f l1 l2 l3).getD i d = f (l1.getD i d1) (l2.getD i d2) (l3.getD i d3)
  | [], _, _, _, h, _, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, [], _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, _ :: _, 0, _, _, _ => rfl
  | _ :: xs, _ :: ys, _ :: zs, i + 1, h1, h2, h3 => by
      simp only [List.zipWith3, List.getD_cons_succ]
      exact getD_zipWith3 f d d1 d2 d3 xs ys zs i (by simpa using h1) (by simpa using h2)
        (by simpa using h3)

theorem length_zipWith3 {α β γ δ : Type*} (f : α → β → γ → δ) :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ), l2.length = l1.length →
      l3.length = l1.length → (List.zipWith3 f l1 l2 l3).length = l1.length
  | [], _, _, _, _ => rfl
  | _ :: _, [], _, h, _ => by simp at h
  | _ :: _, _ :: _, [], _, h => by simp at h
  | _ :: xs, _ :: ys, _ :: zs, h2, h3 => by
      simp only [List.zipWith3, List.length_cons]
      rw [length_zipWith3 f xs ys zs (by simpa using h2) (by simpa using h3)]

theorem getD_zip {α β : Type*} (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β) (i : ℕ), i < l1.length → i < l2.length →
      (l1.zip l2).getD i (d1, d2) = (l1.getD i d1, l2.getD i d2)
  | [], _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | _ :: _, [], _, _, h => absurd h (Nat.not_lt_zero _)
  | _ :: _, _ :: _, 0, _, _ => rfl
  | _ :: xs, _ :: ys, i + 1, h1, h2 => by
      simp only [List.zip_cons_cons, List.getD_cons_succ]
      exact getD_zip d1 d2 xs ys i (by simpa using h1) (by simpa using h2)

theorem sum_zipWith {α β : Type*} (f : α → β → ℤ) (d1 : α) (d2 : β) :
    ∀ (l1 : List α) (l2 : List β), l2.length = l1.length →
      (List.zipWith f l1 l2).sum = ∑ k ∈ Finset.range l1.length, f (l1.getD k d1) (l2.getD k d2)
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.zipWith_cons_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ',
        List.getD_cons_succ, List.getD_cons_zero]
      rw [sum_zipWith f d1 d2 xs ys (by simpa using h)]
      ring

/-- The coercion `List ℕ → List ℤ` of the duals `Z` in `caseValue` is elaborated through the
list monad; it is the pointwise cast. -/
theorem bind_pure_cast (Z : List ℕ) :
    (Z >>= fun a => pure (a : ℤ) : List ℤ) = Z.map (Nat.cast : ℕ → ℤ) := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    show [(a : ℤ)] ++ (Z >>= fun a => pure (a : ℤ) : List ℤ) = _
    rw [ih]
    rfl

theorem getD_map_cast (Z : List ℕ) (k : ℕ) :
    (Z.map (Nat.cast : ℕ → ℤ)).getD k 0 = ((Z.getD k 0 : ℕ) : ℤ) := by
  have := List.getD_map Z 0 (n := k) (Nat.cast : ℕ → ℤ)
  simpa using this

/-! ### Well-formedness, costs and budgets -/

theorem wf_col {L : Leaf} (hwf : wellFormed L = true) {col : Col} (hcol : col ∈ L.cols) :
    col.v.length = L.rows.length ∧ col.D.length = L.rows.length := by
  simp only [wellFormed, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hwf
  exact (hwf.1 col hcol).1

theorem colCosts_length {L : Leaf} (hwf : wellFormed L = true) {col : Col} (hcol : col ∈ L.cols)
    {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length) {cs : List ℕ}
    (hcs : cs.length = L.rows.length) : (colCosts col box cs).length = L.rows.length := by
  obtain ⟨hv, hD⟩ := wf_col hwf hcol
  unfold colCosts
  rw [length_zipWith3 _ _ _ _ (by simp [hv, hD, hbox]) (by rw [hcs, hbox]), hbox]

/-- Entry `k` of `colCosts` is the cost of the column in row `k`, as in `RelaxHolds`. -/
theorem colCosts_getD {L : Leaf} (hwf : wellFormed L = true) {col : Col} (hcol : col ∈ L.cols)
    {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length) {cs : List ℕ}
    (hcs : cs.length = L.rows.length) {k : ℕ} (hk : k < L.rows.length) :
    (colCosts col box cs).getD k 0 = colCost (col.v.getD k 0) (col.D.getD k 1)
      (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) := by
  obtain ⟨hv, hD⟩ := wf_col hwf hcol
  unfold colCosts
  rw [getD_zipWith3 _ _ (0, 0) (0, 1) 0 _ _ _ k (by omega) (by simp [hv, hD]; omega) (by omega),
    getD_zip 0 1 _ _ k (by omega) (by omega)]

theorem budgets_length {L : Leaf} {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length)
    {cs : List ℕ} (hcs : cs.length = L.rows.length) :
    (budgets L box cs).length = L.rows.length := by
  unfold budgets
  rw [length_zipWith3 _ _ _ _ hbox hcs]

/-- Entry `k` of `budgets` is the budget of row `k`, as in `RelaxHolds`. -/
theorem budgets_getD {L : Leaf} {box : List (ℤ × ℤ)} (hbox : box.length = L.rows.length)
    {cs : List ℕ} (hcs : cs.length = L.rows.length) {k : ℕ} (hk : k < L.rows.length) :
    (budgets L box cs).getD k 0 = rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1
      (box.getD k (0, 0)).2 (cs.getD k 0) := by
  unfold budgets
  rw [getD_zipWith3 _ _ ⟨1, []⟩ (0, 0) 0 _ _ _ k hk (by omega) (by omega)]

/-! ### Weak duality for one case -/

theorem le_mul_ceilDiv (a : ℤ) {b : ℤ} (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  unfold ceilDiv
  have := Int.ediv_mul_le (-a) hb.ne'
  linarith

/-- Weak duality in real form: column inequalities, the linear constraints and the relaxed near
rows, combined with nonnegative multipliers (and a free one `Q` for the equality). -/
theorem weak_duality {m n : ℕ} (x : Fin m → ℝ) (hx : ∀ j, 0 ≤ x j)
    (G W C NH E : Fin m → ℝ) (c : Fin m → ℕ → ℝ) (bud : ℕ → ℝ) (z : ℕ → ℝ) (hz : ∀ k, 0 ≤ z k)
    (Y V U Q F C0 N0 E0 DSr : ℝ) (hY : 0 ≤ Y) (hV : 0 ≤ V) (hU : 0 ≤ U)
    (hcol : ∀ j, DSr * G j ≤
      Y * W j + V * C j + U * NH j + Q * E j + ∑ k ∈ Finset.range n, z k * c j k)
    (hW : ∑ j, W j * x j ≤ F) (hC : ∑ j, C j * x j ≤ C0) (hNH : ∑ j, NH j * x j ≤ N0)
    (hE : ∑ j, E j * x j = E0) (hrel : ∀ k < n, ∑ j, c j k * x j ≤ bud k) :
    DSr * ∑ j, G j * x j ≤
      Y * F + V * C0 + U * N0 + Q * E0 + ∑ k ∈ Finset.range n, z k * bud k := by
  have hsplit : ∑ j, (Y * W j + V * C j + U * NH j + Q * E j +
      ∑ k ∈ Finset.range n, z k * c j k) * x j =
      Y * ∑ j, W j * x j + V * ∑ j, C j * x j + U * ∑ j, NH j * x j + Q * ∑ j, E j * x j +
        ∑ k ∈ Finset.range n, z k * ∑ j, c j k * x j := by
    simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  have h1 : DSr * ∑ j, G j * x j ≤ ∑ j, (Y * W j + V * C j + U * NH j + Q * E j +
      ∑ k ∈ Finset.range n, z k * c j k) * x j := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hcol j) (hx j)
  have h2 : ∑ k ∈ Finset.range n, z k * ∑ j, c j k * x j ≤ ∑ k ∈ Finset.range n, z k * bud k :=
    Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hrel k (Finset.mem_range.mp hk)) (hz k)
  have h3 := mul_le_mul_of_nonneg_left hW hY
  have h4 := mul_le_mul_of_nonneg_left hC hV
  have h5 := mul_le_mul_of_nonneg_left hNH hU
  rw [hsplit, hE] at h1
  linarith

/-- From `DS · Σ G x ≤ T` to the certified value `⌈T / DS⌉ + first + final`. -/
theorem obj_le_of {L : Leaf} {x : Fin L.cols.length → ℝ} {T : ℤ}
    (h : ((DS : ℤ) : ℝ) * ∑ j, ((L.cols.get j).G : ℝ) * x j ≤ (T : ℝ)) :
    objective L x ≤ ((ceilDiv T DS + L.first + L.final : ℤ) : ℝ) := by
  have hDS : (0 : ℤ) < DS := by norm_num [DS]
  have h2 : (T : ℝ) ≤ (DS : ℝ) * (ceilDiv T DS : ℝ) := by exact_mod_cast le_mul_ceilDiv T hDS
  have hDSr : (0 : ℝ) < (DS : ℝ) := by exact_mod_cast hDS
  have h3 := le_of_mul_le_mul_left (h.trans h2) hDSr
  unfold objective
  push_cast
  linarith

/-- Weak duality for one case: if the relaxed constraint of every row holds for the case vector
`cs`, then the value certified by the duals bounds the objective. -/
theorem caseValue_sound {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) {cs : List ℕ} (hcs : cs.length = L.rows.length)
    {du : Duals} {v : ℤ} (hv : caseValue L box cs du = some v)
    {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ} (hfeas : Feasible L x τ)
    (hrel : ∀ k < L.rows.length,
      RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0)) :
    objective L x ≤ v := by
  obtain ⟨hx, hW, hC, hNH, hE, -⟩ := hfeas
  unfold caseValue at hv
  split_ifs at hv with hcond
  rw [bind_pure_cast] at hv hcond
  obtain ⟨hZ, hcols⟩ := hcond
  have hZm : (du.Z.map (Nat.cast : ℕ → ℤ)).length = L.rows.length := by rw [List.length_map, hZ]
  obtain rfl := Option.some.inj hv
  apply obj_le_of
  rw [sum_zipWith _ 0 0 _ _ (by rw [budgets_length hbox hcs, hZm]), hZm]
  have hsum : ∑ k ∈ Finset.range L.rows.length,
      (du.Z.map (Nat.cast : ℕ → ℤ)).getD k 0 * (budgets L box cs).getD k 0 =
      ∑ k ∈ Finset.range L.rows.length, ((du.Z.getD k 0 : ℕ) : ℤ) *
        rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1 (box.getD k (0, 0)).2
          (cs.getD k 0) :=
    Finset.sum_congr rfl fun k hk => by
      rw [getD_map_cast, budgets_getD hbox hcs (Finset.mem_range.mp hk)]
  rw [hsum]
  have hcol : ∀ j : Fin L.cols.length, ((DS : ℤ) : ℝ) * ((L.cols.get j).G : ℝ) ≤
      (du.Y : ℝ) * ((L.cols.get j).W : ℝ) + (du.V : ℝ) * ((L.cols.get j).C : ℝ) +
        (du.U : ℝ) * ((L.cols.get j).NH : ℝ) +
        ((du.P : ℝ) - (du.M : ℝ)) * ((L.cols.get j).E : ℝ) +
        ∑ k ∈ Finset.range L.rows.length, ((du.Z.getD k 0 : ℕ) : ℝ) *
          ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
            (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ) := by
    intro j
    have hmem : L.cols.get j ∈ L.cols := List.get_mem _ _
    have h1 := List.all_eq_true.mp hcols _ hmem
    rw [decide_eq_true_eq, sum_zipWith _ 0 0 _ _
      (by rw [colCosts_length hwf hmem hbox hcs, hZm]), hZm] at h1
    have h2 : ∑ k ∈ Finset.range L.rows.length,
        (du.Z.map (Nat.cast : ℕ → ℤ)).getD k 0 * (colCosts (L.cols.get j) box cs).getD k 0 =
        ∑ k ∈ Finset.range L.rows.length, ((du.Z.getD k 0 : ℕ) : ℤ) *
          colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
            (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) :=
      Finset.sum_congr rfl fun k hk => by
        rw [getD_map_cast, colCosts_getD hwf hmem hbox hcs (Finset.mem_range.mp hk)]
    rw [h2] at h1
    exact_mod_cast h1
  have key := weak_duality x hx (fun j => ((L.cols.get j).G : ℝ))
    (fun j => ((L.cols.get j).W : ℝ)) (fun j => ((L.cols.get j).C : ℝ))
    (fun j => ((L.cols.get j).NH : ℝ)) (fun j => ((L.cols.get j).E : ℝ))
    (fun j k => ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
      (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ))
    (fun k => ((rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1 (box.getD k (0, 0)).2
      (cs.getD k 0) : ℤ) : ℝ))
    (fun k => ((du.Z.getD k 0 : ℕ) : ℝ)) (fun k => Nat.cast_nonneg _)
    (du.Y : ℝ) (du.V : ℝ) (du.U : ℝ) ((du.P : ℝ) - (du.M : ℝ)) (L.F : ℝ) (2 * (S : ℝ))
    ((L.ng : ℝ) * S) ((L.n2 : ℝ) * S) ((DS : ℤ) : ℝ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hcol hW hC hNH hE hrel
  push_cast
  exact key

/-! ### Exclusion -/

/-- A case whose relaxed constraints all hold at some `x ≥ 0` is not excludable. -/
theorem not_excludable {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) {cs : List ℕ} (hcs : cs.length = L.rows.length)
    {x : Fin L.cols.length → ℝ} (hx : ∀ j, 0 ≤ x j)
    (hrel : ∀ k < L.rows.length,
      RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0)) :
    excludable L box cs ≠ true := by
  intro hex
  unfold excludable at hex
  obtain ⟨k, hk, hk'⟩ := List.any_eq_true.mp hex
  rw [List.mem_range] at hk
  rw [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hk'
  obtain ⟨hneg, hcost⟩ := hk'
  rw [budgets_getD hbox hcs hk] at hneg
  have hr := hrel k hk
  unfold RelaxHolds at hr
  have hnn : (0 : ℝ) ≤ ∑ j, ((colCost ((L.cols.get j).v.getD k 0) ((L.cols.get j).D.getD k 1)
      (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 (cs.getD k 0) : ℤ) : ℝ) * x j := by
    refine Finset.sum_nonneg fun j _ => ?_
    have hmem : L.cols.get j ∈ L.cols := List.get_mem _ _
    have h1 := hcost _ hmem
    rw [decide_eq_true_eq, colCosts_getD hwf hmem hbox hcs hk] at h1
    exact mul_nonneg (by exact_mod_cast h1) (hx j)
  have hneg' : ((rowBudget (L.rows.getD k ⟨1, []⟩) (box.getD k (0, 0)).1 (box.getD k (0, 0)).2
      (cs.getD k 0) : ℤ) : ℝ) < 0 := by exact_mod_cast hneg
  linarith

/-! ### Case vectors -/

/-- If every row of order `1` satisfies `P k 0 ∨ P k 1` and every other row satisfies `P k 2`,
some case vector satisfies `P` in every row. -/
theorem exists_caseVector (P : ℕ → ℕ → Prop) (os : List ℕ)
    (h : ∀ k < os.length, (os.getD k 0 = 1 → P k 0 ∨ P k 1) ∧ (os.getD k 0 ≠ 1 → P k 2)) :
    ∃ cs ∈ caseVectors os, cs.length = os.length ∧ ∀ k < os.length, P k (cs.getD k 0) := by
  induction os generalizing P with
  | nil => exact ⟨[], by simp [caseVectors], rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | cons o os ih =>
    obtain ⟨cs, hcs, hlen, hP⟩ := ih (fun k c => P (k + 1) c)
      (fun k hk => by simpa using h (k + 1) (by simpa using hk))
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    have hext : ∀ c, P 0 c → ∀ k < (o :: os).length, P k ((c :: cs).getD k 0) := by
      intro c hc k hk
      cases k with
      | zero => simpa using hc
      | succ k => simpa using hP k (by simpa using hk)
    by_cases ho : o = 1
    · rcases h0.1 ho with hp | hp
      · exact ⟨0 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 0 hp⟩
      · exact ⟨1 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 1 hp⟩
    · exact ⟨2 :: cs, by simp [caseVectors, ho, hcs], by simp [hlen], hext 2 (h0.2 ho)⟩

/-! ### The fold over cases -/

theorem foldl_some {α : Type*} (f : Option ℤ → α → Option ℤ) (Q : α → ℤ → Prop)
    (hf : ∀ acc a m, f acc a = some m → ∃ m0, acc = some m0 ∧ m0 ≤ m ∧ Q a m)
    (hQ : ∀ a m1 m2, Q a m1 → m1 ≤ m2 → Q a m2) (l : List α) :
    ∀ (init : Option ℤ) (m : ℤ), l.foldl f init = some m →
      (∃ m0, init = some m0 ∧ m0 ≤ m) ∧ ∀ a ∈ l, Q a m := by
  induction l with
  | nil => intro init m h; exact ⟨⟨m, h, le_rfl⟩, fun a ha => absurd ha List.not_mem_nil⟩
  | cons a l ih =>
    intro init m h
    rw [List.foldl_cons] at h
    obtain ⟨⟨m1, hm1, hm1le⟩, hl⟩ := ih _ _ h
    obtain ⟨m0, hinit, hm0, hQa⟩ := hf _ _ _ hm1
    refine ⟨⟨m0, hinit, hm0.trans hm1le⟩, fun b hb => ?_⟩
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hQ _ _ _ hQa hm1le
    · exact hl b hb

/-- If a node's box passes, every case vector is excluded or carries duals certifying a value
`≤` the box value. -/
theorem checkBox_spec {L : Leaf} {box : List (ℤ × ℤ)} {orders : List ℕ} {certs : List CaseCert}
    {m : ℤ} (h : checkBox L box orders certs = some m) :
    orders.length = L.rows.length ∧ ∀ cv ∈ caseVectors orders,
      excludable L box cv = true ∨ ∃ du v, caseValue L box cv du = some v ∧ v ≤ m := by
  unfold checkBox at h
  dsimp only at h
  split_ifs at h with hc
  obtain ⟨hord, hlen, -⟩ := hc
  refine ⟨hord, ?_⟩
  have key := foldl_some _ (fun (cc : List ℕ × CaseCert) m =>
      excludable L box cc.1 = true ∨ ∃ du v, caseValue L box cc.1 du = some v ∧ v ≤ m)
    ?_ ?_ _ _ _ h
  · intro cv hcv
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hcv
    have hi' : i < ((caseVectors orders).zip certs).length := by simp [hlen, hi]
    have := key.2 _ (List.getElem_mem hi')
    rwa [List.getElem_zip] at this
  · intro acc cc m' hf
    cases acc with
    | none => simp at hf
    | some m0 =>
      refine ⟨m0, rfl, ?_⟩
      rcases cc with ⟨cv, cert⟩
      cases cert with
      | excluded =>
        simp only [Option.bind_some] at hf
        split_ifs at hf with hex
        cases hf
        exact ⟨le_rfl, Or.inl hex⟩
      | duals du =>
        simp only [Option.bind_some] at hf
        obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hf
        exact ⟨le_max_left _ _, Or.inr ⟨du, v, hv, le_max_right _ _⟩⟩
  · intro cc m1 m2 hQ hle
    rcases hQ with hQ | ⟨du, v, hv, hvle⟩
    · exact Or.inl hQ
    · exact Or.inr ⟨du, v, hv, hvle.trans hle⟩

/-- The value of a node bounds the objective at every feasible point whose thresholds lie in the
node's box. -/
theorem checkBox_sound {L : Leaf} (hwf : wellFormed L = true) {box : List (ℤ × ℤ)}
    (hbox : box.length = L.rows.length) (hlo : ∀ k < L.rows.length, 0 ≤ (box.getD k (0, 0)).1)
    {orders : List ℕ} {certs : List CaseCert} {m : ℤ} (h : checkBox L box orders certs = some m)
    {x : Fin L.cols.length → ℝ} {τ : ℕ → ℝ} (hfeas : Feasible L x τ)
    (hτ : ∀ k < L.rows.length,
      ((box.getD k (0, 0)).1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ (box.getD k (0, 0)).2) :
    objective L x ≤ m := by
  obtain ⟨hord, hcv⟩ := checkBox_spec h
  have hx := hfeas.1
  have hrow := hfeas.2.2.2.2.2
  obtain ⟨cs, hcs, hlen, hrel⟩ := exists_caseVector
    (fun k c => RelaxHolds L x k (box.getD k (0, 0)).1 (box.getD k (0, 0)).2 c) orders (by
      intro k hk
      rw [hord] at hk
      obtain ⟨-, -, hr⟩ := hrow k hk
      obtain ⟨ha, hb⟩ := hτ k hk
      exact ⟨fun _ => relax_tangent L hwf x hx hk ha hb hr,
        fun _ => relax_first L hwf x hx hk (hlo k hk) ha hb hr⟩)
  rw [hord] at hlen hrel
  rcases hcv cs hcs with hex | ⟨du, v, hv, hvm⟩
  · exact absurd hex (not_excludable hwf hbox hlen hx hrel)
  · exact (caseValue_sound hwf hbox hlen hv hfeas hrel).trans (by exact_mod_cast hvm)

/-! ### The bisection tree -/

theorem getD_set_of_lt {box : List (ℤ × ℤ)} {k : ℕ} (hk : k < box.length) (p : ℤ × ℤ) (i : ℕ) :
    (box.set k p).getD i (0, 0) = if i = k then p else box.getD i (0, 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set, List.getD_eq_getElem?_getD]
  by_cases hi : i = k
  · subst hi
    simp [hk]
  · simp [Ne.symm hi, hi]

/-- Induction over the tree: on a box of the right length with nonnegative lower ends that
contains every `τ_k·TS`, the value of the tree bounds the objective. -/
theorem verifyTree_sound {L : Leaf} (hwf : wellFormed L = true) {x : Fin L.cols.length → ℝ}
    {τ : ℕ → ℝ} (hfeas : Feasible L x τ) (T : Tree) :
    ∀ (box : List (ℤ × ℤ)) (m : ℤ), verifyTree L T box = some m →
      box.length = L.rows.length → (∀ k < L.rows.length, 0 ≤ (box.getD k (0, 0)).1) →
      (∀ k < L.rows.length,
        ((box.getD k (0, 0)).1 : ℝ) ≤ τ k * TS ∧ τ k * TS ≤ (box.getD k (0, 0)).2) →
      objective L x ≤ m := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box m h hlen hlo hτ
    simp only [verifyTree] at h
    split at h
    · rename_i a b hk
      split_ifs at h with hab
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      obtain ⟨hkl, hkv⟩ := List.getElem?_eq_some_iff.mp hk
      have hgk : box.getD k (0, 0) = (a, b) := by rw [List.getD_eq_getElem _ _ hkl, hkv]
      have hkn : k < L.rows.length := hlen ▸ hkl
      obtain ⟨hτa, hτb⟩ := hτ k hkn
      rw [hgk] at hτa hτb
      have ha0 : 0 ≤ a := by
        have := hlo k hkn
        rwa [hgk] at this
      by_cases hmid : τ k * TS ≤ (mid : ℝ)
      · have := ihl _ _ h1 (by rw [List.length_set, hlen])
          (fun i hi => by
            rw [getD_set_of_lt hkl]
            split_ifs with hik
            · exact ha0
            · exact hlo i hi)
          (fun i hi => by
            rw [getD_set_of_lt hkl]
            split_ifs with hik
            · subst hik; exact ⟨hτa, hmid⟩
            · exact hτ i hi)
        exact this.trans (by exact_mod_cast le_max_left _ _)
      · have hmid' : (mid : ℝ) ≤ τ k * TS := (not_le.mp hmid).le
        have := ihr _ _ h3 (by rw [List.length_set, hlen])
          (fun i hi => by
            rw [getD_set_of_lt hkl]
            split_ifs with hik
            · exact ha0.trans hab.1.le
            · exact hlo i hi)
          (fun i hi => by
            rw [getD_set_of_lt hkl]
            split_ifs with hik
            · subst hik; exact ⟨hmid', hτb⟩
            · exact hτ i hi)
        exact this.trans (by exact_mod_cast le_max_right _ _)
    · simp at h
  | node orders certs =>
    intro box m h hlen hlo hτ
    simp only [verifyTree] at h
    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h' with hvS
    cases h'
    exact checkBox_sound hwf hlen hlo hv hfeas hτ

/-- Every node value is `< S`, and so is their maximum. -/
theorem verifyTree_lt {L : Leaf} (T : Tree) :
    ∀ (box : List (ℤ × ℤ)) (m : ℤ), verifyTree L T box = some m → m < S := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box m h
    simp only [verifyTree] at h
    split at h
    · split_ifs at h with hab
      obtain ⟨m1, h1, h2⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨m2, h3, rfl⟩ := Option.map_eq_some_iff.mp h2
      exact max_lt (ihl _ _ h1) (ihr _ _ h3)
    · simp at h
  | node orders certs =>
    intro box m h
    simp only [verifyTree] at h
    obtain ⟨v, hv, h'⟩ := Option.bind_eq_some_iff.mp h
    split_ifs at h' with hvS
    cases h'
    exact hvS

/-! ### The root box -/

theorem isqrtUp_sq (n : ℕ) : n ≤ isqrtUp n * isqrtUp n := by
  unfold isqrtUp
  split_ifs with h
  · exact h.ge
  · exact (Nat.lt_succ_sqrt n).le

/-- The root end contains every admissible threshold: `(τ·TS)² ≤ d TS²/S < ⌊d TS²/S⌋ + 1 ≤
rootEnd²`. -/
theorem le_rootEnd {d : ℤ} {t : ℝ} (ht : 0 ≤ t) (htd : t ^ 2 ≤ (d : ℝ) / S) :
    t * TS ≤ rootEnd d := by
  have hS : (0 : ℤ) < S := by norm_num [S]
  have h1 : d * TS * TS < (d * TS * TS / S + 1) * S := Int.lt_ediv_add_one_mul_self _ hS
  have h2 : d * TS * TS / S ≤ ((d * TS * TS / S).toNat : ℤ) := Int.self_le_toNat _
  have h3 := isqrtUp_sq ((d * TS * TS / S).toNat + 1)
  unfold rootEnd
  generalize d * TS * TS / S = q at h1 h2 h3 ⊢
  generalize isqrtUp (q.toNat + 1) = r at h3 ⊢
  have hSr : (0 : ℝ) < S := by exact_mod_cast hS
  have h1r : (d : ℝ) * TS * TS < ((q : ℝ) + 1) * S := by exact_mod_cast h1
  have h2r : (q : ℝ) ≤ (q.toNat : ℝ) := by exact_mod_cast h2
  have h3r : ((q.toNat : ℝ) + 1) ≤ (r : ℝ) * r := by exact_mod_cast h3
  have h4 : t ^ 2 * S ≤ d := by rwa [le_div_iff₀ hSr] at htd
  have h5 : (t * TS) ^ 2 * S < ((q : ℝ) + 1) * S := by
    have := mul_le_mul_of_nonneg_right h4 (sq_nonneg (TS : ℝ))
    calc (t * TS) ^ 2 * S = t ^ 2 * S * (TS : ℝ) ^ 2 := by ring
      _ ≤ d * (TS : ℝ) ^ 2 := this
      _ = d * TS * TS := by ring
      _ < ((q : ℝ) + 1) * S := h1r
  have h6 : (t * TS) ^ 2 < (q : ℝ) + 1 := lt_of_mul_lt_mul_right h5 hSr.le
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hTS : (0 : ℝ) ≤ TS := by norm_num [TS]
  have htT : 0 ≤ t * TS := mul_nonneg ht hTS
  push_cast
  nlinarith

theorem rootBox_length (L : Leaf) : (rootBox L).length = L.rows.length := by
  simp [rootBox]

theorem rootBox_getD {L : Leaf} {k : ℕ} (hk : k < L.rows.length) :
    (rootBox L).getD k (0, 0) = (0, rootEnd (L.rows.getD k ⟨1, []⟩).d) := by
  unfold rootBox
  rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_map,
    List.getD_eq_getElem _ _ hk]

end SoundAux

/-- **Soundness of the checker.** If `checkLeaf L T = some val`, then every feasible point of the
leaf LP (`Feasible`: real column values `x ≥ 0` and thresholds `τ`) has objective at most
`val`. -/
theorem checkLeaf_sound {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x ≤ val := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  refine SoundAux.verifyTree_sound hwf hfeas T _ _ h (SoundAux.rootBox_length L) ?_ ?_
  · intro k hk
    rw [SoundAux.rootBox_getD hk]
  · intro k hk
    rw [SoundAux.rootBox_getD hk]
    obtain ⟨h0, hd, -⟩ := hfeas.2.2.2.2.2 k hk
    refine ⟨?_, SoundAux.le_rootEnd h0 hd⟩
    push_cast
    exact mul_nonneg h0 (by norm_num [TS])

/-- The value of an accepted certificate is below `S`, since every tree node's value is checked
to be `< S`. -/
theorem checkLeaf_lt {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val) :
    val < S := by
  unfold checkLeaf at h
  split_ifs at h with hwf
  exact SoundAux.verifyTree_lt T _ _ h

/-- A certified leaf: every feasible point has objective `< 1` (in units of `S`). -/
theorem certified {L : Leaf} {T : Tree} {val : ℤ} (h : checkLeaf L T = some val)
    (x : Fin L.cols.length → ℝ) (τ : ℕ → ℝ) (hfeas : Feasible L x τ) :
    objective L x < S :=
  lt_of_le_of_lt (checkLeaf_sound h x τ hfeas) (by exact_mod_cast checkLeaf_lt h)

end GradedNear.Cert
