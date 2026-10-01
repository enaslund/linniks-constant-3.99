module

public import GradedNear.Defs
public import CertCore

/-!
# The compiled checker computes the verified one

`CertCore` (`lean-graded/CertCore.lean`) is a copy of the leaf-certificate checker
`GradedNear.Cert.checkLeaf` that depends on Lean core only, so that it compiles to a native
executable (`CertRunNative.lean`, `lake build certrun`) without Mathlib. This file converts the
checker's data (`Leaf.toCore`, `Tree.toCore`, field by field) and proves

`checkLeaf_toCore : CertCore.checkLeaf L.toCore T.toCore = checkLeaf L T`,

so a value computed by the native checker is a value of the verified checker. The conversions
are bijective (`Leaf.ofCore`, `Tree.ofCore`), so every input of the native checker is covered:
`checkLeaf_ofCore : CertCore.checkLeaf L T = checkLeaf (Leaf.ofCore L) (Tree.ofCore T)`. Hence
if the native checker returns `some v` on `(L, T)`, then `checkLeaf_sound` (with
`(checkLeaf_ofCore L T).symm.trans h`) bounds the objective of `Leaf.ofCore L` by `v` at every
feasible point.

The proof goes function by function. Most functions are copies whose equality is definitional
(Mathlib's instances on `ℤ` and `ℚ` unfold to the core ones, and Mathlib's ceiling on `ℚ` is
`-Rat.floor (-q)`, which is `CertCore.ratCeil`). The differences are bridged as follows:
* `CertCore.zipWith3` and Mathlib's `List.zipWith3` have the same recursion (`zipWith3_eq`);
* the lists of columns and rows of `Leaf.toCore` are mapped (`List.all_map`, `zipWith3_map`);
* `GradedNear.Cert.caseValue` casts the duals `Z : List ℕ` through Mathlib's list monad
  (`bind_pure_cast`), while `CertCore.caseValue` maps `Int.ofNat` over them once;
* `CertCore.caseValue` accumulates the column and budget sums row by row: `addMul_eq`,
  `costOf_costPrep`, `dotAcc_eq` and `budgetAcc_eq` identify the accumulations with the sums of
  `GradedNear.Cert.caseValue`.
-/

@[expose] public section

namespace GradedNear.Cert

/-! ## Conversions -/

/-- A column as `CertCore` data. -/
def Col.toCore (c : Col) : CertCore.Col := ⟨c.G, c.W, c.C, c.NH, c.E, c.v, c.D⟩

/-- A near row as `CertCore` data. -/
def RowHead.toCore (r : RowHead) : CertCore.RowHead := ⟨r.d, r.fam⟩

/-- A leaf as `CertCore` data. -/
def Leaf.toCore (L : Leaf) : CertCore.Leaf :=
  ⟨L.cols.map Col.toCore, L.rows.map RowHead.toCore, L.F, L.ng, L.n2, L.first, L.final⟩

/-- Duals as `CertCore` data. -/
def Duals.toCore (du : Duals) : CertCore.Duals := ⟨du.Y, du.V, du.U, du.P, du.M, du.Z⟩

/-- A case certificate as `CertCore` data. -/
def CaseCert.toCore : CaseCert → CertCore.CaseCert
  | .excluded => .excluded
  | .duals du => .duals du.toCore

/-- A certificate tree as `CertCore` data. -/
def Tree.toCore : Tree → CertCore.Tree
  | .split k mid l r => .split k mid l.toCore r.toCore
  | .node orders certs => .node orders (certs.map CaseCert.toCore)

/-- A `CertCore` column as checker data. -/
def Col.ofCore (c : CertCore.Col) : Col := ⟨c.G, c.W, c.C, c.NH, c.E, c.v, c.D⟩

/-- A `CertCore` near row as checker data. -/
def RowHead.ofCore (r : CertCore.RowHead) : RowHead := ⟨r.d, r.fam⟩

/-- A `CertCore` leaf as checker data. -/
def Leaf.ofCore (L : CertCore.Leaf) : Leaf :=
  ⟨L.cols.map Col.ofCore, L.rows.map RowHead.ofCore, L.F, L.ng, L.n2, L.first, L.final⟩

/-- `CertCore` duals as checker data. -/
def Duals.ofCore (du : CertCore.Duals) : Duals := ⟨du.Y, du.V, du.U, du.P, du.M, du.Z⟩

/-- A `CertCore` case certificate as checker data. -/
def CaseCert.ofCore : CertCore.CaseCert → CaseCert
  | .excluded => .excluded
  | .duals du => .duals (Duals.ofCore du)

/-- A `CertCore` certificate tree as checker data. -/
def Tree.ofCore : CertCore.Tree → Tree
  | .split k mid l r => .split k mid (Tree.ofCore l) (Tree.ofCore r)
  | .node orders certs => .node orders (certs.map CaseCert.ofCore)

namespace FastEq

/-! ## Generic list lemmas -/

theorem zipWith3_eq {α β γ δ : Type} (f : α → β → γ → δ) :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ),
      CertCore.zipWith3 f l1 l2 l3 = List.zipWith3 f l1 l2 l3
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: xs, y :: ys, z :: zs => by
    simp only [CertCore.zipWith3, List.zipWith3, zipWith3_eq f xs ys zs]

theorem zipWith3_map {α α' β γ δ : Type} (f : α' → β → γ → δ) (g : α → α') :
    ∀ (l1 : List α) (l2 : List β) (l3 : List γ),
      CertCore.zipWith3 f (l1.map g) l2 l3 = List.zipWith3 (fun a b c => f (g a) b c) l1 l2 l3
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | _ :: _, _ :: _, [] => rfl
  | x :: xs, y :: ys, z :: zs => by
    simp only [List.map_cons, CertCore.zipWith3, List.zipWith3, zipWith3_map f g xs ys zs]

/-- The coercion `List ℕ → List ℤ` of the duals `Z` in `caseValue` is elaborated through the
list monad; it is the pointwise cast. -/
theorem bind_pure_cast (Z : List ℕ) :
    (Z >>= fun a => pure (a : ℤ) : List ℤ) = Z.map Int.ofNat := by
  induction Z with
  | nil => rfl
  | cons a Z ih =>
    show [(a : ℤ)] ++ (Z >>= fun a => pure (a : ℤ) : List ℤ) = _
    rw [ih]
    rfl

/-! ## Rows and columns -/

theorem colCosts_toCore (col : Col) (box : List (ℤ × ℤ)) (cs : List ℕ) :
    CertCore.colCosts col.toCore box cs = colCosts col box cs := by
  unfold CertCore.colCosts colCosts
  rw [zipWith3_eq]
  rfl

theorem budgets_toCore (L : Leaf) (box : List (ℤ × ℤ)) (cs : List ℕ) :
    CertCore.budgets L.toCore box cs = budgets L box cs := by
  unfold CertCore.budgets budgets
  exact zipWith3_map _ _ _ _ _

theorem rows_length_toCore (L : Leaf) : L.toCore.rows.length = L.rows.length :=
  List.length_map _

theorem cols_all_toCore (L : Leaf) (p : CertCore.Col → Bool) :
    L.toCore.cols.all p = L.cols.all (fun col => p col.toCore) :=
  List.all_map

/-! ## The dual check of a case -/

theorem addMul_eq (acc x y : ℤ) : CertCore.addMul acc x y = acc + x * y := by
  unfold CertCore.addMul
  split_ifs with hx hy
  · rw [hx, zero_mul, add_zero]
  · rw [hy, mul_zero, add_zero]
  · rfl

theorem costOf_costPrep (ab : ℤ × ℤ) (c : ℕ) (v D : ℤ) :
    CertCore.costOf (CertCore.costPrep ab c) v D = colCost v D ab.1 ab.2 c := by
  obtain ⟨a, b⟩ := ab
  unfold CertCore.costPrep CertCore.costOf colCost tangentCost
  by_cases hc : c = 2
  · simp only [hc, ite_true]
    change (if v - b * (S / TS) ≤ 0 then 0 else (v - b * (S / TS)) * (v - b * (S / TS)) / D) =
      max (v - b * (S / TS)) 0 ^ 2 / D
    split_ifs with hx
    · rw [max_eq_right hx]
      simp
    · rw [max_eq_left (le_of_lt (not_le.mp hx)), sq]
  · simp only [hc, ite_false]
    change (if v - (a + b) * HS ≤ 0 then 0 else
        (if c = 0 then (v - (a + b) * HS) * (v - (a + b) * HS + 2 * ((b - a) * HS))
          else (v - (a + b) * HS) * (v - (a + b) * HS - 2 * ((b - a) * HS))) / S * S / D) =
      (if v - (a + b) * HS ≤ 0 then 0 else
        (if c = 0 then (v - (a + b) * HS) * (v - (a + b) * HS + 2 * ((b - a) * HS))
          else (v - (a + b) * HS) * (v - (a + b) * HS - 2 * ((b - a) * HS))) / S) * S / D
    split_ifs with hx
    · simp
    all_goals rfl

/-- The row-by-row accumulation of a column's dual-weighted costs is the sum of
`GradedNear.Cert.caseValue`. -/
theorem dotAcc_eq : ∀ (Z : List ℤ) (box : List (ℤ × ℤ)) (cs : List ℕ) (v D : List ℤ) (acc : ℤ),
    CertCore.dotAcc acc Z (List.zipWith CertCore.costPrep box cs) v D =
      acc + (List.zipWith (fun z c => z * c) Z
        (List.zipWith3 (fun ab vD c => colCost vD.1 vD.2 ab.1 ab.2 c) box (v.zip D) cs)).sum
  | [], _, _, _, _, acc => by simp [CertCore.dotAcc]
  | _ :: _, [], _, _, _, acc => by simp [CertCore.dotAcc, List.zipWith3]
  | _ :: _, _ :: _, [], _, _, acc => by simp [CertCore.dotAcc, List.zipWith3]
  | _ :: _, _ :: _, _ :: _, [], _, acc => by simp [CertCore.dotAcc, List.zipWith3]
  | _ :: _, _ :: _, _ :: _, _ :: _, [], acc => by simp [CertCore.dotAcc, List.zipWith3]
  | z :: Z, ab :: box, c :: cs, v :: vs, D :: Ds, acc => by
    simp only [List.zipWith_cons_cons, List.zip_cons_cons, List.zipWith3, CertCore.dotAcc,
      List.sum_cons]
    rw [dotAcc_eq Z box cs vs Ds, ← costOf_costPrep ab c v D]
    split_ifs with hz hc
    · rw [hz, zero_mul, zero_add]
    · rw [hc, mul_zero, zero_add]
    · rw [add_assoc]

/-- The row-by-row accumulation of the dual-weighted budgets is the sum of
`GradedNear.Cert.caseValue`. -/
theorem budgetAcc_eq : ∀ (Z : List ℤ) (rows : List RowHead) (box : List (ℤ × ℤ)) (cs : List ℕ)
    (acc : ℤ),
    CertCore.budgetAcc acc Z (rows.map RowHead.toCore) box cs =
      acc + (List.zipWith (fun z b => z * b) Z
        (List.zipWith3 (fun r ab c => rowBudget r ab.1 ab.2 c) rows box cs)).sum
  | [], _, _, _, acc => by simp [CertCore.budgetAcc]
  | _ :: _, [], _, _, acc => by simp [CertCore.budgetAcc, List.zipWith3]
  | _ :: _, _ :: _, [], _, acc => by simp [CertCore.budgetAcc, List.zipWith3]
  | _ :: _, _ :: _, _ :: _, [], acc => by simp [CertCore.budgetAcc, List.zipWith3]
  | z :: Z, r :: rows, ab :: box, c :: cs, acc => by
    simp only [List.map_cons, List.zipWith_cons_cons, List.zipWith3, CertCore.budgetAcc,
      List.sum_cons]
    rw [budgetAcc_eq Z rows box cs]
    split_ifs with hz
    · rw [hz, zero_mul, zero_add]
    · rw [add_assoc]
      rfl

theorem dotAcc_toCore (col : Col) (Z : List ℤ) (box : List (ℤ × ℤ)) (cs : List ℕ) (acc : ℤ) :
    CertCore.dotAcc acc Z (List.zipWith CertCore.costPrep box cs) col.toCore.v col.toCore.D =
      acc + (List.zipWith (fun z c => z * c) Z (colCosts col box cs)).sum :=
  dotAcc_eq Z box cs col.v col.D acc

theorem budgetAcc_toCore (L : Leaf) (Z : List ℤ) (box : List (ℤ × ℤ)) (cs : List ℕ) (acc : ℤ) :
    CertCore.budgetAcc acc Z L.toCore.rows box cs =
      acc + (List.zipWith (fun z b => z * b) Z (budgets L box cs)).sum :=
  budgetAcc_eq Z L.rows box cs acc

theorem caseValue_toCore (L : Leaf) (box : List (ℤ × ℤ)) (cs : List ℕ) (du : Duals) :
    CertCore.caseValue L.toCore box cs du.toCore = caseValue L box cs du := by
  unfold CertCore.caseValue caseValue
  simp only [bind_pure_cast, cols_all_toCore, rows_length_toCore, addMul_eq, dotAcc_toCore,
    budgetAcc_toCore]
  rfl

/-! ## Exclusion, case vectors and boxes -/

theorem excludable_toCore (L : Leaf) (box : List (ℤ × ℤ)) (cs : List ℕ) :
    CertCore.excludable L.toCore box cs = excludable L box cs := by
  unfold CertCore.excludable excludable
  simp only [rows_length_toCore, budgets_toCore, cols_all_toCore, colCosts_toCore]

theorem caseVectors_eq : ∀ os : List ℕ, CertCore.caseVectors os = caseVectors os
  | [] => rfl
  | o :: os => by
    simp only [CertCore.caseVectors, caseVectors, caseVectors_eq os]

theorem foldl_map_congr {α β γ : Type} (f : α → γ → α) (g : α → β → α) (h : β → γ)
    (hfg : ∀ a b, f a (h b) = g a b) (l : List β) (a : α) :
    List.foldl f a (l.map h) = List.foldl g a l := by
  rw [List.foldl_map]
  congr 1
  funext a b
  exact hfg a b

theorem checkBox_toCore (L : Leaf) (box : List (ℤ × ℤ)) (orders : List ℕ)
    (certs : List CaseCert) :
    CertCore.checkBox L.toCore box orders (certs.map CaseCert.toCore) =
      checkBox L box orders certs := by
  unfold CertCore.checkBox checkBox
  simp only [caseVectors_eq, rows_length_toCore, List.length_map, List.zip_map_right]
  split_ifs with h
  · apply foldl_map_congr
    rintro acc ⟨cv, cert⟩
    cases cert with
    | excluded => simp only [Prod.map_apply, id, CaseCert.toCore, excludable_toCore]
    | duals du => simp only [Prod.map_apply, id, CaseCert.toCore, caseValue_toCore]
  · rfl

/-! ## Trees and leaves -/

theorem verifyTree_toCore (L : Leaf) (T : Tree) :
    ∀ box : List (ℤ × ℤ), CertCore.verifyTree L.toCore T.toCore box = verifyTree L T box := by
  induction T with
  | split k mid l r ihl ihr =>
    intro box
    simp only [Tree.toCore, CertCore.verifyTree, verifyTree, ihl, ihr]
    rfl
  | node orders certs =>
    intro box
    simp only [Tree.toCore, CertCore.verifyTree, verifyTree, checkBox_toCore]
    rfl

theorem rows_all_toCore (L : Leaf) (p : CertCore.RowHead → Bool) :
    L.toCore.rows.all p = L.rows.all (fun r => p r.toCore) :=
  List.all_map

theorem wellFormed_toCore (L : Leaf) : CertCore.wellFormed L.toCore = wellFormed L := by
  unfold CertCore.wellFormed wellFormed
  simp only [cols_all_toCore, rows_all_toCore, rows_length_toCore]
  rfl

theorem rootBox_toCore (L : Leaf) : CertCore.rootBox L.toCore = rootBox L := by
  unfold CertCore.rootBox rootBox
  simp only [Leaf.toCore, List.map_map]
  rfl

theorem toCore_ofCore_cols (l : List CertCore.Col) : (l.map Col.ofCore).map Col.toCore = l := by
  rw [List.map_map]
  exact List.map_id'' (fun _ => rfl) l

theorem toCore_ofCore_rows (l : List CertCore.RowHead) :
    (l.map RowHead.ofCore).map RowHead.toCore = l := by
  rw [List.map_map]
  exact List.map_id'' (fun _ => rfl) l

theorem toCore_ofCore_certs (l : List CertCore.CaseCert) :
    (l.map CaseCert.ofCore).map CaseCert.toCore = l := by
  rw [List.map_map]
  refine List.map_id'' (fun c => ?_) l
  cases c <;> rfl

end FastEq

open FastEq

theorem Leaf.toCore_ofCore (L : CertCore.Leaf) : (Leaf.ofCore L).toCore = L := by
  simp only [Leaf.ofCore, Leaf.toCore, toCore_ofCore_cols, toCore_ofCore_rows]

theorem Tree.toCore_ofCore (T : CertCore.Tree) : (Tree.ofCore T).toCore = T := by
  induction T with
  | split k mid l r ihl ihr => simp only [Tree.ofCore, Tree.toCore, ihl, ihr]
  | node orders certs => simp only [Tree.ofCore, Tree.toCore, toCore_ofCore_certs]

/-- **The compiled checker computes the verified one.** On a leaf and a tree converted field by
field, `CertCore.checkLeaf` (Lean core only, compiled by `lake build certrun`) returns exactly
`GradedNear.Cert.checkLeaf`, whose soundness is `checkLeaf_sound`. -/
theorem checkLeaf_toCore (L : Leaf) (T : Tree) :
    CertCore.checkLeaf L.toCore T.toCore = checkLeaf L T := by
  unfold CertCore.checkLeaf checkLeaf
  rw [wellFormed_toCore, rootBox_toCore, verifyTree_toCore]

/-- The same for every input of `CertCore.checkLeaf`: it is `checkLeaf` on the converted data. -/
theorem checkLeaf_ofCore (L : CertCore.Leaf) (T : CertCore.Tree) :
    CertCore.checkLeaf L T = checkLeaf (Leaf.ofCore L) (Tree.ofCore T) := by
  rw [← checkLeaf_toCore, Leaf.toCore_ofCore, Tree.toCore_ofCore]

end GradedNear.Cert
