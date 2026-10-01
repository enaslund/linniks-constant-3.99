module

/-!
# The leaf-certificate checker, without Mathlib

A copy of the checker `GradedNear.Cert.checkLeaf` (`GradedNear/Defs.lean`, section "Exact
certificates for the leaf LPs") that depends on Lean core only, so that it can be compiled to a
native executable (`CertRunNative.lean`, `lake build certrun`) without compiling Mathlib.

The definitions are those of `GradedNear.Defs`, with `Int`, `Nat`, core `Rat` and core `List`
functions. The pieces that `GradedNear.Defs` takes from Mathlib are replaced:
* `List.zipWith3` is `CertCore.zipWith3` (the same recursion);
* the ceiling `⌈·⌉ : ℚ → ℤ` is `ratCeil q = -Rat.floor (-q)`, which is how Mathlib's
  `FloorRing ℚ` instance defines it.

The one function computed differently is `caseValue`, the dual check of a case, where almost all
the time goes (every column, every case, every box). Instead of building the list of costs of a
column and summing its products with the duals `Z`, it accumulates the sum row by row
(`dotAcc`), skipping rows whose dual or cost is `0`, with the per-row constants of the costs
computed once per case (`costPrep`, `costOf`); the products of the duals `V`, `U`, `P - M` with
zero column coefficients are skipped too (`addMul`), and the budgets are computed only for rows
with a nonzero dual (`budgetAcc`). The casts of the duals to `Int` are done once per case. The
results are the same integers, by `0 * x = 0`, `x + 0 = x`, the associativity of `+`,
`x ^ 2 = x * x` and `max y 0 = y` for `y > 0`.

`GradedNear.Cert.checkLeaf_toCore` and `GradedNear.Cert.checkLeaf_ofCore`
(`GradedNear/Cert/FastEq.lean`) prove that `CertCore.checkLeaf` computes exactly
`GradedNear.Cert.checkLeaf` on the data converted field by field, so the soundness theorem
`GradedNear.Cert.checkLeaf_sound` applies to the values computed by the compiled checker.
-/

@[expose] public section

namespace CertCore

/-- Input scale. -/
def S : Int := 10 ^ 16
/-- Threshold ticks per unit. -/
def TS : Int := 10 ^ 6
/-- Dual scale. -/
def DS : Int := 10 ^ 12
/-- Half a threshold tick in input units, `S / TS / 2`. -/
def HS : Int := 5 * 10 ^ 9

/-- A column: objective, far weight, count cost, hidden-count cost, second-family indicator,
and per-row feature and diagonal. -/
structure Col where
  G : Int
  W : Int
  C : Int
  NH : Int
  E : Int
  v : List Int
  D : List Int
deriving Repr

/-- A near row: its radius `d` and its fixed family terms `(n, v, D)`. -/
structure RowHead where
  d : Int
  fam : List (Int × Int × Int)
deriving Repr

/-- The integer data of a leaf. -/
structure Leaf where
  cols : List Col
  rows : List RowHead
  F : Int
  ng : Int
  n2 : Int
  first : Int
  final : Int
deriving Repr

/-! ## The checker -/

/-- Ternary `List.zipWith` (Mathlib's `List.zipWith3`). -/
def zipWith3 {α β γ δ : Type} (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | x :: xs, y :: ys, z :: zs => f x y z :: zipWith3 f xs ys zs
  | _, _, _ => []

/-- The ceiling of a rational number (Mathlib's `⌈·⌉` on `ℚ`). -/
def ratCeil (q : Rat) : Int := -Rat.floor (-q)

/-- `⌈√n⌉`. -/
def isqrtUp (n : Nat) : Nat := if Nat.sqrt n * Nat.sqrt n = n then Nat.sqrt n else Nat.sqrt n + 1

/-- The end (in ticks) of the root threshold box of a row of radius `d`. -/
def rootEnd (d : Int) : Int := (isqrtUp ((d * TS * TS / S).toNat + 1) : Int)

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

/-- The tangent-case cost of a feature `v` on a box of midpoint `m2/2` and half-width `h2/2`
ticks: `((v - m)₊ ± h)² - h²`, floored at scale `S`. -/
def tangentCost (v m2 h2 : Int) (c : Nat) : Int :=
  let x := v - m2 * HS
  if x ≤ 0 then 0 else
    let hS := h2 * HS
    (if c = 0 then x * (x + 2 * hS) else x * (x - 2 * hS)) / S

/-- The exact tangent-case family term `((v - m)₊ ± h)² - h²`. -/
def tangentExact (v m h : Rat) (c : Nat) : Rat :=
  let x := max (v - m) 0
  if c = 0 then (x + h) ^ 2 - h ^ 2 else if 0 < x then (x - h) ^ 2 - h ^ 2 else 0

/-- The cost of a column in a row on the box interval `[a, b]` (ticks), for case `c`
(`2` first-order; `0`, `1` tangent). -/
def colCost (v D a b : Int) (c : Nat) : Int :=
  if c = 2 then (max (v - b * (S / TS)) 0) ^ 2 / D
  else (tangentCost v (a + b) (b - a) c * S) / D

/-- The budget of a row on the box interval `[a, b]` for case `c`. -/
def rowBudget (r : RowHead) (a b : Int) (c : Nat) : Int :=
  if c = 2 then
    S - (S * S * a * a) / (TS * TS * r.d) -
      (r.fam.map (fun t => (t.1 * (max (t.2.1 - b * (S / TS)) 0) ^ 2) / t.2.2)).sum
  else
    let p : Rat := (if c = 0 then (a : Rat) else (b : Rat)) / (TS : Rat)
    let hq : Rat := ((b - a : Int) : Rat) / (2 * (TS : Rat))
    let bq : Rat := 1 - (p ^ 2 - hq ^ 2) / ((r.d : Rat) / (S : Rat)) -
      (r.fam.map (fun t => (t.1 : Rat) * tangentExact ((t.2.1 : Rat) / (S : Rat))
        (((a + b : Int) : Rat) / (2 * (TS : Rat))) hq c / ((t.2.2 : Rat) / (S : Rat)))).sum
    ratCeil (bq * (S : Rat))

/-- The costs of a column in every row, for a box and a case vector. -/
def colCosts (col : Col) (box : List (Int × Int)) (cs : List Nat) : List Int :=
  zipWith3 (fun ab vD c => colCost vD.1 vD.2 ab.1 ab.2 c) box (col.v.zip col.D) cs

/-- The budgets of every row, for a box and a case vector. -/
def budgets (L : Leaf) (box : List (Int × Int)) (cs : List Nat) : List Int :=
  zipWith3 (fun r ab c => rowBudget r ab.1 ab.2 c) L.rows box cs

/-- Nonnegative integer duals: far `Y`, count `V`, hidden count `U`, the free dual `P - M` of the
second-family equality, and one multiplier per near row. -/
structure Duals where
  Y : Nat
  V : Nat
  U : Nat
  P : Nat
  M : Nat
  Z : List Nat
deriving Repr

/-- The certificate of one case. -/
inductive CaseCert where
  | excluded
  | duals (du : Duals)
deriving Repr

/-! ### The dual check of a case, computed row by row -/

/-- `acc + x * y`, skipping the product when `x` or `y` is `0`. -/
def addMul (acc x y : Int) : Int :=
  if x = 0 then acc else if y = 0 then acc else acc + x * y

/-- The constants of the column costs of a row on the box interval `[a, b]` for case `c`: the
case, the shift `m` (`b·S/TS` for `c = 2`, `(a + b)·HS` otherwise) and, for the tangent cases,
`h = 2(b - a)·HS`. -/
structure CostPrep where
  c : Nat
  m : Int
  h : Int

/-- The constants of the column costs of a row (see `CostPrep`). -/
def costPrep (ab : Int × Int) (c : Nat) : CostPrep :=
  if c = 2 then ⟨c, ab.2 * (S / TS), 0⟩ else ⟨c, (ab.1 + ab.2) * HS, 2 * ((ab.2 - ab.1) * HS)⟩

/-- The cost of a column with feature `v` and diagonal `D` in a row with constants `p`; it is
`colCost v D a b c` for `p = costPrep (a, b) c`. -/
def costOf (p : CostPrep) (v D : Int) : Int :=
  let x := v - p.m
  if x ≤ 0 then 0
  else if p.c = 2 then x * x / D
  else (if p.c = 0 then x * (x + p.h) else x * (x - p.h)) / S * S / D

/-- `acc + Σ_k z_k · cost_k` for a column with features `vs` and diagonals `Ds`, the duals `zs` and
the row constants `ps`, skipping the rows whose dual or cost is `0`. -/
def dotAcc (acc : Int) : List Int → List CostPrep → List Int → List Int → Int
  | z :: zs, p :: ps, v :: vs, D :: Ds =>
    dotAcc (if z = 0 then acc else
      let c := costOf p v D
      if c = 0 then acc else acc + z * c) zs ps vs Ds
  | _, _, _, _ => acc

/-- `acc + Σ_k z_k · budget_k`, computing the budgets of the rows with a nonzero dual only. -/
def budgetAcc (acc : Int) : List Int → List RowHead → List (Int × Int) → List Nat → Int
  | z :: zs, r :: rs, ab :: box, c :: cs =>
    budgetAcc (if z = 0 then acc else acc + z * rowBudget r ab.1 ab.2 c) zs rs box cs
  | _, _, _, _ => acc

/-- The value certified by duals for one case (`none` if a column inequality fails). This is
`GradedNear.Cert.caseValue`: the column inequality
`DS·G ≤ Y W + V C + U NH + (P - M) E + Σ_k Z_k cost_k` and the value
`⌈(Y F + 2 V S + U ng S + (P - M) n₂ S + Σ_k Z_k budget_k) / DS⌉ + first + final`, computed
row by row (`addMul`, `dotAcc`, `budgetAcc`). -/
def caseValue (L : Leaf) (box : List (Int × Int)) (cs : List Nat) (du : Duals) : Option Int :=
  let Z : List Int := du.Z.map Int.ofNat
  let Y : Int := du.Y
  let V : Int := du.V
  let U : Int := du.U
  let PM : Int := (du.P : Int) - du.M
  let ps := List.zipWith costPrep box cs
  if du.Z.length = L.rows.length ∧
      L.cols.all (fun col => decide (DS * col.G ≤
        dotAcc (addMul (addMul (addMul (Y * col.W) V col.C) U col.NH) PM col.E) Z ps col.v
          col.D)) then
    some (ceilDiv (budgetAcc (Y * L.F + V * (2 * S) + U * (L.ng * S) + PM * (L.n2 * S)) Z L.rows
      box cs) DS + L.first + L.final)
  else none

/-- A case may be excluded if some row has all column costs `≥ 0` and a negative budget. -/
def excludable (L : Leaf) (box : List (Int × Int)) (cs : List Nat) : Bool :=
  (List.range L.rows.length).any fun k =>
    decide ((budgets L box cs).getD k 0 < 0) &&
      L.cols.all fun col => decide (0 ≤ (colCosts col box cs).getD k 0)

/-- All case vectors for the given orders: `{0, 1}` for order 1, `{2}` otherwise. -/
def caseVectors : List Nat → List (List Nat)
  | [] => [[]]
  | o :: os =>
    let rest := caseVectors os
    if o = 1 then rest.map (0 :: ·) ++ rest.map (1 :: ·) else rest.map (2 :: ·)

/-- The value of a tree node's box: the maximum over its cases (`-1` if all are excluded). -/
def checkBox (L : Leaf) (box : List (Int × Int)) (orders : List Nat) (certs : List CaseCert) :
    Option Int :=
  let cvs := caseVectors orders
  if orders.length = L.rows.length ∧ certs.length = cvs.length ∧
      orders.all (fun o => o = 1 ∨ o = 2) then
    (List.zip cvs certs).foldl (fun acc cc =>
      acc.bind fun m =>
        match cc.2 with
        | .excluded => if excludable L box cc.1 then some m else none
        | .duals du => (caseValue L box cc.1 du).map (max m)) (some (-1))
  else none

/-- A certificate tree: a bisection of dimension `k` at tick `mid`, or a node with its orders
and case certificates. -/
inductive Tree where
  | split (k : Nat) (mid : Int) (left right : Tree)
  | node (orders : List Nat) (certs : List CaseCert)
deriving Repr

/-- Checks a tree on a box; returns the maximum certified value, each node's value `< S`. -/
def verifyTree (L : Leaf) : Tree → List (Int × Int) → Option Int
  | .split k mid l r, box =>
    match box[k]? with
    | some (a, b) =>
      if a < mid ∧ mid < b then
        (verifyTree L l (box.set k (a, mid))).bind fun m₁ =>
          (verifyTree L r (box.set k (mid, b))).map (max m₁)
      else none
    | none => none
  | .node orders certs, box =>
    (checkBox L box orders certs).bind fun v => if v < S then some v else none

/-- Well-formedness: every column has one feature and one diagonal per row, all diagonals,
radii and family diagonals are positive, and family counts are nonnegative. -/
def wellFormed (L : Leaf) : Bool :=
  L.cols.all (fun col => col.v.length = L.rows.length && col.D.length = L.rows.length &&
    col.D.all (fun x => decide (0 < x))) &&
  L.rows.all (fun r => decide (0 < r.d) &&
    r.fam.all (fun t => decide (0 ≤ t.1) && decide (0 < t.2.2)))

/-- The root box `∏_k [0, end_k]`. -/
def rootBox (L : Leaf) : List (Int × Int) := L.rows.map fun r => (0, rootEnd r.d)

/-- The checker: `some v` certifies that the leaf LP's objective is at most `v` (scaled by `S`)
at every feasible point (`GradedNear.Cert.checkLeaf_sound`, through
`GradedNear.Cert.checkLeaf_ofCore`). -/
def checkLeaf (L : Leaf) (T : Tree) : Option Int :=
  if wellFormed L then verifyTree L T (rootBox L) else none

end CertCore
