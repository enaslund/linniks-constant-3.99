module

/-!
# Leaf metadata (Mathlib-free)

The metadata that `computations/graded/graded_lean_export.py --numerics` in the research repository exports for each leaf, in
the form the native numeric checker reads (`research/notes/leaf-data-semantics-2026-09-29.md` in the research repository).
Its meaning, the real-valued predicate `GradedNear.Cert.MetaValid`, is in
`GradedNear/Cert/NumericsSpec.lean`.
-/

@[expose] public section

namespace LeafMetaCore

/-- A column's objective function. -/
inductive Obj where
  /-- `λ ↦ e^{−(L−2T)λ} B_φ(λ)`: ordinary bins (`φ = 1/3`), second-family columns (`φ₂`). -/
  | G (φ : Rat)
  /-- `t ↦ e^{−(L−2T)t} B_φ(p)`: hidden columns of an outside leaf. -/
  | hidden (φ p : Rat)
  deriving Repr, Inhabited, BEq

/-- A column's parameter range: a bin `[lo, hi]` or a tail `[R, ∞)`. -/
inductive Span where
  | bin (lo hi : Rat)
  | tail (R : Rat)
  deriving Repr, Inhabited, BEq

/-- The meaning of one column. -/
structure ColMeta where
  span : Span
  obj : Obj
  deriving Repr, Inhabited, BEq

/-- A far profile: `c₁`, `c₂`, `θ` and the ten weights `α_i`. -/
structure Profile where
  c₁ : Rat
  c₂ : Rat
  θ : Rat
  α : List Rat
  deriving Repr, Inhabited, BEq

/-- The inside first family's charge: `n`, `α`, `φ_t`, `a`, `p`, and whether `J_new` applies, in
which case the charge is `min(J_old, J_new)`. The family is the case's `[a, b]`; its right end `b`
is the one of the far budget's inside family `farInside = (n, b)` (the same family). `J_new`
applies only when `p ≥ b`: for `useJnew = true` the numeric checker requires
`farInside = some (n, b)` with the same `n` and `b ≤ p` (`LeafCheckCore.jnewOk`,
`GradedNear.Cert.checkNum_jnew`). -/
structure FirstInside where
  n : Nat
  α : Nat
  φ : Rat
  a : Rat
  p : Rat
  useJnew : Bool
  deriving Repr, Inhabited, BEq

/-- A reserved family charged in `first` rather than in columns: `n₂ G_{φ₂}(lo₂)`. -/
structure Reserved where
  n₂ : Nat
  φ₂ : Rat
  lo₂ : Rat
  hi₂ : Rat
  deriving Repr, Inhabited, BEq

/-- All metadata of one leaf. -/
structure LeafMeta where
  /-- The exponent `L`. -/
  L : Rat
  /-- The far tolerance `η` of the budget `⌈(1+η)V⌉`. -/
  eta : Rat
  prof : Profile
  cols : List ColMeta
  /-- The inside first family `(n, b)` subtracted from the far budget, if any. -/
  farInside : Option (Nat × Rat)
  /-- The inside first family's charge in `first`, if any. -/
  firstInside : Option FirstInside
  /-- A reserved family charged without columns (in `first` and in the far budget), if any. -/
  reserved : Option Reserved
  deriving Repr, Inhabited

end LeafMetaCore
