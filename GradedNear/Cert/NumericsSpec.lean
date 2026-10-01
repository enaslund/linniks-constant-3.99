module

public import LeafMetaCore
public import GradedNear.Functions
public import GradedNear.Cert.Semantics

/-!
# What a leaf's numbers must satisfy (paper §§5–6, 10)

`MetaValid m L` states that the integer data of the leaf `L` are valid for its metadata
`m` (`LeafMetaCore`, exported by `graded_lean_export.py --numerics`). This is the real-valued
content of the leaf builders' interval enclosures (`research/notes/leaf-data-semantics-2026-09-29.md` in the research repository):
* **every column** is valid for its meaning (`ColSem.Valid`). A bin `[lo, hi]` needs
  `G_c ≥ S·g(lo)` and `W_c ≤ S·w(hi)`; a tail `[R, ∞)` needs `G_c ≥ S·g(R)/w(R)` and `W_c ≤ S`.
  Here `g` is the column's objective (`G_φ`, or `t ↦ e^{−At} B_φ(p)` for hidden columns) and `w`
  is the leaf's far weight;
* **the far budget** `F ≥ S·[(1 + η/2)V − n·w(b) − n₂·w(hi₂)]`, with the inside first family and a
  reserved family charged without columns. The far lemma is applied with `η/2` (it holds for every
  tolerance), which leaves the budget's own `η` as slack;
* **the first-family charge** `first ≥ S·[J + n₂ G_{φ₂}(lo₂)]`, where `J = J_old`, or
  `min(J_old, J_new)` when `J_new` applies, and the reserved term appears only when the family is
  charged without columns.

These are the hypotheses on the leaf data in `Cert.leaf_interpretation` and
`GradedNear.certified_leaf_gives_prime`.
-/

@[expose] public section

noncomputable section

namespace GradedNear.Cert

open Kernel LeafMetaCore

/-- The real objective function of a column at exponent `L`. -/
def objFun (L : ℝ) : Obj → ℝ → ℝ
  | .G φ => Gphi L φ
  | .hidden φ p => fun t => Real.exp (-((L - 2 * T) * t)) * Benv φ p

/-- The meaning of a column's metadata. -/
def colSem (L : ℝ) (c : ColMeta) : ColSem :=
  match c.span with
  | .bin lo hi => .bin lo hi (objFun L c.obj)
  | .tail R => .tail R (objFun L c.obj)

/-- The far profile named by the metadata. -/
def profileFar (P : LeafMetaCore.Profile) : FarProfile :=
  ⟨P.c₁, P.c₂, P.θ, fun i => P.α.getD i 0⟩

/-- The inside first family's charge: `J_old`, or `min(J_old, J_new)` when `J_new` applies. -/
def firstInsideCharge (L : ℝ) (f : FirstInside) : ℝ :=
  if f.useJnew then
    min (Jold L f.n f.α f.φ f.a f.p) (Jnew L f.n f.α f.φ f.a f.p)
  else Jold L f.n f.α f.φ f.a f.p

/-- The far weights subtracted from the far budget: the inside first family `n·w(b)` and a
reserved family charged without columns `n₂·w(hi₂)`. -/
def farReserved (m : LeafMeta) : ℝ :=
  (match m.farInside with
    | some (n, b) => (n : ℝ) * (profileFar m.prof).w b
    | none => 0) +
  (match m.reserved with
    | some r => (r.n₂ : ℝ) * (profileFar m.prof).w r.hi₂
    | none => 0)

/-- The first-family charge: the inside family's `J`, plus a reserved family charged without
columns, `n₂ G_{φ₂}(lo₂)`. -/
def firstCharge (m : LeafMeta) : ℝ :=
  (match m.firstInside with
    | some f => firstInsideCharge m.L f
    | none => 0) +
  (match m.reserved with
    | some r => (r.n₂ : ℝ) * Gphi m.L r.φ₂ r.lo₂
    | none => 0)

/-- **The leaf's numbers are valid for its metadata** (see the module docstring). -/
structure MetaValid (m : LeafMeta) (L : Leaf) : Prop where
  length : m.cols.length = L.cols.length
  cols : ∀ c : Fin L.cols.length,
    (colSem m.L (m.cols.getD c default)).Valid (profileFar m.prof).w (L.cols.get c)
  far : (S : ℝ) * ((1 + m.eta / 2) * (profileFar m.prof).V - farReserved m) ≤ L.F
  first : (S : ℝ) * firstCharge m ≤ L.first

end GradedNear.Cert
