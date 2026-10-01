module

public import CertCore
public import LeafMetaCore
public import LeafNumCore
public import Std.Data.HashMap

/-!
# The numeric checker of a leaf's data, without Mathlib

`checkNum m L` checks that the integer data of the leaf `L` (`CertCore.Leaf`) are valid for its
metadata `m` (`LeafMetaCore.LeafMeta`, exported by `graded_lean_export.py --numerics`), by
rational comparisons against the verified enclosures of `LeafNumCore` (precision `128`):

* every column: a bin `[lo, hi]` with objective `g` needs `S·(g(lo)).hi ≤ G` and
  `W ≤ S·(w(hi)).lo`; a tail `[R, ∞)` needs `S·(g(R)·w⁻¹(R)).hi ≤ G` (as `g/w = g·w⁻¹`) and
  `W ≤ S`. The objective `g` is `G_φ` (`gphi`) or, for a hidden column, `t ↦ e^{−At} B_φ(p)`;
* the far budget: `S·((1 + η/2)·vUpper − n·(w(b)).lo − n₂·(w(hi₂)).lo) ≤ F`;
* the first-family charge: `S·(J + n₂·(G_{φ₂}(lo₂)).hi) ≤ first`, with `J = (J_old).hi`, or
  `min((J_old).hi, (J_new).hi)` when `J_new` applies;
* where `J_new` applies: the charged family is the far budget's inside family `[a, b]`
  (`farInside = (n, b)` with the same `n`) and `b ≤ p` (`jnewOk`; `GradedNear.Cert.checkNum_jnew`);
* the side conditions of the enclosures' soundness (`λ ≠ 0` for `B_φ`, `a, p ≠ 0` for the
  first-family bounds, `c₁, c₂ > 0` for the far weight), which are checked as positivity, together
  with `φ ≥ 0`, `η > 0`, `L ≥ 3.99`, ten weights `α_i`, and a far profile equal to one of the two
  corpus profiles (`LeafNumCore.inherited`, `LeafNumCore.retuned`).

The soundness theorem `GradedNear.Cert.checkNum_sound` (`GradedNear/Cert/NumericsSound.lean`)
turns `checkNum m L = true` into `GradedNear.Cert.MetaValid m (Leaf.ofCore L)`.

**Memoization.** The bin ends lie on grids shared between columns (the hidden columns of an
outside leaf use the ordinary grid, the last bin ends at the tail's `R`), and the hidden columns
share one `B_φ(p)`. Each distinct `(φ, λ)` of `G_φ`, `(φ, p)` of `B_φ` and `λ` of `w⁻¹` is
evaluated once per leaf into a hash table (`memo`); a lookup (`look`) falls back to evaluating
the function, so `look f (memo f ks) k = f k` for every key (`GradedNear.Cert.look_memo`).
-/

@[expose] public section

namespace LeafMetaCore.Obj

/-- The `φ` of a column's objective. -/
def phi : LeafMetaCore.Obj → Rat
  | .G φ => φ
  | .hidden φ _ => φ

end LeafMetaCore.Obj

namespace LeafCheckCore

open IntervalCore LeafMetaCore

/-- The precision of the enclosures (`LeafNumCore`'s default, `128`). -/
def prec : Nat := defaultPrec

/-- The input scale `S = 10¹⁶` as a rational. -/
def Sq : Rat := ((CertCore.S : Int) : Rat)

/-! ## Memoized evaluation -/

/-- A table of the values of `f` at the keys `ks`, each distinct key evaluated once. -/
def memo {α : Type} [BEq α] [Hashable α] (f : α → Ival) (ks : List α) : Std.HashMap α Ival :=
  ks.foldl (fun t k => if t.contains k then t else t.insert k (f k)) {}

/-- `f k`, read from the table `t` when it has the key `k`. -/
def look {α : Type} [BEq α] [Hashable α] (f : α → Ival) (t : Std.HashMap α Ival) (k : α) :
    Ival :=
  match t[k]? with
  | some v => v
  | none => f k

/-! ## The functions evaluated -/

/-- `G_φ(λ)` at the key `(φ, λ)`. -/
def gphiAt (L : Rat) (k : Rat × Rat) : Ival := LeafNumCore.gphi L k.1 k.2 prec

/-- `B_φ(p)` at the key `(φ, p)`. -/
def benvAt (k : Rat × Rat) : Ival := LeafNumCore.benv k.1 k.2 prec

/-- `w(λ)⁻¹` for the profile `P`. -/
def winvAt (P : LeafMetaCore.Profile) (lam : Rat) : Ival := LeafNumCore.winv P.c₁ P.c₂ P.θ lam prec

/-- The lower end of `LeafNumCore.w` computed from the enclosure `I` of `w(λ)⁻¹`. -/
def wLoOf (I : Ival) : Rat := if 0 < I.lo then roundDown prec I.hi⁻¹ else 0

/-- The left end of a span (where the objective is charged): `lo` or `R`. -/
def spanLeft : Span → Rat
  | .bin lo _ => lo
  | .tail R => R

/-- The right end of a span (where the far weight is evaluated): `hi` or `R`. -/
def spanRight : Span → Rat
  | .bin _ hi => hi
  | .tail R => R

/-- The keys `(φ, λ)` of `G_φ`: the columns with objective `G_φ`, and a reserved family. -/
def gKeys (m : LeafMeta) : List (Rat × Rat) :=
  m.cols.filterMap (fun c => match c.obj with
    | .G φ => some (φ, spanLeft c.span)
    | .hidden _ _ => none) ++
  (match m.reserved with
    | some r => [(r.φ₂, r.lo₂)]
    | none => [])

/-- The keys `(φ, p)` of `B_φ`: the hidden columns. -/
def bKeys (m : LeafMeta) : List (Rat × Rat) :=
  m.cols.filterMap (fun c => match c.obj with
    | .G _ => none
    | .hidden φ p => some (φ, p))

/-- The points `λ` of `w⁻¹`: the right ends of the columns, `b` and `hi₂`. -/
def wKeys (m : LeafMeta) : List Rat :=
  m.cols.map (fun c => spanRight c.span) ++
  (match m.farInside with
    | some (_, b) => [b]
    | none => []) ++
  (match m.reserved with
    | some r => [r.hi₂]
    | none => [])

/-- The tables of one leaf. -/
structure Ctx where
  /-- The exponent `L`. -/
  L : Rat
  /-- The far profile. -/
  P : LeafMetaCore.Profile
  /-- `G_φ(λ)` at the keys `gKeys`. -/
  gt : Std.HashMap (Rat × Rat) Ival
  /-- `B_φ(p)` at the keys `bKeys`. -/
  bt : Std.HashMap (Rat × Rat) Ival
  /-- `w(λ)⁻¹` at the keys `wKeys`. -/
  wt : Std.HashMap Rat Ival

/-- The tables of the leaf with metadata `m`. -/
def mkCtx (m : LeafMeta) : Ctx :=
  ⟨m.L, m.prof, memo (gphiAt m.L) (gKeys m), memo benvAt (bKeys m), memo (winvAt m.prof) (wKeys m)⟩

namespace Ctx

variable (x : Ctx)

/-- `G_φ(λ)`. -/
def gAt (φ lam : Rat) : Ival := look (gphiAt x.L) x.gt (φ, lam)

/-- `B_φ(p)`. -/
def bAt (φ p : Rat) : Ival := look benvAt x.bt (φ, p)

/-- `w(λ)⁻¹`. -/
def winvL (lam : Rat) : Ival := look (winvAt x.P) x.wt lam

/-- A lower bound for `w(λ)`. -/
def wLo (lam : Rat) : Rat := wLoOf (x.winvL lam)

/-- The enclosure of a column's objective at `λ`: `G_φ(λ)`, or `e^{−(L−2T)t} B_φ(p)` for a
hidden column. -/
def objAt : Obj → Rat → Ival
  | .G φ, lam => x.gAt φ lam
  | .hidden φ p, t =>
    (LeafNumCore.expI (-((x.L - 2 * LeafNumCore.T) * t)) prec).mul (x.bAt φ p) prec

/-- One column's data against its meaning. -/
def colOk (c : ColMeta) (col : CertCore.Col) : Bool :=
  match c.span with
  | .bin lo hi =>
    decide (0 < lo) && decide (0 < hi) &&
      decide (Sq * (x.objAt c.obj lo).hi ≤ ((col.G : Int) : Rat)) &&
      decide (((col.W : Int) : Rat) ≤ Sq * x.wLo hi)
  | .tail R =>
    decide (0 < R) &&
      decide (Sq * ((x.objAt c.obj R).mul (x.winvL R) prec).hi ≤ ((col.G : Int) : Rat)) &&
      decide (col.W ≤ CertCore.S)

/-- The far weights subtracted from the budget, bounded below: `n·(w(b)).lo + n₂·(w(hi₂)).lo`. -/
def farLower (m : LeafMeta) : Rat :=
  (match m.farInside with
    | some (n, b) => (n : Rat) * x.wLo b
    | none => 0) +
  (match m.reserved with
    | some r => (r.n₂ : Rat) * x.wLo r.hi₂
    | none => 0)

/-- An upper bound for the first-family charge. -/
def firstUpper (m : LeafMeta) : Rat :=
  (match m.firstInside with
    | some f =>
      if f.useJnew then
        rmin (LeafNumCore.jold x.L f.n f.α f.φ f.a f.p prec).hi
          (LeafNumCore.jnew x.L f.n f.α f.φ f.a f.p prec).hi
      else (LeafNumCore.jold x.L f.n f.α f.φ f.a f.p prec).hi
    | none => 0) +
  (match m.reserved with
    | some r => (r.n₂ : Rat) * (x.gAt r.φ₂ r.lo₂).hi
    | none => 0)

end Ctx

/-! ## The checks -/

/-- The objective's parameters: `φ ≥ 0`, and `p > 0` for a hidden column. -/
def objOk : Obj → Bool
  | .G φ => decide (0 ≤ φ)
  | .hidden φ p => decide (0 ≤ φ) && decide (0 < p)

/-- The profile has the constants of `Q` (a corpus profile of `LeafNumCore`). -/
def sameProfile (P : LeafMetaCore.Profile) (Q : LeafNumCore.Profile) : Bool :=
  decide (P.c₁ = Q.c₁) && decide (P.c₂ = Q.c₂) && decide (P.θ = Q.θ) && decide (P.α = Q.α)

/-- The far profile: ten weights, `c₁, c₂ > 0`, and one of the two corpus profiles. -/
def profileOk (P : LeafMetaCore.Profile) : Bool :=
  decide (P.α.length = 10) && decide (0 < P.c₁) && decide (0 < P.c₂) &&
    (sameProfile P LeafNumCore.inherited || sameProfile P LeafNumCore.retuned)

/-- The first family's parameters: `a, p > 0`; a reserved family's `lo₂, hi₂ > 0`. -/
def firstParamsOk (m : LeafMeta) : Bool :=
  (match m.firstInside with
    | some f => decide (0 < f.a) && decide (0 < f.p)
    | none => true) &&
  (match m.reserved with
    | some r => decide (0 < r.lo₂) && decide (0 < r.hi₂)
    | none => true)

/-- Where `J_new` applies (`useJnew`), the charged family is the far budget's inside family
`[a, b]`: `farInside = some (n', b)` with `n' = n` and `b ≤ p`, the condition `p ≥ b` under
which `J_new` bounds the family's charge. -/
def jnewOk (m : LeafMeta) : Bool :=
  match m.firstInside with
  | some f =>
    if f.useJnew then
      match m.farInside with
      | some (n', b) => decide (n' = f.n) && decide (b ≤ f.p)
      | none => false
    else true
  | none => true

/-- The leaf-independent conditions on the metadata. -/
def metaOk (m : LeafMeta) : Bool :=
  decide (399 / 100 ≤ m.L) && decide (0 < m.eta) && profileOk m.prof && firstParamsOk m &&
    m.cols.all (fun c => objOk c.obj) && jnewOk m

/-- The far budget: `S·((1 + η/2)·vUpper − farLower) ≤ F`. -/
def farOk (x : Ctx) (m : LeafMeta) (F : Int) : Bool :=
  decide (Sq * ((1 + m.eta / 2) *
      LeafNumCore.vUpper m.prof.c₁ m.prof.c₂ m.prof.θ m.prof.α prec - x.farLower m) ≤ (F : Rat))

/-- The first-family charge: `S·firstUpper ≤ first`. -/
def firstOk (x : Ctx) (m : LeafMeta) (first : Int) : Bool :=
  decide (Sq * x.firstUpper m ≤ (first : Rat))

/-- Every column's data against its meaning. -/
def colsOk (x : Ctx) (m : LeafMeta) (L : CertCore.Leaf) : Bool :=
  (m.cols.zip L.cols).all (fun p => x.colOk p.1 p.2)

/-- **The numeric checker**: the data of `L` are valid for the metadata `m`
(`GradedNear.Cert.checkNum_sound`: every column, the far budget with `η/2`, the first-family
charge). It also checks what the leaf composition needs: a corpus far profile
(`checkNum_profile`), `φ ≥ 0` (`checkNum_phi`), `L ≥ 3.99` (`checkNum_L`), `η > 0`
(`checkNum_eta`), and, where `J_new` applies, that the charged family is the far budget's inside
family `(n, b)` with `b ≤ p` (`checkNum_jnew`). -/
def checkNum (m : LeafMeta) (L : CertCore.Leaf) : Bool :=
  decide (m.cols.length = L.cols.length) && metaOk m &&
    (let x := mkCtx m
     colsOk x m L && farOk x m L.F && firstOk x m L.first)

/-! ## Diagnostics (not verified: they only name the first failing check) -/

/-- The first failing check of `checkNum m L`, if any (for reports). -/
def diagnose (m : LeafMeta) (L : CertCore.Leaf) : Option String :=
  if m.cols.length ≠ L.cols.length then some "columns:length"
  else if !decide (399 / 100 ≤ m.L) then some "L"
  else if !decide (0 < m.eta) then some "eta"
  else if !profileOk m.prof then some "profile"
  else if !firstParamsOk m then some "first:params"
  else if !jnewOk m then some "first:jnew"
  else match (m.cols.map (fun c => objOk c.obj)).idxOf false with
  | i =>
    if i < m.cols.length then some s!"column:{i}:objective-params"
    else
      let x := mkCtx m
      let bad := ((m.cols.zip L.cols).map (fun p => x.colOk p.1 p.2)).idxOf false
      if bad < m.cols.length then some s!"column:{bad}"
      else if !farOk x m L.F then some "far"
      else if !firstOk x m L.first then some "first"
      else none

end LeafCheckCore
