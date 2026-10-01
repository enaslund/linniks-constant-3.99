module

public import LeafNumCore
public import CertCore

/-!
# The near-row checker, without Mathlib

`rowCheck` decides, in exact rational and interval arithmetic, that the stored integers of one
near row of a leaf (its radius `d`, and the feature `v` and diagonal `D` of each entry with a
positive feature) are valid for a concrete instance of the graded near lemma
(`GradedNear/Row.lean`). The row's parameters `RowP` are those of
`computations/sieve_near/sieve_inputs.py` in the research repository (`SieveNearTest`): the parabolic detector of width `2γ`,
the parabolic Gram test of width `2g₁`, the anchors `s ≥ s₁ ≥ 0`, and the sieve heights `h_k` on
`m` cells of `[t₀, 2γ)`. Each entry `Ent` names the entry's semantics: its feature is taken at
`hi` from the response anchor `anc`, its diagonal at the offset `del ≤ s - anc`, and `sp` names a
second kept zero, if any (`Spec`).

The checker computes, as the builders do:
* an upper bound `I_L ≥ I_B` (`ibUpper`), the upper Riemann sum with `nShort = 2000` cells on
  `[0, t₀)` and the `m` sieve cells, whose exponentials run along geometric sequences;
* enclosures of `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + e^{-2δt₀} Σ_k c_k ρ^k`, `ρ = e^{-2δ(2γ - t₀)/m}`
  (`dI`, Horner's rule), for the listed offsets;
* enclosures of `F(x) = 2γ Φ(2γ x)` (`fI`) for the listed feature points;
* for each entry, the values `(add, exc)` of its semantics (`specVals`): a lower bound for its
  second kept zero's term and an upper bound for its pair excess, from enclosures of
  `Re F(x + iy)` at complex points (`reFI`, with `cos` and `sin` from `cosSinI`) and of the
  exponential moment `E₂` (`e2I`);

and then chooses the normalizer `D_u` as the least value that the radius and every diagonal
allow (`duOf`), and checks every feature against it:
`(v + Sη)² I_L D_u ≤ S² (F(x) + add - 1/6)²` with `F(x) + add > 1/6`.

`Φ(u) = ∫₀¹ P(s) e^{-us} ds` is enclosed by its closed form for `|u| ≥ 1` and by its Taylor
polynomial of degree `< 40` with the remainder bound for `|u| < 1` (`phiI`, and `rePhiCI` at
complex points). The soundness theorems are `GradedNear.Row.rowCheck_sound`
(`GradedNear/Row/RowSound.lean`) and `GradedNear.Row.specVals_sound`
(`GradedNear/Row/SpecSound.lean`).

`checkRows` applies the check to every near row of a leaf (`CertCore.Leaf`) that has metadata
(`RowMeta`; the inherited two-test row has none): the entries are the columns with a positive
feature in the row, each of which must have a semantics, and the family terms with a positive
feature and a semantics. Every family term's diagonal must be positive.
-/

@[expose] public section

namespace RowCheckCore

open IntervalCore LeafNumCore

/-- The integer scale `S = 10¹⁶`. -/
def S : Int := 10 ^ 16

/-- The allowance `η = 10⁻⁶`. -/
def eta : Rat := 1 / 1000000

/-- The level margin `ε' = 1/2000`. -/
def epsLev : Rat := 1 / 2000

/-- The number of short cells of the Riemann sum on `[0, t₀)`. -/
def nShort : Nat := 2000

/-- The number of Taylor terms of `Φ` for `|u| < 1`. -/
def taylorN : Nat := 40

/-! ## The parabolic tests and `Φ` -/

/-- `P(u) = 1 - 5u² + 5u³ - u⁵`. -/
def P (u : Rat) : Rat := 1 - 5 * u ^ 2 + 5 * u ^ 3 - u ^ 5

/-- The parabolic test of width `c`: `P(t/c)` for `t ≤ c`, `0` beyond. -/
def fpar (c t : Rat) : Rat := if t ≤ c then P (t / c) else 0

/-- The moments `m_n = ∫₀¹ sⁿ P(s) ds`. -/
def mom (n : Nat) : Rat :=
  1 / ((n : Rat) + 1) - 5 / ((n : Rat) + 3) + 5 / ((n : Rat) + 4) - 1 / ((n : Rat) + 6)

/-- `Σ_{n<N} (-u)ⁿ m_n / n!` (exact). -/
def taylorQ (u : Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => taylorQ u n + (-u) ^ n / (fact n : Rat) * mom n

/-- The remainder bound `(5/12) |u|^N (N+1)/(N!·N)` of the Taylor polynomial. -/
def taylorRem (u : Rat) (N : Nat) : Rat :=
  5 / 12 * (rabs u ^ N * (((N + 1 : Nat) : Rat) / ((fact N : Rat) * (N : Rat))))

/-- An enclosure of `Φ(u)`: the closed form
`1/u - 10/u³ + 30/u⁴ - 120/u⁶ + e^{-u}(30/u⁴ + 120/u⁵ + 120/u⁶)` for `|u| ≥ 1`, the Taylor
polynomial with its remainder for `|u| < 1`. -/
def phiI (u : Rat) (prec : Nat := defaultPrec) : Ival :=
  if 1 ≤ rabs u then
    ((expI (-u) prec).mulRat (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6) prec).addRat
      (1 / u - 10 / u ^ 3 + 30 / u ^ 4 - 120 / u ^ 6) prec
  else
    let t := taylorQ u taylorN
    let r := taylorRem u taylorN
    ⟨roundDown prec (t - r), roundUp prec (t + r)⟩

/-- An enclosure of the transform `F_c(x) = c Φ(c x)` of the test of width `c` at a real `x`. -/
def fI (c x : Rat) (prec : Nat := defaultPrec) : Ival := (phiI (c * x) prec).mulRat c prec

/-! ## The row parameters -/

/-- The rational parameters of a near row (as `GradedNear.Row.Params`). -/
structure RowP where
  γ : Rat
  g1 : Rat
  t0 : Rat
  s : Rat
  s1 : Rat
  h : List Rat
  deriving Repr, Inhabited, BEq

namespace RowP

variable (p : RowP)

/-- The number of sieve cells. -/
def m : Nat := p.h.length

/-- The cell ends `t_k = t₀ + (2γ - t₀) k / m`. -/
def tk (k : Nat) : Rat := p.t0 + (2 * p.γ - p.t0) * k / p.m

/-- The sieve height of cell `k`. -/
def hk (k : Nat) : Rat := p.h.getD k 0

/-- The cell width `(2γ - t₀)/m`. -/
def dt : Rat := (2 * p.γ - p.t0) / p.m

/-- The conditions of `GradedNear.Row.Params.Good`. -/
def good : Bool :=
  decide (0 < p.γ) && decide (0 < p.g1) && decide (0 ≤ p.s1) && decide (p.s1 ≤ p.s) &&
    decide (1 / 3 + 2 * epsLev < p.t0) && decide (p.t0 < 2 * p.γ) && decide (p.t0 < 2 * p.g1) &&
    decide (0 < p.m) && p.h.all (fun x => decide (0 ≤ x))

/-- The coefficients `c_k = h_k (t_{k+1}² - t_k²) / (2 δ_k)` with `δ_k = (t_k - 1/3)/2 - ε'`. -/
def ck (k : Nat) : Rat :=
  p.hk k * (p.tk (k + 1) ^ 2 - p.tk k ^ 2) / (2 * ((p.tk k - 1 / 3) / 2 - epsLev))

end RowP

/-! ## The Riemann sum of `I_B` -/

/-- The short cells `j, j+1, …` of `[0, t₀)` (`n` in all), with `E ∋ e^{(2s-s₁) b_j}` and the ratio
`R ∋ e^{(2s-s₁) t₀/n}`: the upper bound of `Σ (t₀/n) e^{(2s-s₁)b_j} f(a_j)²/g(b_j)`, rounded up;
`none` if some `g(b_j) ≤ 0`. -/
def shortSum (p : RowP) (n : Nat) (R : Ival) (prec : Nat) :
    (fuel j : Nat) → (E : Ival) → (acc : Rat) → Option Rat
  | 0, _, _, acc => some acc
  | fuel + 1, j, E, acc =>
    let a := p.t0 * j / n
    let b := p.t0 * (j + 1) / n
    let gb := fpar (2 * p.g1) b
    if gb ≤ 0 then none
    else
      let f := fpar (2 * p.γ) a
      let term := roundUp prec (p.t0 / n * E.hi * (f * f) / gb)
      shortSum p n R prec fuel (j + 1) (E.mul R prec) (roundUp prec (acc + term))

/-- The sieve cells `k, k+1, …`, with `E1 ∋ e^{2s t_{k+1}}`, `E2 ∋ e^{s₁ t_k}` and the ratios
`R1 ∋ e^{2s Δt}`, `R2 ∋ e^{s₁ Δt}`: the upper bound of `Σ Δt e^{2s t_{k+1}} f(t_k)²/L_k` with the
lower bounds `L_k ≥ g(t_{k+1}) E2.lo + h_k`, rounded; `none` if some such bound is `≤ 0`. -/
def longSum (p : RowP) (R1 R2 : Ival) (prec : Nat) :
    (fuel k : Nat) → (E1 E2 : Ival) → (acc : Rat) → Option Rat
  | 0, _, _, _, acc => some acc
  | fuel + 1, k, E1, E2, acc =>
    let lo := roundDown prec (fpar (2 * p.g1) (p.tk (k + 1)) * E2.lo + p.hk k)
    if lo ≤ 0 then none
    else
      let f := fpar (2 * p.γ) (p.tk k)
      let term := roundUp prec ((p.tk (k + 1) - p.tk k) * E1.hi * (f * f) / lo)
      longSum p R1 R2 prec fuel (k + 1) (E1.mul R1 prec) (E2.mul R2 prec)
        (roundUp prec (acc + term))

/-- An upper bound `I_L ≥ I_B` of the row, or `none`. -/
def ibUpper (p : RowP) (prec : Nat := defaultPrec) : Option Rat := do
  let d := (2 * p.s - p.s1) * p.t0 / nShort
  let sh ← shortSum p nShort (expI d prec) prec nShort 0 (expI d prec) 0
  let lg ← longSum p (expI (2 * p.s * p.dt) prec) (expI (p.s1 * p.dt) prec) prec p.m 0
    (expI (2 * p.s * p.tk 1) prec) (expI (p.s1 * p.tk 0) prec) 0
  return roundUp prec (sh + lg)

/-! ## The diagonal `D(δ)` -/

/-- Horner's rule over a list of fixed-point coefficients: `Σ_i cs_i x^i` for `x ∈ X`. -/
def hornerL (X : Fx) (w : Nat) : List Fx → Fx
  | [] => ⟨0, 0⟩
  | c :: cs => (X.mul (hornerL X w cs) w).add c

/-- The coefficients `c_k` at scale `2^w`. -/
def ckFx (p : RowP) (w : Nat) : List Fx := (List.range p.m).map fun k => Fx.ofRat (p.ck k) w

/-- An enclosure of `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + e^{-2δt₀} Σ_k c_k ρ^k`, `ρ = e^{-2δΔt}`, from the
fixed-point coefficients `cs = ckFx p (prec + 16)`. -/
def dI (p : RowP) (cs : List Fx) (δ : Rat) (prec : Nat := defaultPrec) : Ival :=
  let w := prec + 16
  let G := fI (2 * p.g1) (2 * δ - p.s1) prec
  let E0 := expI (-(2 * δ * p.t0)) prec
  let R := Fx.ofIval (expI (-(2 * δ * p.dt)) prec) w
  G.add (E0.mul ((hornerL R w cs).toIval w) prec) prec

/-! ## Complex points -/

/-- A complex number with rational real and imaginary parts. -/
structure CQ where
  re : Rat
  im : Rat
  deriving Repr, Inhabited, BEq

namespace CQ

def add (a b : CQ) : CQ := ⟨a.re + b.re, a.im + b.im⟩
def mul (a b : CQ) : CQ := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def smul (q : Rat) (a : CQ) : CQ := ⟨q * a.re, q * a.im⟩
def neg (a : CQ) : CQ := ⟨-a.re, -a.im⟩
/-- `1/a` (for `a ≠ 0`; `0` for `a = 0`). -/
def inv (a : CQ) : CQ := ⟨a.re / (a.re * a.re + a.im * a.im), -a.im / (a.re * a.re + a.im * a.im)⟩
/-- `|a|²`. -/
def normSq (a : CQ) : Rat := a.re * a.re + a.im * a.im

/-- `aⁿ`. -/
def pow (a : CQ) : Nat → CQ
  | 0 => ⟨1, 0⟩
  | n + 1 => mul (pow a n) a

end CQ

/-! ## `cos` and `sin` -/

/-- `Σ_{m<N} (iy)^m/m!`, exactly: the state is `(m, term, sum)` with `term = (iy)^m/m!`. -/
def expITaylorAux (y : Rat) : (fuel m : Nat) → (term sum : CQ) → CQ
  | 0, _, _, sum => sum
  | fuel + 1, m, term, sum =>
    expITaylorAux y fuel (m + 1) (CQ.smul (1 / ((m + 1 : Nat) : Rat)) (CQ.mul term ⟨0, y⟩))
      (CQ.add sum term)

/-- `Σ_{m<N} (iy)^m/m!`. -/
def expITaylor (y : Rat) (N : Nat) : CQ := expITaylorAux y N 0 ⟨1, 0⟩ ⟨0, 0⟩

/-- The number of Taylor terms for `cos` and `sin`. -/
def trigN : Nat := 30

/-- The remainder bound `|y|^N (N+1)/(N!·N)`. -/
def trigRem (y : Rat) (N : Nat) : Rat :=
  rabs y ^ N * (((N + 1 : Nat) : Rat) / ((fact N : Rat) * (N : Rat)))

/-- The number of halvings `k` with `|q| / 2^k ≤ 1/2`. -/
def halvings (q : Rat) : Nat := (natCeil (rabs q)).log2 + 2

/-- Enclosures of `cos y` and `sin y` for `|y| ≤ 1`. -/
def cosSin0 (y : Rat) (prec : Nat) : Ival × Ival :=
  let t := expITaylor y trigN
  let r := trigRem y trigN
  (⟨roundDown prec (t.re - r), roundUp prec (t.re + r)⟩,
    ⟨roundDown prec (t.im - r), roundUp prec (t.im + r)⟩)

/-- `k` angle doublings `(C, S) ↦ (C² − S², 2CS)`. -/
def doubling (prec : Nat) : Nat → Ival × Ival → Ival × Ival
  | 0, cs => cs
  | k + 1, cs => doubling prec k (((cs.1.sqr prec).sub (cs.2.sqr prec) prec),
      ((cs.1.mul cs.2 prec).mulRat 2 prec))

/-- **Enclosures of `cos q` and `sin q`.** -/
def cosSinI (q : Rat) (prec : Nat := defaultPrec) : Ival × Ival :=
  let k := halvings q
  doubling prec k (cosSin0 (q / (2 ^ k : Nat)) prec)

/-! ## `Re ΦC` and `Re F` -/

/-- `Σ_{n<N} (−u)ⁿ m_n/n!`, exactly: the state is `(n, term, sum)` with `term = (−u)ⁿ/n!`. -/
def phiTaylorAux (u : CQ) : (fuel n : Nat) → (term sum : CQ) → CQ
  | 0, _, _, sum => sum
  | fuel + 1, n, term, sum =>
    phiTaylorAux u fuel (n + 1) (CQ.smul (1 / ((n + 1 : Nat) : Rat)) (CQ.mul term (CQ.neg u)))
      (CQ.add sum (CQ.smul (mom n) term))

/-- An enclosure of `Re ΦC(ur + i ui)`. -/
def rePhiCI (ur ui : Rat) (prec : Nat := defaultPrec) : Ival :=
  let u : CQ := ⟨ur, ui⟩
  if 1 ≤ u.normSq then
    let w := u.inv
    let w3 := w.pow 3
    let w4 := w.pow 4
    let w5 := w.pow 5
    let w6 := w.pow 6
    let Are := w.re - 10 * w3.re + 30 * w4.re - 120 * w6.re
    let B : CQ := ⟨30 * w4.re + 120 * w5.re + 120 * w6.re, 30 * w4.im + 120 * w5.im + 120 * w6.im⟩
    let cs := cosSinI ui prec
    let lin := ((cs.1.mulRat B.re prec).add (cs.2.mulRat B.im prec) prec)
    ((expI (-ur) prec).mul lin prec).addRat Are prec
  else
    let t := phiTaylorAux u taylorN 0 ⟨1, 0⟩ ⟨0, 0⟩
    -- `|u|^N (N+1)/(N!·N)` with `|u|^N = (|u|²)^{N/2}` (`N = 40` is even)
    let r : Rat := 5 / 12 * (u.normSq ^ (taylorN / 2) *
      (((taylorN + 1 : Nat) : Rat) / ((fact taylorN : Rat) * (taylorN : Rat))))
    ⟨roundDown prec (t.re - r), roundUp prec (t.re + r)⟩

/-- **An enclosure of `Re F_c(x + iy)`** for the parabolic test of width `c`. -/
def reFI (c x y : Rat) (prec : Nat := defaultPrec) : Ival :=
  (rePhiCI (c * x) (c * y) prec).mulRat c prec

/-! ## The exponential moment `E₂` -/

/-- `Σ_{j<N} αʲ m_{j+2}/j!`, exactly. -/
def e2TaylorAux (α : Rat) : (fuel j : Nat) → (term sum : Rat) → Rat
  | 0, _, _, sum => sum
  | fuel + 1, j, term, sum =>
    e2TaylorAux α fuel (j + 1) (term * α / ((j + 1 : Nat) : Rat)) (sum + term * mom (j + 2))

/-- **An enclosure of `E₂(α)`.** -/
def e2I (α : Rat) (prec : Nat := defaultPrec) : Ival :=
  if 1 ≤ rabs α then
    let A : Rat := 30 / α ^ 4 - 360 / α ^ 5 + 1920 / α ^ 6 - 5040 / α ^ 7 + 5040 / α ^ 8
    let C : Rat := -2 / α ^ 3 + 120 / α ^ 5 + 600 / α ^ 6 - 5040 / α ^ 8
    ((expI α prec).mulRat A prec).addRat C prec
  else
    let t := e2TaylorAux α taylorN 0 1 0
    let r := mom 2 * (rabs α ^ taylorN *
      (((taylorN + 1 : Nat) : Rat) / ((fact taylorN : Rat) * (taylorN : Rat))))
    ⟨roundDown prec (t - r), roundUp prec (t + r)⟩

/-! ## The special entries (paper §9.4)

Three family terms keep a second zero besides the one at the entry's height: the `rc` pair and the
first family's second zero (a second zero left of the test point, at height difference `y`), and
the shifted `rc` entry (the conjugate zero, somewhere in `Re z ≥ a - s`). An entry's `Spec` names
the case, and `specVals` computes its values `(add, exc)`: a lower bound `add` for the second
zero's term and an upper bound `exc` for the entry's pair excess `(Re G(-s₁ + iy) - 1/6)₊`.
* `two`: `Re F(x + iy)` at the midpoint `x₀` of `[xa, xb]` and `Re G(-s₁ + iy)` on a uniform grid of
  `n` cells of `[ylo, min(yhi, ytop)]`, with the second-derivative slacks `c³m₂h²/8` and
  `c₁³E₂(c₁s₁)h²/8` and the Lipschitz slack `c²m₁(xb - xa)/2`; beyond `ytop` the closed-form tail
  of `G` and `Re F ≥ 0`; `add = max(R, 0)` and `exc = max(C - 1/6, 0)`;
* `cz`: `C ≥ -Re F` on the line `Re z = -d` from the cells between consecutive points of `ys`
  (starting at `0`), the second-derivative slack `c³E₂(cd)(b - a)²/8`, and the closed-form tail
  beyond the last point; `add = -C`, `exc = 0` (the half-plane follows by the minimum principle).
-/

/-- The semantics of an entry's second kept zero, if any. -/
inductive Spec where
  /-- The entry keeps one zero. -/
  | one
  /-- A second zero left of the test point: the real offsets `x ∈ [xa, xb]` (`x ≥ 0`) and the height
  differences `|y| ∈ [ylo, yhi]` (`yhi = none`: unbounded); `n` grid cells on
  `[ylo, min(yhi, ytop)]`, the tail beyond `ytop`. -/
  | two (xa xb ylo : Rat) (yhi : Option Rat) (ytop : Rat) (n : Nat)
  /-- A second zero anywhere in `Re z ≥ -d`: the line `Re z = -d` is covered by the cells between
  consecutive points of `ys` (from `0`), and the tail beyond the last point. -/
  | cz (d : Rat) (ys : List Rat)
  deriving Repr, Inhabited

/-- `min_{k ≤ n} (reFI c x (lo + k h)).lo`. -/
def gridMin (c x lo h : Rat) (prec : Nat) : Nat → Rat
  | 0 => (reFI c x lo prec).lo
  | k + 1 => rmin (gridMin c x lo h prec k) (reFI c x (lo + ((k + 1 : Nat) : Rat) * h) prec).lo

/-- `max_{k ≤ n} (reFI c x (lo + k h)).hi`. -/
def gridMax (c x lo h : Rat) (prec : Nat) : Nat → Rat
  | 0 => (reFI c x lo prec).hi
  | k + 1 => rmax (gridMax c x lo h prec k) (reFI c x (lo + ((k + 1 : Nat) : Rat) * h) prec).hi

/-- `R(u, E) = 10/u³ + 30/u⁴ + 120/u⁶ + E (30/u⁴ + 120/u⁵ + 120/u⁶)`. -/
def tailRQ (u E : Rat) : Rat :=
  10 / u ^ 3 + 30 / u ^ 4 + 120 / u ^ 6 + E * (30 / u ^ 4 + 120 / u ^ 5 + 120 / u ^ 6)

/-- The grid part of a `two` entry on `[lo, top]` with `n` cells: a lower bound `R` of
`Re F_{2γ}(x + iy)` for `x ∈ [xa, xb]`, and an upper bound `C` of `Re G_{2g₁}(-s₁ + iy)`. -/
def twoGrid (p : RowP) (xa xb lo top : Rat) (n : Nat) (prec : Nat) : Rat × Rat :=
  let c := 2 * p.γ
  let c1 := 2 * p.g1
  let h := (top - lo) / n
  (gridMin c ((xa + xb) / 2) lo h prec n -
      (c ^ 3 * mom 2 * h ^ 2 / 8 + c ^ 2 * mom 1 * ((xb - xa) / 2)),
    gridMax c1 (-p.s1) lo h prec n + c1 ^ 3 * (e2I (c1 * p.s1) prec).hi * h ^ 2 / 8)

/-- The tail of `Re G_{2g₁}(-s₁ + iy)` for `|y| ≥ U`: `c₁ R(c₁U, e^{c₁s₁})`. -/
def gramTail (p : RowP) (U : Rat) (prec : Nat) : Rat :=
  2 * p.g1 * tailRQ (2 * p.g1 * U) (expI (2 * p.g1 * p.s1) prec).hi

/-- The end of the grid of a `two` entry: `min(yhi, ytop)`. -/
def twoTop (yhi : Option Rat) (ytop : Rat) : Rat :=
  match yhi with
  | none => ytop
  | some v => rmin v ytop

/-- Whether a `two` entry's range extends beyond `ytop` (then the tail is used). -/
def twoTail (yhi : Option Rat) (ytop : Rat) : Bool :=
  match yhi with
  | none => true
  | some v => decide (ytop < v)

/-- The bounds `(R, C)` of a `two` entry: `R ≤ Re F(x + iy)` and `Re G(-s₁ + iy) ≤ C` on its range,
from the grid on `[ylo, twoTop]` (if nonempty) and the tail beyond `ytop` (if used). -/
def twoRC (p : RowP) (xa xb ylo : Rat) (yhi : Option Rat) (ytop : Rat) (n : Nat) (prec : Nat) :
    Option (Rat × Rat) :=
  if ylo < twoTop yhi ytop then
    let g := twoGrid p xa xb ylo (twoTop yhi ytop) n prec
    if twoTail yhi ytop then some (rmin g.1 0, rmax g.2 (gramTail p ytop prec)) else some g
  else if twoTail yhi ytop then some (0, gramTail p ytop prec) else none

/-- The values `(add, exc) = (max(R, 0), max(C - 1/6, 0))` of a `two` entry. -/
def twoVals (p : RowP) (xa xb ylo : Rat) (yhi : Option Rat) (ytop : Rat) (n : Nat)
    (prec : Nat) : Option (Rat × Rat) :=
  if 0 ≤ xa ∧ xa ≤ xb ∧ 0 ≤ ylo ∧ 0 < ytop ∧ 0 < n then
    (twoRC p xa xb ylo yhi ytop n prec).map fun rc => (rmax rc.1 0, rmax (rc.2 - 1 / 6) 0)
  else none

/-- The cells of the line `Re z = -d` between consecutive points of `a :: rest`: the largest bound
`max(-Re F(-d + ia'), -Re F(-d + ib')) + M (b' - a')²/8` (and the bound at the last point), or `none`
if the points do not increase. -/
def cellsMax (c d M : Rat) (prec : Nat) : Rat → List Rat → Option Rat
  | a, [] => some (-(reFI c (-d) a prec).lo)
  | a, b :: rest =>
    if a < b then
      (cellsMax c d M prec b rest).map fun m =>
        rmax m (rmax (-(reFI c (-d) a prec).lo) (-(reFI c (-d) b prec).lo) + M * (b - a) ^ 2 / 8)
    else none

/-- The last of the points `a :: rest`. -/
def lastPt : Rat → List Rat → Rat
  | a, [] => a
  | _, b :: rest => lastPt b rest

/-- The bound `C ≥ -Re F_{2γ}` on the line `Re z = -d` of a `cz` entry. -/
def czC (p : RowP) (d : Rat) (ys : List Rat) (prec : Nat) : Option Rat :=
  let c := 2 * p.γ
  match ys with
  | [] => none
  | y0 :: rest =>
    if y0 = 0 ∧ 0 ≤ d ∧ 0 < lastPt y0 rest then
      (cellsMax c d (c ^ 3 * (e2I (c * d) prec).hi) prec y0 rest).map fun m =>
        rmax m (d / lastPt y0 rest ^ 2 +
          c * tailRQ (c * lastPt y0 rest) (expI (c * d) prec).hi)
    else none

/-- **The values `(add, exc)` of an entry's semantics.** -/
def specVals (p : RowP) (sp : Spec) (prec : Nat := defaultPrec) : Option (Rat × Rat) :=
  match sp with
  | .one => some (0, 0)
  | .two xa xb ylo yhi ytop n => twoVals p xa xb ylo yhi ytop n prec
  | .cz d ys => (czC p d ys prec).map fun C => (-C, 0)

/-! ## The row check -/

/-- The semantics of an entry: its feature is taken at `hi` from the response anchor `anc`, so its
offset in the near lemma is `s - anc`. The diagonal's upper bound is taken at an offset
`del ≤ s - anc` (the builders' grid point below), its positivity at an offset `delHi ≥ s - anc`
(`D` decreases). `xi`, `di` and `dj` index the row's lists of feature points `hi - anc` and offsets
where `del` and `delHi` are. `sp` names the entry's second kept zero, if any. -/
structure Ent where
  hi : Rat
  anc : Rat
  del : Rat
  delHi : Rat
  xi : Nat
  di : Nat
  dj : Nat
  sp : Spec
  deriving Repr, Inhabited

/-- An entry to check: its stored feature `v > 0` and diagonal `D`, and its semantics. -/
structure Item where
  v : Int
  D : Int
  e : Ent
  deriving Repr, Inhabited

/-- An entry with the values `(add, exc)` of its semantics. -/
abbrev VItem := Item × Rat × Rat

/-- The least normalizer that the radius `d` allows: `(1/6) / (d/(S(1+η)) - η)`. -/
def duRad (d : Int) : Rat := (1 / 6) / ((d : Rat) / ((S : Rat) * (1 + eta)) - eta)

/-- The least normalizer that an entry's diagonal `D` allows, given the upper bound `Dhi` of its
`D(δ)` plus its excess: `S(1+η)(Dhi - 1/6)/D`. -/
def duEnt (Dhi : Rat) (D : Int) : Rat := (S : Rat) * (1 + eta) * (Dhi - 1 / 6) / (D : Rat)

/-- The per-entry conditions that do not involve the normalizer: the offsets are admissible
(`0 ≤ del ≤ s - anc ≤ delHi`), the stored diagonal is positive, the lower bound of `D(delHi)`
exceeds `1/6`, the listed points are the entry's, and `F(hi - anc) + add > 1/6`. -/
def itemPre (p : RowP) (xs ds : List Rat) (FT DT : List Ival) (x : VItem) : Bool :=
  let it := x.1
  decide (0 < it.v) && decide (0 < it.D) &&
    decide (0 ≤ it.e.del) && decide (it.e.del ≤ p.s - it.e.anc) &&
    decide (p.s - it.e.anc ≤ it.e.delHi) &&
    decide (it.e.xi < xs.length) && decide (xs.getD it.e.xi 0 = it.e.hi - it.e.anc) &&
    decide (it.e.di < ds.length) && decide (ds.getD it.e.di 0 = it.e.del) &&
    decide (it.e.dj < ds.length) && decide (ds.getD it.e.dj 0 = it.e.delHi) &&
    decide (1 / 6 < (DT.getD it.e.dj default).lo) &&
    decide (1 / 6 < (FT.getD it.e.xi default).lo + x.2.1)

/-- The normalizer: the largest of the radius's and the entries' lower bounds. -/
def duOf (d : Int) (DT : List Ival) (vs : List VItem) : Rat :=
  vs.foldl (fun acc x => rmax acc (duEnt ((DT.getD x.1.e.di default).hi + x.2.2) x.1.D)) (duRad d)

/-- The feature condition `(v + Sη)² I_L D_u ≤ S² (F.lo + add - 1/6)²`. -/
def itemFeat (IL Du : Rat) (FT : List Ival) (x : VItem) : Bool :=
  let r := (FT.getD x.1.e.xi default).lo + x.2.1 - 1 / 6
  decide (((x.1.v : Rat) + (S : Rat) * eta) ^ 2 * IL * Du ≤ (S : Rat) ^ 2 * r ^ 2)

/-- **The row check.** `xs` lists the feature points and `ds` the offsets that the entries use. -/
def rowCheck (p : RowP) (d : Int) (xs ds : List Rat) (items : List Item)
    (prec : Nat := defaultPrec) : Bool :=
  p.good &&
    decide (0 < (d : Rat) / ((S : Rat) * (1 + eta)) - eta) &&
    match ibUpper p prec, items.mapM (fun it => specVals p it.e.sp prec) with
    | some IL, some vals =>
      let cs := ckFx p (prec + 16)
      let FT := xs.map fun x => fI (2 * p.γ) x prec
      let DT := ds.map fun δ => dI p cs δ prec
      let vs := items.zip vals
      let Du := duOf d DT vs
      vs.all (itemPre p xs ds FT DT) && vs.all (itemFeat IL Du FT)
    | _, _ => false

/-! ## The rows of a leaf -/

/-- The metadata of a near row: its parameters, the feature points and offsets its entries use,
and the semantics of each column's and each family term's entry (`none`: no checked entry). -/
structure RowMeta where
  p : RowP
  xs : List Rat
  ds : List Rat
  cols : List (Option Ent)
  fam : List (Option Ent)
  deriving Repr, Inhabited

/-- The entry of column `c` in row `k`: `some none` if its feature is `≤ 0`, `some (some item)` if
it is positive and the column has a semantics, `none` (a failure) otherwise. -/
def colItem (k : Nat) (c : CertCore.Col) (e : Option Ent) : Option (Option Item) :=
  if 0 < c.v.getD k 0 then e.map fun e => some ⟨c.v.getD k 0, c.D.getD k 1, e⟩ else some none

/-- The entry of a family term `(n, v, D)`, if its feature is positive and it has a semantics. -/
def famItem (t : Int × Int × Int) (e : Option Ent) : Option Item :=
  if 0 < t.2.1 then e.map fun e => ⟨t.2.1, t.2.2, e⟩ else none

/-- The checked entries of row `k`, or `none` if a column with a positive feature has no
semantics. -/
def rowItems (L : CertCore.Leaf) (k : Nat) (rm : RowMeta) : Option (List Item) :=
  ((L.cols.zip rm.cols).mapM fun ce => colItem k ce.1 ce.2).map fun cis =>
    cis.filterMap id ++
      ((L.rows.getD k ⟨1, []⟩).fam.zip rm.fam).filterMap fun te => famItem te.1 te.2

/-- **The check of row `k`** of a leaf against its metadata. -/
def checkRow (L : CertCore.Leaf) (k : Nat) (rm : RowMeta) (prec : Nat := defaultPrec) : Bool :=
  let row := L.rows.getD k ⟨1, []⟩
  decide (rm.cols.length = L.cols.length) && decide (rm.fam.length = row.fam.length) &&
    row.fam.all (fun t => decide (0 < t.2.2)) &&
    match rowItems L k rm with
    | none => false
    | some items => rowCheck rm.p row.d rm.xs rm.ds items prec

/-- **The check of every near row** of a leaf that has metadata. -/
def checkRows (L : CertCore.Leaf) (rms : List (Option RowMeta)) (prec : Nat := defaultPrec) :
    Bool :=
  decide (rms.length = L.rows.length) &&
    (List.range rms.length).all fun k =>
      match rms.getD k none with
      | none => true
      | some rm => checkRow L k rm prec

end RowCheckCore
