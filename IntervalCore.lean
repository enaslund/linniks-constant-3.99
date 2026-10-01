module

/-!
# Interval arithmetic with rational endpoints, without Mathlib

An interval `Ival` is a pair of rationals `[lo, hi]`. Every operation returns an interval that
contains the image of its inputs: exact rational results are rounded outward (`roundDown` for
lower ends, `roundUp` for upper ends) to the dyadic grid `2^-p`, which keeps numerators and
denominators bounded. The precision `p` is the last argument of each operation, with default
`defaultPrec = 128` (about 38 decimal digits of absolute precision).

The library depends on Lean core only (`Int`, `Nat`, core `Rat`), so it can be compiled to native
code without compiling Mathlib. The soundness theorems (every operation contains the true values,
for real numbers and `Real.exp`) are in `GradedNear/Interval/Sound.lean`.

Nothing here assumes `lo ≤ hi`: for an interval with `lo > hi` no real number is a member, and
the inclusion theorems hold vacuously.

## The exponential

`expLo p q ≤ exp q ≤ expHi p q` for a rational `q`, and `Ival.exp` applies these to the two ends
(`exp` is increasing; `expBoth` shares the work when `lo = hi`). For `q ≥ 0` write `q = n / d`;
with `k = expShift n d` we have `Y = q / 2^k < 2^-8`. The computation is in fixed point: a natural
number `a` stands for `a / 2^w`, with `w = p + k + 12`. With `y = ⌊2^w Y⌋`, one pass of the Taylor
series of `exp (y / 2^w)` with the terms rounded down (`taylor`) gives a lower bound `s` and an
error bound `e`: every rounded term is within `3` units of the exact term, and the pass stops at
the first term that rounds to `0`, whose tail is at most twice the term (`Real.exp_bound`: the tail
after `m ≥ 1` terms is at most `Y^m (m+1)/(m!·m) ≤ 2 Y^m/m!`). The upper bound `s + e` is
multiplied by `1 + 2^(1-w) ≥ exp (2^-w)` to cover the rounding of `y`. Then `k` squarings, rounded
down or up, give `exp q = exp(Y)^(2^k)`. For `q < 0` we use `exp q = 1 / exp(-q)`, and for
`q ≤ -p` the bounds `0 ≤ exp q ≤ 2^-p`.

With the default precision the enclosures of `exp q` have width at most about `2^-128` for
`q ≤ 0` and relative width about `2^-128` for `q ≥ 0` (about 38 correct digits). Values below
`2^-p` are only known to lie in `[0, 2^-p]`, as the grid is absolute.
-/

@[expose] public section

namespace IntervalCore

/-- The default precision: results are rounded outward to the grid `2^-128`. -/
def defaultPrec : Nat := 128

/-! ## Comparisons of rationals -/

/-- `a ≤ b` as a `Bool`. -/
@[inline] def ratLe (a b : Rat) : Bool := decide (a ≤ b)

/-- `a < b` as a `Bool`. -/
@[inline] def ratLt (a b : Rat) : Bool := decide (a < b)

/-- The minimum of two rationals. -/
@[inline] def rmin (a b : Rat) : Rat := if a ≤ b then a else b

/-- The maximum of two rationals. -/
@[inline] def rmax (a b : Rat) : Rat := if a ≤ b then b else a

/-! ## Outward rounding to the grid `2^-p` -/

/-- `⌊n·2^p/d⌋ / 2^p`, the largest multiple of `2^-p` that is `≤ n / d` (for `d > 0`). -/
@[inline] def divDown (p : Nat) (n : Int) (d : Nat) : Rat :=
  mkRat (n * ((2 ^ p : Nat) : Int) / (d : Int)) (2 ^ p)

/-- `⌈n·2^p/d⌉ / 2^p`, the smallest multiple of `2^-p` that is `≥ n / d` (for `d > 0`). -/
@[inline] def divUp (p : Nat) (n : Int) (d : Nat) : Rat :=
  mkRat (-(-n * ((2 ^ p : Nat) : Int) / (d : Int))) (2 ^ p)

/-- `q` rounded down to the grid `2^-p`. Rationals on the grid (denominator dividing `2^p`) are
returned unchanged. -/
def roundDown (p : Nat) (q : Rat) : Rat :=
  if 2 ^ p % q.den = 0 then q else divDown p q.num q.den

/-- `q` rounded up to the grid `2^-p`. Rationals on the grid are returned unchanged. -/
def roundUp (p : Nat) (q : Rat) : Rat :=
  if 2 ^ p % q.den = 0 then q else divUp p q.num q.den

/-! ## Intervals -/

/-- The closed interval `[lo, hi]` of real numbers. -/
structure Ival where
  lo : Rat
  hi : Rat
  deriving Repr, Inhabited, BEq, DecidableEq

namespace Ival

/-! ### Constructors and checks -/

/-- The point interval `[q, q]`. -/
def ofRat (q : Rat) : Ival := ⟨q, q⟩

/-- `lo ≤ hi`. -/
def valid (I : Ival) : Bool := decide (I.lo ≤ I.hi)

/-- `q ∈ [lo, hi]`. -/
def contains (I : Ival) (q : Rat) : Bool := decide (I.lo ≤ q) && decide (q ≤ I.hi)

/-- `I ⊆ J` (as closed intervals of reals). -/
def subset (I J : Ival) : Bool := decide (J.lo ≤ I.lo) && decide (I.hi ≤ J.hi)

/-- Every point of `I` is `≤` every point of `J`. -/
def le (I J : Ival) : Bool := decide (I.hi ≤ J.lo)

/-- Every point of `I` is `<` every point of `J`. -/
def lt (I J : Ival) : Bool := decide (I.hi < J.lo)

/-- Every point of `I` is `≤ q`. -/
def leRat (I : Ival) (q : Rat) : Bool := decide (I.hi ≤ q)

/-- Every point of `I` is `< q`. -/
def ltRat (I : Ival) (q : Rat) : Bool := decide (I.hi < q)

/-- Every point of `I` is `≥ q`. -/
def geRat (I : Ival) (q : Rat) : Bool := decide (q ≤ I.lo)

/-- Every point of `I` is `> q`. -/
def gtRat (I : Ival) (q : Rat) : Bool := decide (q < I.lo)

/-- The width `hi - lo`. -/
def width (I : Ival) : Rat := I.hi - I.lo

/-- The smallest interval containing `I` and `J`. -/
def join (I J : Ival) : Ival := ⟨rmin I.lo J.lo, rmax I.hi J.hi⟩

/-- `I` with its ends rounded outward to the grid `2^-p` (e.g. to normalize input data). -/
def round (I : Ival) (p : Nat := defaultPrec) : Ival := ⟨roundDown p I.lo, roundUp p I.hi⟩

/-! ### Arithmetic -/

/-- `-I` (exact). -/
def neg (I : Ival) : Ival := ⟨-I.hi, -I.lo⟩

/-- `I + J`. -/
def add (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  ⟨roundDown p (I.lo + J.lo), roundUp p (I.hi + J.hi)⟩

/-- `I - J`. -/
def sub (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  ⟨roundDown p (I.lo - J.hi), roundUp p (I.hi - J.lo)⟩

/-- `I + q`. -/
def addRat (I : Ival) (q : Rat) (p : Nat := defaultPrec) : Ival :=
  ⟨roundDown p (I.lo + q), roundUp p (I.hi + q)⟩

/-- `q · I`. -/
def mulRat (I : Ival) (q : Rat) (p : Nat := defaultPrec) : Ival :=
  if 0 ≤ q then ⟨roundDown p (I.lo * q), roundUp p (I.hi * q)⟩
  else ⟨roundDown p (I.hi * q), roundUp p (I.lo * q)⟩

/-- `I / q`, as `q⁻¹ · I` (for `q = 0` this is `[0, 0]`, matching `x / 0 = 0`). -/
def divRat (I : Ival) (q : Rat) (p : Nat := defaultPrec) : Ival :=
  mulRat I q⁻¹ p

/-- `I · J`: the minimum and maximum of the four products of ends, rounded outward (two products
when both intervals are nonnegative). -/
def mul (I J : Ival) (p : Nat := defaultPrec) : Ival :=
  if 0 ≤ I.lo ∧ 0 ≤ J.lo then
    ⟨roundDown p (I.lo * J.lo), roundUp p (I.hi * J.hi)⟩
  else
    let a := I.lo * J.lo
    let b := I.lo * J.hi
    let c := I.hi * J.lo
    let d := I.hi * J.hi
    ⟨roundDown p (rmin (rmin a b) (rmin c d)), roundUp p (rmax (rmax a b) (rmax c d))⟩

/-- `{x² : x ∈ I}`. -/
def sqr (I : Ival) (p : Nat := defaultPrec) : Ival :=
  if 0 ≤ I.lo then ⟨roundDown p (I.lo * I.lo), roundUp p (I.hi * I.hi)⟩
  else if I.hi ≤ 0 then ⟨roundDown p (I.hi * I.hi), roundUp p (I.lo * I.lo)⟩
  else ⟨0, roundUp p (rmax (I.lo * I.lo) (I.hi * I.hi))⟩

/-- `{xⁿ : x ∈ I}`, from the exact powers of the ends. -/
def pow (I : Ival) (n : Nat) (p : Nat := defaultPrec) : Ival :=
  if n = 0 then ofRat 1
  else if n % 2 = 1 ∨ 0 ≤ I.lo then ⟨roundDown p (I.lo ^ n), roundUp p (I.hi ^ n)⟩
  else if I.hi ≤ 0 then ⟨roundDown p (I.hi ^ n), roundUp p (I.lo ^ n)⟩
  else ⟨0, roundUp p (rmax (I.lo ^ n) (I.hi ^ n))⟩

/-- `{1/x : x ∈ I}`, defined when `I` does not contain `0` (`lo > 0` or `hi < 0`). -/
def inv (I : Ival) (p : Nat := defaultPrec) : Option Ival :=
  if 0 < I.lo ∨ I.hi < 0 then some ⟨roundDown p I.hi⁻¹, roundUp p I.lo⁻¹⟩ else none

/-- `{x/y : x ∈ I, y ∈ J}`, defined when `J` does not contain `0` (`lo > 0` or `hi < 0`):
the product of `I` with the exact interval `[1/J.hi, 1/J.lo]`. -/
def div (I J : Ival) (p : Nat := defaultPrec) : Option Ival :=
  if 0 < J.lo ∨ J.hi < 0 then some (mul I ⟨J.hi⁻¹, J.lo⁻¹⟩ p) else none

end Ival

/-! ## Fixed-point helpers: a natural number `a` stands for `a / 2^w` -/

/-- `⌊a / 2^w⌋ + 1`, an upper bound for `a / 2^w`. -/
@[inline] def shrUp (a w : Nat) : Nat := (a >>> w) + 1

/-- Taylor sum of `exp Y`, `Y = y / 2^w`, with the terms rounded down. With `T_m = 2^w Y^m/m!`,
the state satisfies `t ≤ T_m ≤ t + 3` and `s ≤ ∑_{j<m} T_j ≤ s + e` (the upper bounds for
`1 ≤ m` and `Y ≤ 1`). The sum stops when a term is `0` and returns `(s, e + 2 (t + 3))`: then
`s ≤ 2^w exp Y ≤ s + e + 2 (t + 3)`, because the tail after `m ≥ 1` terms is at most `2 T_m`. -/
def taylor (w y : Nat) : (fuel m t s e : Nat) → Nat × Nat
  | 0, _, t, s, e => (s, e + 2 * t + 6)
  | fuel + 1, m, t, s, e =>
    if t = 0 then (s, e + 6)
    else taylor w y fuel (m + 1) (((t * y) >>> w) / (m + 1)) (s + t) (e + 3)

/-- `k` squarings `a ↦ ⌊a² / 2^w⌋`. -/
def sqrLo (w : Nat) : Nat → Nat → Nat
  | 0, a => a
  | k + 1, a => sqrLo w k ((a * a) >>> w)

/-- `k` squarings `a ↦ ⌊a² / 2^w⌋ + 1`. -/
def sqrHi (w : Nat) : Nat → Nat → Nat
  | 0, a => a
  | k + 1, a => sqrHi w k (shrUp (a * a) w)

/-- Argument reduction: `exp` is evaluated at `n/d / 2^k < 2^-expRed`. -/
def expRed : Nat := 8

/-- Guard bits of the working precision. -/
def expGuard : Nat := 12

/-- The number `k` of squarings for `exp (n / d)`: `n / d ≤ 2^k`, in fact
`n / d < 2^(k - expRed)`. -/
def expShift (n d : Nat) : Nat := if n = 0 then 0 else (n.log2 + 1 + expRed) - d.log2

/-- A lower bound for `2^w · exp (n / d)` (for `d > 0`): with `y = ⌊2^w n/(d 2^k)⌋`, the Taylor sum
of `exp (y / 2^w)`, squared `k` times. -/
def expMantLo (w k n d : Nat) : Nat :=
  let y := (n <<< w) / (d <<< k)
  sqrLo w k (taylor w y (w + 2) 1 y (2 ^ w) 0).1

/-- An upper bound for `2^w · exp (n / d)` (for `d > 0` and `n / d ≤ 2^k`): the Taylor sum plus
its error bound `v ≥ 2^w exp (y / 2^w)`, times `1 + 2^(1-w) ≥ exp (2^-w)` for the rounding of `y`,
squared `k` times. -/
def expMantHi (w k n d : Nat) : Nat :=
  let y := (n <<< w) / (d <<< k)
  let r := taylor w y (w + 2) 1 y (2 ^ w) 0
  let v := r.1 + r.2
  sqrHi w k (v + 2 * shrUp v w)

/-- `(expMantLo w k n d, expMantHi w k n d)`, sharing the Taylor sum. -/
def expMantBoth (w k n d : Nat) : Nat × Nat :=
  let y := (n <<< w) / (d <<< k)
  let r := taylor w y (w + 2) 1 y (2 ^ w) 0
  let v := r.1 + r.2
  (sqrLo w k r.1, sqrHi w k (v + 2 * shrUp v w))

/-- A lower bound for `exp q` on the grid `2^-p`. -/
def expLo (p : Nat) (q : Rat) : Rat :=
  if 0 ≤ q then
    let n := q.num.toNat
    let k := expShift n q.den
    let w := p + k + expGuard
    mkRat ((expMantLo w k n q.den >>> (k + expGuard) : Nat) : Int) (2 ^ p)
  else if q ≤ -(p : Rat) then 0
  else
    let n := q.num.natAbs
    let k := expShift n q.den
    let w := p + k + expGuard
    mkRat ((2 ^ (w + p) / expMantHi w k n q.den : Nat) : Int) (2 ^ p)

/-- An upper bound for `exp q` on the grid `2^-p`. -/
def expHi (p : Nat) (q : Rat) : Rat :=
  if 0 ≤ q then
    let n := q.num.toNat
    let k := expShift n q.den
    let w := p + k + expGuard
    mkRat ((shrUp (expMantHi w k n q.den) (k + expGuard) : Nat) : Int) (2 ^ p)
  else if q ≤ -(p : Rat) then mkRat 1 (2 ^ p)
  else
    let n := q.num.natAbs
    let k := expShift n q.den
    let w := p + k + expGuard
    mkRat ((2 ^ (w + p) / max (expMantLo w k n q.den) 1 + 1 : Nat) : Int) (2 ^ p)

/-- `(expLo p q, expHi p q)`, sharing the Taylor sum and the argument reduction. -/
def expBoth (p : Nat) (q : Rat) : Rat × Rat :=
  if 0 ≤ q then
    let n := q.num.toNat
    let k := expShift n q.den
    let w := p + k + expGuard
    let r := expMantBoth w k n q.den
    (mkRat ((r.1 >>> (k + expGuard) : Nat) : Int) (2 ^ p),
      mkRat ((shrUp r.2 (k + expGuard) : Nat) : Int) (2 ^ p))
  else if q ≤ -(p : Rat) then (0, mkRat 1 (2 ^ p))
  else
    let n := q.num.natAbs
    let k := expShift n q.den
    let w := p + k + expGuard
    let r := expMantBoth w k n q.den
    (mkRat ((2 ^ (w + p) / r.2 : Nat) : Int) (2 ^ p),
      mkRat ((2 ^ (w + p) / max r.1 1 + 1 : Nat) : Int) (2 ^ p))

namespace Ival

/-- `{exp x : x ∈ I}`: `[expLo p lo, expHi p hi]` (one shared evaluation when `lo = hi`). -/
def exp (I : Ival) (p : Nat := defaultPrec) : Ival :=
  if I.lo = I.hi then
    let r := expBoth p I.lo
    ⟨r.1, r.2⟩
  else ⟨expLo p I.lo, expHi p I.hi⟩

/-! ### Notation at the default precision -/

instance : Neg Ival := ⟨neg⟩
instance : Add Ival := ⟨fun I J => add I J⟩
instance : Sub Ival := ⟨fun I J => sub I J⟩
instance : Mul Ival := ⟨fun I J => mul I J⟩

end Ival

end IntervalCore
