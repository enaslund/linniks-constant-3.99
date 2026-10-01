module

public import IntervalCore

/-!
# Interval enclosures of the leaf functions, without Mathlib

Interval enclosures (in `IntervalCore.Ival`, at precision `prec`, default `128`) of the real
functions of `GradedNear/Functions.lean` whose values a certificate leaf stores (specification:
§1 of `research/notes/leaf-data-semantics-2026-09-29.md` in the research repository). The inputs are rationals. The soundness
theorems (every enclosure contains the true value) are in `GradedNear/LeafNumSound.lean`.

* The kernel constants `T`, `beta`, `kappa` and `H0` as rationals (the same rationals as
  `GradedNear.Kernel.T`, `beta`, `kappa`, and `H₀ = (κ Σ β_i)²`).
* `benv φ λ`: the envelope `B_φ(λ)` by its closed form
  `H₀ B_φ(λ) = Σ_i E^i (β_i² (Q₀ + (φ/2) U) + κ U β_i Σ_{j>i} β_j)`, `E = e^{−2κλ}`,
  `U = (1 − E)/λ`, `Q₀ = κ/λ − U/(2λ)` (for `λ ≠ 0`); the two polynomials in `E` are evaluated by
  Horner's rule.
* `gphi L φ λ = e^{−(L−2T)λ} B_φ(λ)`; `hratio λ = h(λ)`; `cpa p a = C(p, a)` from the exact
  step-cell sums (`a ≠ 0`); `jold`, `jnew`: the first-family bounds `J_old`, `J_new`.
* The far weight of a profile `(c₁, c₂, θ)`: with `a = 2λ − θ`, `ε = 10⁻⁷`,
  `w(λ)⁻¹ = 2 e^{a(u−ε)} ∫_{√ε}^{√(c₂+ε)} r² e^{a r²} dr + √(c₂+ε) ∫_v^x e^{at} dt`
  (`winv`), and `w = 1/winv` (`w`).
* `vUpper`: an upper bound for the constant `V` of the far bound, through
  `J_i = K(ih) − K((i+1)h)` with `K(d) = ∫_u^x w₀(t)⁻² (t − u − d)₊ dt`.

**The integrals `∫ (r² − D) e^{c r²} dr`** (`rInt`) over `[√y_a, √y_b]` are computed from the
Taylor polynomial `P_N` of `exp` with `N = seriesTerms + 4⌈|c| y_b⌉` terms: the polynomial part
integrates exactly to `√y_b Φ(y_b) − √y_a Φ(y_a)` with
`Φ(y) = Σ_{k<N} (cy)^k/k! (y/(2k+3) − D/(2k+1))` (`serPhi`), and
`|e^x − P_N(x)| ≤ 2|x|^N/N!` for `2|x| ≤ N + 1` bounds the rest. The square roots of rationals are
enclosed by rationals checked by squaring (`sqrtI`).

**Fixed point.** The two inner loops, Horner's rule (`horner`) and the series `Φ` (`serStep`),
run on `Fx`: intervals with integer ends at a fixed scale `2^w`, where additions are exact and
products round outward by one floor or ceiling division (about 4× faster than `Ival`, whose every
operation normalizes a `Rat`). The exponentials are `IntervalCore.Ival.exp`.

**Precision and cost.** With the default precision `128` the enclosures have widths of about
`10⁻³⁶` (relative) for `λ ∈ [0, 3]`. Natively compiled, one `gphi` takes about 0.25 ms and one
`w`/`winv` about 0.6 ms (on a loaded machine); `cpa` and `jnew` a few ms, `vUpper` about 20 ms.
-/

@[expose] public section

namespace LeafNumCore

open IntervalCore

/-! ## The kernel constants -/

/-- `T = .416829`. -/
def T : Rat := 416829 / 1000000

/-- The sixteen step heights `β₀, …, β₁₅` of `config_v4.py`. -/
def betaList : List Rat := [2318741 / 100000000, 7159337 / 100000000, 12265085 / 100000000,
  17627704 / 100000000, 23237155 / 100000000, 29081583 / 100000000, 35147264 / 100000000,
  41418551 / 100000000, 47877833 / 100000000, 54505502 / 100000000, 61279917 / 100000000,
  68177389 / 100000000, 75172165 / 100000000, 82236428 / 100000000, 89340300 / 100000000,
  96451862 / 100000000]

/-- `β_i` (`0` for `i ≥ 16`). -/
def beta (i : Nat) : Rat := betaList.getD i 0

/-- The step width `κ = T/16`. -/
def kappa : Rat := T / 16

/-- A finite sum `Σ_{i<n} f i` of rationals. -/
def sumQ (f : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumQ f n + f n

/-- `Σ_{j>i} β_j`. -/
def betaTail (i : Nat) : Rat := sumQ (fun j => if i < j then beta j else 0) 16

/-- `H₀ = (κ Σ_i β_i)²`. -/
def H0 : Rat := (kappa * sumQ beta 16) ^ 2

/-- The coefficients `β_i Σ_{j>i} β_j`. -/
def crossList : List Rat := (List.range 16).map fun i => beta i * betaTail i

/-- `β_i Σ_{j>i} β_j` (`0` for `i ≥ 16`). -/
def cross (i : Nat) : Rat := crossList.getD i 0

/-! ## Interval helpers -/

/-- An enclosure of `exp q`. -/
def expI (q : Rat) (prec : Nat := defaultPrec) : Ival := Ival.exp (Ival.ofRat q) prec

/-- `{max 0 x : x ∈ I}`. -/
def max0 (I : Ival) : Ival := ⟨rmax 0 I.lo, rmax 0 I.hi⟩

/-- `Σ_{i<n} f i` in interval arithmetic. -/
def sumI (f : Nat → Ival) (prec : Nat) : Nat → Ival
  | 0 => Ival.ofRat 0
  | n + 1 => (sumI f prec n).add (f n) prec

/-! ### Fixed-point intervals

The two inner loops (Horner's rule and the Taylor series of `rInt`) run on intervals with integer
ends at a fixed scale `2^w`: additions are exact and the other operations round outward by a
floor or ceiling division, without the `gcd` normalizations of `Rat`. -/

/-- `⌊n / d⌋` for `d > 0`. -/
@[inline] def fdivI (n : Int) (d : Nat) : Int := n / (d : Int)

/-- `⌈n / d⌉` for `d > 0`. -/
@[inline] def cdivI (n : Int) (d : Nat) : Int := -((-n) / (d : Int))

/-- A fixed-point interval: `⟨lo, hi⟩` stands for `[lo/2^w, hi/2^w]`, at a scale `2^w` fixed by
the computation. -/
structure Fx where
  lo : Int
  hi : Int

namespace Fx

/-- `[lo/2^w, hi/2^w]` as an `Ival` (exact). -/
def toIval (A : Fx) (w : Nat) : Ival := ⟨mkRat A.lo (2 ^ w), mkRat A.hi (2 ^ w)⟩

/-- `[⌊2^w q⌋, ⌈2^w q⌉]`. -/
def ofRat (q : Rat) (w : Nat) : Fx :=
  ⟨fdivI (q.num * ((2 ^ w : Nat) : Int)) q.den, cdivI (q.num * ((2 ^ w : Nat) : Int)) q.den⟩

/-- `I` rounded outward to the grid `2^-w`. -/
def ofIval (I : Ival) (w : Nat) : Fx :=
  ⟨fdivI (I.lo.num * ((2 ^ w : Nat) : Int)) I.lo.den,
    cdivI (I.hi.num * ((2 ^ w : Nat) : Int)) I.hi.den⟩

/-- `A + B` (exact). -/
def add (A B : Fx) : Fx := ⟨A.lo + B.lo, A.hi + B.hi⟩

/-- `q · A`. -/
def mulRat (A : Fx) (q : Rat) : Fx :=
  if 0 ≤ q then ⟨fdivI (A.lo * q.num) q.den, cdivI (A.hi * q.num) q.den⟩
  else ⟨fdivI (A.hi * q.num) q.den, cdivI (A.lo * q.num) q.den⟩

/-- `A · B`: the least and greatest products of ends, divided by `2^w` outward. -/
def mul (A B : Fx) (w : Nat) : Fx :=
  let a := A.lo * B.lo
  let b := A.lo * B.hi
  let c := A.hi * B.lo
  let d := A.hi * B.hi
  ⟨fdivI (min (min a b) (min c d)) (2 ^ w), cdivI (max (max a b) (max c d)) (2 ^ w)⟩

end Fx

/-- `hornerFx c X w k m` encloses `Σ_{i<m} c(k+i) x^i` for `x ∈ X` (Horner's rule, at scale
`2^w`). -/
def hornerFx (c : Nat → Rat) (X : Fx) (w : Nat) : Nat → Nat → Fx
  | _, 0 => ⟨0, 0⟩
  | k, m + 1 => (X.mul (hornerFx c X w (k + 1) m) w).add (Fx.ofRat (c k) w)

/-- `Σ_{i<n} c(i) x^i` for `x ∈ X`, at scale `2^(prec+16)`. -/
def horner (c : Nat → Rat) (n : Nat) (X : Ival) (prec : Nat) : Ival :=
  (hornerFx c (Fx.ofIval X (prec + 16)) (prec + 16) 0 n).toIval (prec + 16)

/-- `|q|`. -/
def rabs (q : Rat) : Rat := if 0 ≤ q then q else -q

/-- A natural number `> q` for `q ≥ 0`: `⌊q⌋ + 1`. -/
def natCeil (q : Rat) : Nat := q.num.toNat / q.den + 1

/-- `n!`. -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- An enclosure of `√y` for `y ≥ 0`: `⌊2^p √y⌋ / 2^p` and the next grid point, used only after
checking them by squaring; otherwise the crude `[0, max 1 y]`. -/
def sqrtI (y : Rat) (prec : Nat := defaultPrec) : Ival :=
  let m := Nat.sqrt (y.num.toNat * 2 ^ (2 * prec) / y.den)
  let lo : Rat := mkRat m (2 ^ prec)
  let hi : Rat := mkRat (m + 1) (2 ^ prec)
  if decide (lo * lo ≤ y) && decide (y ≤ hi * hi) then ⟨lo, hi⟩ else ⟨0, rmax 1 y⟩

/-! ## The envelope, `G_φ`, `h`, `C(p, a)` and the first-family bounds -/

/-- The envelope `B_φ(λ)` (for `λ ≠ 0`):
`((Q₀ + (φ/2)U) Σ_i β_i² E^i + κU Σ_i β_i (Σ_{j>i} β_j) E^i)/H₀` with `E = e^{−2κλ}`,
`Q₀ + (φ/2)U = κ/λ + (1 − E)(φ/(2λ) − 1/(2λ²))` and `κU = (1 − E) κ/λ`. -/
def benv (φ lam : Rat) (prec : Nat := defaultPrec) : Ival :=
  let E := expI (-(2 * kappa * lam)) prec
  let M := (Ival.ofRat 1).sub E prec
  let A1 := (M.mulRat (φ / (2 * lam) - 1 / (2 * lam * lam)) prec).addRat (kappa / lam) prec
  let A2 := M.mulRat (kappa / lam) prec
  let P1 := horner (fun i => beta i * beta i) 16 E prec
  let P2 := horner cross 16 E prec
  ((A1.mul P1 prec).add (A2.mul P2 prec) prec).divRat H0 prec

/-- The objective `G_φ(λ) = e^{−(L−2T)λ} B_φ(λ)`. -/
def gphi (L φ lam : Rat) (prec : Nat := defaultPrec) : Ival :=
  (expI (-((L - 2 * T) * lam)) prec).mul (benv φ lam prec) prec

/-- `h(λ) = Ψ(λ)²/H₀` with `Ψ(λ) = (Σ_i β_i e^{−iκλ}) (1 − e^{−κλ})/λ` (for `λ ≠ 0`). -/
def hratio (lam : Rat) (prec : Nat := defaultPrec) : Ival :=
  let e := expI (-(kappa * lam)) prec
  let S := horner beta 16 e prec
  let psi := (S.mul ((Ival.ofRat 1).sub e prec) prec).divRat lam prec
  (psi.sqr prec).divRat H0 prec

/-- `X(r, j) = ∫_{jκ}^{(j+1)κ} e^{−ru} du = e^{−rjκ}(1 − e^{−rκ})/r` (`κ` for `r = 0`), from an
enclosure `er` of `e^{−rκ}`. -/
def cellI (r : Rat) (er : Ival) (j : Nat) (prec : Nat) : Ival :=
  if r = 0 then Ival.ofRat kappa
  else ((er.pow j prec).mul ((Ival.ofRat 1).sub er prec) prec).divRat r prec

/-- The cross term `C(p, a) = (2/H₀) Σ_j β_j [(β_j/a) X(2p, j) + D_j X(2p − a, j)]` with
`D_j = Σ_{k>j} β_k X(a, k) − (β_j/a) e^{−a(j+1)κ}` (for `a ≠ 0`). -/
def cpa (p a : Rat) (prec : Nat := defaultPrec) : Ival :=
  let ea := expI (-(a * kappa)) prec
  let e2p := expI (-(2 * p * kappa)) prec
  let e2pa := expI (-((2 * p - a) * kappa)) prec
  let xa := (List.range 16).map fun k => (cellI a ea k prec).mulRat (beta k) prec
  let term (j : Nat) : Ival :=
    let tail := sumI (fun k => if j < k then xa.getD k (Ival.ofRat 0) else Ival.ofRat 0) prec 16
    let dj := tail.sub ((ea.pow (j + 1) prec).mulRat (beta j / a) prec) prec
    (((cellI (2 * p) e2p j prec).mulRat (beta j / a) prec).add
      (dj.mul (cellI (2 * p - a) e2pa j prec) prec) prec).mulRat (beta j) prec
  (sumI term prec 16).mulRat (2 / H0) prec

/-- `J_old = n [e^{−Ap} (B_φ(a) − α h(a))₊ + α e^{−Aa} h(a)]`, `A = L − 2T` (for `a ≠ 0`). -/
def jold (L : Rat) (n α : Nat) (φ a p : Rat) (prec : Nat := defaultPrec) : Ival :=
  let A := L - 2 * T
  let h := hratio a prec
  let d := max0 ((benv φ a prec).sub (h.mulRat α prec) prec)
  (((expI (-(A * p)) prec).mul d prec).add
    (((expI (-(A * a)) prec).mul h prec).mulRat α prec) prec).mulRat n prec

/-- `J_new = n {α e^{−Aa} h(a) + e^{−Ap} [B_φ(p) − α C(p, a)]}`, `A = L − 2T`
(for `a ≠ 0`, `p ≠ 0`). -/
def jnew (L : Rat) (n α : Nat) (φ a p : Rat) (prec : Nat := defaultPrec) : Ival :=
  let A := L - 2 * T
  let t1 := ((expI (-(A * a)) prec).mul (hratio a prec) prec).mulRat α prec
  let t2 := (expI (-(A * p)) prec).mul
    ((benv φ p prec).sub ((cpa p a prec).mulRat α prec) prec) prec
  (t1.add t2 prec).mulRat n prec

/-! ## The integrals `∫ (r² − D) e^{c r²} dr` -/

/-- The base number of Taylor terms. -/
def seriesTerms : Nat := 30

/-- The number of Taylor terms for `e^{c r²}`, `r² ≤ y_b`: `seriesTerms + 4⌈|c| y_b⌉`, so that
`2|c| y_b ≤ N + 1`. -/
def nTerms (c yb : Rat) : Nat := seriesTerms + 4 * natCeil (rabs c * yb)

/-- `serStep z y D w k = (S, T)` (fixed point at scale `2^w`) with
`S ∋ Σ_{j<k} z^j/j! (y/(2j+3) − D/(2j+1))` and `T ∋ z^k/k!`. -/
def serStep (z y D : Rat) (w : Nat) : Nat → Fx × Fx
  | 0 => (⟨0, 0⟩, Fx.ofRat 1 w)
  | k + 1 =>
    let st := serStep z y D w k
    (st.1.add (st.2.mulRat (y / (2 * k + 3) - D / (2 * k + 1))), st.2.mulRat (z / (k + 1)))

/-- `Φ(y) = Σ_{k<N} (cy)^k/k! (y/(2k+3) − D/(2k+1))`, so that
`∫_0^{√y} (r² − D) P_N(c r²) dr = √y Φ(y)` (at scale `2^prec`). -/
def serPhi (c D y : Rat) (N prec : Nat) : Ival := (serStep (c * y) y D prec N).1.toIval prec

/-- An enclosure of `∫_{√y_a}^{√y_b} (r² − D) e^{c r²} dr`, for `0 ≤ D ≤ y_a ≤ y_b`. -/
def rInt (c D ya yb : Rat) (prec : Nat := defaultPrec) : Ival :=
  let N := nTerms c yb
  let q := prec + 32
  let sa := sqrtI ya q
  let sb := sqrtI yb q
  let M := (sb.mul (serPhi c D yb N q) q).sub (sa.mul (serPhi c D ya N q) q) q
  let e0 := roundUp q (2 * (rabs c * yb) ^ N / (fact N : Rat))
  let err := roundUp q (e0 * sb.hi * (yb - D))
  ⟨roundDown prec (M.lo - err), roundUp prec (M.hi + err)⟩

/-- `∫_v^x e^{at} dt`: `(e^{ax} − e^{av})/a`, or `x − v` for `a = 0` (the exponentials with
64 guard bits, against cancellation for small `a`). -/
def expIntI (a v x : Rat) (prec : Nat := defaultPrec) : Ival :=
  if a = 0 then Ival.ofRat (x - v)
  else ((expI (a * x) (prec + 64)).sub (expI (a * v) (prec + 64)) (prec + 64)).divRat a prec

/-! ## The far weight -/

/-- The profile's `ε = 10⁻⁷`. -/
def epsQ : Rat := 1 / 10000000

/-- `w(λ)⁻¹ = ∫_u^x e^{−θt} √(min(t − u, c₂) + ε) e^{2λt} dt`
`= 2 e^{a(u−ε)} ∫_{√ε}^{√(c₂+ε)} r² e^{a r²} dr + √(c₂+ε) ∫_v^x e^{at} dt`, `a = 2λ − θ`,
`u = 1/3 + 2c₁`, `v = u + c₂`, `x = 2/3 + 3c₁ + c₂`. -/
def winv (c₁ c₂ θ lam : Rat) (prec : Nat := defaultPrec) : Ival :=
  let u := 1 / 3 + 2 * c₁
  let v := u + c₂
  let x := 2 / 3 + 3 * c₁ + c₂
  let a := 2 * lam - θ
  let y := c₂ + epsQ
  let first := ((rInt a 0 epsQ y prec).mul (expI (a * (u - epsQ)) prec) prec).mulRat 2 prec
  let second := (sqrtI y prec).mul (expIntI a v x prec) prec
  first.add second prec

/-- The far weight `w(λ) = 1/w(λ)⁻¹` (when the enclosure of `w(λ)⁻¹` is positive; otherwise only
the lower end `0` is meaningful). -/
def w (c₁ c₂ θ lam : Rat) (prec : Nat := defaultPrec) : Ival :=
  let I := winv c₁ c₂ θ lam prec
  if 0 < I.lo then ⟨roundDown prec I.hi⁻¹, roundUp prec I.lo⁻¹⟩ else ⟨0, 0⟩

/-! ## The constant `V` -/

/-- `∫_v^x e^{θt}(t − c) dt = e^{θt}((t − c)/θ − 1/θ²) |_v^x` (`((x−c)² − (v−c)²)/2` for
`θ = 0`). -/
def affExpI (θ c v x : Rat) (prec : Nat := defaultPrec) : Ival :=
  if θ = 0 then Ival.ofRat (((x - c) ^ 2 - (v - c) ^ 2) / 2)
  else
    let q := prec + 64
    ((expI (θ * x) q).mulRat ((x - c) / θ - 1 / (θ * θ)) q).sub
      ((expI (θ * v) q).mulRat ((v - c) / θ - 1 / (θ * θ)) q) prec

/-- `K(d) = ∫_u^x w₀(t)⁻² (t − u − d)₊ dt`
`= 2 e^{θ(u−ε)} ∫_{√(d+ε)}^{√(c₂+ε)} (r² − d − ε) e^{θ r²} dr`
`+ (c₂+ε)^{−1/2} ∫_v^x e^{θt}(t − u − d) dt` for `0 ≤ d ≤ c₂`. -/
def kI (c₁ c₂ θ d : Rat) (prec : Nat := defaultPrec) : Ival :=
  let u := 1 / 3 + 2 * c₁
  let v := u + c₂
  let x := 2 / 3 + 3 * c₁ + c₂
  let y := c₂ + epsQ
  let first := ((rInt θ (d + epsQ) (d + epsQ) y prec).mul (expI (θ * (u - epsQ)) prec)
    prec).mulRat 2 prec
  let second := (sqrtI (1 / y) prec).mul (affExpI θ (u + d) v x prec) prec
  first.add second prec

/-- `V = (100/(c₁c₂²)) Σ_{i<10} α_i² (K(ih) − K((i+1)h))`, `h = c₂/10`. -/
def vI (c₁ c₂ θ : Rat) (α : List Rat) (prec : Nat := defaultPrec) : Ival :=
  let h := c₂ / 10
  (sumI (fun i => ((kI c₁ c₂ θ (i * h) prec).sub (kI c₁ c₂ θ ((i + 1) * h) prec) prec).mulRat
    (α.getD i 0 ^ 2) prec) prec 10).mulRat (100 / (c₁ * c₂ ^ 2)) prec

/-- An upper bound for the constant `V` of the far profile `(c₁, c₂, θ, α)`. -/
def vUpper (c₁ c₂ θ : Rat) (α : List Rat) (prec : Nat := defaultPrec) : Rat :=
  (vI c₁ c₂ θ α prec).hi

/-! ## The two far profiles of the corpus -/

/-- A far profile `(c₁, c₂, θ, α)` (`GradedNear.Kernel.FarProfile`, with `α` as a list). -/
structure Profile where
  c₁ : Rat
  c₂ : Rat
  θ : Rat
  α : List Rat

/-- The inherited far profile (`config_v4.py`). -/
def inherited : Profile where
  c₁ := 9035 / 100000
  c₂ := 235968 / 1000000
  θ := 128683 / 100000
  α := [788827218 / 10000000000, 849386148 / 10000000000, 895629779 / 10000000000,
    938231516 / 10000000000, 979710491 / 10000000000, 1021284916 / 10000000000,
    1063732939 / 10000000000, 1107651869 / 10000000000, 1153565492 / 10000000000,
    1201979632 / 10000000000]

/-- The retuned far profile (`far_enclosures.CANDIDATE`). -/
def retuned : Profile where
  c₁ := 821922 / 10000000
  c₂ := 2170903 / 10000000
  θ := 14964274 / 10000000
  α := [806195583 / 10000000000, 862705300 / 10000000000, 905489307 / 10000000000,
    944644867 / 10000000000, 982543287 / 10000000000, 1020315591 / 10000000000,
    1058668825 / 10000000000, 1098131140 / 10000000000, 1139152197 / 10000000000,
    1182153903 / 10000000000]

end LeafNumCore
