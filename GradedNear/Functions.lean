module

public import GradedNear.Kernel

/-!
# The functions behind a leaf's objective, far and first-family data (paper §§5–6)

These are the real functions whose values the leaf builders enclose (traced from the code in
`research/notes/leaf-data-semantics-2026-09-29.md` in the research repository):
* the step kernel `ψ`, its transform `Ψ`, `H₀ = Ψ(0)² = (κ Σ β_i)²` and `h(λ) = Ψ(λ)²/H₀`;
* the envelope `B_φ(λ) = H₀⁻¹ [F_λ(−λ) + (φ/2) f_λ(0)]`, where
  `f_λ(t) = 2∫₀^{T−t} ψ(u) ψ(u+t) e^{−λ(2u+t)} du` and `F_λ` is its Laplace transform;
* the objective `G_φ(λ) = e^{−Aλ} B_φ(λ)` (`A = L − 2T`), with `G = G_{1/3}` for ordinary bins;
* the first-family quantities `C(p, a)`, `J_old` and `J_new` (paper §5);
* the far profile `w₀(t)² = e^{−θt} √(min(t − u, c₂) + ε)` on `[u, x]`, the far weight
  `w(λ) = (∫_u^x w₀² e^{2λt} dt)⁻¹` and the constant `V` of [X, Lemma 5.1, (5.19)] with `M = 10`.

`inherited` and `retuned` are the two far profiles of the corpus (`config_v4.py` and
`far_enclosures.CANDIDATE`).
-/

@[expose] public section

noncomputable section

namespace GradedNear.Kernel

open MeasureTheory

/-- The step kernel `ψ = Σ_i β_i 1_{[iκ, (i+1)κ)}`. -/
def psi (t : ℝ) : ℝ :=
  ∑ i : Fin 16, if (i.val : ℝ) * kappa ≤ t ∧ t < ((i.val : ℝ) + 1) * kappa then (beta i : ℝ) else 0

/-- `Ψ(z) = ∫₀^∞ ψ(t) e^{−zt} dt`. -/
def Psi (z : ℂ) : ℂ := laplace psi z

/-- `H₀ = Ψ(0)² = (κ Σ_i β_i)²`. -/
def H0 : ℝ := ((kappa : ℝ) * ∑ i, (beta i : ℝ)) ^ 2

/-- `h(λ) = Ψ(λ)² / H₀` for real `λ`. -/
def hRatio (lam : ℝ) : ℝ := (Psi lam).re ^ 2 / H0

/-- `f_λ(t) = 2 ∫₀^{T−t} ψ(u) ψ(u+t) e^{−λ(2u+t)} du` (paper §5). -/
def fLam (lam t : ℝ) : ℝ :=
  2 * ∫ u in (0 : ℝ)..((T : ℝ) - t), psi u * psi (u + t) * Real.exp (-(lam * (2 * u + t)))

/-- The envelope `B_φ(λ) = H₀⁻¹ [F_λ(−λ) + (φ/2) f_λ(0)]`, where `F_λ` is the Laplace
transform of `f_λ` (paper §5; [X, (3.60)]). -/
def Benv (φ lam : ℝ) : ℝ :=
  ((laplace (fLam lam) ((-lam : ℝ) : ℂ)).re + φ / 2 * fLam lam 0) / H0

/-- The objective of a zero parameter at exponent `L`: `G_φ(λ) = e^{−Aλ} B_φ(λ)`,
`A = L − 2T`. -/
def Gphi (L φ lam : ℝ) : ℝ := Real.exp (-((L - 2 * T) * lam)) * Benv φ lam

/-- The ordinary objective `G(λ) = e^{−Aλ} B_{1/3}(λ)` (paper §5). -/
def G (L lam : ℝ) : ℝ := Gphi L (1 / 3) lam

/-- `C(p, a) = (2/H₀) ∫₀^T ψ(u) e^{−2pu} ∫_u^T ψ(v) e^{−a(v−u)} dv du` (paper §5). -/
def Cpa (p a : ℝ) : ℝ :=
  2 / H0 * ∫ u in (0 : ℝ)..T, psi u * Real.exp (-(2 * p * u)) *
    ∫ v in u..T, psi v * Real.exp (-(a * (v - u)))

/-- The old first-family bound `J_old = n [e^{−Ap} (B_t(a) − α h(a))₊ + α e^{−Aa} h(a)]`
(paper §5). -/
def Jold (L : ℝ) (n α : ℕ) (φ a p : ℝ) : ℝ :=
  n * (Real.exp (-((L - 2 * T) * p)) * max 0 (Benv φ a - α * hRatio a) +
    α * Real.exp (-((L - 2 * T) * a)) * hRatio a)

/-- The shifted first-family bound `J_new = n {α e^{−Aa} h(a) + e^{−Ap} [B_t(p) − α C(p, a)]}`
(paper §5.6, used when `p ≥ b`). -/
def Jnew (L : ℝ) (n α : ℕ) (φ a p : ℝ) : ℝ :=
  n * (α * Real.exp (-((L - 2 * T) * a)) * hRatio a +
    Real.exp (-((L - 2 * T) * p)) * (Benv φ p - α * Cpa p a))

/-- A far profile of the repository's shape: `c₁`, `c₂`, `θ` and ten weights `α_i` (`M = 10`). -/
structure FarProfile where
  c₁ : ℚ
  c₂ : ℚ
  θ : ℚ
  α : Fin 10 → ℚ

namespace FarProfile

variable (P : FarProfile)

/-- `u = 1/3 + 2c₁`. -/
def u : ℝ := 1 / 3 + 2 * (P.c₁ : ℝ)

/-- `v = u + c₂`. -/
def v : ℝ := P.u + P.c₂

/-- `x = 2/3 + 3c₁ + c₂`. -/
def x : ℝ := 2 / 3 + 3 * (P.c₁ : ℝ) + P.c₂

/-- The profile's `ε = 10⁻⁷`. -/
def eps : ℝ := 1 / 10 ^ 7

/-- `w₀(t)² = e^{−θt} √(min(t − u, c₂) + ε)`. -/
def w0sq (t : ℝ) : ℝ := Real.exp (-((P.θ : ℝ) * t)) * Real.sqrt (min (t - P.u) P.c₂ + FarProfile.eps)

/-- `w(λ)⁻¹ = ∫_u^x w₀(t)² e^{2λt} dt`. -/
def winv (lam : ℝ) : ℝ := ∫ t in P.u..P.x, P.w0sq t * Real.exp (2 * lam * t)

/-- The far weight `w(λ)`. -/
def w (lam : ℝ) : ℝ := (P.winv lam)⁻¹

/-- `V = (M²/(c₁c₂²)) Σ_i α_i² ∫_u^x w₀(t)⁻² min((t − u − ih)₊, h) dt` with `M = 10`,
`h = c₂/10`: the constant of [X, (5.19)] without its `ε`. -/
def V : ℝ :=
  100 / ((P.c₁ : ℝ) * (P.c₂ : ℝ) ^ 2) * ∑ i : Fin 10, ((P.α i : ℝ)) ^ 2 *
    ∫ t in P.u..P.x, (P.w0sq t)⁻¹ * min (max 0 (t - P.u - (i.val : ℝ) * (P.c₂ / 10))) (P.c₂ / 10)

end FarProfile

/-- The inherited far profile (`config_v4.py`: `C1`, `C2`, `THETA`, `ALPHA`). -/
def inherited : FarProfile where
  c₁ := 9035 / 100000
  c₂ := 235968 / 1000000
  θ := 128683 / 100000
  α := ![788827218 / 10000000000, 849386148 / 10000000000, 895629779 / 10000000000,
    938231516 / 10000000000, 979710491 / 10000000000, 1021284916 / 10000000000,
    1063732939 / 10000000000, 1107651869 / 10000000000, 1153565492 / 10000000000,
    1201979632 / 10000000000]

/-- The retuned far profile (`far_enclosures.CANDIDATE`). -/
def retuned : FarProfile where
  c₁ := 821922 / 10000000
  c₂ := 2170903 / 10000000
  θ := 14964274 / 10000000
  α := ![806195583 / 10000000000, 862705300 / 10000000000, 905489307 / 10000000000,
    944644867 / 10000000000, 982543287 / 10000000000, 1020315591 / 10000000000,
    1058668825 / 10000000000, 1098131140 / 10000000000, 1139152197 / 10000000000,
    1182153903 / 10000000000]

end GradedNear.Kernel
