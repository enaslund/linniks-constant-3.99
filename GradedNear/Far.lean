module

public import GradedNear.Functions

/-!
# The far density lemma (paper §6; [X, Lemma 5.1, (5.19), p. 66])

Xylouris's Lemma 5.1 is a printed result and enters as the hypothesis `XylourisLemma51`,
stated as printed. With the notation of [X, §3.2.2, p. 25–26]:
* fix `c₁, c₂ > 0`, `M ∈ ℕ` and weights `α_i ≥ 0` (`i = 1, …, M`) with `Σ α_i = 1`;
* put `x = 2/3 + 3c₁ + c₂` and `u_i = 1/3 + 2c₁ + i c₂/M` (`i = 0, …, M`);
* let `w₀ : [u₀, x] → ℝ` be continuous, continuously differentiable except at finitely many
  points, with `1 ≪ w₀ ≪ 1` and `w₀′ ≪ 1`;
* put `λ₀ = (1/3) log log 𝓛`. For every character `χ` with a zero in `σ ≥ 1 − 𝓛⁻¹λ₀`,
  `|t| ≤ 1`, choose one such zero `ρ(χ) = 1 − λ(χ)/𝓛 + iγ(χ)`.

Then for `q ≥ q₀` (depending on all these choices),
`Σ_χ (∫_{u₀}^x w₀(t)² e^{2λ(χ)t} dt)⁻¹ ≤ (M² + ε)/(c₁c₂²) Σ_i α_i² ∫_{u_{i−1}}^x w₀(t)⁻² min{t − u_{i−1}, u_i − u_{i−1}} dt`.

The sum may run over any set of non-principal characters with one chosen zero each, since
the terms are positive and the print sums over all characters with a zero in the region.
Restricting to `χ ≠ 1` only weakens the statement. (For `q ≥ 2`, `L(s, χ₀)` has no zero in
the region anyway, but that is not needed.)
-/

@[expose] public section

noncomputable section

namespace GradedNear

open MeasureTheory

/-- The printed conditions on the profile `w₀` of [X, Lemma 5.1] on `[a, b]`: continuous,
continuously differentiable except at finitely many points, bounded above and below by positive
constants, with bounded derivative. -/
structure ProfileCondition (w₀ : ℝ → ℝ) (a b : ℝ) : Prop where
  cont : ContinuousOn w₀ (Set.Icc a b)
  smooth : ∃ E : Finset ℝ, ∀ t ∈ Set.Ioo a b, t ∉ E →
    ContDiffAt ℝ 1 w₀ t
  bounds : ∃ m K : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc a b, m ≤ w₀ t ∧ w₀ t ≤ K
  deriv_bound : ∃ K : ℝ, ∀ t ∈ Set.Ioo a b, |deriv w₀ t| ≤ K

/-- **[X, Lemma 5.1, (5.19), p. 66]**, as printed (see the module docstring). -/
def XylourisLemma51 : Prop :=
  ∀ (c₁ c₂ : ℝ), 0 < c₁ → 0 < c₂ → ∀ (M : ℕ) (α : Fin M → ℝ), (∀ i, 0 ≤ α i) →
    ∑ i, α i = 1 → ∀ w₀ : ℝ → ℝ,
    ProfileCondition w₀ (1 / 3 + 2 * c₁) (2 / 3 + 3 * c₁ + c₂) →
    ∀ ε : ℝ, 0 < ε → ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ (s : Finset (DirichletCharacter ℂ q)) (ρ : DirichletCharacter ℂ q → ℂ),
        (∀ χ ∈ s, χ ≠ 1 ∧ DirichletCharacter.LFunction χ (ρ χ) = 0 ∧
          1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (ρ χ).re ∧
          |(ρ χ).im| ≤ 1) →
        ∑ χ ∈ s, (∫ t in (1 / 3 + 2 * c₁)..(2 / 3 + 3 * c₁ + c₂),
            w₀ t ^ 2 * Real.exp (2 * ((1 - (ρ χ).re) * Real.log q) * t))⁻¹ ≤
          (M ^ 2 + ε) / (c₁ * c₂ ^ 2) * ∑ i : Fin M, α i ^ 2 *
            ∫ t in (1 / 3 + 2 * c₁ + i.val * c₂ / M)..(2 / 3 + 3 * c₁ + c₂),
              (w₀ t)⁻¹ ^ 2 * min (t - (1 / 3 + 2 * c₁ + i.val * c₂ / M)) (c₂ / M)

end GradedNear
