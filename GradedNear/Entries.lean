module

public import GradedNear.Gram

/-!
# Bounds for the Gram entries

* principal entries (same character) from [X, Lemma 3.1]:
  `𝓛⁻¹ Re primeSum(1, g, s) ≤ Re G((s - 1)𝓛) + ε`;
* non-principal entries (distinct characters) from [X, Lemma 3.2], when no zero of the
  quotient `L`-function in the local disc lies to the right of `s`: `≤ g(0)/6 + ε`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

/-- Eventually `√(log log q) ≥ K` and `log log q ≥ K`. -/
lemma eventually_loglog_ge (K : ℝ) : ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
    K ≤ Real.sqrt (Real.log (Real.log q)) ∧ K ≤ Real.log (Real.log q) ∧ 2 ≤ q := by
  -- choose q₀ with log log q₀ ≥ max K² K + 1
  set M : ℝ := max (K ^ 2) K + 1
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (Real.exp M))
  refine ⟨max N 2, fun q hq => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqN : (N : ℝ) ≤ q := by exact_mod_cast le_trans (le_max_left _ _) hq
  have h1 : Real.exp (Real.exp M) < q := lt_of_lt_of_le hN hqN
  have h2 : Real.exp M < Real.log q := by
    rw [Real.lt_log_iff_exp_lt (by exact_mod_cast (show 0 < q by omega))]; exact h1
  have h3 : M < Real.log (Real.log q) := by
    rw [Real.lt_log_iff_exp_lt (lt_trans (Real.exp_pos M) h2)]; exact h2
  have hM1 : K ^ 2 < Real.log (Real.log q) := by
    have := le_max_left (K ^ 2) K; linarith
  have hM2 : K < Real.log (Real.log q) := by
    have := le_max_right (K ^ 2) K; linarith
  refine ⟨?_, hM2.le, hq2⟩
  calc K ≤ |K| := le_abs_self K
    _ = Real.sqrt (K ^ 2) := (Real.sqrt_sq_eq_abs K).symm
    _ ≤ Real.sqrt (Real.log (Real.log q)) := Real.sqrt_le_sqrt hM1.le

/-- Principal Gram entries: for fixed `K`, eventually, for every `s` with
`|Re s - 1| ≤ K / log q` and `|Im s| ≤ log q`,
`Re primeSum(1, g, s) / log q ≤ Re G((s - 1) log q) + ε`. -/
lemma principal_entry (hX31 : XylourisLemma31) {g : ℝ → ℝ} {xg Bg : ℝ}
    (hg : Condition1 g xg Bg) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ s : ℂ, |s.re - 1| ≤ K / Real.log q → |s.im| ≤ Real.log q →
      (primeSum (1 : DirichletCharacter ℂ q) g s).re / Real.log q ≤
        (laplace g ((s - 1) * (Real.log q : ℂ))).re + ε := by
  obtain ⟨C, q₁, hC⟩ := hX31 g xg Bg hg
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge (max K (|C| / ε + 1))
  refine ⟨max q₁ q₂, fun q hq s hre him => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  have hq2 : q₂ ≤ q := le_trans (le_max_right _ _) hq
  obtain ⟨hsq, hll, hq2'⟩ := hq₂ q hq2
  have hℓ := log_q_pos hq2'
  have hll_pos : 0 < Real.log (Real.log q) :=
    lt_of_lt_of_le (by positivity) (le_trans (le_max_right _ _) hll)
  have hreg : LemmaRegion q s := by
    refine ⟨le_trans hre ?_, him⟩
    exact div_le_div_of_nonneg_right (le_trans (le_max_left _ _) hsq) hℓ.le
  have hb := hC q hq1 s hreg
  have hre_le : (primeSum (1 : DirichletCharacter ℂ q) g s).re ≤
      Real.log q * (laplace g ((s - 1) * (Real.log q : ℂ))).re + C * Real.log q /
        Real.log (Real.log q) := by
    have h1 := (Complex.re_le_norm (primeSum (1 : DirichletCharacter ℂ q) g s - (Real.log q : ℂ) *
      laplace g ((s - 1) * (Real.log q : ℂ)))).trans hb
    rw [Complex.sub_re, Complex.re_ofReal_mul] at h1
    linarith
  have hsmall : C / Real.log (Real.log q) ≤ ε := by
    rw [div_le_iff₀ hll_pos]
    have h2 : |C| / ε + 1 ≤ Real.log (Real.log q) := le_trans (le_max_right _ _) hll
    have h3 : |C| ≤ ε * (Real.log (Real.log q) - 1) := by
      rw [div_add_one hε.ne', div_le_iff₀ hε] at h2
      nlinarith [abs_nonneg C]
    nlinarith [le_abs_self C]
  rw [div_le_iff₀ hℓ]
  have : C * Real.log q / Real.log (Real.log q) = C / Real.log (Real.log q) * Real.log q := by
    ring
  rw [this] at hre_le
  nlinarith

/-- A zero sum with every term's real part nonnegative is nonnegative. -/
lemma zeroSum_nonneg {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {g : ℝ → ℝ}
    (hg2 : Condition2 g) (s : ℂ) (δ : ℝ)
    (hz : ∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 →
      ‖(1 + (s.im : ℂ) * I) - ρ‖ ≤ δ → ρ.re ≤ s.re)
    (hℓ : 0 ≤ Real.log q) :
    0 ≤ zeroSum χ g s δ := by
  unfold zeroSum
  refine finsum_nonneg fun ρ => finsum_nonneg fun hρ => ?_
  refine mul_nonneg (Nat.cast_nonneg _) (hg2.re_nonneg _ ?_)
  have hle := hz ρ hρ.2 hρ.1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.sub_re]
  exact mul_nonneg (by linarith) hℓ

/-- Non-principal Gram entries: for fixed `K`, eventually, for every non-principal `ψ` and
every `s` with `|Re s - 1| ≤ K / log q` and `|Im s| ≤ log q`, if no zero of `L(·, ψ)` within
distance `δ` of `1 + i Im s` lies to the right of `s`, then
`Re primeSum(ψ, g, s) / log q ≤ g(0)/6 + ε`. -/
lemma nonprincipal_entry (hX32 : XylourisLemma32) {g : ℝ → ℝ} {xg Bg : ℝ}
    (hg : Condition1 g xg Bg) (hg2 : Condition2 g) (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ s : ℂ,
        |s.re - 1| ≤ K / Real.log q → |s.im| ≤ Real.log q →
        (∀ ρ : ℂ, DirichletCharacter.LFunction ψ ρ = 0 →
          ‖(1 + (s.im : ℂ) * I) - ρ‖ ≤ δ → ρ.re ≤ s.re) →
        (primeSum ψ g s).re / Real.log q ≤ g 0 / 6 + ε := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ :=
    hX32 g xg Bg hg (hg2.nonneg 0 le_rfl) ε hε
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge K
  refine ⟨δ, hδ0, hδ1, max q₁ q₂, fun q _ hq ψ hψ s hre him hz => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  obtain ⟨hsq, -, hq2'⟩ := hq₂ q (le_trans (le_max_right _ _) hq)
  have hℓ := log_q_pos hq2'
  have hreg : LemmaRegion q s :=
    ⟨le_trans hre (div_le_div_of_nonneg_right hsq hℓ.le), him⟩
  have hb := hq₁ q hq1 ψ hψ s hreg
  have hzs := zeroSum_nonneg ψ hg2 s δ hz hℓ.le
  rw [div_le_iff₀ hℓ]
  nlinarith

end GradedNear
