module

public import GradedNear.Defs
public import GradedNear.LaplaceDecay
public import GradedNear.ZeroFinite
public import GradedNear.Entries

/-!
# The response lemma (paper Lemma 8.7)

For an entry `(χ, γ, σ)`, the response `R = -𝓛⁻¹ Re Σ Λ(n) χ(n) n^{-((1 - σ/𝓛) + iγ)} f(t_n)`
is bounded below by the zeros kept in a finite set `S` of zeros of `L(s, χ)` in the local disc:
`R ≥ Σ_{ρ ∈ S} m_ρ Re F((1 - Re ρ)𝓛 - σ + i(γ - Im ρ)𝓛) - f(0)/6 - η`, provided every disc zero
not in `S` either lies to the right of the anchor (`(1 - Re ρ)𝓛 ≥ σ`) or is at normalized
height distance `≥ M`, and at most `K₀` of the latter (with multiplicity) lie to the left.

Proof: [X, Lemma 3.2]; the disc zeros are finite; zeros to the right have `Re F ≥ 0` by
Condition 2; the adverse zeros have `|F| ≤ η/(2(K₀+1))` by the decay of `F`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

lemma response_arg {q : ℕ} (σ γ : ℝ) (ρ : ℂ) (hℓ : Real.log q ≠ 0) :
    ((((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I - ρ) * (Real.log q : ℂ) =
      ((((1 - ρ.re) * Real.log q - σ : ℝ)) : ℂ) + (((γ - ρ.im) * Real.log q : ℝ) : ℂ) * I := by
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
      Complex.add_im]
    field_simp
    ring
  · simp only [Complex.mul_re, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.sub_im,
      Complex.add_im]
    ring

/-- **The response lemma** (paper Lemma 8.7; [X, Lemma 3.2]). Fix a test `f` satisfying Conditions 1
and 2, a bound `σmax` for the anchors, a count `K₀` and `η > 0`. There are a separation `M > 0`, a
disc radius `δ < 1` and a `q₀` such that the following holds for `q ≥ q₀`, a non-principal `χ`,
an anchor `|σ| ≤ σmax` and a height `|γ| ≤ log q`. Keep a finite set `S` of zeros of `L(s, χ)` in
the disc of radius `δ` about `1 + iγ`. Suppose every other disc zero with `λ_ρ = (1 - Re ρ) log q
< σ` is at normalized height distance `≥ M`, and there are at most `K₀` of them, with
multiplicity. Then the response of `(χ, γ, σ)` is at least
`Σ_{ρ ∈ S} m_ρ Re F((λ_ρ - σ) + i(γ - Im ρ) log q) - f(0)/6 - η`. -/
theorem response_lemma (hX32 : XylourisLemma32) {f : ℝ → ℝ} {x₀ B : ℝ}
    (hf1 : Condition1 f x₀ B) (hf2 : Condition2 f) (σmax : ℝ) (K₀ : ℕ) {η : ℝ}
    (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ γ : ℝ, |σ| ≤ σmax → |γ| ≤ Real.log q →
      ∀ Sz : Finset ℂ,
        (∀ ρ ∈ Sz, DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ) →
        (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ →
          ρ ∉ Sz → (1 - ρ.re) * Real.log q < σ → M ≤ |γ - ρ.im| * Real.log q) →
        (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
            ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ},
          zmult χ ρ) ≤ K₀ →
        ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ - f 0 / 6 - η ≤ responseAt χ f σ γ := by
  obtain ⟨δ, hδ0, hδ1, q₁, hq₁⟩ := hX32 f x₀ B hf1 (hf2.nonneg 0 le_rfl) (η / 2) (half_pos hη)
  have hK1 : (0 : ℝ) < (K₀ : ℝ) + 1 := by positivity
  set ε' : ℝ := η / 2 / ((K₀ : ℝ) + 1) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨M, hM, hdecay⟩ := laplace_decay hf1 σmax hε'pos
  obtain ⟨q₂, hq₂⟩ := eventually_loglog_ge σmax
  refine ⟨M, hM, δ, hδ0, hδ1, max q₁ q₂, fun q _ hq χ hχ σ γ hσ hγ Sz hSz hsep hK => ?_⟩
  have hq1 : q₁ ≤ q := le_trans (le_max_left _ _) hq
  obtain ⟨hsq, -, hq2⟩ := hq₂ q (le_trans (le_max_right _ _) hq)
  have hℓ := log_q_pos hq2
  set s : ℂ := (((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I with hs
  have hsre : s.re = 1 - σ / Real.log q := by
    simp only [hs, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hsim : s.im = γ := by
    simp only [hs, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, mul_zero, mul_one, zero_add, add_zero]
  have hreg : LemmaRegion q s := by
    refine ⟨?_, by rw [hsim]; exact hγ⟩
    rw [hsre, show 1 - σ / Real.log q - 1 = -(σ / Real.log q) by ring, abs_neg, abs_div,
      abs_of_pos hℓ]
    exact div_le_div_of_nonneg_right (hσ.trans hsq) hℓ.le
  have hX := hq₁ q hq1 χ hχ s hreg
  -- the zeros in the disc
  set Z : Set ℂ := {ρ : ℂ | ‖(1 + (s.im : ℂ) * I) - ρ‖ ≤ δ ∧
    DirichletCharacter.LFunction χ ρ = 0} with hZ
  have hZfin : Z.Finite := LFunction_zeros_finite hχ _ _
  have hzs : zeroSum χ f s δ = ∑ ρ ∈ hZfin.toFinset, zmult χ ρ * zeroTerm f q σ γ ρ := by
    unfold zeroSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hZfin]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold zeroTerm
    rw [hs, response_arg σ γ ρ hℓ.ne']
  have hmem : ∀ ρ, ρ ∈ hZfin.toFinset ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ := by
    intro ρ
    rw [Set.Finite.mem_toFinset, hZ, Set.mem_ofPred_eq, hsim]
    exact And.comm
  have hSsub : Sz ⊆ hZfin.toFinset := fun ρ hρ => (hmem ρ).2 (hSz ρ hρ)
  -- split the zeros: kept, to the right of the anchor, adverse
  set g : ℂ → ℝ := fun ρ => zmult χ ρ * zeroTerm f q σ γ ρ with hg
  set T := hZfin.toFinset \ Sz with hT
  have hsplit : ∑ ρ ∈ hZfin.toFinset, g ρ = ∑ ρ ∈ Sz, g ρ +
      (∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ +
        ∑ ρ ∈ T.filter (fun ρ => ¬ (1 - ρ.re) * Real.log q < σ), g ρ) := by
    rw [Finset.sum_filter_add_sum_filter_not, hT, add_comm, Finset.sum_sdiff hSsub]
  -- zeros of L lie in Re ρ < 1
  have hre1 : ∀ ρ, DirichletCharacter.LFunction χ ρ = 0 → ρ.re < 1 := by
    intro ρ hρ
    by_contra h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (not_lt.1 h) hρ
  -- zeros to the right of the anchor contribute ≥ 0
  have hgood : 0 ≤ ∑ ρ ∈ T.filter (fun ρ => ¬ (1 - ρ.re) * Real.log q < σ), g ρ := by
    refine Finset.sum_nonneg fun ρ hρ => ?_
    rw [Finset.mem_filter] at hρ
    refine mul_nonneg (Nat.cast_nonneg _) (hf2.re_nonneg _ ?_)
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith [not_lt.1 hρ.2]
  -- adverse zeros: each term ≥ -ε', and their multiplicity is ≤ K₀
  have hadv_term : ∀ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ),
      -ε' ≤ zeroTerm f q σ γ ρ := by
    intro ρ hρ
    rw [Finset.mem_filter, hT, Finset.mem_sdiff] at hρ
    obtain ⟨⟨hρZ, hρS⟩, hρadv⟩ := hρ
    obtain ⟨hL, hd⟩ := (hmem ρ).1 hρZ
    have hsepρ := hsep ρ hL hd hρS hρadv
    have hr1 := hre1 ρ hL
    have hx : (1 - ρ.re) * Real.log q - σ ∈ Set.Icc (-σmax) σmax := by
      have h0 : 0 ≤ (1 - ρ.re) * Real.log q := mul_nonneg (by linarith) hℓ.le
      constructor
      · linarith [le_abs_self σ]
      · linarith [abs_nonneg σ]
    have hY : M ≤ |(γ - ρ.im) * Real.log q| := by
      rw [abs_mul, abs_of_pos hℓ]; exact hsepρ
    have := hdecay _ hx _ hY
    unfold zeroTerm
    have h1 := Complex.abs_re_le_norm (laplace f ((((1 - ρ.re) * Real.log q - σ : ℝ)) +
      (((γ - ρ.im) * Real.log q : ℝ) : ℂ) * I))
    linarith [neg_abs_le ((laplace f ((((1 - ρ.re) * Real.log q - σ : ℝ)) +
      (((γ - ρ.im) * Real.log q : ℝ) : ℂ) * I)).re)]
  have hadv_mult : ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), zmult χ ρ ≤ K₀ := by
    have hset : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
        ‖(1 + (γ : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz ∧ (1 - ρ.re) * Real.log q < σ} =
        ↑(T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ)) := by
      ext ρ
      simp only [Set.mem_ofPred_eq, Finset.coe_filter, hT, Finset.mem_sdiff, hmem]
      tauto
    rw [hset, finsum_mem_coe_finset] at hK
    exact hK
  have hadv : -(η / 2) ≤ ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ := by
    have h1 : ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), zmult χ ρ * (-ε') ≤
        ∑ ρ ∈ T.filter (fun ρ => (1 - ρ.re) * Real.log q < σ), g ρ :=
      Finset.sum_le_sum fun ρ hρ =>
        mul_le_mul_of_nonneg_left (hadv_term ρ hρ) (Nat.cast_nonneg _)
    rw [← Finset.sum_mul] at h1
    have h2 : (K₀ : ℝ) * ε' ≤ η / 2 := by
      rw [hε', mul_div_assoc']
      rw [div_le_iff₀ hK1]
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hadv_mult hε'pos.le]
  -- assemble
  have hzs' : ∑ ρ ∈ Sz, g ρ - η / 2 ≤ zeroSum χ f s δ := by
    rw [hzs, hsplit]; linarith
  unfold responseAt
  rw [← hs]
  have hℓpos := hℓ
  rw [le_div_iff₀ hℓpos]
  have : ∑ ρ ∈ Sz, zmult χ ρ * zeroTerm f q σ γ ρ = ∑ ρ ∈ Sz, g ρ := rfl
  rw [this]
  nlinarith [mul_le_mul_of_nonneg_left hzs' hℓpos.le]

end GradedNear
