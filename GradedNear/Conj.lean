module

public import GradedNear.Entry

/-!
# Conjugate zeros of a real character's `L`-function

For a non-principal Dirichlet character `χ` with real values, `L(s̄, χ) = conj L(s, χ)` for every
`s` (`LFunction_conj`): the Dirichlet series has real coefficients, so the identity holds termwise
for `Re s > 1`, and the identity theorem extends it to all `s`, since both `L(·, χ)` and
`s ↦ conj L(s̄, χ)` are entire. So the zeros come in conjugate pairs
(`LFunction_conj_eq_zero_iff`), and since conjugation `f ↦ conj ∘ f ∘ conj` preserves the order of
vanishing (`analyticOrderAt_conj_conj`), `ρ` and `ρ̄` have the same multiplicity (`zmult_conj`).
Hence the multiplicity hypothesis of `keptBound_pair_neg` holds automatically for the conjugate
pair `{ρ, ρ̄}` of a real character (`keptBound_pair_neg_real`).

Real values are stated as `∀ a, conj (χ a) = χ a`; a character equal to its own inverse has real
values (`conj_apply_of_inv_eq_self`).
-/

@[expose] public section

open Complex Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GradedNear

/-! ## Conjugation and the order of vanishing -/

/-- Conjugation maps neighbourhoods of `z̄` into neighbourhoods of `z`. -/
lemma tendsto_conj_nhds_conj (z : ℂ) : Tendsto (starRingEnd ℂ) (𝓝 (conj z)) (𝓝 z) := by
  simpa using Complex.continuous_conj.tendsto (conj z)

/-- If `g` is analytic at `z₀`, then `z ↦ conj (g (conj z))` is analytic at `conj z₀`. -/
lemma analyticAt_conj_conj {g : ℂ → ℂ} {z₀ : ℂ} (hg : AnalyticAt ℂ g z₀) :
    AnalyticAt ℂ (fun z => conj (g (conj z))) (conj z₀) := by
  rw [analyticAt_iff_eventually_differentiableAt] at hg ⊢
  filter_upwards [(tendsto_conj_nhds_conj z₀).eventually hg] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

/-- The order of vanishing is invariant under `f ↦ conj ∘ f ∘ conj`, taken at `conj z₀`: if
`f(z) = (z - z₀)ⁿ g(z)` near `z₀` with `g(z₀) ≠ 0`, then
`conj f(z̄) = (z - z̄₀)ⁿ conj g(z̄)` near `z̄₀`; and `f` vanishes near `z₀` iff `conj ∘ f ∘ conj`
vanishes near `z̄₀`. -/
lemma analyticOrderAt_conj_conj {f : ℂ → ℂ} {z₀ : ℂ} (hf : AnalyticAt ℂ f z₀) :
    analyticOrderAt (fun z => conj (f (conj z))) (conj z₀) = analyticOrderAt f z₀ := by
  have hT := tendsto_conj_nhds_conj z₀
  rcases eq_or_ne (analyticOrderAt f z₀) ⊤ with htop | htop
  · rw [htop, analyticOrderAt_eq_top]
    filter_upwards [hT.eventually (analyticOrderAt_eq_top.mp htop)] with z hz
    rw [hz, map_zero]
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn]
    obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hn.symm
    refine (analyticAt_conj_conj hf).analyticOrderAt_eq_natCast.mpr
      ⟨fun z => conj (g (conj z)), analyticAt_conj_conj hg, by simpa using hg0, ?_⟩
    filter_upwards [hT.eventually hfg] with z hz
    rw [hz, smul_eq_mul, smul_eq_mul, map_mul, map_pow, map_sub, conj_conj]

/-! ## `L(s̄, χ) = conj L(s, χ)` for a real character -/

variable {q : ℕ}

/-- A character equal to its inverse has real values: `conj χ(a) = χ⁻¹(a) = χ(a)`. -/
lemma conj_apply_of_inv_eq_self {χ : DirichletCharacter ℂ q} (h : χ⁻¹ = χ) (a : ZMod q) :
    conj (χ a) = χ a := by
  have := MulChar.star_apply' χ a
  rw [h] at this
  exact this

/-- A term of the Dirichlet series of a real-valued `χ`: `conj (χ(n) / n^{s̄}) = χ(n) / n^s`. -/
lemma conj_LSeries_term_conj (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (s : ℂ) (n : ℕ) :
    conj (LSeries.term (fun n : ℕ => χ n) (conj s) n) = LSeries.term (fun n : ℕ => χ n) s n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀, hreal,
      ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]

variable [NeZero q]

/-- For `Re s > 1` and real-valued `χ`: `conj L(s̄, χ) = L(s, χ)`, termwise in the Dirichlet
series. -/
lemma conj_LFunction_conj_of_one_lt_re (χ : DirichletCharacter ℂ q)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) {s : ℂ} (hs : 1 < s.re) :
    conj (DirichletCharacter.LFunction χ (conj s)) = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ (by rwa [conj_re]),
    DirichletCharacter.LFunction_eq_LSeries χ hs, LSeries, LSeries, conj_tsum]
  exact tsum_congr fun n => conj_LSeries_term_conj χ hreal s n

/-- **Conjugation symmetry of a real character's `L`-function**: for a non-principal `χ` with
real values, `L(s̄, χ) = conj L(s, χ)` for all `s`. Both `L(·, χ)` and `s ↦ conj L(s̄, χ)` are
entire and they agree on the open set `Re s > 1`, so they agree everywhere by the identity
theorem. -/
theorem LFunction_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (s : ℂ) :
    DirichletCharacter.LFunction χ (conj s) = conj (DirichletCharacter.LFunction χ s) := by
  have hL := DirichletCharacter.differentiable_LFunction hχ
  have h1 : AnalyticOnNhd ℂ (fun z => conj (DirichletCharacter.LFunction χ (conj z))) Set.univ :=
    analyticOnNhd_univ_iff_differentiable.mpr fun z => differentiableAt_conj_conj_iff.mpr (hL _)
  have heq : (fun z => conj (DirichletCharacter.LFunction χ (conj z))) =
      DirichletCharacter.LFunction χ :=
    h1.eq_of_eventuallyEq (analyticOnNhd_univ_iff_differentiable.mpr hL) (z₀ := 2) <|
      eventuallyEq_of_mem ((isOpen_lt continuous_const continuous_re).mem_nhds
        (show (1 : ℝ) < (2 : ℂ).re by norm_num))
        fun z hz => conj_LFunction_conj_of_one_lt_re χ hreal hz
  calc DirichletCharacter.LFunction χ (conj s)
      = conj (conj (DirichletCharacter.LFunction χ (conj s))) := (conj_conj _).symm
    _ = conj (DirichletCharacter.LFunction χ s) := by
      rw [show conj (DirichletCharacter.LFunction χ (conj s)) = DirichletCharacter.LFunction χ s
        from congrFun heq s]

/-- For a non-principal real-valued `χ`, `ρ̄` is a zero of `L(·, χ)` iff `ρ` is. -/
theorem LFunction_conj_eq_zero_iff {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    DirichletCharacter.LFunction χ (conj ρ) = 0 ↔ DirichletCharacter.LFunction χ ρ = 0 := by
  rw [LFunction_conj hχ hreal, map_eq_zero]

/-- For a non-principal real-valued `χ`, `L(·, χ)` has the same order of vanishing at `ρ̄` as at
`ρ` (in `ℕ∞`). -/
theorem analyticOrderAt_LFunction_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    analyticOrderAt (DirichletCharacter.LFunction χ) (conj ρ) =
      analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
  have hfun : (fun z => conj (DirichletCharacter.LFunction χ (conj z))) =
      DirichletCharacter.LFunction χ := by
    funext z
    rw [LFunction_conj hχ hreal, conj_conj]
  rw [← analyticOrderAt_conj_conj
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ), hfun]

/-- **Conjugate zeros of a real character's `L`-function have equal multiplicity**: for a
non-principal real-valued `χ`, `m(ρ̄) = m(ρ)`. -/
theorem zmult_conj {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hreal : ∀ a : ZMod q, conj (χ a) = χ a) (ρ : ℂ) :
    zmult χ (conj ρ) = zmult χ ρ := by
  simp only [zmult, analyticOrderNatAt, analyticOrderAt_LFunction_conj hχ hreal ρ]

variable {ι : Type*}

/-- **`keptBound_pair_neg` for the conjugate pair of a real character**: the entry keeps a zero
`ρ` at its height and the conjugate zero `ρ̄`. For a real character, conjugate zeros have equal
multiplicity (`zmult_conj`), so the multiplicity hypothesis of `keptBound_pair_neg` is automatic.
All other hypotheses are those of `keptBound_pair_neg` with `ρ' = ρ̄`; the zero hypothesis
`hρ'` follows from `L(ρ, χ) = 0` by `LFunction_conj_eq_zero_iff`. -/
theorem keptBound_pair_neg_real (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1)
    (hreal : ∀ a : ZMod q, starRingEnd ℂ (E.χ j a) = E.χ j a) {ρ : ℂ} {hi C : ℝ}
    (hne : ρ ≠ starRingEnd ℂ ρ) (hS : Sz j = {ρ, starRingEnd ℂ ρ}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) (starRingEnd ℂ ρ) = 0)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) (starRingEnd ℂ ρ)) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ 0 :=
  keptBound_pair_neg D hD hf2 E Sz j hχ hne hS hγ hhi hρ' (zmult_conj hχ hreal ρ).le hC

end GradedNear
