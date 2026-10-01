module

public import GradedNear.Defs

/-!
# Zeros of a non-principal `L`-function in a closed disc are finite

`L(s, χ)` is entire for `χ ≠ 1` and not identically zero (it does not vanish at `s = 2`), so
its zeros are isolated and a compact disc contains finitely many.
-/

@[expose] public section

namespace GradedNear

theorem LFunction_zeros_finite {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (c : ℂ) (r : ℝ) :
    {ρ : ℂ | ‖c - ρ‖ ≤ r ∧ DirichletCharacter.LFunction χ ρ = 0}.Finite := by
  -- `L(s, χ)` is entire, hence analytic on all of `ℂ`.
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  -- It does not vanish at `s = 2`.
  have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num)
  -- Identity theorem: either `L ≡ 0`, or its non-zeros are codiscrete in `ℂ`.
  rcases ha.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with h | h
  · exact absurd (h (Set.mem_univ 2)) h2
  -- Restrict to the compact disc, where a codiscrete set has finite complement.
  have hK : IsCompact (Metric.closedBall c r) := isCompact_closedBall c r
  have hfin := hK.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono (Set.subset_univ _) h)
  refine hfin.subset ?_
  rintro ρ ⟨hρ, hL⟩
  refine ⟨?_, ?_⟩
  · rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm]
  · simp [hL]

end GradedNear
