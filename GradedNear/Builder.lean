module

public import GradedNear.Entry
public import GradedNear.Cert.Bins

/-!
# The graded near lemma in the leaf builders' normalization

The leaf builders (`computations/sieve_near/sieve_inputs.py` in the research repository) normalize the threshold form
as in Corollary 8.10 of the paper, not as in Proposition 8.8. For a row with an upper bound `I_u ≥ I_B` and a normalizer `D_u > 0`
(an upper bound for `D(0)`), they compute:
* the feature `r_j / √(I_u D_u) - η` of an entry, where `r_j` is a lower bound for its kept terms
  minus `f(0)/6`;
* the diagonal `(1 + η) D_j⁺ / D_u`, where `D_j⁺ ≥ D(δ_j) - d₁ + e_j`;
* the radius `(1 + η)(d₁ / D_u + η)`.

`builder_threshold` proves (T) for exactly these quantities, with no numerical side conditions.
It applies the zero form `graded_near_threshold` with the smaller allowance
`η' = η · min(1, √(I_B D_u), D_u)` and the normalizer `D_n = D_u / (1 + η')`. Every builder
quantity is then on the safe side of the corresponding quantity of the zero form
(`threshold_weaken`).

`pairExcess_eq_zero` shows that same-character pairs at separated normalized heights have no pair
excess, as the rows of §6.5 assume for them.
-/

@[expose] public section

open Complex

noncomputable section

namespace GradedNear

/-- **Same-character pairs at separated heights have no pair excess.** If `g(0) > 0`, there is an
`M > 0` such that an entry `j` has `e_j = 0` whenever every other entry of the same character is
at normalized height distance `|γ_j - γ_k| log q ≥ M` from it. The reason is that
`|G(x + iY)| ≤ d₁` for `|Y| ≥ M` and `x` in the fixed range of `-σ_jk`. -/
theorem pairExcess_eq_zero (D : NearData) (hD : D.Valid) (hg0 : 0 < D.g 0) :
    ∃ M : ℝ, 0 < M ∧ ∀ {q : ℕ} {ι : Type} [Fintype ι] (E : Entries q ι), (∀ j, E.δ j ∈ D.Δ) →
      ∀ j, (∀ k, k ≠ j → E.χ k = E.χ j → M ≤ |E.γ j - E.γ k| * Real.log q) →
        pairExcess D E j = 0 := by
  classical
  have hd₁ : 0 < D.d₁ := by unfold NearData.d₁; linarith
  obtain ⟨M, hM, hdec⟩ := laplace_decay hD.g_cond1 (|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|) hd₁
  refine ⟨M, hM, fun {q} {ι} _ E hΔ j hsep => ?_⟩
  unfold pairExcess
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' : k ≠ j ∧ E.χ k = E.χ j := by
    unfold sameCharOthers at hk
    exact (Finset.mem_filter.1 hk).2
  have hY : M ≤ |(E.γ j - E.γ k) * Real.log q| := by
    rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg q)]
    exact hsep k hk'.1 hk'.2
  have hx : -(D.s₁ - E.δ j - E.δ k) ∈
      Set.Icc (-(|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|)) (|D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ|) := by
    have hj := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ j)
    have hk2 := Finset.single_le_sum (f := fun δ => |δ|) (fun _ _ => abs_nonneg _) (hΔ k)
    rw [Set.mem_Icc, ← abs_le]
    calc |-(D.s₁ - E.δ j - E.δ k)| = |D.s₁ - E.δ j - E.δ k| := abs_neg _
      _ ≤ |D.s₁ - E.δ j| + |E.δ k| := abs_sub _ _
      _ ≤ |D.s₁| + |E.δ j| + |E.δ k| := by gcongr; exact abs_sub _ _
      _ ≤ |D.s₁| + 2 * ∑ δ ∈ D.Δ, |δ| := by linarith
  have h := hdec _ hx _ hY
  apply max_eq_left
  have := (abs_le.1 (Complex.abs_re_le_norm (laplace D.g (((-(D.s₁ - E.δ j - E.δ k) : ℝ) : ℂ) +
    (((E.γ j - E.γ k) * Real.log q : ℝ) : ℂ) * I)))).2
  linarith

/-- (T) survives lowering the features (or making them `≤ 0`), raising the diagonals and
raising the radius. -/
lemma threshold_weaken {ι : Type*} [Fintype ι] {v v' Dg Dg' : ι → ℝ} {d d' τ : ℝ}
    (hDg : ∀ j, 0 < Dg j) (hDD : ∀ j, Dg j ≤ Dg' j) (hvv : ∀ j, v' j ≤ v j ∨ v' j ≤ 0)
    (hd : 0 < d) (hdd : d ≤ d') (hτ0 : 0 ≤ τ) (hτd : τ ≤ Real.sqrt d)
    (hT : ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j ≤ 1 - τ ^ 2 / d) :
    τ ≤ Real.sqrt d' ∧ ∑ j, (max 0 (v' j - τ)) ^ 2 / Dg' j ≤ 1 - τ ^ 2 / d' := by
  refine ⟨hτd.trans (Real.sqrt_le_sqrt hdd), ?_⟩
  have h1 : ∑ j, (max 0 (v' j - τ)) ^ 2 / Dg' j ≤ ∑ j, (max 0 (v j - τ)) ^ 2 / Dg j :=
    Finset.sum_le_sum fun j _ => Cert.term_le (hvv j) hτ0 (hDg j) (hDD j)
  have h2 : τ ^ 2 / d' ≤ τ ^ 2 / d := div_le_div_of_nonneg_left (sq_nonneg _) hd hdd
  linarith

/-- **The graded near lemma in the normalization of the leaf builders.** Fix the row data `D`, a
zero count `K₀`, the allowance `η > 0`, an upper bound `I_u ≥ I_B` and a normalizer `D_u > 0`.
There are `M`, `δ < 1` and `q₀` such that, for entries with kept zeros as in
`graded_near_threshold`, the following holds. Suppose each `r_j` is at most the entry's kept
terms minus `f(0)/6` (`keptBound … 0`), or `r_j ≤ 0`, and each `D_j⁺` is at least the entry's
diagonal numerator `D(δ_j) - d₁ + e_j > 0`. Then (T) holds with the features
`r_j / √(I_u D_u) - η`, the diagonals `(1 + η) D_j⁺ / D_u` and the radius
`(1 + η)(d₁ / D_u + η)`. -/
theorem builder_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) {Iu Du : ℝ} (hIu : D.IB ≤ Iu)
    (hDu : 0 < Du) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ) ≤ K₀) →
          ∀ r De : ι → ℝ, (∀ j, r j ≤ keptBound D E Sz 0 j ∨ r j ≤ 0) →
            (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            (∀ j, D.Dδ (E.δ j) - D.d₁ + pairExcess D E j ≤ De j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((1 + η) * (D.d₁ / Du + η)) ∧
              ∑ j, (max 0 (r j / Real.sqrt (Iu * Du) - η - τ)) ^ 2 / ((1 + η) * De j / Du) ≤
                1 - τ ^ 2 / ((1 + η) * (D.d₁ / Du + η)) := by
  have hIB := hD.IB_pos
  have hNpos : 0 < Real.sqrt (D.IB * Du) := Real.sqrt_pos.2 (by positivity)
  have hmin : 0 < min 1 (min (Real.sqrt (D.IB * Du)) Du) :=
    lt_min one_pos (lt_min hNpos hDu)
  have hη'pos : 0 < η * min 1 (min (Real.sqrt (D.IB * Du)) Du) := mul_pos hη hmin
  have hη'η : η * min 1 (min (Real.sqrt (D.IB * Du)) Du) ≤ η := by
    have := min_le_left 1 (min (Real.sqrt (D.IB * Du)) Du)
    nlinarith
  have hη'N : η * min 1 (min (Real.sqrt (D.IB * Du)) Du) ≤ η * Real.sqrt (D.IB * Du) :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_left _ _)) hη.le
  have hη'D : η * min 1 (min (Real.sqrt (D.IB * Du)) Du) ≤ η * Du :=
    mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hη.le
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ :=
    graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη'pos
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj Sz hSz hsep hK r De hr hDj hDe
  set η' := η * min 1 (min (Real.sqrt (D.IB * Du)) Du) with hη'
  set N := Real.sqrt (D.IB * Du) with hN
  have hDnpos : 0 < Du / (1 + η') := div_pos hDu (by linarith)
  obtain ⟨τ, hτ0, hτd, hT⟩ :=
    h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj Sz hSz hsep hK (Du / (1 + η')) hDnpos hDj
  have hd₁ : 0 ≤ D.d₁ := by
    have := hD.g_cond2.nonneg 0 le_rfl
    unfold NearData.d₁; linarith
  have hNn : Real.sqrt ((1 + η') * D.IB * (Du / (1 + η'))) = N := by
    rw [hN]
    congr 1
    field_simp
  rw [hNn] at hT
  have hsq : N ≤ Real.sqrt (Iu * Du) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hIu hDu.le)
  have hw := threshold_weaken (v := fun j => keptBound D E Sz η' j / N)
    (v' := fun j => r j / Real.sqrt (Iu * Du) - η)
    (Dg := fun j => (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / (Du / (1 + η')))
    (Dg' := fun j => (1 + η) * De j / Du)
    (d := (D.d₁ + η') / (Du / (1 + η'))) (d' := (1 + η) * (D.d₁ / Du + η)) (τ := τ)
    (fun j => div_pos (hDj j) hDnpos) (fun j => ?_) (fun j => ?_)
    (div_pos (by linarith) hDnpos) ?_ hτ0 hτd hT
  · exact ⟨τ, hτ0, hw.1, hw.2⟩
  · -- the diagonals
    have e : (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / (Du / (1 + η')) =
        (1 + η') * (D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Du := by
      field_simp
    rw [e]
    apply div_le_div_of_nonneg_right _ hDu.le
    exact mul_le_mul (by linarith) (hDe j) (hDj j).le (by linarith)
  · -- the features
    by_cases hr0 : r j ≤ 0
    · right
      have : r j / Real.sqrt (Iu * Du) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hr0 (Real.sqrt_nonneg _)
      linarith
    · left
      have hrk : r j ≤ keptBound D E Sz 0 j := (hr j).resolve_right hr0
      have hk : keptBound D E Sz η' j = keptBound D E Sz 0 j - η' := by
        unfold keptBound; ring
      have hrpos : 0 < r j := lt_of_not_ge hr0
      have h1 : r j / Real.sqrt (Iu * Du) ≤ r j / N :=
        div_le_div_of_nonneg_left hrpos.le hNpos hsq
      have h2 : η' / N ≤ η := by
        rw [div_le_iff₀ hNpos]; linarith
      show r j / Real.sqrt (Iu * Du) - η ≤ keptBound D E Sz η' j / N
      rw [hk, sub_div]
      have h3 : r j / N ≤ keptBound D E Sz 0 j / N := div_le_div_of_nonneg_right hrk hNpos.le
      linarith
  · -- the radius
    have e1 : (D.d₁ + η') / (Du / (1 + η')) = (1 + η') * (D.d₁ + η') / Du := by
      field_simp
    have e2 : (1 + η) * (D.d₁ / Du + η) = (1 + η) * (D.d₁ + η * Du) / Du := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hDu.le
    exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

end GradedNear
