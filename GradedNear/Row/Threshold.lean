module

public import GradedNear.Row.RowSound
public import GradedNear.Builder

/-!
# The stored integers of a checked row satisfy the threshold form

`row_threshold`: for a near row accepted by the checker (`RowNum`, from `rowCheck_sound`), the
graded near lemma (`builder_threshold`, conditional on X Lemmas 3.1–3.2, Burgess and Graham)
gives (T) for **the row's stored integers**:
`∃ τ ∈ [0, √(d/S)], Σ_j ((v_j/S − τ)₊)² / (D_j/S) ≤ 1 − τ²/(d/S)`,
for every family of entries of the configuration that the row describes. Each entry `j` is one
of the row's checked items (its stored feature `v_j` and diagonal `D_j`, and its semantics
`(hi, anc, sp)`), has offset `s − anc` in the near lemma, and for every values `(add, exc)` of its
semantics (`SpecSem`):
* its kept zeros give at least `F(hi − anc) + add − 1/6`, or that number is `≤ 0` (for an ordinary
  character, `keptBound_single` with `add = 0`; for the `rc` pair and the first family's second
  zero, `keptBound_pair`; for the shifted `rc` entry, `keptBound_pair_neg_real` with `add = -C_Z`);
* its pair excess is at most `exc`.

The zero-level conditions are those of `builder_threshold`. With `near_row_of_bins` this is the row
of the leaf LP at the configuration's masses.
-/

@[expose] public section

noncomputable section

open Complex

namespace GradedNear.Row

open Parabolic

lemma near_Dδ_eq (q : Params) (Δ : Finset ℝ) (x : ℝ) : (q.near Δ).Dδ x = (q.near ∅).Dδ x := rfl

lemma near_IB_eq (q : Params) (Δ : Finset ℝ) : (q.near Δ).IB = (q.near ∅).IB := rfl

/-- **The stored integers of a checked row satisfy (T)** for every configuration of entries that
the row describes (see the module docstring). -/
theorem row_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate)
    {p : RowCheckCore.RowP} {d : ℤ} {items : List RowCheckCore.Item} (hnum : RowNum p d items)
    (Δ : Finset ℝ) (hΔ : ∀ δ ∈ Δ, 0 ≤ δ) (K₀ : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q p.s1 (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι) (it : ι → RowCheckCore.Item),
        (∀ j, it j ∈ items) → (∀ j, E.δ j = (p.s : ℝ) - (it j).e.anc) → (∀ j, E.δ j ∈ Δ) →
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) →
        ((∃ k < p.m, p.hk k ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < ((ofCore p).near Δ).s - E.δ j →
            M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < ((ofCore p).near Δ).s - E.δ j},
              zmult (E.χ j) ρ) ≤ K₀) →
          (∀ j, ∀ add exc : ℝ, SpecSem (ofCore p) (it j).e.sp add exc →
            ((laplace (fpar (2 * (p.γ : ℝ))) ((((it j).e.hi : ℝ) - (it j).e.anc : ℝ) : ℂ)).re +
                add - 1 / 6 ≤ keptBound ((ofCore p).near Δ) E Sz 0 j ∨
              (laplace (fpar (2 * (p.γ : ℝ))) ((((it j).e.hi : ℝ) - (it j).e.anc : ℝ) : ℂ)).re +
                add - 1 / 6 ≤ 0) ∧
            pairExcess ((ofCore p).near Δ) E j ≤ exc) →
          ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((d : ℝ) / SR) ∧
            ∑ j, (max 0 (((it j).v : ℝ) / SR - τ)) ^ 2 / (((it j).D : ℝ) / SR) ≤
              1 - τ ^ 2 / ((d : ℝ) / SR) := by
  obtain ⟨hg, hLpos, Iu, Du, hIu, hDu, hrad, hent⟩ := hnum
  have hLpos' : ∀ k < (ofCore p).m, 0 < (ofCore p).Lk k := fun k hk => hLpos k hk
  have hD := Params.valid hg Δ hΔ hLpos'
  have hf2 : Condition2 ((ofCore p).near Δ).f := fpar_condition2 (Params.γ_pos' hg)
  have hIu' : ((ofCore p).near Δ).IB ≤ Iu := by rw [near_IB_eq]; exact hIu
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, H⟩ :=
    builder_threshold hX31 hX32 hBur hGr ((ofCore p).near Δ) hD hf2 K₀ ηR_pos hIu' hDu
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun q _ hq T hT0 hTl hsafe ι _ E it hit hδE hΔE hχ hγ hinj Sz
    hSz hsep hK hent' => ?_⟩
  have hd₁ := Params.d₁_eq hg Δ
  -- the entries' data from `EntValid`
  have hv := fun j => hent (it j) (hit j)
  choose add exc hv using hv
  choose hsem hanc hfeat hpos De hDe hDD using hv
  have hke := fun j => hent' j (add j) (exc j) (hsem j)
  have hsδ : ∀ j, ((ofCore p).near Δ).Dδ (E.δ j) = ((ofCore p).near ∅).Dδ ((ofCore p).s -
      (it j).e.anc) := fun j => by rw [near_Dδ_eq, hδE j]; rfl
  have hpe : ∀ j, 0 ≤ pairExcess ((ofCore p).near Δ) E j := fun j =>
    Finset.sum_nonneg fun k _ => le_max_left _ _
  obtain ⟨τ, hτ0, hτd, hT⟩ := H q hq T hT0 hTl (by simpa using hsafe) ι E hχ hγ hΔE
    (by simpa using hinj) Sz hSz hsep hK
    (fun j => (laplace (fpar (2 * (p.γ : ℝ))) ((((it j).e.hi : ℝ) - (it j).e.anc : ℝ) : ℂ)).re +
      add j - 1 / 6) De (fun j => (hke j).1)
    (fun j => by rw [hsδ, hd₁]; linarith [hpos j, hpe j])
    (fun j => by rw [hsδ, hd₁]; linarith [hDe j, (hke j).2])
  -- weaken to the stored integers
  have hDg : ∀ j, 0 < (1 + ηR) * De j / Du := fun j => by
    have := hpos j; have := hDe j; have := ηR_pos; have := (hsem j).exc_nonneg
    have : 0 < De j := by linarith
    positivity
  have hd0 : 0 < (1 + ηR) * (((ofCore p).near Δ).d₁ / Du + ηR) := by
    rw [hd₁]; have := ηR_pos; positivity
  have hw := threshold_weaken (v := fun j => ((laplace (fpar (2 * (p.γ : ℝ)))
      ((((it j).e.hi : ℝ) - (it j).e.anc : ℝ) : ℂ)).re + add j - 1 / 6) / Real.sqrt (Iu * Du) - ηR)
    (v' := fun j => ((it j).v : ℝ) / SR) (Dg := fun j => (1 + ηR) * De j / Du)
    (Dg' := fun j => ((it j).D : ℝ) / SR) (d' := (d : ℝ) / SR) hDg (fun j => hDD j)
    (fun j => Or.inl (by simpa [ofCore_γ] using hfeat j)) hd0 (by rw [hd₁]; exact hrad) hτ0 hτd hT
  exact ⟨τ, hτ0, hw.1, hw.2⟩

end GradedNear.Row

end
