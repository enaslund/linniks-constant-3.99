module

public import GradedNear.Row.Threshold
public import GradedNear.Cert.Bins
public import GradedNear.Cert.FastEq

/-!
# A checked near row holds at the configuration's masses

`row_at_masses` joins the three steps for one near row `k` of a leaf that the native row checker
accepts (`RowCheckCore.checkRow`):
* `checkRow_sound`: the row's stored integers are valid for a concrete instance of the graded near
  lemma, and every column with a positive feature has a checked entry;
* `row_threshold`: for a family of entries satisfying the zero-level conditions of
  `builder_threshold`, the stored integers satisfy (T);
* `near_row_of_bins`: binning the entries into the leaf's columns and family terms turns (T) into
  row `k` of the leaf LP (`Cert.Feasible`), at every column vector bounded by the bin counts.

Each entry `j` of the configuration is binned (`bin j`) to a column or a family term with a
positive feature in row `k`, and carries that column's or term's semantics `sem j` from the row
metadata: its offset is `s - anc`, and for every values `(add, exc)` of its semantics (`SpecSem`)
its kept zeros give at least `F(hi - anc) + add - 1/6` (or that number is `≤ 0`) and its pair
excess is at most `exc`. The conclusion is the conjunct of `Cert.valid_leaf_gives_prime`'s
hypothesis `hrows` for row `k`.
-/

@[expose] public section

noncomputable section

open Complex

namespace GradedNear.Row

open Parabolic Cert

lemma ofCore_cols_length (L : CertCore.Leaf) : (Leaf.ofCore L).cols.length = L.cols.length := by
  simp [Leaf.ofCore]

lemma ofCore_col_getElem (L : CertCore.Leaf) (c : ℕ) (hc : c < (Leaf.ofCore L).cols.length) :
    (Leaf.ofCore L).cols[c] = Col.ofCore (L.cols[c]'(by rwa [ofCore_cols_length] at hc)) := by
  simp only [Leaf.ofCore, List.getElem_map]

lemma ofCore_col_get (L : CertCore.Leaf) (c : Fin (Leaf.ofCore L).cols.length) :
    (Leaf.ofCore L).cols.get c = Col.ofCore (L.cols[c.1]'(by
      rw [← ofCore_cols_length]; exact c.2)) := by
  rw [List.get_eq_getElem, ofCore_col_getElem]

lemma ofCore_row (L : CertCore.Leaf) (k : ℕ) :
    (Leaf.ofCore L).rows.getD k ⟨1, []⟩ = RowHead.ofCore (L.rows.getD k ⟨1, []⟩) := by
  unfold Leaf.ofCore
  simp only
  rw [show (⟨1, []⟩ : RowHead) = RowHead.ofCore ⟨1, []⟩ from rfl, List.getD_map]

/-- The stored item of an entry: the feature and diagonal of its column or family term in row
`k`, with its semantics. -/
def itemOf (L : CertCore.Leaf) (k : ℕ) (e : RowCheckCore.Ent) :
    Option (Fin (Leaf.ofCore L).cols.length ⊕
      Fin ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.length) → RowCheckCore.Item
  | some (Sum.inl c) => ⟨((Leaf.ofCore L).cols.get c).v.getD k 0,
      ((Leaf.ofCore L).cols.get c).D.getD k 1, e⟩
  | some (Sum.inr i) => ⟨(((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).2.1,
      (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).2.2, e⟩
  | none => ⟨0, 1, e⟩

lemma itemOf_e (L : CertCore.Leaf) (k : ℕ) (e : RowCheckCore.Ent) (b : Option
    (Fin (Leaf.ofCore L).cols.length ⊕ Fin ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.length)) :
    (itemOf L k e b).e = e := by
  rcases b with _ | c | i <;> rfl

/-- **A checked near row holds at the masses** (see the module docstring). -/
theorem row_at_masses (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate)
    {L : CertCore.Leaf} {k : ℕ} {rm : RowCheckCore.RowMeta} {prec : ℕ}
    (hchk : RowCheckCore.checkRow L k rm prec = true)
    (Δ : Finset ℝ) (hΔ : ∀ δ ∈ Δ, 0 ≤ δ) (K₀ : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q rm.p.s1 (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι)
        (bin : ι → Option (Fin (Leaf.ofCore L).cols.length ⊕
          Fin ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.length))
        (sem : ι → RowCheckCore.Ent),
        (∀ j c, bin j = some (Sum.inl c) → rm.cols.getD c none = some (sem j) ∧
          0 < ((Leaf.ofCore L).cols.get c).v.getD k 0) →
        (∀ j i, bin j = some (Sum.inr i) → rm.fam.getD i none = some (sem j) ∧
          0 < (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).2.1) →
        (∀ j, bin j ≠ none) →
        (∀ j, E.δ j = (rm.p.s : ℝ) - (sem j).anc) → (∀ j, E.δ j ∈ Δ) →
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) →
        ((∃ k' < rm.p.m, rm.p.hk k' ≠ 0) → Function.Injective E.χ) →
        ∀ Sz : ι → Finset ℂ,
          (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) →
          (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
            (1 - ρ.re) * Real.log q < ((ofCore rm.p).near Δ).s - E.δ j →
            M ≤ |E.γ j - ρ.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
              (1 - ρ.re) * Real.log q < ((ofCore rm.p).near Δ).s - E.δ j},
              zmult (E.χ j) ρ) ≤ K₀) →
          (∀ j, ∀ add exc : ℝ, SpecSem (ofCore rm.p) (sem j).sp add exc →
            ((laplace (fpar (2 * (rm.p.γ : ℝ))) ((((sem j).hi : ℝ) - (sem j).anc : ℝ) : ℂ)).re +
                add - 1 / 6 ≤ keptBound ((ofCore rm.p).near Δ) E Sz 0 j ∨
              (laplace (fpar (2 * (rm.p.γ : ℝ))) ((((sem j).hi : ℝ) - (sem j).anc : ℝ) : ℂ)).re +
                add - 1 / 6 ≤ 0) ∧
            pairExcess ((ofCore rm.p).near Δ) E j ≤ exc) →
          (∀ i, ((((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).1 : ℝ) ≤
            ((Finset.univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ)) →
          ∀ x : Fin (Leaf.ofCore L).cols.length → ℝ, (∀ c, 0 ≤ x c) →
          (∀ c, 0 < ((Leaf.ofCore L).cols.get c).v.getD k 0 →
            x c ≤ ((Finset.univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ)) →
          ∃ τ : ℝ, 0 ≤ τ ∧ τ ^ 2 ≤ (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
            rowLHS (Leaf.ofCore L) x k τ ≤
              1 - τ ^ 2 / ((((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S) := by
  obtain ⟨items, hitems, hnum, hfamD, hlc, hlf, hcov, hcovf⟩ := checkRow_sound hchk
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, H⟩ := row_threshold hX31 hX32 hBur hGr hnum Δ hΔ K₀
  obtain ⟨_, _, Iu, Du, _, hDu, hrad, hent⟩ := hnum
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun q _ hq T hT0 hTl hsafe ι _ E bin sem hbinc hbinf hbin hδE
    hΔE hχ hγ hinj Sz hSz hsep hK hent' hn x hx0 hx => ?_⟩
  have hrow := ofCore_row L k
  have hlen : ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.length =
      (L.rows.getD k ⟨1, []⟩).fam.length := by rw [hrow]; rfl
  have hfam : ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam = (L.rows.getD k ⟨1, []⟩).fam := by
    rw [hrow]; rfl
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hSR : SR = (S : ℝ) := by simp [SR, RowCheckCore.S, S]
  -- every entry's stored item is a checked entry
  have hit : ∀ j, itemOf L k (sem j) (bin j) ∈ items := by
    intro j
    rcases hb : bin j with _ | c | i
    · exact absurd hb (hbin j)
    · obtain ⟨he, hv⟩ := hbinc j c hb
      have hc : c.1 < L.cols.length := by rw [← ofCore_cols_length]; exact c.2
      rw [ofCore_col_get] at hv
      obtain ⟨e, he', hmem⟩ := hcov c.1 hc (by simpa [Col.ofCore] using hv)
      rw [he] at he'
      cases he'
      simp only [itemOf, ofCore_col_get, Col.ofCore]
      exact hmem
    · obtain ⟨he, hv⟩ := hbinf j i hb
      have hi : i.1 < (L.rows.getD k ⟨1, []⟩).fam.length := lt_of_lt_of_eq i.2 hlen
      have hget : ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i =
          (L.rows.getD k ⟨1, []⟩).fam.getD i.1 (0, 0, 0) := by
        rw [List.getD_eq_getElem _ _ hi, List.get_eq_getElem]
        simp only [hfam]
      rw [hget] at hv
      have := hcovf i.1 hi (sem j) hv he
      simp only [itemOf, hget]
      exact this
  obtain ⟨τ, hτ0, hτd, hT⟩ := H q hq T hT0 hTl hsafe ι E (fun j => itemOf L k (sem j) (bin j)) hit
    (fun j => by rw [itemOf_e, hδE j]) hΔE hχ hγ hinj Sz hSz hsep hK
    (fun j add exc h => by rw [itemOf_e] at h ⊢; exact hent' j add exc h)
  -- the radius as a real number
  have hdrow : ((L.rows.getD k ⟨1, []⟩).d : ℝ) / SR =
      (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S := by
    rw [hrow, hSR]; rfl
  have hd0 : (0 : ℝ) < ((L.rows.getD k ⟨1, []⟩).d : ℝ) / SR := by
    have := ηR_pos
    have : (0 : ℝ) < (1 + ηR) * (1 / 6 / Du + ηR) := by positivity
    linarith
  have hDg : ∀ j, 0 < ((itemOf L k (sem j) (bin j)).D : ℝ) / SR := fun j => by
    obtain ⟨add, exc, hsem, _, _, hpos, De, hDe, hDD⟩ := hent _ (hit j)
    have := ηR_pos
    have := hsem.exc_nonneg
    have hDe' : 0 < De := by linarith
    have : 0 < (1 + ηR) * De / Du := by positivity
    linarith
  have hnr := near_row_of_bins (Leaf.ofCore L) k (fun j => ((itemOf L k (sem j) (bin j)).v : ℝ) / SR)
    (fun j => ((itemOf L k (sem j) (bin j)).D : ℝ) / SR) (((L.rows.getD k ⟨1, []⟩).d : ℝ) / SR) τ
    hDg hd0 hτ0 hτd hT bin
    (fun j c hb => by
      simp only [hb, itemOf, hSR]
      exact ⟨Or.inl le_rfl, le_rfl⟩)
    (fun j i hb => by
      simp only [hb, itemOf, hSR]
      exact ⟨Or.inl le_rfl, le_rfl⟩)
    (fun i => by
      have hmem : ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i ∈
          (L.rows.getD k ⟨1, []⟩).fam := by
        rw [List.get_eq_getElem]
        simp only [hfam]
        exact List.getElem_mem _
      exact hfamD _ hmem)
    hn (by rw [hdrow]) x hx0 hx
  rw [← hdrow] at hnr ⊢
  exact ⟨τ, hnr.1, hnr.2.1, hnr.2.2⟩

end GradedNear.Row

end
