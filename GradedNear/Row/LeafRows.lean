module

public import GradedNear.Row.Masses
public import GradedNear.LeafChecked

/-!
# A leaf whose certificate, numerics and near rows are checked gives primes

`checked_leaf_rows_gives_prime` composes `Cert.checked_leaf_gives_prime` with `row_at_masses`.
The leaf theorem's hypothesis on the near rows (`hrows`: every row of the leaf LP holds at the
configuration's masses, for some thresholds) is discharged row by row for every row that the
native row checker accepts (`RowCheckCore.checkRows`), from the row's zero-level configuration
(`RowZero`): its entries, their bins and semantics, their kept zeros, and the zero-level
conditions of `row_at_masses`. A row without metadata (the two-test row, paper §9.6)
still enters as the statement that it holds.

What remains as hypotheses is therefore:
* the literature inputs (X Lemmas 3.1–3.2, Burgess, Graham, X (3.57), X Lemma 5.1 through the far
  bound) and the leaf's zero-level facts, as in `checked_leaf_gives_prime`;
* the count-type constraints (`C`, `NH`, `E`) and the budget `final`, as they are;
* for each checked near row, its zero-level configuration (`RowZero`);
* for each row without metadata, the row itself.
-/

@[expose] public section

noncomputable section

open Complex Finset

namespace GradedNear.Row

open Parabolic Cert Kernel LeafMetaCore

/-- **The zero-level configuration of a checked near row** `k` of a leaf, at the column vector
`x`: the safe anchor; entries `E` with bins into the row's columns and family terms, the
semantics `sem` of their column or term, and kept zeros `Sz`; and the hypotheses of
`row_at_masses` for the separation `M`, the disc radius `δ`, the zero count `K₀` and the offsets
`Δ`. -/
def RowZero (q : ℕ) [NeZero q] (T M δ : ℝ) (K₀ : ℕ) (Δ : Finset ℝ) (L : CertCore.Leaf) (k : ℕ)
    (rm : RowCheckCore.RowMeta) (x : Fin (Leaf.ofCore L).cols.length → ℝ) : Prop :=
  SafeAnchor q rm.p.s1 (2 * T + 1) ∧
  ∃ (ι : Type) (_ : Fintype ι) (E : Entries q ι)
    (bin : ι → Option (Fin (Leaf.ofCore L).cols.length ⊕
      Fin ((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.length))
    (sem : ι → RowCheckCore.Ent) (Sz : ι → Finset ℂ),
    (∀ j c, bin j = some (Sum.inl c) → rm.cols.getD c none = some (sem j) ∧
      0 < ((Leaf.ofCore L).cols.get c).v.getD k 0) ∧
    (∀ j i, bin j = some (Sum.inr i) → rm.fam.getD i none = some (sem j) ∧
      0 < (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).2.1) ∧
    (∀ j, bin j ≠ none) ∧
    (∀ j, E.δ j = (rm.p.s : ℝ) - (sem j).anc) ∧ (∀ j, E.δ j ∈ Δ) ∧
    (∀ j, E.χ j ≠ 1) ∧ (∀ j, |E.γ j| ≤ T) ∧
    ((∃ k' < rm.p.m, rm.p.hk k' ≠ 0) → Function.Injective E.χ) ∧
    (∀ j, ∀ ρ ∈ Sz j, DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
      ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ) ∧
    (∀ j, ∀ ρ : ℂ, DirichletCharacter.LFunction (E.χ j) ρ = 0 →
      ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ → ρ ∉ Sz j →
      (1 - ρ.re) * Real.log q < ((ofCore rm.p).near Δ).s - E.δ j →
      M ≤ |E.γ j - ρ.im| * Real.log q) ∧
    (∀ j, (∑ᶠ ρ ∈ {ρ : ℂ | DirichletCharacter.LFunction (E.χ j) ρ = 0 ∧
        ‖(1 + (E.γ j : ℂ) * I) - ρ‖ ≤ δ ∧ ρ ∉ Sz j ∧
        (1 - ρ.re) * Real.log q < ((ofCore rm.p).near Δ).s - E.δ j},
        zmult (E.χ j) ρ) ≤ K₀) ∧
    (∀ j, ∀ add exc : ℝ, SpecSem (ofCore rm.p) (sem j).sp add exc →
      ((laplace (fpar (2 * (rm.p.γ : ℝ))) ((((sem j).hi : ℝ) - (sem j).anc : ℝ) : ℂ)).re +
          add - 1 / 6 ≤ keptBound ((ofCore rm.p).near Δ) E Sz 0 j ∨
        (laplace (fpar (2 * (rm.p.γ : ℝ))) ((((sem j).hi : ℝ) - (sem j).anc : ℝ) : ℂ)).re +
          add - 1 / 6 ≤ 0) ∧
      pairExcess ((ofCore rm.p).near Δ) E j ≤ exc) ∧
    (∀ i, ((((Leaf.ofCore L).rows.getD k ⟨1, []⟩).fam.get i).1 : ℝ) ≤
      ((Finset.univ.filter fun j => bin j = some (Sum.inr i)).card : ℝ)) ∧
    (∀ c, 0 < ((Leaf.ofCore L).cols.get c).v.getD k 0 →
      x c ≤ ((Finset.univ.filter fun j => bin j = some (Sum.inl c)).card : ℝ))

/-- Row `k` of the leaf LP holds at `x` for some threshold. -/
def RowHolds (L : CertCore.Leaf) (x : Fin (Leaf.ofCore L).cols.length → ℝ) (k : ℕ) : Prop :=
  ∃ τ : ℝ, 0 ≤ τ ∧ τ ^ 2 ≤ (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
    rowLHS (Leaf.ofCore L) x k τ ≤ 1 - τ ^ 2 / ((((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S)

/-- **A checked row holds at every column vector of a zero-level configuration**, with `M`, `δ`
and `q₀` depending only on the row. -/
theorem checked_row_holds (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate)
    {L : CertCore.Leaf} {k : ℕ} {rm : RowCheckCore.RowMeta} {prec : ℕ}
    (hchk : RowCheckCore.checkRow L k rm prec = true)
    (Δ : Finset ℝ) (hΔ : ∀ δ ∈ Δ, 0 ≤ δ) (K₀ : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ x : Fin (Leaf.ofCore L).cols.length → ℝ, (∀ c, 0 ≤ x c) →
      RowZero q T M δ K₀ Δ L k rm x → RowHolds L x k := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, H⟩ := row_at_masses hX31 hX32 hBur hGr hchk Δ hΔ K₀
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun q _ hq T hT0 hTl x hx0 hz => ?_⟩
  obtain ⟨hsafe, ι, _, E, bin, sem, Sz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13,
    h14⟩ := hz
  exact H q hq T hT0 hTl hsafe ι E bin sem h1 h2 h3 h4 h5 h6 h7 h8 Sz h9 h10 h11 h12 h13 x hx0 h14

/-- **A leaf whose certificate, numerics and near rows pass the native checks gives primes.**
For every modulus `q ≥ q₀` and every configuration satisfying the zero-level hypotheses of
`checked_leaf_gives_prime`, where each checked near row has a zero-level configuration
(`RowZero`, with the row's own `M k` and `δ k`, at heights at most `Th`) and each row without
metadata holds, every reduced class mod `q` contains a prime `q^{L−2T} < p < q^L` (`T` the step
kernel's parameter). -/
theorem checked_leaf_rows_gives_prime (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (hcrit : XylourisCriterion357)
    {L : CertCore.Leaf} {Tr : CertCore.Tree} {v : ℤ} (hcert : CertCore.checkLeaf L Tr = some v)
    (m : LeafMeta) (hnum : LeafCheckCore.checkNum m L = true)
    {rms : List (Option RowCheckCore.RowMeta)} {prec : ℕ}
    (hrc : RowCheckCore.checkRows L rms prec = true)
    (Δ : ℕ → Finset ℝ) (hΔ : ∀ k, ∀ δ ∈ Δ k, 0 ≤ δ) (K₀ : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ M δ : ℕ → ℝ, (∀ k, 0 < M k ∧ 0 < δ k ∧ δ k < 1) ∧ ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ,
      ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C → ∀ Th : ℝ, 0 ≤ Th → Th ≤ Real.log q / 3 →
      ∀ (ι : Type) [Fintype ι] (χ : ι → DirichletCharacter ℂ q), Function.Injective χ →
      (∀ j, χ j ≠ 1) → ∀ (col : ι → Fin (Leaf.ofCore L).cols.length) (lam err : ι → ℝ)
        (restCost extra : ℝ),
      (∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1 ∧ ψ ∉ Set.range χ),
          rectZeroSum ψ (primeKernel m.L).H C) ≤ H0 * restCost →
      (∀ j, rectZeroSum (χ j) (primeKernel m.L).H C ≤
        H0 * ((colSem m.L (m.cols.getD (col j) default)).g (lam j) + err j)) →
      (∀ j, (colSem m.L (m.cols.getD (col j) default)).Contains (lam j)) →
      restCost ≤ firstCharge m + extra →
      (extra + ∑ j, err j + ε / H0) * S ≤ (Leaf.ofCore L).final →
      ∑ j, (profileFar m.prof).w (lam j) + farReserved m ≤
        (1 + m.eta / 2) * (profileFar m.prof).V →
      (∑ j, (((Leaf.ofCore L).cols.get (col j)).C : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) ≤ 2 * S) →
      (∑ j, (((Leaf.ofCore L).cols.get (col j)).NH : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) ≤
          (Leaf.ofCore L).ng * S) →
      (∑ j, (((Leaf.ofCore L).cols.get (col j)).E : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) =
          (Leaf.ofCore L).n2 * S) →
      (∀ k < (Leaf.ofCore L).rows.length, rms.getD k none = none →
        RowHolds L (massVec (Leaf.ofCore L) (fun j => some (col j)) (fun j =>
          (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j))) k) →
      (∀ k rm, rms.getD k none = some rm →
        RowZero q Th (M k) (δ k) K₀ (Δ k) L k rm (massVec (Leaf.ofCore L) (fun j => some (col j))
          (fun j => (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w
            (lam j)))) →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ ((m.L : ℝ) - 2 * (T : ℝ)) < p ∧ (p : ℝ) < (q : ℝ) ^ (m.L : ℝ) := by
  obtain ⟨hlen, hrow⟩ := checkRows_sound hrc
  -- each row's constants (dummies for a row without metadata)
  have H : ∀ k, ∃ Mk : ℝ, 0 < Mk ∧ ∃ δk : ℝ, 0 < δk ∧ δk < 1 ∧ ∃ q₀ : ℕ, ∀ rm,
      rms.getD k none = some rm → ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ x : Fin (Leaf.ofCore L).cols.length → ℝ, (∀ c, 0 ≤ x c) →
      RowZero q T Mk δk K₀ (Δ k) L k rm x → RowHolds L x k := by
    intro k
    rcases hk : rms.getD k none with _ | rm
    · exact ⟨1, one_pos, 1 / 2, by norm_num, by norm_num, 0, fun rm h => by simp at h⟩
    · have hklt : k < rms.length := by
        by_contra hge
        rw [List.getD_eq_default _ _ (not_lt.1 hge)] at hk
        simp at hk
      obtain ⟨M, hM, δ, hδ0, hδ1, q₀, Hk⟩ :=
        checked_row_holds hX31 hX32 hBur hGr (hrow k hklt rm hk) (Δ k) (hΔ k) K₀
      refine ⟨M, hM, δ, hδ0, hδ1, q₀, fun rm' hrm' => ?_⟩
      cases hrm'
      exact Hk
  choose M hM δ hδ0 hδ1 q₀ Hrow using H
  obtain ⟨C₀, hC₀, q₀L, HL⟩ := checked_leaf_gives_prime hcrit hcert m hnum hε
  have hprof := checkNum_profile m L hnum
  have hwpos := (profileFar m.prof).w_pos_corpus hprof
  refine ⟨M, δ, fun k => ⟨hM k, hδ0 k, hδ1 k⟩, C₀, hC₀,
    max q₀L ((Finset.range (Leaf.ofCore L).rows.length).sup q₀),
    fun q _ hq C hC Th hT0 hTl ι _ χ hinj hχ col lam err restCost extra h1 h2 h3 h4 h5 h6 h7 h8 h9
      hold hzero a ha => ?_⟩
  set x := massVec (Leaf.ofCore L) (fun j => some (col j)) (fun j =>
    (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j)) with hx
  have hx0 : ∀ c, 0 ≤ x c := fun c =>
    Finset.sum_nonneg fun j _ => ColSem.mass_nonneg hwpos _ _
  -- the thresholds, row by row
  have hτ : ∀ k, k < (Leaf.ofCore L).rows.length → RowHolds L x k := by
    intro k hk
    rcases hk' : rms.getD k none with _ | rm
    · exact hold k hk hk'
    · have hq' : q₀ k ≤ q := by
        refine le_trans ?_ (le_trans (le_max_right _ _) hq)
        exact Finset.le_sup (f := q₀) (Finset.mem_range.2 hk)
      exact Hrow k rm hk' q hq' Th hT0 hTl x hx0 (hzero k rm hk')
  choose! τ hτ using hτ
  exact HL q (le_trans (le_max_left _ _) hq) C hC ι χ hinj hχ col lam err restCost extra
    h1 h2 h3 h4 h5 h6 h7 h8 h9 τ (fun k hk => hτ k hk) a ha

end GradedNear.Row

end
