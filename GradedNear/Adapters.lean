module

public import GradedNear.LeafTheorem
public import GradedNear.Envelope

/-!
# From the literature inputs to the zero hypotheses of a leaf (paper §§5–6)

The hypotheses of `Cert.valid_leaf_gives_prime` that concern zeros have the form the literature
inputs deliver:
* `envelope_column`: for an ordinary column (objective `G = G_{1/3}`), the envelope
  (`OrdinaryEnvelope`) bounds a character's zero sum by `H₀ (g(λ) + err)`, with `err = ε e^{−Aλ}/H₀`,
  whenever the character has no zero with parameter below `λ` in the disc `|1 − ρ| ≤ δ`;
* `far_from_lemma`: the far lemma for the corpus profiles (`far_bound_corpus`), applied with `η/2`,
  bounds the far weights of the placed characters plus those charged without columns. Each placed
  character contributes a chosen zero with parameter `λ_j`. Each character charged without
  columns contributes a chosen zero with parameter `≤ b_k`, whose weight dominates `w(b_k)`. This
  covers `farReserved`: the inside first family (`n·w(b)`) and a reserved family charged without
  columns (`n₂·w(hi₂)`).
-/

@[expose] public section

noncomputable section

namespace GradedNear

open Kernel Cert LeafMetaCore Finset

/-- **The envelope gives the zero-sum hypothesis of an ordinary column.** -/
theorem envelope_column {Lx : ℝ} (henv : OrdinaryEnvelope Lx) {C ε lamMin : ℝ} (hC : 0 < C)
    (hε : 0 < ε) (hmin : 0 < lamMin) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 2 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ (span : Span) (lam : ℝ), lamMin ≤ lam →
      (∀ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 → ‖1 - ρ‖ ≤ δ →
        lam ≤ (1 - ρ.re) * Real.log q) →
      rectZeroSum χ (primeKernel Lx).H C ≤
        H0 * ((colSem Lx ⟨span, .G (1 / 3)⟩).g lam +
          ε * Real.exp (-((Lx - 2 * T) * lam)) / H0) := by
  obtain ⟨δ, hδ, hδ2, q₀, h⟩ := henv C hC ε hε lamMin hmin
  refine ⟨δ, hδ, hδ2, q₀, fun q _ hq χ hχ span lam hlam hfree => ?_⟩
  have hg : (colSem Lx ⟨span, .G (1 / 3)⟩).g lam = G Lx lam := by
    cases span <;> simp [colSem, objFun, ColSem.g, G]
  rw [hg, mul_add, mul_div_cancel₀ _ H0_pos.ne']
  simpa using h q hq χ hχ lam hlam hfree

/-- **The far lemma gives the far hypothesis of a leaf.** Assume `XylourisLemma51` and a corpus
profile. For `q ≥ q₀`, take distinct non-principal characters, all with a chosen zero in
Xylouris's far region:
* the placed characters `χ_j`, with chosen zeros `ρ_j` (parameters `λ_j`);
* further characters `ψ_k` charged without columns, with chosen zeros of parameter `≤ b_k`.

Then `Σ_j w(λ_j) + Σ_k w(b_k) ≤ (1 + η/2) V`. The leaf's `farReserved m` is such a sum over
`κ = Fin n ⊕ Fin n₂`: `n·w(b)` for the inside first family, and `n₂·w(hi₂)` for a reserved
family charged without columns. -/
theorem far_from_lemma (hX : XylourisLemma51) {P : FarProfile} (hP : P = inherited ∨ P = retuned)
    {η : ℝ} (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (χ : ι → DirichletCharacter ℂ q)
        (ψ : κ → DirichletCharacter ℂ q) (ρ : ι → ℂ) (σ : κ → ℂ) (b : κ → ℝ),
      Function.Injective (Sum.elim χ ψ) →
      (∀ j, χ j ≠ 1 ∧ DirichletCharacter.LFunction (χ j) (ρ j) = 0 ∧
        1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (ρ j).re ∧ |(ρ j).im| ≤ 1) →
      (∀ k, ψ k ≠ 1 ∧ DirichletCharacter.LFunction (ψ k) (σ k) = 0 ∧
        1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (σ k).re ∧ |(σ k).im| ≤ 1 ∧
        (1 - (σ k).re) * Real.log q ≤ b k) →
      ∑ j, P.w ((1 - (ρ j).re) * Real.log q) + ∑ k, P.w (b k) ≤ (1 + η / 2) * P.V := by
  classical
  obtain ⟨q₀, h⟩ := P.far_bound_corpus hX hP (half_pos hη)
  refine ⟨q₀, fun q _ hq ι κ _ _ χ ψ ρ σ b hinj hρ hσ => ?_⟩
  -- the chosen zero of each character in the image of `Sum.elim χ ψ`
  let e : ι ⊕ κ → DirichletCharacter ℂ q := Sum.elim χ ψ
  let z : ι ⊕ κ → ℂ := Sum.elim ρ σ
  let s : Finset (DirichletCharacter ℂ q) := univ.image e
  -- the chosen zero of a character in the image (any default elsewhere)
  let ρ' : DirichletCharacter ℂ q → ℂ := fun c => if hc : ∃ i, e i = c then z hc.choose else 0
  have hleft : ∀ i, ρ' (e i) = z i := by
    intro i
    have hc : ∃ i', e i' = e i := ⟨i, rfl⟩
    show (if hc : ∃ i', e i' = e i then z hc.choose else 0) = z i
    rw [dite_eq_left hc, hinj hc.choose_spec]
  have hs : ∀ c ∈ s, c ≠ 1 ∧ DirichletCharacter.LFunction c (ρ' c) = 0 ∧
      1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (ρ' c).re ∧ |(ρ' c).im| ≤ 1 := by
    intro c hc
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hc
    rw [hleft i]
    rcases i with j | k
    · exact hρ j
    · exact ⟨(hσ k).1, (hσ k).2.1, (hσ k).2.2.1, (hσ k).2.2.2.1⟩
  have hbound := h q hq s ρ' hs
  -- rewrite the sum over `s` as a sum over `ι ⊕ κ`
  have hsum : ∑ c ∈ s, P.w ((1 - (ρ' c).re) * Real.log q) =
      ∑ i : ι ⊕ κ, P.w ((1 - (z i).re) * Real.log q) := by
    rw [Finset.sum_image (fun i _ i' _ hii' => hinj hii')]
    exact Finset.sum_congr rfl fun i _ => by rw [hleft i]
  rw [hsum, Fintype.sum_sum_type] at hbound
  have hw := P.w_antitone_corpus hP
  have hk : ∑ k, P.w (b k) ≤ ∑ k, P.w ((1 - (z (Sum.inr k)).re) * Real.log q) :=
    Finset.sum_le_sum fun k _ => hw (hσ k).2.2.2.2
  simp only [z, Sum.elim_inl, Sum.elim_inr] at hbound hk
  linarith

end GradedNear
