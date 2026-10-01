module

public import GradedNear.Kernel
public import GradedNear.Cert.Semantics

/-!
# A certified leaf gives primes (paper §§4, 10)

`certified_leaf_gives_prime` composes Xylouris's criterion (3.57) (`Kernel.exists_prime`) with the
leaf LP's meaning (`Cert.leaf_interpretation`). It is the formal interface between one certified
leaf and the rest of the proof. For a modulus `q`, the characters `χ_j` placed in the leaf's
columns must satisfy four conditions:
* each has a parameter `λ_j` in its column;
* each has a zero sum (over the prime window) at most `H₀` times its column's objective at `λ_j`,
  plus an error;
* the remaining characters' zero sum is at most `H₀ · restCost`;
* the far, count, hidden, second-family and near-row constraints hold at the masses.

Then every class coprime to `q` contains a prime `p` with `q^{L−2T} < p < q^L`. The inputs are
supplied elsewhere:
* the zero-sum bounds by the envelope (X Lemma 3.10) and the first- and second-family bounds;
* the far constraint by X Lemma 5.1 (`FarFacts`);
* the near rows by the graded near lemma (`builder_threshold`, `near_row_of_bins`);
* the validity of the column data by verified computation.
-/

@[expose] public section

namespace GradedNear

open Finset Kernel Cert

/-- **A certified leaf gives primes.** See the module docstring. `H₀` is the prime kernel's
`H(0)`; the criterion's `ε` is paid from `first + final`. -/
theorem certified_leaf_gives_prime (hcrit : XylourisCriterion357) {Lx : ℝ}
    (hL : 3 + 2 * (T : ℝ) < Lx) (hH0 : 0 < ((primeKernel Lx).H 0).re)
    {L : Leaf} {Tr : Tree} {v : ℤ} (hcert : checkLeaf L Tr = some v)
    (w : ℝ → ℝ) (hw : Antitone w) (hwpos : ∀ x, 0 < w x)
    (sem : Fin L.cols.length → ColSem)
    (hvalid : ∀ c, (sem c).Valid w (L.cols.get c)) (hmono : ∀ c, (sem c).Mono w)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C →
      ∀ (ι : Type) [Fintype ι] (χ : ι → DirichletCharacter ℂ q), Function.Injective χ →
      (∀ j, χ j ≠ 1) → ∀ (col : ι → Fin L.cols.length) (lam err : ι → ℝ) (restCost : ℝ),
      (∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1 ∧ ψ ∉ Set.range χ),
          rectZeroSum ψ (primeKernel Lx).H C) ≤ ((primeKernel Lx).H 0).re * restCost →
      (∀ j, rectZeroSum (χ j) (primeKernel Lx).H C ≤
        ((primeKernel Lx).H 0).re * ((sem (col j)).g (lam j) + err j)) →
      (∀ j, (sem (col j)).Contains (lam j)) →
      ((restCost + ∑ j, err j + ε / ((primeKernel Lx).H 0).re) * S ≤
        ((L.first + L.final : ℤ) : ℝ)) →
      (∑ j, w (lam j)) * S ≤ L.F →
      (∑ j, ((L.cols.get (col j)).C : ℝ) * (sem (col j)).mass w (lam j) ≤ 2 * S) →
      (∑ j, ((L.cols.get (col j)).NH : ℝ) * (sem (col j)).mass w (lam j) ≤ L.ng * S) →
      (∑ j, ((L.cols.get (col j)).E : ℝ) * (sem (col j)).mass w (lam j) = L.n2 * S) →
      ∀ τ : ℕ → ℝ, (∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
        rowLHS L (massVec L (fun j => some (col j)) (fun j => (sem (col j)).mass w (lam j))) k
          (τ k) ≤ 1 - τ k ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ (Lx - 2 * (T : ℝ)) < p ∧ (p : ℝ) < (q : ℝ) ^ Lx := by
  obtain ⟨C₀, hC₀, q₀, hq₀⟩ := exists_prime hcrit hL hε
  refine ⟨C₀, hC₀, q₀, fun q _ hq C hC ι _ χ hinj hχ col lam err restCost hrest hzero hin hfit
    hfar hcount hhidden hsecond τ hrows a ha => ?_⟩
  set H₀ := ((primeKernel Lx).H 0).re with hH₀
  -- the leaf bounds the total cost below 1
  have hcostj : ∀ j, rectZeroSum (χ j) (primeKernel Lx).H C / H₀ ≤ (sem (col j)).g (lam j) + err j :=
    fun j => by rw [div_le_iff₀ hH0]; linarith [hzero j]
  have hlt := leaf_interpretation hcert w hw hwpos sem hvalid hmono col lam
    (fun j => rectZeroSum (χ j) (primeKernel Lx).H C / H₀) err hin hcostj (restCost + ε / H₀)
    (by linarith) hfar hcount hhidden hsecond τ hrows
  -- split the characters into the placed ones and the rest
  have hsplit : ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1),
      rectZeroSum ψ (primeKernel Lx).H C =
      ∑ j, rectZeroSum (χ j) (primeKernel Lx).H C +
        ∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1 ∧ ψ ∉ Set.range χ),
          rectZeroSum ψ (primeKernel Lx).H C := by
    classical
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter fun ψ : DirichletCharacter ℂ q => ψ ≠ 1)
      (fun ψ => ψ ∈ Set.range χ)]
    congr 1
    · rw [← Finset.sum_image (f := fun ψ => rectZeroSum ψ (primeKernel Lx).H C)
        (fun j _ k _ h => hinj h)]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Set.mem_range]
      constructor
      · rintro ⟨-, j, rfl⟩; exact ⟨j, rfl⟩
      · rintro ⟨j, rfl⟩; exact ⟨hχ j, j, rfl⟩
    · apply Finset.sum_congr _ (fun _ _ => rfl)
      ext ψ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine hq₀ q hq C hC ?_ a ha
  rw [hsplit]
  have hsum : ∑ j, rectZeroSum (χ j) (primeKernel Lx).H C =
      H₀ * ∑ j, rectZeroSum (χ j) (primeKernel Lx).H C / H₀ := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  have hmul := mul_lt_mul_of_pos_left hlt hH0
  have : H₀ * (restCost + ε / H₀) = H₀ * restCost + ε := by field_simp
  nlinarith

end GradedNear
