module

public import GradedNear.LeafTheorem
public import GradedNear.Cert.FastEq
public import GradedNear.Cert.NumericsSound

/-!
# A leaf accepted by the native checks gives primes

`leafcheck` (`LeafCheckNative.lean`) runs two Boolean checks on every leaf of the corpus: the
certificate check `CertCore.checkLeaf L T = some v` and the numeric check
`LeafCheckCore.checkNum m L = true`. `checked_leaf_gives_prime` states what the two checks prove:
the conclusion of `Cert.valid_leaf_gives_prime` for the leaf. Two results connect the checks to
the proved statements:
* `Cert.checkLeaf_ofCore`: the Mathlib-free checker computes `Cert.checkLeaf`;
* `Cert.checkNum_sound`, with `checkNum_profile`, `checkNum_phi` and `checkNum_L`: an accepted leaf
  has valid data for its metadata (`MetaValid`), a corpus far profile, `φ ≥ 0` and `L ≥ 3.99`.

The native run itself is compiled code. Its trust base is the Lean compiler and runtime, and the
runner's JSON parsing, which is not verified.
-/

@[expose] public section

noncomputable section

namespace GradedNear.Cert

open Kernel LeafMetaCore Finset

/-- **A leaf accepted by the native checks gives primes.** For a leaf `L` and metadata `m` with
`CertCore.checkLeaf L T = some v` and `LeafCheckCore.checkNum m L = true`, the conclusion of
`valid_leaf_gives_prime` holds for `Leaf.ofCore L`: under the zero-level hypotheses, every class
coprime to `q` contains a prime `p` with `q^{L−2T} < p < q^L`. -/
theorem checked_leaf_gives_prime (hcrit : XylourisCriterion357)
    {L : CertCore.Leaf} {Tr : CertCore.Tree} {v : ℤ} (hcert : CertCore.checkLeaf L Tr = some v)
    (m : LeafMeta) (hnum : LeafCheckCore.checkNum m L = true) {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C →
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
      ∀ τ : ℕ → ℝ, (∀ k < (Leaf.ofCore L).rows.length, 0 ≤ τ k ∧
        τ k ^ 2 ≤ (((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
        rowLHS (Leaf.ofCore L) (massVec (Leaf.ofCore L) (fun j => some (col j)) (fun j =>
          (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j))) k
          (τ k) ≤ 1 - τ k ^ 2 / ((((Leaf.ofCore L).rows.getD k ⟨1, []⟩).d : ℝ) / S)) →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ ((m.L : ℝ) - 2 * (T : ℝ)) < p ∧ (p : ℝ) < (q : ℝ) ^ (m.L : ℝ) :=
  valid_leaf_gives_prime hcrit (Tr := Tree.ofCore Tr) (v := v)
    ((checkLeaf_ofCore L Tr).symm.trans hcert) m (checkNum_sound m L hnum)
    (checkNum_profile m L hnum)
    (fun c hc => by
      have h := checkNum_phi m L hnum c hc
      rcases c with ⟨_, _ | _⟩ <;> exact h)
    (checkNum_L m L hnum) hε

end GradedNear.Cert
