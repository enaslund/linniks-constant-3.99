module

public import GradedNear.LeafPrime
public import GradedNear.ColumnMono
public import GradedNear.Cert.NumericsSpec

/-!
# A certified leaf with valid data gives primes (paper §§4–6, 10)

`valid_leaf_gives_prime` specializes `certified_leaf_gives_prime` to a leaf whose integer data
are valid for its metadata (`Cert.MetaValid`), with a corpus far profile, nonnegative `φ` and
`L ≥ 3.99`. The hypotheses on the columns' objective and far data, the far budget and the
first-family charge are then discharged:
* column validity, from `MetaValid.cols`;
* column monotonicity, from `ColumnMono`;
* positivity and monotonicity of `w`, from `FarFacts`;
* the normalization `H(0) = H₀`, from `KernelFacts`;
* the far budget and the first-family charge, from `MetaValid.far` and `MetaValid.first`.

What remains are statements about the zeros of the characters mod `q`. Some of them involve
integers of the leaf that `MetaValid` does not constrain and that enter as they are: `C`, `NH`,
`E`, `ng`, `n2`, `final` and the near rows (`v`, `D`, `d`). The remaining statements are:
* each placed character's zero sum is bounded by its column's objective at its parameter, plus an
  error (from the envelope, `OrdinaryEnvelope`, for ordinary characters);
* the remaining zero sums are covered by the first-family charge plus an extra term;
* the far weights of the placed characters, plus the reserved ones, are at most `(1 + η/2)V` (from
  the far lemma, `far_bound_corpus`);
* the count, hidden-count and second-family constraints and every near row hold at the masses
  (the graded near lemma supplies the near rows).
-/

@[expose] public section

noncomputable section

namespace GradedNear.Cert

open Kernel LeafMetaCore Finset

/-- The `φ` of a column's objective. -/
def objPhi : Obj → ℚ
  | .G φ => φ
  | .hidden φ _ => φ

/-- Every column of the metadata is monotone, for a corpus profile, `φ ≥ 0` and `L ≥ 3.99`. -/
lemma colSem_mono (m : LeafMeta) (hprof : profileFar m.prof = inherited ∨ profileFar m.prof = retuned)
    (hL : (399 / 100 : ℝ) ≤ m.L) (c : ColMeta) (hφ : 0 ≤ (objPhi c.obj : ℝ)) :
    (colSem m.L c).Mono (profileFar m.prof).w := by
  have hL' : (3.99 : ℝ) ≤ m.L := by norm_num at hL ⊢; linarith
  rcases c with ⟨span, obj⟩
  cases span with
  | bin lo hi =>
    cases obj with
    | G φ => exact mono_bin_Gphi hL' hφ _ _ _
    | hidden φ p => exact mono_bin_hidden hL' hφ _ _ _ _
  | tail R =>
    cases obj with
    | G φ => exact mono_tail_Gphi hL' hφ hprof _
    | hidden φ p => exact mono_tail_hidden hL' hφ _ hprof _

/-- **A certified leaf with valid data gives primes.** See the module docstring. -/
theorem valid_leaf_gives_prime (hcrit : XylourisCriterion357)
    {L : Leaf} {Tr : Tree} {v : ℤ} (hcert : checkLeaf L Tr = some v)
    (m : LeafMeta) (hm : MetaValid m L)
    (hprof : profileFar m.prof = inherited ∨ profileFar m.prof = retuned)
    (hφ : ∀ c ∈ m.cols, 0 ≤ (objPhi c.obj : ℝ)) (hLx : (399 / 100 : ℝ) ≤ m.L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C →
      ∀ (ι : Type) [Fintype ι] (χ : ι → DirichletCharacter ℂ q), Function.Injective χ →
      (∀ j, χ j ≠ 1) → ∀ (col : ι → Fin L.cols.length) (lam err : ι → ℝ) (restCost extra : ℝ),
      (∑ ψ ∈ univ.filter (fun ψ : DirichletCharacter ℂ q => ψ ≠ 1 ∧ ψ ∉ Set.range χ),
          rectZeroSum ψ (primeKernel m.L).H C) ≤ H0 * restCost →
      (∀ j, rectZeroSum (χ j) (primeKernel m.L).H C ≤
        H0 * ((colSem m.L (m.cols.getD (col j) default)).g (lam j) + err j)) →
      (∀ j, (colSem m.L (m.cols.getD (col j) default)).Contains (lam j)) →
      restCost ≤ firstCharge m + extra →
      (extra + ∑ j, err j + ε / H0) * S ≤ L.final →
      ∑ j, (profileFar m.prof).w (lam j) + farReserved m ≤
        (1 + m.eta / 2) * (profileFar m.prof).V →
      (∑ j, ((L.cols.get (col j)).C : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) ≤ 2 * S) →
      (∑ j, ((L.cols.get (col j)).NH : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) ≤
          L.ng * S) →
      (∑ j, ((L.cols.get (col j)).E : ℝ) *
        (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j) =
          L.n2 * S) →
      ∀ τ : ℕ → ℝ, (∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
        rowLHS L (massVec L (fun j => some (col j)) (fun j =>
          (colSem m.L (m.cols.getD (col j) default)).mass (profileFar m.prof).w (lam j))) k
          (τ k) ≤ 1 - τ k ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ ((m.L : ℝ) - 2 * (T : ℝ)) < p ∧ (p : ℝ) < (q : ℝ) ^ (m.L : ℝ) := by
  have hT : (3 + 2 * (T : ℝ)) < m.L := by
    have : (T : ℝ) = 416829 / 1000000 := by norm_num [T]
    rw [this]; linarith
  have hA : 0 ≤ (m.L : ℝ) - 2 * T := by
    have : (T : ℝ) = 416829 / 1000000 := by norm_num [T]
    rw [this]; linarith
  have hH : ((primeKernel m.L).H 0).re = H0 := primeKernel_H_zero hA
  have hH0 : 0 < ((primeKernel (m.L : ℝ)).H 0).re := by rw [hH]; exact H0_pos
  have hw := (profileFar m.prof).w_antitone_corpus hprof
  have hwpos := (profileFar m.prof).w_pos_corpus hprof
  have hmono : ∀ c : Fin L.cols.length,
      (colSem m.L (m.cols.getD c default)).Mono (profileFar m.prof).w := by
    intro c
    apply colSem_mono m hprof hLx
    apply hφ
    have hc : (c : ℕ) < m.cols.length := by rw [hm.length]; exact c.isLt
    rw [List.getD_eq_getElem _ _ hc]
    exact List.getElem_mem hc
  obtain ⟨C₀, hC₀, q₀, h⟩ := certified_leaf_gives_prime hcrit hT hH0 hcert
    (profileFar m.prof).w hw hwpos (fun c => colSem m.L (m.cols.getD c default)) hm.cols hmono hε
  refine ⟨C₀, hC₀, q₀, fun q _ hq C hC ι _ χ hinj hχ col lam err restCost extra hrestZ hzero hin
    hrestC hfinal hfar hcount hhidden hsecond τ hrows a ha => ?_⟩
  refine h q hq C hC ι χ hinj hχ col lam err restCost (by rw [hH]; exact hrestZ)
    (fun j => by rw [hH]; exact hzero j) hin ?_ ?_ hcount hhidden hsecond τ hrows a ha
  · -- the rest fits in first + final
    have hfirst := hm.first
    have hS : (0 : ℝ) < S := by norm_num [S]
    rw [hH]
    have hff : ((L.first + L.final : ℤ) : ℝ) = (L.first : ℝ) + L.final := by push_cast; ring
    rw [hff]
    nlinarith
  · -- the far budget
    have hfar' := hm.far
    have hS : (0 : ℝ) < S := by norm_num [S]
    nlinarith

end GradedNear.Cert
