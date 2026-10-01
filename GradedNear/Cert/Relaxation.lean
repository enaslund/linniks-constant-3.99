module

public import GradedNear.Cert.Sound

/-!
# The leaf LP as a relaxation of a configuration (paper §§5, 6, 10)

As in the paper (Proposition 11.6), the configuration is feasible for the leaf's relaxation, so
`W` is at most the LP maximum. `leaf_relaxation` states this deduction for an abstract configuration. A
configuration is a finite family of characters. Each is placed in at most one column of the leaf
with a nonnegative mass, and carries a cost (its share of the zero-cost sum `W`) and a far
weight. The LP point is the column vector of total masses (`massVec`). Ordinary bins, hidden
columns and second-family sub-bins take mass `1` per character; the tail column takes the mass
`w(λ)` (paper §6.4, the tail column).

Suppose the following hold, all in units of `S = 10¹⁶`:
* each character's cost is at most its column's objective coefficient times its mass;
* the costs outside the columns (the first family, the error allowance) are at most
  `first + final`;
* each character's far weight is at least its column's far cost times its mass, and the far
  weights sum to at most `F`;
* the count, hidden-count and second-family constraints hold for the masses;
* every near row holds at the masses (as `near_row_of_bins` provides).

Then a certified leaf bounds the total cost below `1`.
-/

@[expose] public section

namespace GradedNear.Cert

open Finset

variable {ι : Type*} [Fintype ι]

/-- The column vector of a configuration: the total mass placed in each column. -/
noncomputable def massVec (L : Leaf) (col : ι → Option (Fin L.cols.length)) (mass : ι → ℝ) :
    Fin L.cols.length → ℝ :=
  fun c => ∑ j ∈ univ.filter (fun j => col j = some c), mass j

/-- A column coefficient seen from a character: its column's coefficient, or `0` for a character
without a column. -/
def colCoef (L : Leaf) (col : ι → Option (Fin L.cols.length)) (f : Col → ℤ) (j : ι) : ℤ :=
  match col j with
  | some c => f (L.cols.get c)
  | none => 0

/-- `Σ_c a_c x_c = Σ_j a_{col(j)} m_j` for the column vector `x` of a configuration. -/
lemma sum_mul_massVec (L : Leaf) (col : ι → Option (Fin L.cols.length)) (mass : ι → ℝ)
    (f : Col → ℤ) :
    ∑ c, (f (L.cols.get c) : ℝ) * massVec L col mass c =
      ∑ j, (colCoef L col f j : ℝ) * mass j := by
  rw [← Finset.sum_fiberwise univ col (fun j => (colCoef L col f j : ℝ) * mass j),
    Fintype.sum_option]
  have hnone : ∑ j ∈ univ.filter (fun j => col j = none), (colCoef L col f j : ℝ) * mass j = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [Finset.mem_filter] at hj
    simp [colCoef, hj.2]
  rw [hnone, zero_add]
  refine Finset.sum_congr rfl fun c _ => ?_
  unfold massVec
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Finset.mem_filter] at hj
  simp [colCoef, hj.2]

lemma massVec_nonneg (L : Leaf) (col : ι → Option (Fin L.cols.length)) (mass : ι → ℝ)
    (hmass : ∀ j, 0 ≤ mass j) (c : Fin L.cols.length) : 0 ≤ massVec L col mass c :=
  Finset.sum_nonneg fun j _ => hmass j

/-- **The leaf LP is a relaxation of the configuration** (paper §10 and Proposition 11.6). For a certified leaf and
a configuration satisfying the column semantics above, the total cost is below `1`. -/
theorem leaf_relaxation {L : Leaf} {T : Tree} {v : ℤ} (hcert : checkLeaf L T = some v)
    (col : ι → Option (Fin L.cols.length)) (mass cost far : ι → ℝ) (restCost : ℝ)
    (hmass : ∀ j, 0 ≤ mass j)
    (hcost : ∀ j, cost j * S ≤ (colCoef L col Col.G j : ℝ) * mass j)
    (hrest : restCost * S ≤ ((L.first + L.final : ℤ) : ℝ))
    (hfarj : ∀ j, (colCoef L col Col.W j : ℝ) * mass j ≤ far j * S)
    (hfar : (∑ j, far j) * S ≤ L.F)
    (hcount : ∑ j, (colCoef L col Col.C j : ℝ) * mass j ≤ 2 * S)
    (hhidden : ∑ j, (colCoef L col Col.NH j : ℝ) * mass j ≤ L.ng * S)
    (hsecond : ∑ j, (colCoef L col Col.E j : ℝ) * mass j = L.n2 * S)
    (τ : ℕ → ℝ)
    (hrows : ∀ k < L.rows.length, 0 ≤ τ k ∧ τ k ^ 2 ≤ ((L.rows.getD k ⟨1, []⟩).d : ℝ) / S ∧
      rowLHS L (massVec L col mass) k (τ k) ≤
        1 - τ k ^ 2 / (((L.rows.getD k ⟨1, []⟩).d : ℝ) / S)) :
    restCost + ∑ j, cost j < 1 := by
  have hS : (0 : ℝ) < S := by norm_num [S]
  have hfeas : Feasible L (massVec L col mass) τ := by
    refine ⟨massVec_nonneg L col mass hmass, ?_, ?_, ?_, ?_, hrows⟩
    · rw [sum_mul_massVec]
      calc ∑ j, (colCoef L col Col.W j : ℝ) * mass j ≤ ∑ j, far j * S :=
            Finset.sum_le_sum fun j _ => hfarj j
        _ = (∑ j, far j) * S := (Finset.sum_mul _ _ _).symm
        _ ≤ L.F := hfar
    · rw [sum_mul_massVec]; exact hcount
    · rw [sum_mul_massVec]; exact hhidden
    · rw [sum_mul_massVec]; exact hsecond
  have hobj := certified hcert (massVec L col mass) τ hfeas
  unfold objective at hobj
  rw [sum_mul_massVec] at hobj
  have hsum : (∑ j, cost j) * S ≤ ∑ j, (colCoef L col Col.G j : ℝ) * mass j := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun j _ => hcost j
  have hfr : ((L.first + L.final : ℤ) : ℝ) = (L.first : ℝ) + L.final := by push_cast; ring
  have htot : (restCost + ∑ j, cost j) * S < 1 * S := by
    rw [hfr] at hrest
    nlinarith
  exact lt_of_mul_lt_mul_right htot hS.le

end GradedNear.Cert
