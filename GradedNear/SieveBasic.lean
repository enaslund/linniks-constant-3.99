module

public import GradedNear.Defs

/-!
# Proof-side auxiliary definitions (not part of the statement)
-/

@[expose] public section

namespace GradedNear

/-- The Selberg majorant `ν_V(n) = (Σ_{d ∣ n} ψ_d)²` with the weights of `grahamWeight`. -/
noncomputable def sieveNu (V : ℝ) (n : ℕ) : ℝ := (∑ d ∈ n.divisors, grahamWeight V d) ^ 2

lemma sieveNu_nonneg (V : ℝ) (n : ℕ) : 0 ≤ sieveNu V n := sq_nonneg _

end GradedNear
