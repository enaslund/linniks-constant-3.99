module

public import Mathlib

/-!
# The sieve error terms tend to zero

For fixed `h_k, t_k, λ_k = level k > 0` with `λ_k < t_k`, and constants `CB, CC, κ > 0`,
`Σ_{k<m} h_k [CB t_{k+1}²/(λ_k² 𝓛) + CB/(λ_k² 𝓛³) + |CC| q^{-κ}/𝓛 + 2 λ_k q^{λ_k - t_k}] → 0`.
-/

@[expose] public section

open Filter Topology

namespace GradedNear

lemma tendsto_log_nat_atTop : Tendsto (fun q : ℕ => Real.log q) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

lemma tendsto_inv_log_nat : Tendsto (fun q : ℕ => (Real.log q)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_nat_atTop

lemma tendsto_rpow_neg_nat {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun q : ℕ => (q : ℝ) ^ (-κ)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop hκ).comp tendsto_natCast_atTop_atTop

lemma sieve_error_eventually (m : ℕ) (h t lev : ℕ → ℝ) (hlev : ∀ k < m, 0 < lev k)
    (hlt : ∀ k < m, lev k < t k) (CB CC κ : ℝ) (hκ : 0 < κ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∑ k ∈ Finset.range m, h k * (CB * t (k + 1) ^ 2 / (lev k ^ 2 * Real.log q) +
        CB / (lev k ^ 2 * Real.log q ^ 3) + |CC| * (q : ℝ) ^ (-κ) / Real.log q +
          2 * lev k * (q : ℝ) ^ (lev k - t k)) ≤ ε := by
  have hT : Tendsto (fun q : ℕ => ∑ k ∈ Finset.range m, h k * (CB * t (k + 1) ^ 2 /
      (lev k ^ 2 * Real.log q) + CB / (lev k ^ 2 * Real.log q ^ 3) +
        |CC| * (q : ℝ) ^ (-κ) / Real.log q + 2 * lev k * (q : ℝ) ^ (lev k - t k)))
      atTop (𝓝 0) := by
    rw [show (0 : ℝ) = ∑ k ∈ Finset.range m, h k * (0 + 0 + 0 + 0) by simp]
    refine tendsto_finsetSum _ fun k hk => ?_
    have hk' : k < m := Finset.mem_range.1 hk
    have hl := hlev k hk'
    refine Tendsto.const_mul _ ?_
    have hinv := tendsto_inv_log_nat
    have h1 : Tendsto (fun q : ℕ => CB * t (k + 1) ^ 2 / (lev k ^ 2 * Real.log q)) atTop (𝓝 0) := by
      have : (fun q : ℕ => CB * t (k + 1) ^ 2 / (lev k ^ 2 * Real.log q)) =
          fun q : ℕ => (CB * t (k + 1) ^ 2 / lev k ^ 2) * (Real.log q)⁻¹ := by
        funext q; field_simp
      rw [this]; simpa using hinv.const_mul (CB * t (k + 1) ^ 2 / lev k ^ 2)
    have h2 : Tendsto (fun q : ℕ => CB / (lev k ^ 2 * Real.log q ^ 3)) atTop (𝓝 0) := by
      have : (fun q : ℕ => CB / (lev k ^ 2 * Real.log q ^ 3)) =
          fun q : ℕ => (CB / lev k ^ 2) * ((Real.log q)⁻¹) ^ 3 := by
        funext q; field_simp
      rw [this]; simpa using (hinv.pow 3).const_mul (CB / lev k ^ 2)
    have h3 : Tendsto (fun q : ℕ => |CC| * (q : ℝ) ^ (-κ) / Real.log q) atTop (𝓝 0) := by
      have : (fun q : ℕ => |CC| * (q : ℝ) ^ (-κ) / Real.log q) =
          fun q : ℕ => |CC| * ((q : ℝ) ^ (-κ) * (Real.log q)⁻¹) := by
        funext q; ring
      rw [this]; simpa using ((tendsto_rpow_neg_nat hκ).mul hinv).const_mul |CC|
    have h4 : Tendsto (fun q : ℕ => 2 * lev k * (q : ℝ) ^ (lev k - t k)) atTop (𝓝 0) := by
      have hneg : 0 < t k - lev k := by linarith [hlt k hk']
      have : (fun q : ℕ => 2 * lev k * (q : ℝ) ^ (lev k - t k)) =
          fun q : ℕ => 2 * lev k * (q : ℝ) ^ (-(t k - lev k)) := by
        funext q; congr 2; ring
      rw [this]; simpa using (tendsto_rpow_neg_nat hneg).const_mul (2 * lev k)
    exact ((h1.add h2).add h3).add h4
  have hev := (tendsto_order.1 hT).2 ε hε
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.1 hev
  exact ⟨q₀, fun q hq => (hq₀ q hq).le⟩

end GradedNear
