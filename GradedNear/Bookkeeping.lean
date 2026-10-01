module

public import Mathlib

/-!
# Gram bookkeeping

If `M_{jk} ≤ R_{jk} + ε` on pairs of the same class and `M_{jk} ≤ d + ε` otherwise, with `R`
symmetric and `a ≥ 0`, then
`Σ_{j,k} a_j a_k M_{jk} ≤ Σ_j (R_{jj} - d + Σ_{k ≠ j, same} (R_{jk} - d)_+) a_j² + (d + ε)(Σ a)²`.
The pair excess uses `2 a_j a_k ≤ a_j² + a_k²` (paper §8.5).
-/

@[expose] public section

namespace GradedNear

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma gram_bookkeeping (same : ι → ι → Prop) [DecidableRel same]
    (hsymm : ∀ j k, same j k → same k j) (hrefl : ∀ j, same j j)
    (M R : ι → ι → ℝ) (hR : ∀ j k, R j k = R k j) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (d ε : ℝ)
    (hsame : ∀ j k, same j k → M j k ≤ R j k + ε) (hdiff : ∀ j k, ¬ same j k → M j k ≤ d + ε) :
    ∑ j, ∑ k, a j * a k * M j k ≤
      ∑ j, (R j j - d + ∑ k ∈ univ.filter (fun k => k ≠ j ∧ same k j), max 0 (R j k - d)) *
          a j ^ 2 + (d + ε) * (∑ j, a j) ^ 2 := by
  classical
  -- excess over `d`, only on distinct pairs of the same class
  set P : ι → ι → ℝ := fun j k => if k ≠ j ∧ same k j then max 0 (R j k - d) else 0 with hP
  have hPsymm : ∀ j k, P j k = P k j := by
    intro j k
    simp only [hP]
    by_cases h : k ≠ j ∧ same k j
    · have h' : j ≠ k ∧ same j k := ⟨fun e => h.1 e.symm, hsymm _ _ h.2⟩
      rw [ite_eq_left_iff.2 (fun hn => absurd h hn), ite_eq_left_iff.2 (fun hn => absurd h' hn), hR]
    · have h' : ¬ (j ≠ k ∧ same j k) := fun h' => h ⟨fun e => h'.1 e.symm, hsymm _ _ h'.2⟩
      rw [ite_eq_right_iff.2 (fun hh => absurd hh h), ite_eq_right_iff.2 (fun hh => absurd hh h')]
  -- termwise bound
  have hterm : ∀ j k, a j * a k * M j k ≤
      a j * a k * (d + ε) + (if k = j then a j * a k * (R j k - d) else 0) +
        a j * a k * P j k := by
    intro j k
    have hajk : 0 ≤ a j * a k := mul_nonneg (ha j) (ha k)
    by_cases hkj : k = j
    · subst hkj
      have hP0 : P k k = 0 := by simp [hP]
      rw [ite_eq_left_iff.2 (fun h => absurd rfl h), hP0, mul_zero, add_zero]
      have := mul_le_mul_of_nonneg_left (hsame k k (hrefl k)) hajk
      nlinarith
    · rw [ite_eq_right_iff.2 (fun h => absurd h hkj)]
      by_cases hs : same k j
      · have hPjk : P j k = max 0 (R j k - d) := by simp [hP, hkj, hs]
        rw [hPjk]
        have := mul_le_mul_of_nonneg_left (hsame j k (hsymm _ _ hs)) hajk
        have hm : R j k - d ≤ max 0 (R j k - d) := le_max_right _ _
        nlinarith [mul_le_mul_of_nonneg_left hm hajk]
      · have hPjk : P j k = 0 := by simp [hP, hs]
        rw [hPjk]
        have hns : ¬ same j k := fun h => hs (hsymm _ _ h)
        have := mul_le_mul_of_nonneg_left (hdiff j k hns) hajk
        nlinarith
  -- the pair excess via 2 a_j a_k ≤ a_j² + a_k²
  have hpair : ∑ j, ∑ k, a j * a k * P j k ≤ ∑ j, (∑ k, P j k) * a j ^ 2 := by
    have hPnn : ∀ j k, 0 ≤ P j k := by
      intro j k; simp only [hP]; split_ifs <;> simp
    have h1 : ∀ j k, a j * a k * P j k ≤ (a j ^ 2 * P j k + a k ^ 2 * P j k) / 2 := by
      intro j k
      have := mul_le_mul_of_nonneg_right (two_mul_le_add_sq (a j) (a k)) (hPnn j k)
      nlinarith
    calc ∑ j, ∑ k, a j * a k * P j k
        ≤ ∑ j, ∑ k, (a j ^ 2 * P j k + a k ^ 2 * P j k) / 2 :=
          sum_le_sum fun j _ => sum_le_sum fun k _ => h1 j k
      _ = (∑ j, ∑ k, a j ^ 2 * P j k + ∑ j, ∑ k, a k ^ 2 * P j k) / 2 := by
          rw [← sum_add_distrib, sum_div]
          refine sum_congr rfl fun j _ => ?_
          rw [← sum_add_distrib, sum_div]
      _ = (∑ j, ∑ k, a j ^ 2 * P j k + ∑ j, ∑ k, a j ^ 2 * P j k) / 2 := by
          congr 2
          rw [sum_comm]
          refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
          rw [hPsymm]
      _ = ∑ j, (∑ k, P j k) * a j ^ 2 := by
          rw [add_self_div_two]
          refine sum_congr rfl fun j _ => ?_
          rw [sum_mul]
          refine sum_congr rfl fun k _ => ?_
          ring
  -- assemble
  have hdiag : ∑ j, ∑ k, (if k = j then a j * a k * (R j k - d) else 0) =
      ∑ j, (R j j - d) * a j ^ 2 := by
    refine sum_congr rfl fun j _ => ?_
    rw [sum_ite_eq' univ j (fun k => a j * a k * (R j k - d))]
    simp only [mem_univ, ite_true]
    ring
  have hconst : ∑ j, ∑ k, a j * a k * (d + ε) = (d + ε) * (∑ j, a j) ^ 2 := by
    rw [sq, sum_mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    ring
  have hPsum : ∀ j, ∑ k, P j k = ∑ k ∈ univ.filter (fun k => k ≠ j ∧ same k j),
      max 0 (R j k - d) := by
    intro j
    rw [sum_filter]
  calc ∑ j, ∑ k, a j * a k * M j k
      ≤ ∑ j, ∑ k, (a j * a k * (d + ε) + (if k = j then a j * a k * (R j k - d) else 0) +
          a j * a k * P j k) := sum_le_sum fun j _ => sum_le_sum fun k _ => hterm j k
    _ = ∑ j, ∑ k, a j * a k * (d + ε) +
          ∑ j, ∑ k, (if k = j then a j * a k * (R j k - d) else 0) +
          ∑ j, ∑ k, a j * a k * P j k := by
        rw [← sum_add_distrib, ← sum_add_distrib]
        refine sum_congr rfl fun j _ => ?_
        rw [← sum_add_distrib, ← sum_add_distrib]
    _ ≤ (d + ε) * (∑ j, a j) ^ 2 + ∑ j, (R j j - d) * a j ^ 2 +
          ∑ j, (∑ k, P j k) * a j ^ 2 := by
        rw [hconst, hdiag]; linarith [hpair]
    _ = _ := by
        simp_rw [hPsum]
        simp only [add_mul, sum_add_distrib]
        ring

end GradedNear
