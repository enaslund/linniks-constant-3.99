module

public import GradedNear.Defs

/-!
# Basic identities for the graded near lemma

* `primeSum` as a finite sum over `1 ≤ n ≤ q^X` when the test function vanishes on `[X, ∞)`;
* the factorization `n^{-((A:ℝ) + iγ)} = e^{-A log n} e^{-iγ log n}`;
* a weighted Cauchy–Schwarz inequality for finite sums.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

/-- `t_n = log n / log q`. -/
def tn (q n : ℕ) : ℝ := Real.log n / Real.log q

lemma log_q_pos {q : ℕ} (hq : 2 ≤ q) : 0 < Real.log q :=
  Real.log_pos (by exact_mod_cast (show 1 < q by omega))

lemma tn_nonneg (q n : ℕ) (hq : 2 ≤ q) : 0 ≤ tn q n :=
  div_nonneg (Real.log_natCast_nonneg n) (log_q_pos hq).le

/-- For `n ≥ 1` and real `A, γ`: `n^{-(A + iγ)} = e^{-A log n} · e^{-i γ log n}`. -/
lemma natCast_cpow_neg {n : ℕ} (hn : n ≠ 0) (A γ : ℝ) :
    (n : ℂ) ^ (-((A : ℂ) + (γ : ℂ) * I)) =
      (Real.exp (-A * Real.log n) : ℂ) * cexp (-((γ * Real.log n : ℝ) : ℂ) * I) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  rw [cpow_def_of_ne_zero hn', ← natCast_log, ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Indices beyond `q^X` have `t_n ≥ X`. -/
lemma tn_ge_of_gt {q n : ℕ} (hq : 2 ≤ q) {X : ℝ} (hn : ⌊(q : ℝ) ^ X⌋₊ < n) : X ≤ tn q n := by
  have hℓ := log_q_pos hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have h1 : (q : ℝ) ^ X < n := by
    have := Nat.lt_floor_add_one ((q : ℝ) ^ X)
    have h2 : ((⌊(q : ℝ) ^ X⌋₊ : ℕ) : ℝ) + 1 ≤ n := by exact_mod_cast hn
    linarith
  have hpos : 0 < (q : ℝ) ^ X := Real.rpow_pos_of_pos hq0 X
  have h3 : Real.log ((q : ℝ) ^ X) < Real.log n := Real.log_lt_log hpos h1
  rw [Real.log_rpow hq0] at h3
  unfold tn
  rw [le_div_iff₀ hℓ]
  linarith

/-- `primeSum` is a finite sum when the test function vanishes on `[X, ∞)`. -/
lemma primeSum_eq_sum {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (f : ℝ → ℝ) {X : ℝ}
    (hf : ∀ t, X ≤ t → f t = 0) (s : ℂ) :
    primeSum χ f s = ∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊,
      (Λ n : ℂ) * χ n * (n : ℂ) ^ (-s) * (f (tn q n) : ℂ) := by
  unfold primeSum
  rw [tsum_eq_sum (s := Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊)]
  · rfl
  · intro n hn
    rw [Finset.mem_Icc, not_and_or, not_le, not_le] at hn
    rcases hn with hn | hn
    · have : n = 0 := by omega
      subst this; simp
    · have := hf _ (tn_ge_of_gt hq hn)
      simp [tn] at this
      simp [this]

/-- Weighted Cauchy–Schwarz: `(Σ |c_n| y_n)² ≤ (Σ c_n²/w_n)(Σ w_n y_n²)` when `w ≥ 0`
and `c_n ≠ 0 → w_n > 0`. -/
lemma weighted_cs {β : Type*} (N : Finset β) (c w y : β → ℝ) (hw : ∀ n ∈ N, 0 ≤ w n)
    (hcw : ∀ n ∈ N, c n ≠ 0 → 0 < w n) :
    (∑ n ∈ N, |c n| * y n) ^ 2 ≤ (∑ n ∈ N, c n ^ 2 / w n) * (∑ n ∈ N, w n * y n ^ 2) := by
  have key : ∀ n ∈ N, |c n| * y n = (|c n| / Real.sqrt (w n)) * (Real.sqrt (w n) * y n) := by
    intro n hn
    by_cases hc : c n = 0
    · simp [hc]
    · have hwn := hcw n hn hc
      have hs : Real.sqrt (w n) ≠ 0 := (Real.sqrt_pos.2 hwn).ne'
      field_simp
  rw [Finset.sum_congr rfl key]
  refine (Finset.sum_mul_sq_le_sq_mul_sq N _ _).trans (le_of_eq ?_)
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [div_pow, sq_abs, Real.sq_sqrt (hw n hn)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [mul_pow, Real.sq_sqrt (hw n hn)]

end GradedNear
