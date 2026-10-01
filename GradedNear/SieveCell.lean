module

public import GradedNear.GramForm
public import GradedNear.SieveBasic

/-!
# One sieve cell

For a cell `𝒞` of integers `n ≥ 1` with `t_n ≥ t₀`, if
* `Λ(n) ≤ log n · ν(n) + pp(n)` on `𝒞`,
* `Σ_{𝒞} (log n / n) ν(n) ≤ Dk`,
* `‖Σ_{𝒞} ν(n) ψ_{jj'}(n) log n · n^{-((1+β) + iτ)}‖ ≤ Ok` for every pair `j ≠ j'`,
* `Σ_{𝒞} pp(n)/n ≤ Pk`,

then `Σ_{𝒞} (Λ(n)/n) |Y_n|² ≤ Σ_j e^{-2δ_j t₀} Dk a_j² + (Ok + Pk)(Σ a)²`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- `‖Y_n‖ ≤ Σ_j a_j` for `a ≥ 0` and `δ ≥ 0`, `t_n ≥ 0`. -/
lemma norm_Yn_le (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hδ : ∀ j, 0 ≤ E.δ j)
    {n : ℕ} (hq : 2 ≤ q) : ‖Yn E a n‖ ≤ ∑ j, a j := by
  unfold Yn
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j),
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h1 : Real.exp (-(E.δ j) * tn q n) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have := tn_nonneg q n hq
    nlinarith [hδ j]
  have h2 : ‖E.χ j n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h3 : ‖cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I)‖ = 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  rw [h3, mul_one]
  have := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
  nlinarith [ha j]

omit [Fintype ι] in
/-- The sieve summand identity: `(log n/n) Re(ycomp_j conj ycomp_{j'})` equals
`a_j a_{j'} Re(ψ(n) log n · n^{-((1+β) + iτ)})` with `β = (δ_j + δ_{j'})/𝓛`, `τ = γ_j - γ_{j'}`. -/
lemma sieve_term {n : ℕ} (hn : 1 ≤ n) (hq : 2 ≤ q) (E : Entries q ι) (a : ι → ℝ) (j j' : ι) :
    Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re =
      a j * a j' * ((E.χ j * (E.χ j')⁻¹) n * (Real.log n : ℂ) *
        (n : ℂ) ^ (-(((1 + (E.δ j + E.δ j') / Real.log q : ℝ) : ℂ) +
          ((E.γ j - E.γ j' : ℝ) : ℂ) * I))).re := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hℓ := log_q_pos hq
  rw [ycomp_mul_conj, natCast_cpow_neg hn0]
  have hexp : Real.exp (-(1 + (E.δ j + E.δ j') / Real.log q) * Real.log n) =
      (1 / n) * Real.exp (-(E.δ j + E.δ j') * tn q n) := by
    rw [one_div, ← Real.exp_log hnpos, ← Real.exp_neg, Real.exp_log hnpos, ← Real.exp_add]
    congr 1; unfold tn; field_simp; ring
  rw [hexp]
  have e1 : cexp (-(((E.γ j - E.γ j') * Real.log n : ℝ) : ℂ) * I) =
      cexp (-((((E.γ j - E.γ j' : ℝ)) * Real.log n : ℝ) : ℂ) * I) := rfl
  rw [Complex.re_ofReal_mul]
  have : (E.χ j * (E.χ j')⁻¹) n * (Real.log n : ℂ) *
      (((1 / n * Real.exp (-(E.δ j + E.δ j') * tn q n) : ℝ) : ℂ) *
        cexp (-(((E.γ j - E.γ j') * Real.log n : ℝ) : ℂ) * I)) =
      ((Real.log n * (1 / n * Real.exp (-(E.δ j + E.δ j') * tn q n)) : ℝ) : ℂ) *
        ((E.χ j * (E.χ j')⁻¹) n * cexp (-(((E.γ j - E.γ j') * Real.log n : ℝ) : ℂ) * I)) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  ring

omit [Fintype ι] in
/-- `‖ycomp_j‖² ≤ a_j² e^{-2 δ_j t_n}` as the real part of `ycomp_j · conj ycomp_j`. -/
lemma ycomp_self_le (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (j : ι) (n : ℕ) :
    (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j n)).re ≤
      a j ^ 2 * Real.exp (-2 * E.δ j * tn q n) := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold ycomp
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j),
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have h2 : ‖E.χ j n‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
  have h3 : ‖cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I)‖ = 1 := by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  rw [h3, mul_one]
  have he : Real.exp (-2 * E.δ j * tn q n) = Real.exp (-(E.δ j) * tn q n) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he]
  have hx : 0 ≤ Real.exp (-(E.δ j) * tn q n) := (Real.exp_pos _).le
  have h4 : Real.exp (-(E.δ j) * tn q n) * ‖E.χ j n‖ ≤ Real.exp (-(E.δ j) * tn q n) := by
    nlinarith [norm_nonneg (E.χ j n)]
  have h5 : 0 ≤ Real.exp (-(E.δ j) * tn q n) * ‖E.χ j n‖ := mul_nonneg hx (norm_nonneg _)
  have h6 : (a j * (Real.exp (-(E.δ j) * tn q n) * ‖E.χ j n‖)) ^ 2 ≤
      (a j * Real.exp (-(E.δ j) * tn q n)) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (ha j) h5) (mul_le_mul_of_nonneg_left h4 (ha j)) 2
  calc (a j * (Real.exp (-(E.δ j) * tn q n) * ‖E.χ j n‖)) ^ 2
      ≤ (a j * Real.exp (-(E.δ j) * tn q n)) ^ 2 := h6
    _ = a j ^ 2 * Real.exp (-(E.δ j) * tn q n) ^ 2 := by ring

/-- **Bound for one sieve cell.** -/
lemma cell_bound (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) (hδ : ∀ j, 0 ≤ E.δ j)
    (hq : 2 ≤ q) (V t₀ Dk Ok Pk : ℝ) (C : Finset ℕ) (hC1 : ∀ n ∈ C, 1 ≤ n)
    (hCt : ∀ n ∈ C, t₀ ≤ tn q n) (pp : ℕ → ℝ) (hpp0 : ∀ n, 0 ≤ pp n)
    (hmaj : ∀ n ∈ C, Λ n ≤ Real.log n * sieveNu V n + pp n)
    (hdiag : ∑ n ∈ C, Real.log n / n * sieveNu V n ≤ Dk)
    (hoff : ∀ j j', j ≠ j' → ‖∑ n ∈ C, (sieveNu V n : ℂ) * ((E.χ j * (E.χ j')⁻¹) n *
        (Real.log n : ℂ) * (n : ℂ) ^ (-(((1 + (E.δ j + E.δ j') / Real.log q : ℝ) : ℂ) +
          ((E.γ j - E.γ j' : ℝ) : ℂ) * I)))‖ ≤ Ok)
    (hppsum : ∑ n ∈ C, pp n / n ≤ Pk) (hOk : 0 ≤ Ok) :
    ∑ n ∈ C, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      ∑ j, Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 + (Ok + Pk) * (∑ j, a j) ^ 2 := by
  classical
  have hY : ∀ n, ‖Yn E a n‖ ^ 2 ≤ (∑ j, a j) ^ 2 := fun n =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_Yn_le E a ha hδ hq) 2
  have hsumA : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  -- majorant
  have step1 : ∑ n ∈ C, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 +
        ∑ n ∈ C, pp n / n * ‖Yn E a n‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (hC1 n hn)
    have hm := hmaj n hn
    have hY0 := sq_nonneg ‖Yn E a n‖
    have key : Λ n / n * ‖Yn E a n‖ ^ 2 ≤
        (Real.log n * sieveNu V n + pp n) / n * ‖Yn E a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hm hnpos.le) hY0
    calc Λ n / n * ‖Yn E a n‖ ^ 2 ≤ (Real.log n * sieveNu V n + pp n) / n * ‖Yn E a n‖ ^ 2 :=
          key
      _ = Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 + pp n / n * ‖Yn E a n‖ ^ 2 := by
          ring
  -- small prime powers
  have step2 : ∑ n ∈ C, pp n / n * ‖Yn E a n‖ ^ 2 ≤ Pk * (∑ j, a j) ^ 2 := by
    calc ∑ n ∈ C, pp n / n * ‖Yn E a n‖ ^ 2 ≤ ∑ n ∈ C, pp n / n * (∑ j, a j) ^ 2 :=
          Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (hY n)
            (div_nonneg (hpp0 n) (Nat.cast_nonneg n))
      _ = (∑ n ∈ C, pp n / n) * (∑ j, a j) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ Pk * (∑ j, a j) ^ 2 := mul_le_mul_of_nonneg_right hppsum (sq_nonneg _)
  -- expand the Selberg part
  have hexpand : ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ j', ∑ n ∈ C, sieveNu V n *
        (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) := by
    simp_rw [norm_Yn_sq, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun n _ => ?_
    ring
  have hν : ∀ n, 0 ≤ sieveNu V n := sieveNu_nonneg V
  have hdiagj : ∀ j, ∑ n ∈ C, sieveNu V n *
      (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j n)).re) ≤
      Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 := by
    intro j
    calc ∑ n ∈ C, sieveNu V n *
          (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j n)).re)
        ≤ ∑ n ∈ C, (Real.log n / n * sieveNu V n) * (a j ^ 2 * Real.exp (-2 * E.δ j * t₀)) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hlog : 0 ≤ Real.log n / n :=
            div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
          have h1 := ycomp_self_le E a ha j n
          have h2 : Real.exp (-2 * E.δ j * tn q n) ≤ Real.exp (-2 * E.δ j * t₀) := by
            apply Real.exp_le_exp.2
            nlinarith [hδ j, hCt n hn]
          have h3 : a j ^ 2 * Real.exp (-2 * E.δ j * tn q n) ≤
              a j ^ 2 * Real.exp (-2 * E.δ j * t₀) :=
            mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
          have := mul_le_mul_of_nonneg_left (h1.trans h3) (mul_nonneg hlog (hν n))
          nlinarith [hν n]
      _ = (∑ n ∈ C, Real.log n / n * sieveNu V n) * (a j ^ 2 * Real.exp (-2 * E.δ j * t₀)) := by
          rw [Finset.sum_mul]
      _ ≤ Dk * (a j ^ 2 * Real.exp (-2 * E.δ j * t₀)) :=
          mul_le_mul_of_nonneg_right hdiag (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ = _ := by ring
  have hoffj : ∀ j j', j ≠ j' → ∑ n ∈ C, sieveNu V n *
      (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) ≤
      a j * a j' * Ok := by
    intro j j' hjj'
    have hrw : ∀ n ∈ C, sieveNu V n *
        (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re) =
        a j * a j' * ((sieveNu V n : ℂ) * ((E.χ j * (E.χ j')⁻¹) n * (Real.log n : ℂ) *
          (n : ℂ) ^ (-(((1 + (E.δ j + E.δ j') / Real.log q : ℝ) : ℂ) +
            ((E.γ j - E.γ j' : ℝ) : ℂ) * I)))).re := by
      intro n hn
      rw [sieve_term (hC1 n hn) hq, Complex.re_ofReal_mul]
      ring
    rw [Finset.sum_congr rfl hrw, ← Finset.mul_sum, ← Complex.re_sum]
    exact mul_le_mul_of_nonneg_left ((Complex.re_le_norm _).trans (hoff j j' hjj'))
      (mul_nonneg (ha j) (ha j'))
  have step3 : ∑ n ∈ C, Real.log n / n * sieveNu V n * ‖Yn E a n‖ ^ 2 ≤
      ∑ j, Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 + Ok * (∑ j, a j) ^ 2 := by
    rw [hexpand]
    calc ∑ j, ∑ j', ∑ n ∈ C, sieveNu V n *
          (Real.log n / n * (ycomp E a j n * (starRingEnd ℂ) (ycomp E a j' n)).re)
        ≤ ∑ j, ∑ j', (if j' = j then Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2
            else a j * a j' * Ok) := by
          refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun j' _ => ?_
          by_cases h : j' = j
          · subst h; rw [ite_eq_left_iff.2 (fun hh => absurd rfl hh)]; exact hdiagj j'
          · rw [ite_eq_right_iff.2 (fun hh => absurd hh h)]; exact hoffj j j' (fun e => h e.symm)
      _ ≤ ∑ j, ∑ j', (if j' = j then Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 else 0) +
            ∑ j, ∑ j', a j * a j' * Ok := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun j' _ => ?_
          split_ifs
          · nlinarith [mul_nonneg (ha j) (ha j')]
          · linarith
      _ = ∑ j, Real.exp (-2 * E.δ j * t₀) * Dk * a j ^ 2 + Ok * (∑ j, a j) ^ 2 := by
          congr 1
          · refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_ite_eq' Finset.univ j]
            simp
          · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j' _ => ?_
            ring
  linarith [step1, step2, step3]

end GradedNear
