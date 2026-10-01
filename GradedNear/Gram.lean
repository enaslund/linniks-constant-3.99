module

public import GradedNear.Expansion

/-!
# The Gram part of the second Cauchy–Schwarz factor

`Σ_n (Λ(n)/n) g(t_n) e^{s₁ t_n} |Y_n|² = Σ_{j,k} a_j a_k Re primeSum(χ_j χ_k⁻¹, g, s_{jk})`,
with `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` and `σ_{jk} = s₁ - δ_j - δ_k` (paper §8.5).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- The general term identity: for `n ≥ 1`,
`Λ(n) χ(n) n^{-((1 - σ/𝓛) + iγ)} F(t_n) = (Λ(n)/n) e^{σ t_n} F(t_n) · χ(n) e^{-iγ log n}`. -/
lemma prime_term (F : ℝ → ℝ) {n : ℕ} (hn : 1 ≤ n) (χ : DirichletCharacter ℂ q) (σ γ : ℝ) :
    (Λ n : ℂ) * χ n * (n : ℂ) ^ (-((((1 - σ / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I)) *
        (F (tn q n) : ℂ) =
      ((Λ n / n * Real.exp (σ * tn q n) * F (tn q n) : ℝ) : ℂ) *
        (χ n * cexp (-((γ * Real.log n : ℝ) : ℂ) * I)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [natCast_cpow_neg hn0]
  have hexp : Real.exp (-(1 - σ / Real.log q) * Real.log n) =
      (1 / n) * Real.exp (σ * tn q n) := by
    rw [one_div, ← Real.exp_log hnpos, ← Real.exp_neg, Real.exp_log hnpos, ← Real.exp_add]
    congr 1; unfold tn; ring
  rw [hexp]
  push_cast
  ring

/-- The `j`-th component of `Y_n`. -/
def ycomp (E : Entries q ι) (a : ι → ℝ) (j : ι) (n : ℕ) : ℂ :=
  (a j : ℂ) * ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

lemma Yn_eq_sum (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : Yn E a n = ∑ j, ycomp E a j n := rfl

omit [Fintype ι] in
/-- `ycomp_j · conj(ycomp_k) = a_j a_k e^{-(δ_j+δ_k) t_n} (χ_j χ_k⁻¹)(n) e^{-i(γ_j - γ_k) log n}`. -/
lemma ycomp_mul_conj (E : Entries q ι) (a : ι → ℝ) (j k : ι) (n : ℕ) :
    ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n) =
      ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) *
        ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)) := by
  unfold ycomp
  have hχ : (starRingEnd ℂ) (E.χ k n) = (E.χ k)⁻¹ n := by
    rw [← MulChar.star_apply']; rfl
  have hexp : (starRingEnd ℂ) (cexp (-((E.γ k * Real.log n : ℝ) : ℂ) * I)) =
      cexp (((E.γ k * Real.log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_conj]; congr 1
    rw [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; ring
  have e1 : cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I) *
      cexp (((E.γ k * Real.log n : ℝ) : ℂ) * I) =
      cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have e2r : Real.exp (-(E.δ j + E.δ k) * tn q n) =
      Real.exp (-(E.δ j) * tn q n) * Real.exp (-(E.δ k) * tn q n) := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : ((a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) : ℝ) : ℂ) =
      (a j : ℂ) * (a k : ℂ) * (Real.exp (-(E.δ j) * tn q n) : ℂ) *
        (Real.exp (-(E.δ k) * tn q n) : ℂ) := by
    rw [e2r]; push_cast; ring
  simp only [map_mul, Complex.conj_ofReal, hχ, hexp]
  rw [e2, ← e1, MulChar.coeToFun_mul, Pi.mul_apply]
  ring

/-- `|Y_n|² = Σ_{j,k} Re(ycomp_j · conj ycomp_k)`. -/
lemma norm_Yn_sq (E : Entries q ι) (a : ι → ℝ) (n : ℕ) :
    ‖Yn E a n‖ ^ 2 = ∑ j, ∑ k, (ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n)).re := by
  have h : ‖Yn E a n‖ ^ 2 = (Yn E a n * (starRingEnd ℂ) (Yn E a n)).re := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  rw [h, Yn_eq_sum, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  simp_rw [Complex.re_sum]

/-- The Gram point `s_{jk} = (1 - σ_{jk}/𝓛) + i(γ_j - γ_k)` with `σ_{jk} = s₁ - δ_j - δ_k`. -/
def sjk (D : NearData) (E : Entries q ι) (j k : ι) : ℂ :=
  (((1 - (D.s₁ - E.δ j - E.δ k) / Real.log q : ℝ)) : ℂ) + ((E.γ j - E.γ k : ℝ) : ℂ) * I

omit [Fintype ι] in
/-- The Gram-part summand at `n ≥ 1`, entry `(j,k)`. -/
lemma gram_term (D : NearData) (E : Entries q ι) (a : ι → ℝ) {n : ℕ} (hn : 1 ≤ n) (j k : ι) :
    Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        (ycomp E a j n * (starRingEnd ℂ) (ycomp E a k n)).re =
      a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk D E j k) *
        (D.g (tn q n) : ℂ)).re := by
  rw [ycomp_mul_conj, sjk, prime_term D.g hn, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  have : Real.exp (D.s₁ * tn q n) * Real.exp (-(E.δ j + E.δ k) * tn q n) =
      Real.exp ((D.s₁ - E.δ j - E.δ k) * tn q n) := by
    rw [← Real.exp_add]; congr 1; ring
  calc Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        (a j * a k * Real.exp (-(E.δ j + E.δ k) * tn q n) *
          ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)).re)
      = a j * a k * (Λ n / n * (Real.exp (D.s₁ * tn q n) * Real.exp (-(E.δ j + E.δ k) * tn q n))
          * D.g (tn q n) *
          ((E.χ j * (E.χ k)⁻¹) n * cexp (-(((E.γ j - E.γ k) * Real.log n : ℝ) : ℂ) * I)).re) := by
        ring
    _ = _ := by rw [this]

/-- The Gram part of the second factor as a quadratic form in the prime sums. -/
lemma gram_part_eq (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hg : ∀ t, D.xg ≤ t → D.g t = 0) {N : ℕ} (hN : ⌊(q : ℝ) ^ D.xg⌋₊ ≤ N) :
    ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re := by
  set S := Finset.Icc 1 ⌊(q : ℝ) ^ D.xg⌋₊ with hS
  have hsub : S ⊆ Finset.Icc 1 N := Finset.Icc_subset_Icc le_rfl hN
  have hLHS : ∑ n ∈ Finset.Icc 1 N, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) *
        ‖Yn E a n‖ ^ 2 =
      ∑ n ∈ S, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hn'
    have h1 : 1 ≤ n := (Finset.mem_Icc.1 hn).1
    have h2 : ⌊(q : ℝ) ^ D.xg⌋₊ < n := by
      by_contra h; exact hn' (Finset.mem_Icc.2 ⟨h1, not_lt.1 h⟩)
    rw [hg _ (tn_ge_of_gt hq h2)]
    simp
  rw [hLHS]
  have hR : ∀ j k, a j * a k * (primeSum (E.χ j * (E.χ k)⁻¹) D.g (sjk D E j k)).re =
      ∑ n ∈ S, a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk D E j k) *
        (D.g (tn q n) : ℂ)).re := by
    intro j k
    rw [primeSum_eq_sum hq _ _ hg, Complex.re_sum, Finset.mul_sum]
  simp_rw [hR]
  have hL : ∀ n ∈ S, Λ n / n * (D.g (tn q n) * Real.exp (D.s₁ * tn q n)) * ‖Yn E a n‖ ^ 2 =
      ∑ j, ∑ k, a j * a k * ((Λ n : ℂ) * (E.χ j * (E.χ k)⁻¹) n * (n : ℂ) ^ (-sjk D E j k) *
        (D.g (tn q n) : ℂ)).re := by
    intro n hn
    rw [norm_Yn_sq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact gram_term D E a (Finset.mem_Icc.1 hn).1 j k
  rw [Finset.sum_congr rfl hL, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

end GradedNear
