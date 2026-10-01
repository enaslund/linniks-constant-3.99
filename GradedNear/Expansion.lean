module

public import GradedNear.Basic

/-!
# The responses as one sum over `n`

`Σ_j a_j R_j = -𝓛⁻¹ Re Σ_{1 ≤ n ≤ q^{x_f}} c_n Y_n`, with `c_n = (Λ(n)/n) e^{s t_n} f(t_n)` and
`Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}` (paper §8.5).
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

variable {q : ℕ} {ι : Type*} [Fintype ι]

/-- `Y_n = Σ_j a_j e^{-δ_j t_n} χ_j(n) e^{-i γ_j log n}`. -/
def Yn (E : Entries q ι) (a : ι → ℝ) (n : ℕ) : ℂ :=
  ∑ j, (a j : ℂ) * ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I))

/-- `c_n = (Λ(n)/n) e^{s t_n} f(t_n)`. -/
def cWeight (D : NearData) (q n : ℕ) : ℝ :=
  Λ n / n * Real.exp (D.s * tn q n) * D.f (tn q n)

/-- The term of a response at `n ≥ 1` factors as `c_n` times the entry's component of `Y_n`. -/
lemma response_term (D : NearData) {n : ℕ} (hn : 1 ≤ n)
    (χ : DirichletCharacter ℂ q) (γ δ : ℝ) :
    (Λ n : ℂ) * χ n *
        (n : ℂ) ^ (-((((1 - (D.s - δ) / Real.log q : ℝ)) : ℂ) + (γ : ℂ) * I)) *
        (D.f (tn q n) : ℂ) =
      (cWeight D q n : ℂ) * ((Real.exp (-δ * tn q n) : ℂ) * χ n *
        cexp (-((γ * Real.log n : ℝ) : ℂ) * I)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [natCast_cpow_neg hn0]
  have hexp : Real.exp (-(1 - (D.s - δ) / Real.log q) * Real.log n) =
      (1 / n) * Real.exp (D.s * tn q n) * Real.exp (-δ * tn q n) := by
    rw [one_div, ← Real.exp_log hnpos, ← Real.exp_neg, Real.exp_log hnpos, ← Real.exp_add,
      ← Real.exp_add]
    · congr 1; unfold tn; ring
  rw [hexp]
  unfold cWeight
  push_cast
  ring

/-- `Σ_j a_j R_j = -𝓛⁻¹ Re Σ_{1 ≤ n ≤ q^{x_f}} c_n Y_n`. -/
lemma sum_response (D : NearData) (E : Entries q ι) (a : ι → ℝ) (hq : 2 ≤ q)
    (hf : ∀ t, D.xf ≤ t → D.f t = 0) :
    ∑ j, a j * response D E j =
      -(∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, (cWeight D q n : ℂ) * Yn E a n).re /
        Real.log q := by
  unfold response
  have hrepr : ∀ j, primeSum (E.χ j) D.f
      (((1 - (D.s - E.δ j) / Real.log q : ℝ) : ℂ) + (E.γ j : ℂ) * I) =
      ∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, (cWeight D q n : ℂ) *
        ((Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
          cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I)) := by
    intro j
    rw [primeSum_eq_sum hq _ _ hf]
    refine Finset.sum_congr rfl fun n hn => ?_
    exact response_term D (Finset.mem_Icc.1 hn).1 _ _ _
  simp_rw [hrepr]
  set S := Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊
  set v : ι → ℕ → ℂ := fun j n => (Real.exp (-(E.δ j) * tn q n) : ℂ) * E.χ j n *
    cexp (-((E.γ j * Real.log n : ℝ) : ℂ) * I) with hv
  have h1 : ∀ j, a j * (-(∑ n ∈ S, (cWeight D q n : ℂ) * v j n).re / Real.log q) =
      -((∑ n ∈ S, (a j : ℂ) * ((cWeight D q n : ℂ) * v j n)).re) / Real.log q := by
    intro j
    rw [← Finset.mul_sum, Complex.re_ofReal_mul]
    ring
  rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.sum_div, Finset.sum_neg_distrib,
    ← Complex.re_sum]
  congr 3
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun n _ => ?_
  unfold Yn
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [hv]
  ring

end GradedNear
