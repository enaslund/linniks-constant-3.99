module

public import GradedNear.KernelFacts
public import GradedNear.FarFacts
public import GradedNear.Cert.Semantics

/-!
# The monotonicity of every column kind (paper §§5–6, 10)

`Cert.leaf_interpretation` needs, for each column, that its objective decreases along the bin
(`ColSem.Mono`), or, for a tail, that objective per far weight decreases. For the functions of
the corpus this follows from the proved facts, at every exponent `L ≥ 3.99` and for both far
profiles:
* bins with `G_φ` (ordinary `φ = 1/3`, real `φ = 1/4`, second family `φ₂`), since `G_φ`
  decreases (`Gphi_antitone`);
* tails with `G_φ`: `G_φ/w = (e^{−Aλ} w⁻¹) · B_φ` is a product of nonnegative decreasing factors
  (`tail_antitone`, `Benv_antitone`);
* hidden columns `t ↦ e^{−At} B_φ(p)` and their tail, likewise with `B_φ(p)` fixed.
-/

@[expose] public section

noncomputable section

namespace GradedNear.Kernel

open Cert

/-- A product of two nonnegative decreasing functions decreases. -/
lemma antitone_mul_of_nonneg {f g : ℝ → ℝ} (hf : Antitone f) (hg : Antitone g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) : Antitone fun x => f x * g x :=
  fun _ _ hab => mul_le_mul (hf hab) (hg hab) (hg0 _) (hf0 _)

variable {L : ℝ}

lemma A_ge (hL : 3.99 ≤ L) : 3.156342 ≤ L - 2 * (T : ℝ) := by
  have := three_point_nine_nine_sub_two_T
  linarith

/-- Bins charged by `G_φ` are monotone. -/
theorem mono_bin_Gphi (hL : 3.99 ≤ L) {φ : ℝ} (hφ : 0 ≤ φ) (w : ℝ → ℝ) (lo hi : ℝ) :
    (ColSem.bin lo hi (Gphi L φ)).Mono w := by
  intro a b _ hab
  exact Gphi_antitone (by linarith [A_ge hL]) hφ hab

/-- Tails charged by `G_φ`, for the corpus profiles, are monotone: `G_φ/w` decreases. -/
theorem mono_tail_Gphi (hL : 3.99 ≤ L) {φ : ℝ} (hφ : 0 ≤ φ) {P : FarProfile}
    (hP : P = inherited ∨ P = retuned) (R : ℝ) :
    (ColSem.tail R (Gphi L φ)).Mono P.w := by
  intro a b _ hab
  have h1 : Antitone fun lam => Real.exp (-((L - 2 * T) * lam)) * P.winv lam :=
    P.tail_antitone_corpus hP (A_ge hL)
  have h2 : Antitone (Benv φ) := Benv_antitone hφ
  have hprod := antitone_mul_of_nonneg h1 h2
    (fun x => mul_nonneg (Real.exp_pos _).le (P.winv_pos_corpus hP x).le)
    (fun x => Benv_nonneg hφ x) hab
  have key : ∀ x, Gphi L φ x / P.w x =
      Real.exp (-((L - 2 * T) * x)) * P.winv x * Benv φ x := by
    intro x
    simp only [Gphi, FarProfile.w, div_inv_eq_mul]
    ring
  simp only [key]
  exact hprod

/-- Hidden columns `t ↦ e^{−At} B_φ(p)` are monotone. -/
theorem mono_bin_hidden (hL : 3.99 ≤ L) {φ : ℝ} (hφ : 0 ≤ φ) (p : ℝ) (w : ℝ → ℝ) (lo hi : ℝ) :
    (ColSem.bin lo hi (fun t => Real.exp (-((L - 2 * T) * t)) * Benv φ p)).Mono w := by
  intro a b _ hab
  refine mul_le_mul_of_nonneg_right ?_ (Benv_nonneg hφ p)
  apply Real.exp_le_exp.2
  have := A_ge hL
  nlinarith

/-- The hidden tail, for the corpus profiles, is monotone. -/
theorem mono_tail_hidden (hL : 3.99 ≤ L) {φ : ℝ} (hφ : 0 ≤ φ) (p : ℝ) {P : FarProfile}
    (hP : P = inherited ∨ P = retuned) (R : ℝ) :
    (ColSem.tail R (fun t => Real.exp (-((L - 2 * T) * t)) * Benv φ p)).Mono P.w := by
  intro a b _ hab
  have h1 : Antitone fun lam => Real.exp (-((L - 2 * T) * lam)) * P.winv lam :=
    P.tail_antitone_corpus hP (A_ge hL)
  have key : ∀ x, Real.exp (-((L - 2 * T) * x)) * Benv φ p / P.w x =
      Real.exp (-((L - 2 * T) * x)) * P.winv x * Benv φ p := by
    intro x
    simp only [FarProfile.w, div_inv_eq_mul]
    ring
  simp only [key]
  exact mul_le_mul_of_nonneg_right (h1 hab) (Benv_nonneg hφ p)

end GradedNear.Kernel
