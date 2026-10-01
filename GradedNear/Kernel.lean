module

public import GradedNear.Prime

/-!
# The 16-step prime-detection kernel (paper §4)

The constants are those of `computations/core/code/config_v4.py` in the research repository: `T = .416829`, the step width
`κ = T/16` and the sixteen heights `β₀, …, β₁₅` (written `b_0, …, b_15` in the paper). The step kernel is
`ψ = Σ_i β_i 1_{[iκ,(i+1)κ)}`, and the prime weight is `h(t) = (ψ * ψ)(t − A)` with `A = L − 2T`.
Since `1_{[iκ,(i+1)κ)} * 1_{[jκ,(j+1)κ)}` is Xylouris's triangle `h_{(i+j+2)κ, κ}`, the weight is
the triangle combination `h = Σ_{k=0}^{30} c_k h_{A+(k+2)κ, κ}` with `c_k = Σ_{i+j=k} β_i β_j`
(paper §4.1, Lemma 4.1). `primeKernel L` is that combination. Every component has left endpoint
`A + kκ ≥ A`, and right endpoint at most `A + 32κ = L`.

`exists_prime` applies Xylouris's criterion (3.57) to it: when `A > 3`, a zero sum below
`H(0) − ε` gives a prime `p ≡ a (mod q)` with `q^A < p < q^L`.
-/

@[expose] public section

namespace GradedNear.Kernel

/-- `T = .416829`. -/
def T : ℚ := 416829 / 1000000

/-- The sixteen step heights `β₀, …, β₁₅` of `config_v4.py`. -/
def beta : Fin 16 → ℚ := ![2318741 / 100000000, 7159337 / 100000000, 12265085 / 100000000,
  17627704 / 100000000, 23237155 / 100000000, 29081583 / 100000000, 35147264 / 100000000,
  41418551 / 100000000, 47877833 / 100000000, 54505502 / 100000000, 61279917 / 100000000,
  68177389 / 100000000, 75172165 / 100000000, 82236428 / 100000000, 89340300 / 100000000,
  96451862 / 100000000]

/-- The step width `κ = T/16`. -/
def kappa : ℚ := T / 16

/-- The triangle coefficients `c_k = Σ_{i+j=k} β_i β_j`, `k = 0, …, 30`. -/
def coef (k : Fin 31) : ℚ :=
  ∑ i : Fin 16, ∑ j : Fin 16, if i.val + j.val = k.val then beta i * beta j else 0

/-- The prime kernel at exponent `L`: `h = Σ_{k=0}^{30} c_k h_{A+(k+2)κ, κ}` with `A = L − 2T`. -/
def primeKernel (L : ℝ) : TriKernel where
  n := 31
  α k := coef k
  L k := L - 2 * T + (k.val + 2) * kappa
  K _ := kappa

lemma kappa_pos : (0 : ℝ) < kappa := by norm_num [kappa, T]

lemma two_T_eq : (2 * T : ℝ) = 32 * kappa := by norm_num [kappa, T]

/-- For `A = L − 2T > 3` every component satisfies Xylouris's condition `L_i > 2K_i + 3`. -/
lemma primeKernel_admissible {L : ℝ} (hL : 3 + 2 * (T : ℝ) < L) : (primeKernel L).Admissible := by
  intro k
  refine ⟨kappa_pos, ?_⟩
  show 2 * (kappa : ℝ) + 3 < L - 2 * T + ((k.val : ℝ) + 2) * kappa
  have hk : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  nlinarith [kappa_pos]

/-- Every component of `primeKernel L` is supported in `[L − 2T, L]`. -/
lemma primeKernel_support (L : ℝ) (k : Fin 31) :
    L - 2 * (T : ℝ) ≤ (primeKernel L).L k - 2 * (primeKernel L).K k ∧
      (primeKernel L).L k ≤ L := by
  show L - 2 * (T : ℝ) ≤ L - 2 * T + ((k.val : ℝ) + 2) * kappa - 2 * kappa ∧
    L - 2 * T + ((k.val : ℝ) + 2) * kappa ≤ L
  have hk : (k.val : ℝ) ≤ 30 := by exact_mod_cast Nat.le_of_lt_succ k.isLt
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  constructor
  · nlinarith [kappa_pos]
  · have := two_T_eq
    nlinarith [kappa_pos]

/-- **Prime detection with the 16-step kernel** (paper Proposition 4.4), from [X, (3.57)]. Let
`L > 3 + 2T`, so `A = L − 2T > 3`. For every `ε > 0` there are `C₀ > 0` and `q₀` such that for
`q ≥ q₀` and a prime window `C ≥ C₀`: if the zero sum over the window plus `ε` is below `H(0)`,
then every class `a` coprime to `q` contains a prime `p` with `q^{L−2T} < p < q^L`. -/
theorem exists_prime (hcrit : XylourisCriterion357) {L : ℝ} (hL : 3 + 2 * (T : ℝ) < L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C →
      (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          rectZeroSum χ (primeKernel L).H C) + ε < ((primeKernel L).H 0).re →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ (L - 2 * (T : ℝ)) < p ∧ (p : ℝ) < (q : ℝ) ^ L :=
  exists_prime_of_criterion hcrit (primeKernel L) (primeKernel_admissible hL)
    (fun k => (primeKernel_support L k).1) (fun k => (primeKernel_support L k).2) hε

end GradedNear.Kernel
