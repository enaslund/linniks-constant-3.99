module

public import GradedNear.Entry

/-!
# Prime detection (paper §4; [X, (3.51)–(3.58), pp. 33–35])

Xylouris's criterion (3.57) bounds the weighted prime sum of a residue class from below by
`H(0)` minus the zero sum over a rectangle near `s = 1`, for a kernel that is a finite
combination of his triangles (3.51). It is a printed result and enters here as the hypothesis
`XylourisCriterion357`, stated as printed:
* the kernel `h = Σ_i α_i h_{L_i,K_i}` has real coefficients and `L_i > 2K_i + 3`;
* for every `ε > 0` there are `C₀ > 0` and `q₀`;
* for `q ≥ q₀` and every `a` coprime to `q`, with `𝓛 = log q`,
  `Σ_{p ≡ a (q)} (log p / p) h(log p / 𝓛) ≥ (𝓛 / φ(q)) (H(0) − Σ_{χ ≠ χ₀} Σ′_ρ |H((1 − ρ)𝓛)| − ε)`;
* `Σ′` runs over the zeros `ρ = β + iγ` of `L(s, χ)` in the rectangle
  `1 − C₀/𝓛 ≤ β ≤ 1`, `|γ| ≤ C₀/𝓛` (3.58), counted with multiplicity.

`exists_prime_of_criterion` extracts the prime: if the bracket is positive, some prime
`p ≡ a (mod q)` has `log p / log q` inside the support of `h`, so `q^A < p < q^L` for a kernel
supported in `[A, L]`.
-/

@[expose] public section

open Complex Finset

noncomputable section

namespace GradedNear

/-- Xylouris's triangle (3.51): `h_{L,K}(t)` is `0` for `t ≤ L − 2K`, rises with slope `1` to
`K` at `t = L − K`, falls with slope `−1` to `0` at `t = L`, and is `0` for `t ≥ L`. -/
def triangle (L K t : ℝ) : ℝ := max 0 (K - |t - (L - K)|)

/-- A kernel `h = Σ_i α_i h_{L_i, K_i}`: a finite real combination of triangles. -/
structure TriKernel where
  n : ℕ
  α : Fin n → ℝ
  L : Fin n → ℝ
  K : Fin n → ℝ

namespace TriKernel

variable (k : TriKernel)

/-- The kernel `h(t) = Σ_i α_i h_{L_i,K_i}(t)`. -/
def h (t : ℝ) : ℝ := ∑ i, k.α i * triangle (k.L i) (k.K i) t

/-- Its Laplace transform `H(z) = ∫₀^∞ h(t) e^{-zt} dt`. -/
def H (z : ℂ) : ℂ := laplace k.h z

/-- Xylouris's condition on the components: `K_i > 0` and `L_i > 2K_i + 3`. -/
def Admissible : Prop := ∀ i, 0 < k.K i ∧ 2 * k.K i + 3 < k.L i

end TriKernel

/-- The weighted prime sum `Σ_{p ≡ a (q)} (log p / p) h(log p / log q)` of [X, (3.51)]. The
kernel has compact support, so the sum is finite. -/
def primeSumAP (q a : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∑' p : Nat.Primes, if (p : ℕ) ≡ a [MOD q] then
    Real.log p / p * h (Real.log p / Real.log q) else 0

/-- The zero sum of one character over Xylouris's rectangle (3.58),
`1 − C/𝓛 ≤ β ≤ 1`, `|γ| ≤ C/𝓛`: `Σ′_ρ m_ρ |H((1 − ρ)𝓛)|`, with multiplicity. -/
def rectZeroSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (H : ℂ → ℂ) (C : ℝ) : ℝ :=
  ∑ᶠ ρ ∈ {ρ : ℂ | 1 - C / Real.log q ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ C / Real.log q ∧
      DirichletCharacter.LFunction χ ρ = 0},
    zmult χ ρ * ‖H ((1 - ρ) * (Real.log q : ℂ))‖

/-- **[X, (3.57)–(3.58), pp. 34–35]** (cf. [HB, Lemma 13.2]), as printed. For a kernel
`h = Σ α_i h_{L_i,K_i}` with `L_i > 2K_i + 3` and every `ε > 0` there are `C₀ > 0` and `q₀`
such that for `q ≥ q₀` and `(a, q) = 1`,
`Σ_{p ≡ a (q)} (log p / p) h(log p / 𝓛) ≥ (𝓛 / φ(q)) (H(0) − Σ_{χ ≠ χ₀} Σ′_ρ |H((1 − ρ)𝓛)| − ε)`,
where `Σ′` runs over the zeros of `L(s, χ)` in the rectangle (3.58) with `C = C₀`. -/
def XylourisCriterion357 : Prop :=
  ∀ k : TriKernel, k.Admissible → ∀ ε : ℝ, 0 < ε → ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ,
    ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ a : ℕ, Nat.Coprime a q →
      Real.log q / (Nat.totient q : ℝ) *
          ((k.H 0).re - (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            rectZeroSum χ k.H C₀) - ε) ≤
        primeSumAP q a k.h

/-- A triangle is nonzero only strictly inside its support `(L − 2K, L)`. -/
lemma triangle_pos_mem {L K t : ℝ} (h : triangle L K t ≠ 0) : L - 2 * K < t ∧ t < L := by
  unfold triangle at h
  by_contra hc
  apply h
  apply max_eq_left
  rcases not_and_or.1 hc with h1 | h1
  · rw [not_lt] at h1
    linarith [neg_le_abs (t - (L - K))]
  · rw [not_lt] at h1
    linarith [le_abs_self (t - (L - K))]

/-- The zeros of `L(s, χ)` in the rectangle (3.58) are finitely many (`χ ≠ 1`). -/
lemma rect_finite {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (C : ℝ) :
    {ρ : ℂ | 1 - C / Real.log q ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ C / Real.log q ∧
      DirichletCharacter.LFunction χ ρ = 0}.Finite := by
  refine (LFunction_zeros_finite hχ 1 (2 * |C / Real.log q| + 1)).subset ?_
  rintro ρ ⟨h1, h2, h3, h4⟩
  refine ⟨?_, h4⟩
  calc ‖1 - ρ‖ ≤ |(1 - ρ).re| + |(1 - ρ).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 2 * |C / Real.log q| + 1 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
        abs_neg]
      have ha : |1 - ρ.re| ≤ |C / Real.log q| := by
        rw [abs_le]; constructor <;> [skip; skip] <;>
          linarith [le_abs_self (C / Real.log q), neg_abs_le (C / Real.log q)]
      linarith [h3.trans (le_abs_self (C / Real.log q)), abs_nonneg (C / Real.log q)]

/-- The rectangle zero sum grows with the rectangle. -/
lemma rectZeroSum_mono {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (H : ℂ → ℂ) {C C' : ℝ} (hC : C ≤ C') (hℓ : 0 < Real.log q) :
    rectZeroSum χ H C ≤ rectZeroSum χ H C' := by
  unfold rectZeroSum
  have hsub : {ρ : ℂ | 1 - C / Real.log q ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ C / Real.log q ∧
      DirichletCharacter.LFunction χ ρ = 0} ⊆
      {ρ : ℂ | 1 - C' / Real.log q ≤ ρ.re ∧ ρ.re ≤ 1 ∧ |ρ.im| ≤ C' / Real.log q ∧
      DirichletCharacter.LFunction χ ρ = 0} := by
    have hd : C / Real.log q ≤ C' / Real.log q := div_le_div_of_nonneg_right hC hℓ.le
    rintro ρ ⟨h1, h2, h3, h4⟩
    exact ⟨by linarith, h2, h3.trans hd, h4⟩
  rw [finsum_mem_eq_finite_toFinset_sum _ (rect_finite hχ C),
    finsum_mem_eq_finite_toFinset_sum _ (rect_finite hχ C')]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ρ _ _ =>
    mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)
  intro ρ hρ
  rw [Set.Finite.mem_toFinset] at hρ ⊢
  exact hsub hρ

/-- **Prime extraction from [X, (3.57)].** Let the kernel be admissible with every component
supported in `[A, L]` (`L_i − 2K_i ≥ A`, `L_i ≤ L`). For every `ε > 0` there are `C₀ > 0` and `q₀`
such that for `q ≥ q₀`: if for some prime window `C ≥ C₀` the zero sum plus `ε` is below `H(0)`,
then every class `a` coprime to `q` contains a prime `p` with `q^A < p < q^L`. -/
theorem exists_prime_of_criterion (hcrit : XylourisCriterion357) (k : TriKernel)
    (hk : k.Admissible) {A Lmax : ℝ} (hA : ∀ i, A ≤ k.L i - 2 * k.K i) (hL : ∀ i, k.L i ≤ Lmax)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q → ∀ C : ℝ, C₀ ≤ C →
      (∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), rectZeroSum χ k.H C) + ε <
        (k.H 0).re →
      ∀ a : ℕ, Nat.Coprime a q → ∃ p : ℕ, p.Prime ∧ p ≡ a [MOD q] ∧
        (q : ℝ) ^ A < p ∧ (p : ℝ) < (q : ℝ) ^ Lmax := by
  obtain ⟨C₀, hC₀, q₀, hq₀⟩ := hcrit k hk ε hε
  refine ⟨C₀, hC₀, max q₀ 2, fun q _ hq C hC hsum a ha => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hℓ : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq2)
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.2 (by omega)
  have hmain := hq₀ q (le_trans (le_max_left _ _) hq) a ha
  have hmono : ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), rectZeroSum χ k.H C₀ ≤
      ∑ χ ∈ univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1), rectZeroSum χ k.H C :=
    Finset.sum_le_sum fun χ hχ => rectZeroSum_mono (Finset.mem_filter.1 hχ).2 k.H hC hℓ
  have hpos : 0 < primeSumAP q a k.h := by
    refine lt_of_lt_of_le ?_ hmain
    exact mul_pos (div_pos hℓ hφ) (by linarith)
  -- a positive sum has a nonzero term
  obtain ⟨p, hp⟩ : ∃ p : Nat.Primes, (if (p : ℕ) ≡ a [MOD q] then
      Real.log p / p * k.h (Real.log p / Real.log q) else 0) ≠ 0 := by
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    have : primeSumAP q a k.h = 0 := by
      unfold primeSumAP
      rw [show (fun p : Nat.Primes => if (p : ℕ) ≡ a [MOD q] then
          Real.log p / p * k.h (Real.log p / Real.log q) else 0) = fun _ => 0 from funext hall]
      exact tsum_zero
    linarith
  by_cases hmod : (p : ℕ) ≡ a [MOD q]
  swap
  · rw [ite_eq_right hmod] at hp; exact absurd rfl hp
  rw [ite_eq_left hmod] at hp
  have hh : k.h (Real.log p / Real.log q) ≠ 0 := fun h0 => hp (by rw [h0, mul_zero])
  obtain ⟨i, -, hi⟩ : ∃ i ∈ univ, k.α i * triangle (k.L i) (k.K i) (Real.log p / Real.log q) ≠ 0 := by
    by_contra hall
    simp only [Finset.mem_univ, true_and, ne_eq, not_exists, not_not] at hall
    exact hh (Finset.sum_eq_zero fun i _ => hall i)
  obtain ⟨hlo, hhi⟩ := triangle_pos_mem (right_ne_zero_of_mul hi)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.2.one_lt
  have hlogp : 0 < Real.log p := Real.log_pos hp1
  have hq0 : (0 : ℝ) < q := by positivity
  refine ⟨p, p.2, hmod, ?_, ?_⟩
  · -- q^A < p  ⟸  A log q < log p
    rw [← Real.exp_log (by positivity : (0 : ℝ) < p), Real.rpow_def_of_pos hq0]
    apply Real.exp_lt_exp.2
    have : A < Real.log p / Real.log q := lt_of_le_of_lt (hA i) hlo
    rw [lt_div_iff₀ hℓ] at this
    linarith
  · rw [← Real.exp_log (by positivity : (0 : ℝ) < p), Real.rpow_def_of_pos hq0]
    apply Real.exp_lt_exp.2
    have : Real.log p / Real.log q < Lmax := lt_of_lt_of_le hhi (hL i)
    rw [div_lt_iff₀ hℓ] at this
    linarith

end GradedNear
