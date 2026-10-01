module

public import GradedNear.ZeroForm
public import GradedNear.LaplaceDecay

/-!
# Entry bounds of the rows (paper §9.4)

The rows of §6.5 bound an entry's response through the zeros it keeps.

* **A kept zero at the entry's height.** This covers an ordinary character's representative
  `ρ_j`, the first family's `ρ₁`, the reserved second family's representative, the outside
  global zero and a hidden column. If `Im ρ = γ_j` and `λ_ρ ≤ hi`, the zero contributes at least
  `F(hi - s_j)`:
  * its multiplicity is at least one;
  * the argument `λ_ρ - s_j` of its term is real;
  * `F` is nonnegative and decreasing on the real line, since `f ≥ 0`.
* **A kept zero with `λ_ρ ≥ s_j`**, which lies at or left of the test point. It contributes at
  least its term `Re F(z) ≥ 0`, counted once. The `rc` pair's conjugate zero and the first
  family's second zero are of this kind.

`keptBound_single` and `keptBound_pair` are the resulting lower bounds for `keptBound`, the
numerator of an entry's feature in `graded_near_threshold`.
-/

@[expose] public section

open Complex

noncomputable section

namespace GradedNear

/-- At a real point the Laplace transform is the real integral
`Re F(x) = ∫₀^{x₀} f(t) e^{-xt} dt`. -/
lemma laplace_re_real {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (x : ℝ) :
    (laplace f (x : ℂ)).re = ∫ t in (0 : ℝ)..x₀, f t * Real.exp (-(x * t)) := by
  rw [Decay.laplace_eq_intervalIntegral hf]
  have : ∀ t : ℝ, (f t : ℂ) * Complex.exp (-((x : ℂ) * t)) =
      ((f t * Real.exp (-(x * t)) : ℝ) : ℂ) := by
    intro t
    rw [Complex.ofReal_mul, Complex.ofReal_exp]
    push_cast
    ring_nf
  simp_rw [this]
  rw [intervalIntegral.integral_ofReal, Complex.ofReal_re]

/-- `F ≥ 0` on the real line. -/
lemma laplace_re_real_nonneg {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) (x : ℝ) : 0 ≤ (laplace f (x : ℂ)).re := by
  rw [laplace_re_real hf]
  exact intervalIntegral.integral_nonneg hf.pos.le fun t ht =>
    mul_nonneg (hf2.nonneg t ht.1) (Real.exp_pos _).le

/-- `F` decreases on the real line. -/
lemma laplace_re_real_anti {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) {x y : ℝ} (hxy : x ≤ y) :
    (laplace f (y : ℂ)).re ≤ (laplace f (x : ℂ)).re := by
  rw [laplace_re_real hf, laplace_re_real hf]
  have hc : ∀ z : ℝ, ContinuousOn (fun t => f t * Real.exp (-(z * t))) (Set.uIcc 0 x₀) := by
    intro z
    rw [Set.uIcc_of_le hf.pos.le]
    exact (hf.cont.mono Set.Icc_subset_Ici_self).mul (by fun_prop)
  refine intervalIntegral.integral_mono_on hf.pos.le (hc y).intervalIntegrable
    (hc x).intervalIntegrable fun t ht => ?_
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hf2.nonneg t ht.1)
  have := mul_le_mul_of_nonneg_right hxy ht.1
  linarith

/-- A zero of a non-principal `L(s, χ)` has multiplicity at least one. -/
lemma one_le_zmult {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) : 1 ≤ zmult χ ρ := by
  have ha : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt z
  have h2 : DirichletCharacter.LFunction χ 2 ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) (by norm_num)
  have h2top : analyticOrderAt (DirichletCharacter.LFunction χ) 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.2 (Or.inr h2)]
    exact ENat.zero_ne_top
  have htop : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ :=
    ha.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ 2)
      (Set.mem_univ ρ) h2top
  have hne : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.2 ⟨ha ρ (Set.mem_univ _), hρ⟩
  have hnat : analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro h
    apply hne
    rw [← Nat.cast_analyticOrderNatAt htop, h]
    rfl
  unfold zmult
  exact_mod_cast Nat.one_le_iff_ne_zero.2 hnat

/-- **A kept zero at the entry's height.** If `Im ρ = γ` and `λ_ρ = (1 - Re ρ)𝓛 ≤ hi`, the
zero's term, with multiplicity, is at least `F(hi - σ)`. -/
lemma zeroTerm_at_height {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B) (hf2 : Condition2 f)
    {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ γ hi : ℝ} {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hγ : ρ.im = γ)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zmult χ ρ * zeroTerm f q σ γ ρ := by
  have hterm : zeroTerm f q σ γ ρ = (laplace f (((1 - ρ.re) * Real.log q - σ : ℝ) : ℂ)).re := by
    unfold zeroTerm
    rw [hγ, sub_self, zero_mul, Complex.ofReal_zero, zero_mul, add_zero]
  rw [hterm]
  have h1 : (laplace f ((hi - σ : ℝ) : ℂ)).re ≤
      (laplace f (((1 - ρ.re) * Real.log q - σ : ℝ) : ℂ)).re :=
    laplace_re_real_anti hf hf2 (by linarith)
  have h0 := laplace_re_real_nonneg hf hf2 ((1 - ρ.re) * Real.log q - σ)
  have hm := one_le_zmult hχ hρ
  nlinarith

/-- **A kept zero at or left of the test point** (`λ_ρ ≥ σ`): its term is nonnegative, and with
multiplicity it is at least the term counted once. -/
lemma zeroTerm_left {f : ℝ → ℝ} (hf2 : Condition2 f) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {σ γ : ℝ} {ρ : ℂ}
    (hρ : DirichletCharacter.LFunction χ ρ = 0) (hleft : σ ≤ (1 - ρ.re) * Real.log q) :
    0 ≤ zeroTerm f q σ γ ρ ∧ zeroTerm f q σ γ ρ ≤ zmult χ ρ * zeroTerm f q σ γ ρ := by
  have h0 : 0 ≤ zeroTerm f q σ γ ρ := by
    unfold zeroTerm
    refine hf2.re_nonneg _ ?_
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith
  refine ⟨h0, ?_⟩
  have hm := one_le_zmult hχ hρ
  nlinarith

variable {q : ℕ} {ι : Type*}

/-- **An entry keeping one zero at its height**, as for an ordinary character in the bin
`[lo, hi]`: `keptBound ≥ F(hi - s_j) - f(0)/6 - η`. -/
theorem keptBound_single [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  linarith [zeroTerm_at_height hD.f_cond hf2 hχ (σ := D.s - E.δ j) hρ hγ hhi]

/-- **An entry keeping a zero at its height and a second zero at or left of the test point**,
as for the `rc` pair and the first family's second zero:
`keptBound ≥ F(hi - s_j) + Re F(z') - f(0)/6 - η`, where `Re F(z') ≥ 0` is the second zero's
term. -/
theorem keptBound_pair [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hρ : DirichletCharacter.LFunction (E.χ j) ρ = 0)
    (hγ : ρ.im = E.γ j) (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hleft : D.s - E.δ j ≤ (1 - ρ'.re) * Real.log q) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ' - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  have h1 := zeroTerm_at_height hD.f_cond hf2 hχ (σ := D.s - E.δ j) hρ hγ hhi
  have h2 := (zeroTerm_left hf2 hχ (γ := E.γ j) hρ' hleft).2
  linarith

/-- The threshold form is monotone in the features: lowering them keeps (T). -/
lemma threshold_mono {ι : Type*} [Fintype ι] {v w D : ι → ℝ} {d τ : ℝ} (hD : ∀ j, 0 < D j)
    (hwv : ∀ j, w j ≤ v j) (h : ∑ j, (max 0 (v j - τ)) ^ 2 / D j ≤ 1 - τ ^ 2 / d) :
    ∑ j, (max 0 (w j - τ)) ^ 2 / D j ≤ 1 - τ ^ 2 / d := by
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) h
  refine div_le_div_of_nonneg_right ?_ (hD j).le
  exact pow_le_pow_left₀ (le_max_left _ _) (max_le_max le_rfl (by linarith [hwv j])) 2

/-- **A row whose entries each keep one zero at their own height** (paper §9.4: ordinary
characters, the first family, the reserved second family, the outside global zero and hidden
columns). Entry `j` sits at the height of a zero `ρ_j` of `L(s, χ_j)` in its disc with
`λ_{ρ_j} ≤ hi_j`. Every other disc zero with `λ_ρ < s_j` must be at normalized height distance
`≥ M`, and there are at most `K₀` of them. Then the entries satisfy the threshold form (T) with
the features `(F(hi_j - s_j) - f(0)/6 - η) / N`, which is the form the leaf builders compute. -/
theorem single_zero_threshold (hX31 : XylourisLemma31) (hX32 : XylourisLemma32)
    (hBur : BurgessPrimitive) (hGr : GrahamEstimate) (D : NearData) (hD : D.Valid)
    (hf2 : Condition2 D.f) (K₀ : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 → SafeAnchor q D.s₁ (2 * T + 1) →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι),
        (∀ j, E.χ j ≠ 1) → (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
        ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
        ∀ (ρ : ι → ℂ) (hi : ι → ℝ),
          (∀ j, DirichletCharacter.LFunction (E.χ j) (ρ j) = 0 ∧ (ρ j).im = E.γ j ∧
            ‖(1 + (E.γ j : ℂ) * I) - ρ j‖ ≤ δ ∧ (1 - (ρ j).re) * Real.log q ≤ hi j) →
          (∀ j, ∀ ρ' : ℂ, DirichletCharacter.LFunction (E.χ j) ρ' = 0 →
            ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ → ρ' ≠ ρ j →
            (1 - ρ'.re) * Real.log q < D.s - E.δ j → M ≤ |E.γ j - ρ'.im| * Real.log q) →
          (∀ j, (∑ᶠ ρ' ∈ {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
              ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ ∧ ρ' ≠ ρ j ∧
              (1 - ρ'.re) * Real.log q < D.s - E.δ j}, zmult (E.χ j) ρ') ≤ K₀) →
          ∀ Dn : ℝ, 0 < Dn → (∀ j, 0 < D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) →
            ∃ τ : ℝ, 0 ≤ τ ∧ τ ≤ Real.sqrt ((D.d₁ + η) / Dn) ∧
              ∑ j, (max 0 (((laplace D.f ((hi j - (D.s - E.δ j) : ℝ) : ℂ)).re - D.f 0 / 6 - η) /
                  Real.sqrt ((1 + η) * D.IB * Dn) - τ)) ^ 2 /
                  ((D.Dδ (E.δ j) - D.d₁ + pairExcess D E j) / Dn) ≤
                1 - τ ^ 2 / ((D.d₁ + η) / Dn) := by
  obtain ⟨M, hM, δ, hδ0, hδ1, q₀, h⟩ := graded_near_threshold hX31 hX32 hBur hGr D hD hf2 K₀ hη
  refine ⟨M, hM, δ, hδ0, hδ1, q₀, ?_⟩
  intro q _ hq T hT0 hTl hsafe ι _ E hχ hγ hΔ hinj ρ hi hρ hsep hK Dn hDn hDj
  have hset : ∀ j, {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
      ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ ∧ ρ' ∉ ({ρ j} : Finset ℂ) ∧
      (1 - ρ'.re) * Real.log q < D.s - E.δ j} =
      {ρ' : ℂ | DirichletCharacter.LFunction (E.χ j) ρ' = 0 ∧
      ‖(1 + (E.γ j : ℂ) * I) - ρ'‖ ≤ δ ∧ ρ' ≠ ρ j ∧
      (1 - ρ'.re) * Real.log q < D.s - E.δ j} := by
    intro j
    ext ρ'
    simp only [Set.mem_ofPred_eq, Finset.mem_singleton]
  obtain ⟨τ, hτ0, hτd, hT⟩ := h q hq T hT0 hTl hsafe ι E hχ hγ hΔ hinj (fun j => {ρ j})
    (fun j ρ' hρ' => by
      rw [Finset.mem_singleton] at hρ'
      subst hρ'
      exact ⟨(hρ j).1, (hρ j).2.2.1⟩)
    (fun j ρ' h1 h2 h3 h4 => hsep j ρ' h1 h2 (by simpa using h3) h4)
    (fun j => by rw [hset j]; exact hK j) Dn hDn hDj
  refine ⟨τ, hτ0, hτd, threshold_mono (fun j => div_pos (hDj j) hDn) (fun j => ?_) hT⟩
  have hIB := hD.IB_pos
  have hN : 0 < Real.sqrt ((1 + η) * D.IB * Dn) := Real.sqrt_pos.2 (by positivity)
  exact div_le_div_of_nonneg_right
    (keptBound_single D hD hf2 E (fun j => {ρ j}) η j (hχ j) rfl (hρ j).1 (hρ j).2.1 (hρ j).2.2.2)
    hN.le

/-- A zero at the entry's height has the real term `F(λ_ρ - σ)`, which is at least `F(hi - σ)`
for `λ_ρ ≤ hi`, and nonnegative. -/
lemma zeroTerm_at_height_le {f : ℝ → ℝ} {x₀ B : ℝ} (hf : Condition1 f x₀ B)
    (hf2 : Condition2 f) {q : ℕ} {σ γ hi : ℝ} {ρ : ℂ} (hγ : ρ.im = γ)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace f ((hi - σ : ℝ) : ℂ)).re ≤ zeroTerm f q σ γ ρ ∧ 0 ≤ zeroTerm f q σ γ ρ := by
  have hterm : zeroTerm f q σ γ ρ = (laplace f (((1 - ρ.re) * Real.log q - σ : ℝ) : ℂ)).re := by
    unfold zeroTerm
    rw [hγ, sub_self, zero_mul, Complex.ofReal_zero, zero_mul, add_zero]
  rw [hterm]
  exact ⟨laplace_re_real_anti hf hf2 (by linarith), laplace_re_real_nonneg hf hf2 _⟩

/-- The conjugate entry `(χ̄, -γ)` keeping the conjugate zero `ρ̄` has the same term as
`(χ, γ)` keeping `ρ`, since `Re F(z̄) = Re F(z)` for real `f`. -/
lemma zeroTerm_conj (f : ℝ → ℝ) (q : ℕ) (σ γ : ℝ) (ρ : ℂ) :
    zeroTerm f q σ (-γ) ((starRingEnd ℂ) ρ) = zeroTerm f q σ γ ρ := by
  unfold zeroTerm
  rw [← laplace_re_conj f]
  congr 2
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, map_add,
      map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.neg_re, Complex.neg_im] <;> ring

/-- **A kept multiple zero at the entry's height**, as for the first family's double zero
(`ρ' = ρ₁`, `y = 0`): with multiplicity at least `2`, the kept terms are at least `F(hi - s_j)`
plus the zero's own term. -/
theorem keptBound_double [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (η : ℝ) (j : ι) {ρ : ℂ} {hi : ℝ}
    (hS : Sz j = {ρ}) (hm : 2 ≤ zmult (E.χ j) ρ) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi) :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re +
        zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ - D.f 0 / 6 - η ≤ keptBound D E Sz η j := by
  unfold keptBound
  rw [hS, Finset.sum_singleton]
  obtain ⟨h1, h0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  nlinarith

/-- **An entry keeping a zero at its height and a second zero whose term may be negative**, as
for the shifted row's `rc` entry, whose conjugate zero `ρ̄₁` lies left of the anchor. Suppose the
second zero's term is at least `-C` and its multiplicity is at most the first's (for a real
character, conjugate zeros have equal multiplicity). Then the kept terms minus `f(0)/6` are at
least `F(hi - s_j) - C - f(0)/6`, unless that number is `≤ 0`, in which case the entry's feature
is `≤ 0` and it contributes nothing to (T). -/
theorem keptBound_pair_neg [NeZero q] (D : NearData) (hD : D.Valid) (hf2 : Condition2 D.f)
    (E : Entries q ι) (Sz : ι → Finset ℂ) (j : ι) (hχ : E.χ j ≠ 1) {ρ ρ' : ℂ} {hi C : ℝ}
    (hne : ρ ≠ ρ') (hS : Sz j = {ρ, ρ'}) (hγ : ρ.im = E.γ j)
    (hhi : (1 - ρ.re) * Real.log q ≤ hi)
    (hρ' : DirichletCharacter.LFunction (E.χ j) ρ' = 0)
    (hm : zmult (E.χ j) ρ' ≤ zmult (E.χ j) ρ)
    (hC : -C ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ') :
    (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ keptBound D E Sz 0 j ∨
      (laplace D.f ((hi - (D.s - E.δ j) : ℝ) : ℂ)).re - C - D.f 0 / 6 ≤ 0 := by
  unfold keptBound
  rw [hS, Finset.sum_pair hne]
  obtain ⟨hA, hA0⟩ := zeroTerm_at_height_le hD.f_cond hf2 (σ := D.s - E.δ j) hγ hhi
  have hm2 := one_le_zmult hχ hρ'
  have hf0 := hf2.nonneg 0 le_rfl
  by_cases hAB : 0 ≤ zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ +
      zeroTerm D.f q (D.s - E.δ j) (E.γ j) ρ'
  · left
    nlinarith [mul_le_mul_of_nonneg_right hm hA0, mul_le_mul_of_nonneg_left hm2 hAB]
  · right
    linarith

end GradedNear
