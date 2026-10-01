module

public import GradedNear.Functions

/-!
# Facts about the 16-step kernel: closed forms, monotonicity and `H(0)`

This file proves the analytic facts about the step kernel of `GradedNear.Functions` that the
repository's Python evaluates by closed forms (`computations/core/code/enclosures.py` in the research repository, class
`RigorousWeights`, and `triple_inputs.py`, `cross_envelope`; specification in
§1 of `research/notes/leaf-data-semantics-2026-09-29.md` in the research repository).

* **Step kernel.** `psi_cell` (`ψ = β_i` on `[iκ, (i+1)κ)`), `psi_eq_zero_of_neg`,
  `psi_eq_zero_of_ge`, `psi_nonneg`, `psi_le_one`, `H0_pos`.
* **Fubini step.** `laplace_fLam_re`: `Re F_λ(−λ) = 2 ∫₀^T ψ(u) e^{−2λu} (∫_u^T ψ) du` for all real
  `λ` (with `f_λ(t) = 0` for `t ≥ T`, `fLam_eq_zero`).
* **Closed form of the envelope** (`H0_mul_Benv`): for `λ ≠ 0` and every real `φ`,
  `H₀ B_φ(λ) = Σ_i E^i (β_i² (Q₀ + (φ/2) U) + κ U β_i Σ_{j>i} β_j)`, with `E = e^{−2κλ}`
  (`envE`), `U = (1 − E)/λ` (`envU`) and `Q₀ = κ/λ − U/(2λ)` (`envQ0`).
* **Monotonicity.** For `φ ≥ 0`, `B_φ` is nonnegative and antitone on all of `ℝ`
  (`Benv_nonneg`, `Benv_antitone`) and positive for `λ > 0` (`Benv_pos`); so for `L − 2T ≥ 0`,
  `G_φ` and `G` are antitone (`Gphi_antitone`, `G_antitone`), and they are positive for `λ > 0`.
* **`Ψ` and `h`.** `Psi_im`, `Psi_re`: `Re Ψ(λ) = Σ_i β_i e^{−iκλ} (1 − e^{−κλ})/λ` for real
  `λ ≠ 0`; `hRatio_eq`.
* **`H(0)` of the prime kernel** (`primeKernel_H_zero`): `Re H(0) = H₀` when `L − 2T ≥ 0`.
* **The cross term** (`Cpa_closed`): `C(p, a)` as exact step-cell sums, for `a ≠ 0`.

The method throughout is to split `[0, T]` into the sixteen cells (`integral_cells`), on each of
which `ψ` is constant, and to integrate exponentials times affine functions exactly
(`integral_exp_mul_affine`).
-/

@[expose] public section

noncomputable section

namespace GradedNear.Kernel

open MeasureTheory Set

/-! ## The step kernel -/

lemma T_eq : (T : ℝ) = 16 * kappa := by norm_num [T, kappa]

lemma T_pos : (0 : ℝ) < T := by norm_num [T]

lemma beta_pos (i : Fin 16) : (0 : ℝ) < beta i := by
  fin_cases i <;> norm_num [beta]

lemma beta_le_one (i : Fin 16) : (beta i : ℝ) ≤ 1 := by
  fin_cases i <;> norm_num [beta]

/-- `ψ = β_i` on the `i`-th step `[iκ, (i+1)κ)`. -/
lemma psi_cell (i : Fin 16) {t : ℝ} (h1 : (i.val : ℝ) * kappa ≤ t)
    (h2 : t < ((i.val : ℝ) + 1) * kappa) : psi t = beta i := by
  unfold psi
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left ⟨h1, h2⟩]
  · intro j _ hji
    rw [ite_eq_right]
    rintro ⟨hj1, hj2⟩
    apply hji
    have hk := kappa_pos
    have a1 : (j.val : ℝ) < (i.val : ℝ) + 1 := lt_of_mul_lt_mul_right (hj1.trans_lt h2) hk.le
    have a2 : (i.val : ℝ) < (j.val : ℝ) + 1 := lt_of_mul_lt_mul_right (h1.trans_lt hj2) hk.le
    have b1 : j.val < i.val + 1 := by exact_mod_cast a1
    have b2 : i.val < j.val + 1 := by exact_mod_cast a2
    exact Fin.ext (by omega)
  · intro h; exact absurd (Finset.mem_univ i) h

lemma psi_eq_zero {t : ℝ} (ht : t < 0 ∨ (T : ℝ) ≤ t) : psi t = 0 := by
  unfold psi
  apply Finset.sum_eq_zero
  intro i _
  rw [ite_eq_right]
  rintro ⟨h1, h2⟩
  have hk := kappa_pos
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  have hi : (i.val : ℝ) ≤ 15 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  rcases ht with ht | ht
  · nlinarith
  · rw [T_eq] at ht; nlinarith

lemma psi_eq_zero_of_neg {t : ℝ} (ht : t < 0) : psi t = 0 := psi_eq_zero (Or.inl ht)

lemma psi_eq_zero_of_ge {t : ℝ} (ht : (T : ℝ) ≤ t) : psi t = 0 := psi_eq_zero (Or.inr ht)

lemma measurable_psi : Measurable psi := by
  unfold psi
  refine Finset.measurable_sum _ fun i _ => ?_
  exact Measurable.ite measurableSet_Ico measurable_const measurable_const

lemma psi_nonneg (t : ℝ) : 0 ≤ psi t := by
  unfold psi
  refine Finset.sum_nonneg fun i _ => ?_
  split_ifs
  · exact (beta_pos i).le
  · exact le_rfl

lemma psi_eq_or (t : ℝ) : psi t = 0 ∨ ∃ i : Fin 16, psi t = beta i := by
  by_cases h : t < 0 ∨ (T : ℝ) ≤ t
  · exact Or.inl (psi_eq_zero h)
  · push Not at h
    obtain ⟨h0, hT⟩ := h
    right
    have hk := kappa_pos
    have hn1 : (⌊t / kappa⌋₊ : ℝ) ≤ t / kappa := Nat.floor_le (div_nonneg h0 hk.le)
    have hn2 : t / kappa < ⌊t / kappa⌋₊ + 1 := Nat.lt_floor_add_one _
    have hn16 : ⌊t / (kappa : ℝ)⌋₊ < 16 := by
      have h16 : t / kappa < 16 := by rw [div_lt_iff₀ hk]; rw [T_eq] at hT; linarith
      have : (⌊t / (kappa : ℝ)⌋₊ : ℝ) < 16 := lt_of_le_of_lt hn1 h16
      exact_mod_cast this
    refine ⟨⟨_, hn16⟩, psi_cell ⟨_, hn16⟩ ?_ ?_⟩
    · show (⌊t / (kappa : ℝ)⌋₊ : ℝ) * kappa ≤ t
      rwa [le_div_iff₀ hk] at hn1
    · show t < ((⌊t / (kappa : ℝ)⌋₊ : ℝ) + 1) * kappa
      rwa [div_lt_iff₀ hk] at hn2

lemma psi_le_one (t : ℝ) : psi t ≤ 1 := by
  rcases psi_eq_or t with h | ⟨i, h⟩ <;> rw [h]
  · norm_num
  · exact beta_le_one i

lemma abs_psi_le (t : ℝ) : |psi t| ≤ 1 := by
  rw [abs_of_nonneg (psi_nonneg t)]; exact psi_le_one t

lemma intervalIntegrable_of_abs_le {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  rw [intervalIntegrable_iff]
  exact IntegrableOn.of_bound measure_Ioc_lt_top hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable psi volume a b :=
  intervalIntegrable_of_abs_le measurable_psi abs_psi_le a b

lemma sum_beta_pos : (0 : ℝ) < ∑ i, (beta i : ℝ) :=
  Finset.sum_pos (fun i _ => beta_pos i) Finset.univ_nonempty

/-- `H₀ = (κ Σ β_i)² > 0`. -/
lemma H0_pos : 0 < H0 := by
  unfold H0
  exact pow_pos (mul_pos kappa_pos sum_beta_pos) 2

/-! ## Integrals over the steps -/

/-- Integrating over whole cells: if `f` agrees on each cell `[jκ, (j+1)κ)` with a continuous
`F j`, then `∫_{mκ}^{nκ} f` is the sum over `m ≤ j < n` of the cell integrals of `F j`. -/
lemma integral_cells {f : ℝ → ℝ} (F : Fin 16 → ℝ → ℝ) (hF : ∀ j, Continuous (F j))
    (hf : ∀ (j : Fin 16) (v : ℝ), (j.val : ℝ) * kappa ≤ v → v < ((j.val : ℝ) + 1) * kappa →
      f v = F j v)
    {m n : ℕ} (hmn : m ≤ n) (hn : n ≤ 16) :
    ∫ v in (m : ℝ) * kappa..(n : ℝ) * kappa, f v =
      ∑ j : Fin 16, if m ≤ j.val ∧ j.val < n then
        ∫ v in (j.val : ℝ) * kappa..((j.val : ℝ) + 1) * kappa, F j v else 0 := by
  have hk := kappa_pos
  have hle : ∀ j : ℕ, (j : ℝ) * kappa ≤ ((j : ℝ) + 1) * kappa := fun j => by nlinarith
  have hcell : ∀ j : Fin 16, ∫ v in (j.val : ℝ) * kappa..((j.val : ℝ) + 1) * kappa, f v =
      ∫ v in (j.val : ℝ) * kappa..((j.val : ℝ) + 1) * kappa, F j v := by
    intro j
    exact intervalIntegral.integral_congr_Ioo_of_le (hle j) fun v hv => hf j v hv.1.le hv.2
  have hint : ∀ j : Fin 16,
      IntervalIntegrable f volume ((j.val : ℝ) * kappa) (((j.val : ℝ) + 1) * kappa) := by
    intro j
    refine ((hF j).intervalIntegrable _ _).congr_uIoo ?_
    rw [uIoo_of_le (hle j)]
    intro v hv
    exact (hf j v hv.1.le hv.2).symm
  have key := intervalIntegral.sum_integral_adjacent_intervals_Ico (f := f) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * kappa) hmn (fun k hk' => by
      have hk16 : k < 16 := by
        simp only [Set.mem_Ico] at hk'; omega
      have := hint ⟨k, hk16⟩
      simpa [Nat.cast_succ] using this)
  rw [← key]
  simp_rw [← hcell]
  rw [Fin.sum_univ_eq_sum_range (fun k => if m ≤ k ∧ k < n then
    ∫ v in (k : ℝ) * kappa..((k : ℝ) + 1) * kappa, f v else 0) 16, ← Finset.sum_filter]
  apply Finset.sum_congr
  · ext k; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega
  · intro k _; push_cast; rfl

/-- `∫_a^b e^{−cu}(p + qu) du` for `c ≠ 0`. -/
lemma integral_exp_mul_affine {c : ℝ} (hc : c ≠ 0) (p q a b : ℝ) :
    ∫ u in a..b, Real.exp (-(c * u)) * (p + q * u) =
      Real.exp (-(c * a)) * ((p + q * a) / c + q / c ^ 2) -
        Real.exp (-(c * b)) * ((p + q * b) / c + q / c ^ 2) := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt
      (fun u => -(Real.exp (-(c * u)) * ((p + q * u) / c + q / c ^ 2)))
      (Real.exp (-(c * x)) * (p + q * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun u => Real.exp (-(c * u))) (Real.exp (-(c * x)) * (-(c * 1))) x :=
      ((hasDerivAt_id x).const_mul c).neg.exp
    have h2 : HasDerivAt (fun u => (p + q * u) / c + q / c ^ 2) ((q * 1) / c) x :=
      ((((hasDerivAt_id x).const_mul q).const_add p).div_const c).add_const (q / c ^ 2)
    convert (h1.mul h2).neg using 1
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- `∫_a^b e^{−cu} du` for `c ≠ 0`. -/
lemma integral_exp_neg_mul {c : ℝ} (hc : c ≠ 0) (a b : ℝ) :
    ∫ u in a..b, Real.exp (-(c * u)) = (Real.exp (-(c * a)) - Real.exp (-(c * b))) / c := by
  have := integral_exp_mul_affine hc 1 0 a b
  simp only [zero_mul, add_zero, mul_one, zero_div] at this
  rw [this]
  field_simp

lemma T_eq_cast : (T : ℝ) = ((16 : ℕ) : ℝ) * kappa := by rw [T_eq]; norm_num

lemma Ioi_eq_filter (i : Fin 16) : Finset.Ioi i = Finset.univ.filter (fun j => i < j) := by
  ext j; simp

/-- For `u` in the cell `[iκ, (i+1)κ]` and continuous `g`:
`∫_u^T ψ g = β_i ∫_u^{(i+1)κ} g + Σ_{j>i} β_j ∫_{jκ}^{(j+1)κ} g`. -/
lemma integral_psi_mul_tail (g : ℝ → ℝ) (hg : Continuous g) (i : Fin 16) {u : ℝ}
    (h1 : (i.val : ℝ) * kappa ≤ u) (h2 : u ≤ ((i.val : ℝ) + 1) * kappa) :
    ∫ v in u..T, psi v * g v = beta i * (∫ v in u..((i.val : ℝ) + 1) * kappa, g v) +
      ∑ j ∈ Finset.Ioi i, beta j * ∫ v in (j.val : ℝ) * kappa..((j.val : ℝ) + 1) * kappa, g v := by
  have hint : ∀ a b, IntervalIntegrable (fun v => psi v * g v) volume a b := fun a b =>
    (psi_intervalIntegrable a b).mul_continuousOn hg.continuousOn
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint u (((i.val : ℝ) + 1) * kappa))
    (hint _ T)]
  congr 1
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_Ioo_of_le (μ := volume) h2 fun v hv => ?_
    rw [psi_cell i (by linarith [hv.1]) hv.2]
  · have hcells := integral_cells (f := fun v => psi v * g v) (fun j v => beta j * g v)
      (fun j => continuous_const.mul hg) (fun j v h1 h2 => by rw [psi_cell j h1 h2])
      (m := i.val + 1) (n := 16) (by omega) le_rfl
    rw [T_eq_cast, show ((i.val : ℝ) + 1) * kappa = (((i.val + 1 : ℕ)) : ℝ) * kappa by
      push_cast; ring, hcells, Ioi_eq_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact propext (by rw [Fin.lt_def]; have := j.isLt; omega)

/-- `Φ(u) = ∫_u^T ψ = β_i((i+1)κ − u) + κ Σ_{j>i} β_j` on the cell `[iκ, (i+1)κ]`. -/
lemma integral_psi_tail (i : Fin 16) {u : ℝ} (h1 : (i.val : ℝ) * kappa ≤ u)
    (h2 : u ≤ ((i.val : ℝ) + 1) * kappa) :
    ∫ v in u..T, psi v = beta i * (((i.val : ℝ) + 1) * kappa - u) +
      kappa * ∑ j ∈ Finset.Ioi i, (beta j : ℝ) := by
  have := integral_psi_mul_tail (fun _ => 1) continuous_const i h1 h2
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at this
  rw [this]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

lemma continuous_tail : Continuous fun u : ℝ => ∫ v in u..T, psi v := by
  have := (intervalIntegral.continuous_primitive (μ := volume) psi_intervalIntegrable (T : ℝ)).neg
  refine this.congr fun u => ?_
  show -(∫ x in (T : ℝ)..u, psi x) = ∫ v in u..T, psi v
  rw [intervalIntegral.integral_symm, neg_neg]

lemma tail_nonneg {u : ℝ} (hu : u ≤ T) : 0 ≤ ∫ v in u..T, psi v :=
  intervalIntegral.integral_nonneg hu fun v _ => psi_nonneg v

/-! ## The envelope as an integral -/

/-- `f_λ(t) = 0` for `t ≥ T`. -/
lemma fLam_eq_zero (lam : ℝ) {t : ℝ} (ht : (T : ℝ) ≤ t) : fLam lam t = 0 := by
  unfold fLam
  have : ∫ u in (0 : ℝ)..((T : ℝ) - t),
      psi u * psi (u + t) * Real.exp (-(lam * (2 * u + t))) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro u hu
      rw [uIcc_of_ge (by linarith)] at hu
      simp only
      rw [psi_eq_zero (Or.inr (by linarith [hu.1] : (T : ℝ) ≤ u + t))]
      ring
  rw [this, mul_zero]

lemma integrand_bound (lam t u : ℝ) :
    |psi u * psi (u + t) * Real.exp (-(2 * lam * u))| ≤ Real.exp (2 * |lam| * T) := by
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  by_cases h : u < 0 ∨ (T : ℝ) ≤ u
  · rw [psi_eq_zero h]; simp only [abs_zero, zero_mul]; positivity
  · push Not at h
    have h3 : Real.exp (-(2 * lam * u)) ≤ Real.exp (2 * |lam| * T) := by
      apply Real.exp_le_exp.2
      nlinarith [mul_nonneg (by linarith [neg_abs_le lam] : 0 ≤ |lam| + lam) h.1,
        mul_nonneg (abs_nonneg lam) (by linarith : (0 : ℝ) ≤ T - u)]
    calc |psi u| * |psi (u + t)| * Real.exp (-(2 * lam * u))
        ≤ 1 * 1 * Real.exp (2 * |lam| * T) :=
          mul_le_mul (mul_le_mul (abs_psi_le u) (abs_psi_le _) (abs_nonneg _) zero_le_one) h3
            (Real.exp_pos _).le (by norm_num)
      _ = Real.exp (2 * |lam| * T) := by ring

lemma integrand_intervalIntegrable (lam t a b : ℝ) :
    IntervalIntegrable (fun u => psi u * psi (u + t) * Real.exp (-(2 * lam * u))) volume a b := by
  have hm : Measurable fun u => psi u * psi (u + t) :=
    measurable_psi.mul (measurable_psi.comp (measurable_id.add_const t))
  have hb : ∀ u, |psi u * psi (u + t)| ≤ 1 := fun u => by
    rw [abs_mul]
    exact (mul_le_mul (abs_psi_le u) (abs_psi_le _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  exact (intervalIntegrable_of_abs_le hm hb a b).mul_continuousOn
    (by fun_prop : Continuous fun u => Real.exp (-(2 * lam * u))).continuousOn

lemma fLam_mul_exp (lam : ℝ) {t : ℝ} (ht0 : 0 ≤ t) :
    fLam lam t * Real.exp (lam * t) =
      2 * ∫ u in (0 : ℝ)..T, psi u * psi (u + t) * Real.exp (-(2 * lam * u)) := by
  unfold fLam
  rw [mul_assoc, ← intervalIntegral.integral_mul_const]
  congr 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (integrand_intervalIntegrable lam t 0 (T - t)) (integrand_intervalIntegrable lam t (T - t) T)]
  have hzero : ∫ u in ((T : ℝ) - t)..T, psi u * psi (u + t) * Real.exp (-(2 * lam * u)) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro u hu
      rw [uIcc_of_le (by linarith)] at hu
      simp only
      rw [psi_eq_zero (Or.inr (by linarith [hu.1] : (T : ℝ) ≤ u + t))]
      ring
  rw [hzero, add_zero]
  refine intervalIntegral.integral_congr fun u _ => ?_
  have : Real.exp (-(lam * (2 * u + t))) * Real.exp (lam * t) = Real.exp (-(2 * lam * u)) := by
    rw [← Real.exp_add]; congr 1; ring
  simp only [mul_assoc, this]

lemma psi_shift {u : ℝ} (hu : 0 ≤ u) : ∫ t in (0 : ℝ)..T, psi (u + t) = ∫ v in u..T, psi v := by
  rw [intervalIntegral.integral_comp_add_left, add_zero,
    ← intervalIntegral.integral_add_adjacent_intervals (psi_intervalIntegrable u T)
      (psi_intervalIntegrable T (u + T))]
  have : ∫ v in (T : ℝ)..(u + T), psi v = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro v hv
      rw [uIcc_of_le (by linarith)] at hv
      exact psi_eq_zero (Or.inr hv.1)
  rw [this, add_zero]

/-- **Fubini step.** `Re F_λ(−λ) = 2 ∫₀^T ψ(u) e^{−2λu} (∫_u^T ψ) du` for every real `λ`. -/
theorem laplace_fLam_re (lam : ℝ) :
    (laplace (fLam lam) ((-lam : ℝ) : ℂ)).re =
      2 * ∫ u in (0 : ℝ)..T, psi u * Real.exp (-(2 * lam * u)) * ∫ v in u..T, psi v := by
  have hT := T_pos
  have h1 : (laplace (fLam lam) ((-lam : ℝ) : ℂ)).re =
      ∫ t in Ioi (0 : ℝ), fLam lam t * Real.exp (lam * t) := by
    unfold laplace
    have : ∀ t : ℝ, ((fLam lam t : ℝ) : ℂ) * Complex.exp (-(((-lam : ℝ) : ℂ) * (t : ℂ))) =
        ((fLam lam t * Real.exp (lam * t) : ℝ) : ℂ) := by
      intro t; push_cast; ring_nf
    simp_rw [this]
    rw [integral_complex_ofReal, Complex.ofReal_re]
  have h2 : ∫ t in Ioi (0 : ℝ), fLam lam t * Real.exp (lam * t) =
      ∫ t in Ioc (0 : ℝ) T, fLam lam t * Real.exp (lam * t) := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro t ht
    have : (T : ℝ) < t := by
      simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht; exact ht.2 ht.1
    rw [fLam_eq_zero lam this.le, zero_mul]
  have h3 : ∫ t in Ioc (0 : ℝ) T, fLam lam t * Real.exp (lam * t) =
      ∫ t in Ioc (0 : ℝ) T, 2 * ∫ u in Ioc (0 : ℝ) T,
        psi u * psi (u + t) * Real.exp (-(2 * lam * u)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    rw [fLam_mul_exp lam ht.1.le, intervalIntegral.integral_of_le hT.le]
  have h4 : ∫ t in Ioc (0 : ℝ) T, ∫ u in Ioc (0 : ℝ) T,
        psi u * psi (u + t) * Real.exp (-(2 * lam * u)) =
      ∫ u in Ioc (0 : ℝ) T, ∫ t in Ioc (0 : ℝ) T,
        psi u * psi (u + t) * Real.exp (-(2 * lam * u)) := by
    apply integral_integral_swap
    refine Integrable.of_bound ?_ (Real.exp (2 * |lam| * T))
      (Filter.Eventually.of_forall fun p => ?_)
    · apply Measurable.aestronglyMeasurable
      show Measurable fun p : ℝ × ℝ => psi p.2 * psi (p.2 + p.1) * Real.exp (-(2 * lam * p.2))
      exact ((measurable_psi.comp measurable_snd).mul
        (measurable_psi.comp (measurable_snd.add measurable_fst))).mul
        (by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(2 * lam * p.2))).measurable
    · show ‖psi p.2 * psi (p.2 + p.1) * Real.exp (-(2 * lam * p.2))‖ ≤ _
      rw [Real.norm_eq_abs]; exact integrand_bound lam p.1 p.2
  have h5 : ∀ u ∈ Ioc (0 : ℝ) T, ∫ t in Ioc (0 : ℝ) T,
        psi u * psi (u + t) * Real.exp (-(2 * lam * u)) =
      psi u * Real.exp (-(2 * lam * u)) * ∫ v in u..T, psi v := by
    intro u hu
    have : ∀ t, psi u * psi (u + t) * Real.exp (-(2 * lam * u)) =
        (psi u * Real.exp (-(2 * lam * u))) * psi (u + t) := fun t => by ring
    simp_rw [this]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le hT.le, psi_shift hu.1.le]
  rw [h1, h2, h3, integral_const_mul, h4, setIntegral_congr_fun measurableSet_Ioc h5,
    ← intervalIntegral.integral_of_le hT.le]

/-! ## Closed form of the envelope -/

/-- `E(λ) = e^{−2κλ}`. -/
def envE (lam : ℝ) : ℝ := Real.exp (-(2 * kappa * lam))

/-- `U(λ) = (1 − E(λ))/λ`. -/
def envU (lam : ℝ) : ℝ := (1 - envE lam) / lam

/-- `Q₀(λ) = κ/λ − U(λ)/(2λ)`. -/
def envQ0 (lam : ℝ) : ℝ := kappa / lam - envU lam / (2 * lam)

lemma exp_cell (lam : ℝ) (n : ℕ) :
    Real.exp (-(2 * lam * ((n : ℝ) * kappa))) = envE lam ^ n := by
  rw [envE, ← Real.exp_nat_mul]; congr 1; ring

lemma exp_cell_succ (lam : ℝ) (n : ℕ) :
    Real.exp (-(2 * lam * (((n : ℝ) + 1) * kappa))) = envE lam ^ n * envE lam := by
  rw [envE, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring

/-- `Re F_λ(−λ) = Σ_i E^i (β_i² Q₀ + κ U β_i Σ_{j>i} β_j)` for `λ ≠ 0`. -/
theorem laplace_fLam_re_closed {lam : ℝ} (hlam : lam ≠ 0) :
    (laplace (fLam lam) ((-lam : ℝ) : ℂ)).re =
      ∑ i : Fin 16, envE lam ^ (i : ℕ) * ((beta i : ℝ) ^ 2 * envQ0 lam +
        kappa * envU lam * beta i * ∑ j ∈ Finset.Ioi i, (beta j : ℝ)) := by
  rw [laplace_fLam_re]
  have hcells := integral_cells
    (f := fun u => psi u * Real.exp (-(2 * lam * u)) * ∫ v in u..T, psi v)
    (fun j u => Real.exp (-((2 * lam) * u)) *
      ((beta j : ℝ) * ((beta j : ℝ) * (((j.val : ℝ) + 1) * kappa) +
        kappa * ∑ k ∈ Finset.Ioi j, (beta k : ℝ)) + (-((beta j : ℝ) * beta j)) * u))
    (fun j => by fun_prop)
    (fun j v h1 h2 => by
      rw [psi_cell j h1 h2, integral_psi_tail j h1 h2.le]
      ring)
    (m := 0) (n := 16) (by norm_num) le_rfl
  rw [Nat.cast_zero, zero_mul, ← T_eq_cast] at hcells
  rw [hcells, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left ⟨Nat.zero_le _, j.isLt⟩,
    integral_exp_mul_affine (mul_ne_zero two_ne_zero hlam), exp_cell, exp_cell_succ]
  unfold envQ0 envU
  field_simp
  ring

/-- `f_λ(0) = Σ_i β_i² E^i U` for `λ ≠ 0`. -/
theorem fLam_zero_closed {lam : ℝ} (hlam : lam ≠ 0) :
    fLam lam 0 = ∑ i : Fin 16, (beta i : ℝ) ^ 2 * envE lam ^ (i : ℕ) * envU lam := by
  unfold fLam
  simp only [sub_zero, add_zero]
  have hcells := integral_cells (f := fun u => psi u * psi u * Real.exp (-(lam * (2 * u))))
    (fun j u => (beta j : ℝ) ^ 2 * Real.exp (-((2 * lam) * u)))
    (fun j => by fun_prop)
    (fun j v h1 h2 => by
      rw [psi_cell j h1 h2, show -(lam * (2 * v)) = -(2 * lam * v) by ring]
      ring)
    (m := 0) (n := 16) (by norm_num) le_rfl
  rw [Nat.cast_zero, zero_mul, ← T_eq_cast] at hcells
  rw [hcells, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left ⟨Nat.zero_le _, j.isLt⟩, intervalIntegral.integral_const_mul,
    integral_exp_neg_mul (mul_ne_zero two_ne_zero hlam), exp_cell, exp_cell_succ]
  unfold envU
  field_simp

/-- **Closed form of the envelope.** For `λ ≠ 0` and every real `φ`,
`H₀ B_φ(λ) = Σ_i E^i (β_i² (Q₀ + (φ/2) U) + κ U β_i Σ_{j>i} β_j)`,
with `E = e^{−2κλ}`, `U = (1 − E)/λ`, `Q₀ = κ/λ − U/(2λ)`. -/
theorem H0_mul_Benv (φ : ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    H0 * Benv φ lam = ∑ i : Fin 16, envE lam ^ (i : ℕ) *
      ((beta i : ℝ) ^ 2 * (envQ0 lam + φ / 2 * envU lam) +
        kappa * envU lam * beta i * ∑ j ∈ Finset.Ioi i, (beta j : ℝ)) := by
  unfold Benv
  rw [mul_div_cancel₀ _ H0_pos.ne', laplace_fLam_re_closed hlam, fLam_zero_closed hlam,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- The closed form of `B_φ(λ)` itself, for `λ ≠ 0`. -/
theorem Benv_eq (φ : ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    Benv φ lam = (∑ i : Fin 16, envE lam ^ (i : ℕ) *
      ((beta i : ℝ) ^ 2 * (envQ0 lam + φ / 2 * envU lam) +
        kappa * envU lam * beta i * ∑ j ∈ Finset.Ioi i, (beta j : ℝ))) / H0 := by
  rw [← H0_mul_Benv φ hlam, mul_div_cancel_left₀ _ H0_pos.ne']

/-! ## Monotonicity and positivity -/

lemma fLam_zero_eq (lam : ℝ) :
    fLam lam 0 = 2 * ∫ u in (0 : ℝ)..T, psi u * psi u * Real.exp (-(2 * lam * u)) := by
  unfold fLam
  simp only [sub_zero, add_zero]
  congr 1
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [show -(lam * (2 * u)) = -(2 * lam * u) by ring]

lemma outer_intervalIntegrable (lam : ℝ) :
    IntervalIntegrable (fun u => psi u * Real.exp (-(2 * lam * u)) * ∫ v in u..T, psi v)
      volume 0 T :=
  ((psi_intervalIntegrable 0 T).mul_continuousOn
    (by fun_prop : Continuous fun u => Real.exp (-(2 * lam * u))).continuousOn).mul_continuousOn
    continuous_tail.continuousOn

lemma diag_intervalIntegrable (lam : ℝ) :
    IntervalIntegrable (fun u => psi u * psi u * Real.exp (-(2 * lam * u))) volume 0 T := by
  simpa using integrand_intervalIntegrable lam 0 0 T

lemma laplace_fLam_re_nonneg (lam : ℝ) : 0 ≤ (laplace (fLam lam) ((-lam : ℝ) : ℂ)).re := by
  rw [laplace_fLam_re]
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg T_pos.le fun u hu => ?_)
  exact mul_nonneg (mul_nonneg (psi_nonneg u) (Real.exp_pos _).le) (tail_nonneg hu.2)

lemma fLam_zero_nonneg (lam : ℝ) : 0 ≤ fLam lam 0 := by
  rw [fLam_zero_eq]
  refine mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg T_pos.le fun u _ => ?_)
  exact mul_nonneg (mul_nonneg (psi_nonneg u) (psi_nonneg u)) (Real.exp_pos _).le

lemma laplace_fLam_re_antitone :
    Antitone fun lam : ℝ => (laplace (fLam lam) ((-lam : ℝ) : ℂ)).re := by
  intro l1 l2 hl
  simp only [laplace_fLam_re]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  refine intervalIntegral.integral_mono_on T_pos.le (outer_intervalIntegrable l2)
    (outer_intervalIntegrable l1) fun u hu => ?_
  have h3 : Real.exp (-(2 * l2 * u)) ≤ Real.exp (-(2 * l1 * u)) :=
    Real.exp_le_exp.2 (by nlinarith [hu.1])
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 (psi_nonneg u))
    (tail_nonneg hu.2)

lemma fLam_zero_antitone : Antitone fun lam : ℝ => fLam lam 0 := by
  intro l1 l2 hl
  simp only [fLam_zero_eq]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0 : ℝ) ≤ 2)
  refine intervalIntegral.integral_mono_on T_pos.le (diag_intervalIntegrable l2)
    (diag_intervalIntegrable l1) fun u hu => ?_
  have h3 : Real.exp (-(2 * l2 * u)) ≤ Real.exp (-(2 * l1 * u)) :=
    Real.exp_le_exp.2 (by nlinarith [hu.1])
  exact mul_le_mul_of_nonneg_left h3 (mul_nonneg (psi_nonneg u) (psi_nonneg u))

/-- `B_φ(λ) ≥ 0` for `φ ≥ 0` and every real `λ`. -/
theorem Benv_nonneg {φ : ℝ} (hφ : 0 ≤ φ) (lam : ℝ) : 0 ≤ Benv φ lam := by
  unfold Benv
  refine div_nonneg ?_ H0_pos.le
  exact add_nonneg (laplace_fLam_re_nonneg lam) (mul_nonneg (by linarith) (fLam_zero_nonneg lam))

/-- `B_φ` is antitone on all of `ℝ` for `φ ≥ 0`. -/
theorem Benv_antitone {φ : ℝ} (hφ : 0 ≤ φ) : Antitone (Benv φ) := by
  intro l1 l2 hl
  unfold Benv
  refine div_le_div_of_nonneg_right ?_ H0_pos.le
  exact add_le_add (laplace_fLam_re_antitone hl)
    (mul_le_mul_of_nonneg_left (fLam_zero_antitone hl) (by linarith))

theorem Benv_antitoneOn {φ : ℝ} (hφ : 0 ≤ φ) : AntitoneOn (Benv φ) (Set.Ioi 0) :=
  (Benv_antitone hφ).antitoneOn _

lemma envE_pos (lam : ℝ) : 0 < envE lam := Real.exp_pos _

lemma envE_lt_one {lam : ℝ} (hlam : 0 < lam) : envE lam < 1 := by
  unfold envE
  rw [Real.exp_lt_one_iff]
  nlinarith [kappa_pos]

lemma envU_pos {lam : ℝ} (hlam : 0 < lam) : 0 < envU lam :=
  div_pos (by linarith [envE_lt_one hlam]) hlam

lemma envQ0_pos {lam : ℝ} (hlam : 0 < lam) : 0 < envQ0 lam := by
  have hk := kappa_pos
  have hx : -(2 * (kappa : ℝ) * lam) ≠ 0 := by nlinarith
  have h1 := Real.add_one_lt_exp hx
  have key : 0 < 2 * (kappa : ℝ) * lam - (1 - envE lam) := by unfold envE; linarith
  have : envQ0 lam = (2 * (kappa : ℝ) * lam - (1 - envE lam)) / (2 * lam ^ 2) := by
    unfold envQ0 envU; field_simp
  rw [this]; positivity

/-- `B_φ(λ) > 0` for `φ ≥ 0` and `λ > 0`. -/
theorem Benv_pos {φ : ℝ} (hφ : 0 ≤ φ) {lam : ℝ} (hlam : 0 < lam) : 0 < Benv φ lam := by
  have h := H0_mul_Benv φ hlam.ne'
  have hsum : 0 < ∑ i : Fin 16, envE lam ^ (i : ℕ) *
      ((beta i : ℝ) ^ 2 * (envQ0 lam + φ / 2 * envU lam) +
        kappa * envU lam * beta i * ∑ j ∈ Finset.Ioi i, (beta j : ℝ)) := by
    refine Finset.sum_pos (fun i _ => ?_) Finset.univ_nonempty
    refine mul_pos (pow_pos (envE_pos lam) _) (add_pos_of_pos_of_nonneg ?_ ?_)
    · exact mul_pos (pow_pos (beta_pos i) 2) (add_pos_of_pos_of_nonneg (envQ0_pos hlam)
        (mul_nonneg (by linarith) (envU_pos hlam).le))
    · exact mul_nonneg (mul_nonneg (mul_nonneg kappa_pos.le (envU_pos hlam).le) (beta_pos i).le)
        (Finset.sum_nonneg fun j _ => (beta_pos j).le)
  rw [← h] at hsum
  exact pos_of_mul_pos_right hsum H0_pos.le

/-- `G_φ` is antitone on `ℝ` when `L − 2T ≥ 0` and `φ ≥ 0`. -/
theorem Gphi_antitone {L φ : ℝ} (hL : 0 ≤ L - 2 * (T : ℝ)) (hφ : 0 ≤ φ) :
    Antitone (Gphi L φ) := by
  intro l1 l2 hl
  unfold Gphi
  exact mul_le_mul (Real.exp_le_exp.2 (by nlinarith [mul_nonneg hL (sub_nonneg.2 hl)]))
    (Benv_antitone hφ hl) (Benv_nonneg hφ l2) (Real.exp_pos _).le

theorem Gphi_antitoneOn {L φ : ℝ} (hL : 0 ≤ L - 2 * (T : ℝ)) (hφ : 0 ≤ φ) :
    AntitoneOn (Gphi L φ) (Set.Ioi 0) :=
  (Gphi_antitone hL hφ).antitoneOn _

theorem Gphi_nonneg (L : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) (lam : ℝ) : 0 ≤ Gphi L φ lam :=
  mul_nonneg (Real.exp_pos _).le (Benv_nonneg hφ lam)

theorem Gphi_pos (L : ℝ) {φ : ℝ} (hφ : 0 ≤ φ) {lam : ℝ} (hlam : 0 < lam) : 0 < Gphi L φ lam :=
  mul_pos (Real.exp_pos _) (Benv_pos hφ hlam)

theorem G_antitone {L : ℝ} (hL : 0 ≤ L - 2 * (T : ℝ)) : Antitone (G L) :=
  Gphi_antitone hL (by norm_num)

theorem G_antitoneOn {L : ℝ} (hL : 0 ≤ L - 2 * (T : ℝ)) : AntitoneOn (G L) (Set.Ioi 0) :=
  (G_antitone hL).antitoneOn _

theorem G_pos (L : ℝ) {lam : ℝ} (hlam : 0 < lam) : 0 < G L lam :=
  Gphi_pos L (by norm_num) hlam

/-! ## `Ψ` and `h` -/

lemma Psi_ofReal (lam : ℝ) :
    Psi (lam : ℂ) = ((∫ t in Ioi (0 : ℝ), psi t * Real.exp (-(lam * t)) : ℝ) : ℂ) := by
  unfold Psi laplace
  have : ∀ t : ℝ, ((psi t : ℝ) : ℂ) * Complex.exp (-((lam : ℂ) * (t : ℂ))) =
      ((psi t * Real.exp (-(lam * t)) : ℝ) : ℂ) := by
    intro t; push_cast; ring_nf
  simp_rw [this]
  rw [integral_complex_ofReal]

/-- `Ψ(λ)` is real for real `λ`. -/
theorem Psi_im (lam : ℝ) : (Psi lam).im = 0 := by
  rw [Psi_ofReal, Complex.ofReal_im]

lemma Psi_re_integral (lam : ℝ) :
    (Psi lam).re = ∫ t in (0 : ℝ)..T, psi t * Real.exp (-(lam * t)) := by
  rw [Psi_ofReal, Complex.ofReal_re, intervalIntegral.integral_of_le T_pos.le]
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
  intro t ht
  have : (T : ℝ) < t := by
    simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht; exact ht.2 ht.1
  rw [psi_eq_zero (Or.inr this.le), zero_mul]

/-- **Closed form of `Ψ`.** For real `λ ≠ 0`,
`Re Ψ(λ) = Σ_i β_i e^{−iκλ} (1 − e^{−κλ})/λ`. -/
theorem Psi_re {lam : ℝ} (hlam : lam ≠ 0) :
    (Psi lam).re = ∑ i : Fin 16, (beta i : ℝ) * Real.exp (-(((i : ℕ) : ℝ) * kappa * lam)) *
      (1 - Real.exp (-(kappa * lam))) / lam := by
  rw [Psi_re_integral]
  have hcells := integral_cells (f := fun t => psi t * Real.exp (-(lam * t)))
    (fun j t => (beta j : ℝ) * Real.exp (-(lam * t))) (fun j => by fun_prop)
    (fun j v h1 h2 => by rw [psi_cell j h1 h2]) (m := 0) (n := 16) (by norm_num) le_rfl
  rw [Nat.cast_zero, zero_mul, ← T_eq_cast] at hcells
  rw [hcells]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left ⟨Nat.zero_le _, j.isLt⟩, intervalIntegral.integral_const_mul,
    integral_exp_neg_mul hlam]
  have e1 : Real.exp (-(lam * ((j.val : ℝ) * kappa))) =
      Real.exp (-(((j : ℕ) : ℝ) * kappa * lam)) := by congr 1; ring
  have e2 : Real.exp (-(lam * (((j.val : ℝ) + 1) * kappa))) =
      Real.exp (-(((j : ℕ) : ℝ) * kappa * lam)) * Real.exp (-(kappa * lam)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1, e2]
  ring

/-- `h(λ) = Ψ(λ)²/H₀` in closed form, for real `λ ≠ 0`. -/
theorem hRatio_eq {lam : ℝ} (hlam : lam ≠ 0) :
    hRatio lam = (∑ i : Fin 16, (beta i : ℝ) * Real.exp (-(((i : ℕ) : ℝ) * kappa * lam)) *
      (1 - Real.exp (-(kappa * lam))) / lam) ^ 2 / H0 := by
  unfold hRatio; rw [Psi_re hlam]

/-! ## `H(0)` of the prime kernel -/

lemma continuous_triangle (L K : ℝ) : Continuous (triangle L K) := by
  unfold triangle
  exact continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs)

lemma triangle_eq_zero {L K t : ℝ} (hK : 0 ≤ K) (ht : t ≤ L - 2 * K ∨ L ≤ t) :
    triangle L K t = 0 := by
  unfold triangle
  apply max_eq_left
  rcases ht with ht | ht
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

/-- The integral of Xylouris's triangle over `(0, ∞)` is `K²` when `L − 2K ≥ 0`. -/
lemma integral_triangle {L K : ℝ} (hK : 0 ≤ K) (hLK : 0 ≤ L - 2 * K) :
    ∫ t in Ioi (0 : ℝ), triangle L K t = K ^ 2 := by
  have h1 : ∫ t in Ioi (0 : ℝ), triangle L K t = ∫ t in Ioc (0 : ℝ) L, triangle L K t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioc_subset_Ioi_self
    intro t ht
    have : L < t := by
      simp only [mem_sdiff, mem_Ioi, mem_Ioc, not_and, not_le] at ht; exact ht.2 ht.1
    exact triangle_eq_zero hK (Or.inr this.le)
  rw [h1, ← intervalIntegral.integral_of_le (by linarith)]
  have hc := continuous_triangle L K
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 (L - 2 * K))
      (hc.intervalIntegrable (L - 2 * K) L),
    ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (L - 2 * K) (L - K))
      (hc.intervalIntegrable (L - K) L)]
  have e0 : ∫ t in (0 : ℝ)..(L - 2 * K), triangle L K t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro t ht
      rw [uIcc_of_le hLK] at ht
      exact triangle_eq_zero hK (Or.inl ht.2)
  have e1 : ∫ t in (L - 2 * K)..(L - K), triangle L K t =
      ∫ t in (L - 2 * K)..(L - K), (t - (L - 2 * K)) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    simp only [triangle]
    rw [abs_of_nonpos (by linarith [ht.2]), max_eq_right (by linarith [ht.1])]
    ring
  have e2 : ∫ t in (L - K)..L, triangle L K t = ∫ t in (L - K)..L, (L - t) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (by linarith)] at ht
    simp only [triangle]
    rw [abs_of_nonneg (by linarith [ht.1]), max_eq_right (by linarith [ht.2])]
    ring
  rw [e0, e1, e2, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const,
    intervalIntegral.integral_sub intervalIntegrable_const intervalIntegral.intervalIntegrable_id,
    integral_id,
    integral_id, intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
    smul_eq_mul]
  ring

lemma integrable_triangle (L K : ℝ) (hK : 0 ≤ K) : Integrable (triangle L K) := by
  refine (continuous_triangle L K).integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := L - 2 * K) (b := L)) fun t ht => ?_)
  simp only [mem_Icc, not_and_or, not_le] at ht
  rcases ht with ht | ht
  · exact triangle_eq_zero hK (Or.inl ht.le)
  · exact triangle_eq_zero hK (Or.inr ht.le)

/-- `Σ_k c_k = (Σ_i β_i)²`. -/
lemma sum_coef : ∑ k : Fin 31, coef k = (∑ i : Fin 16, beta i) ^ 2 := by
  unfold coef
  rw [sq, Finset.sum_mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hij : i.val + j.val < 31 := by have := i.isLt; have := j.isLt; omega
  rw [Finset.sum_eq_single (⟨i.val + j.val, hij⟩ : Fin 31)]
  · simp
  · intro k _ hk
    rw [ite_eq_right]
    intro h
    exact hk (Fin.ext h.symm)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- `H(0) = ∫₀^∞ h` is real, for every `L`. -/
lemma primeKernel_H_zero_eq (L : ℝ) :
    (primeKernel L).H 0 = ((∫ t in Ioi (0 : ℝ), (primeKernel L).h t : ℝ) : ℂ) := by
  unfold TriKernel.H laplace
  simp only [zero_mul, neg_zero, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal]

lemma primeKernel_H_zero_im (L : ℝ) : ((primeKernel L).H 0).im = 0 := by
  rw [primeKernel_H_zero_eq, Complex.ofReal_im]

/-- **`H(0)` of the prime kernel.** When `L − 2T ≥ 0` every triangle lies in `[0, ∞)`, and
`H(0) = ∫ h = κ² Σ_k c_k = (κ Σ_i β_i)² = H₀`. -/
theorem primeKernel_H_zero {L : ℝ} (hL : 0 ≤ L - 2 * (T : ℝ)) :
    ((primeKernel L).H 0).re = H0 := by
  have hk := kappa_pos
  have hval : ∀ k : Fin 31, ∫ t in Ioi (0 : ℝ),
      triangle (L - 2 * T + ((k.val : ℝ) + 2) * kappa) kappa t = (kappa : ℝ) ^ 2 := by
    intro k
    have : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
    exact integral_triangle hk.le (by nlinarith)
  rw [primeKernel_H_zero_eq, Complex.ofReal_re]
  unfold TriKernel.h
  show ∫ t in Ioi (0 : ℝ), ∑ k : Fin 31,
      (coef k : ℝ) * triangle (L - 2 * T + ((k.val : ℝ) + 2) * kappa) kappa t = H0
  rw [integral_finsetSum _ (fun k _ =>
    ((integrable_triangle _ _ hk.le).integrableOn).const_mul _)]
  simp_rw [integral_const_mul, hval]
  rw [← Finset.sum_mul, H0]
  have : ∑ k : Fin 31, (coef k : ℝ) = ((∑ k : Fin 31, coef k : ℚ) : ℝ) := by push_cast; rfl
  rw [this, sum_coef]
  push_cast
  ring

/-! ## The cross term `C(p, a)` -/

/-- `X(r, j) = ∫_{jκ}^{(j+1)κ} e^{−ru} du = (e^{−rjκ} − e^{−r(j+1)κ})/r`, and `κ` when `r = 0`
(`int_exp` of `triple_inputs.py`). -/
def cellExp (r : ℝ) (j : ℕ) : ℝ :=
  if r = 0 then kappa else
    (Real.exp (-(r * ((j : ℝ) * kappa))) - Real.exp (-(r * (((j : ℝ) + 1) * kappa)))) / r

lemma integral_cell_exp (r : ℝ) (j : ℕ) :
    ∫ u in (j : ℝ) * kappa..((j : ℝ) + 1) * kappa, Real.exp (-(r * u)) = cellExp r j := by
  unfold cellExp
  split_ifs with hr
  · subst hr; simp; ring
  · exact integral_exp_neg_mul hr _ _

/-- The inner integral of `C(p, a)` on the cell `[jκ, (j+1)κ]`:
`∫_u^T ψ(v) e^{−a(v−u)} dv = β_j/a + e^{au} (Σ_{k>j} β_k X(a, k) − (β_j/a) e^{−a(j+1)κ})`. -/
lemma inner_Cpa {a : ℝ} (ha : a ≠ 0) (j : Fin 16) {u : ℝ} (h1 : (j.val : ℝ) * kappa ≤ u)
    (h2 : u ≤ ((j.val : ℝ) + 1) * kappa) :
    ∫ v in u..T, psi v * Real.exp (-(a * (v - u))) =
      (beta j : ℝ) / a + Real.exp (-(-a * u)) *
        ((∑ k ∈ Finset.Ioi j, (beta k : ℝ) * cellExp a k) -
          (beta j : ℝ) / a * Real.exp (-(a * (((j.val : ℝ) + 1) * kappa)))) := by
  have e : ∀ v, psi v * Real.exp (-(a * (v - u))) =
      Real.exp (a * u) * (psi v * Real.exp (-(a * v))) := by
    intro v; rw [show -(a * (v - u)) = a * u + -(a * v) by ring, Real.exp_add]; ring
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul,
    integral_psi_mul_tail (fun v => Real.exp (-(a * v))) (by fun_prop) j h1 h2,
    integral_exp_neg_mul ha]
  simp_rw [integral_cell_exp]
  rw [show -(-a * u) = a * u by ring, Real.exp_neg (a * u)]
  have hexp : Real.exp (a * u) ≠ 0 := (Real.exp_pos _).ne'
  field_simp
  ring

/-- **Closed form of `C(p, a)`** as exact step-cell sums (`cross_envelope` of
`triple_inputs.py`): for `a ≠ 0` and every real `p`, with `X = cellExp`,
`C(p, a) = (2/H₀) Σ_j β_j [(β_j/a) X(2p, j) + D_j X(2p − a, j)]`, where
`D_j = Σ_{k>j} β_k X(a, k) − (β_j/a) e^{−a(j+1)κ}`. -/
theorem Cpa_closed (p : ℝ) {a : ℝ} (ha : a ≠ 0) :
    Cpa p a = 2 / H0 * ∑ j : Fin 16, (beta j : ℝ) *
      ((beta j : ℝ) / a * cellExp (2 * p) j +
        ((∑ k ∈ Finset.Ioi j, (beta k : ℝ) * cellExp a k) -
          (beta j : ℝ) / a * Real.exp (-(a * ((((j : ℕ) : ℝ) + 1) * kappa)))) *
          cellExp (2 * p - a) j) := by
  unfold Cpa
  congr 1
  have hcells := integral_cells
    (f := fun u => psi u * Real.exp (-(2 * p * u)) *
      ∫ v in u..T, psi v * Real.exp (-(a * (v - u))))
    (fun j u => (beta j : ℝ) * ((beta j : ℝ) / a) * Real.exp (-((2 * p) * u)) +
      (beta j : ℝ) * ((∑ k ∈ Finset.Ioi j, (beta k : ℝ) * cellExp a k) -
          (beta j : ℝ) / a * Real.exp (-(a * (((j.val : ℝ) + 1) * kappa)))) *
        Real.exp (-((2 * p - a) * u)))
    (fun j => by fun_prop)
    (fun j v h1 h2 => by
      rw [psi_cell j h1 h2, inner_Cpa ha j h1 h2.le]
      have : Real.exp (-(2 * p * v)) * Real.exp (-(-a * v)) = Real.exp (-((2 * p - a) * v)) := by
        rw [← Real.exp_add]; congr 1; ring
      linear_combination (beta j : ℝ) * ((∑ k ∈ Finset.Ioi j, (beta k : ℝ) * cellExp a k) -
          (beta j : ℝ) / a * Real.exp (-(a * (((j.val : ℝ) + 1) * kappa)))) * this)
    (m := 0) (n := 16) (by norm_num) le_rfl
  rw [Nat.cast_zero, zero_mul, ← T_eq_cast] at hcells
  rw [hcells]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ite_eq_left ⟨Nat.zero_le _, j.isLt⟩,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_cell_exp,
    integral_cell_exp]
  ring

end GradedNear.Kernel
