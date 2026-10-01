module

public import GradedNear.FirstFactor
public import GradedNear.Basic

/-!
# The first Cauchy–Schwarz factor for the data of the lemma

`𝓛⁻¹ Σ_{1 ≤ n ≤ q^{x_f}} (Λ(n)/n) e^{2 s t_n} f(t_n)² / ω(t_n) ≤ I_B + ε` for all large `q`.
This applies `riemann_upper` to `φ(u) = e^{2su} f(u)² / ω(u)`. `φ` is bounded on `[0, x_f]`
because `ω ≥ c > 0` wherever `f ≠ 0`. It is continuous on `(0, x_f)` away from `x_g` and the
cell endpoints `t_k`; where `ω(u) = 0` we have `f = 0` nearby, so `φ = 0`. Its integral over
`[0, x_f]` is `I_B`, since `f = 0` on `[x_f, ∞)`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

open NearData

namespace FirstPart

open Filter Topology MeasureTheory

variable (D : NearData)

/-- The integrand `φ(u) = e^{2su} f(u)² / ω(u)` of `I_B`. -/
noncomputable def phi (u : ℝ) : ℝ := Real.exp (2 * D.s * u) * D.f u ^ 2 / D.omega u

/-- `|φ(v)| ≤ e^{2sv} f(v)² / c` for `v ≥ 0`, where `ω ≥ c` wherever `f ≠ 0`. -/
lemma abs_phi_le {c : ℝ} (hc : 0 < c) (hcω : ∀ u, 0 ≤ u → D.f u ≠ 0 → c ≤ D.omega u)
    {v : ℝ} (hv : 0 ≤ v) : |phi D v| ≤ Real.exp (2 * D.s * v) * D.f v ^ 2 / c := by
  unfold phi
  by_cases hf : D.f v = 0
  · simp [hf]
  · have hω := hcω v hv hf
    have hωpos : 0 < D.omega v := lt_of_lt_of_le hc hω
    have hnum : 0 ≤ Real.exp (2 * D.s * v) * D.f v ^ 2 := by positivity
    rw [abs_of_nonneg (div_nonneg hnum hωpos.le)]
    exact div_le_div_of_nonneg_left hnum hc hω

/-- `φ` is bounded on `[0, x_f]`. -/
lemma exists_bound (hD : D.Valid) : ∃ M, ∀ u ∈ Set.Icc 0 D.xf, |phi D u| ≤ M := by
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  have hf : ContinuousOn D.f (Set.Icc 0 D.xf) := hD.f_cond.cont.mono Set.Icc_subset_Ici_self
  have hcont : ContinuousOn (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / c)
      (Set.Icc 0 D.xf) := by
    fun_prop
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨M, fun u hu => ?_⟩
  have h2 := hM u hu
  rw [Real.norm_eq_abs] at h2
  exact (abs_phi_le D hc hcω hu.1).trans ((le_abs_self _).trans h2)

/-- The indicator-type function `1_{[a, b)} · c` is continuous away from `a` and `b`. -/
lemma continuousAt_ite_Ico {a b c u : ℝ} (ha : u ≠ a) (hb : u ≠ b) :
    ContinuousAt (fun v : ℝ => if a ≤ v ∧ v < b then c else 0) u := by
  rcases lt_or_gt_of_ne ha with hua | hua
  · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) u).congr ?_
    filter_upwards [Iio_mem_nhds hua] with v hv
    rw [ite_eq_right (fun h => absurd h.1 (not_le.2 hv))]
  · rcases lt_or_gt_of_ne hb with hub | hub
    · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => c) u).congr ?_
      filter_upwards [Ioo_mem_nhds hua hub] with v hv
      rw [ite_eq_left ⟨hv.1.le, hv.2⟩]
    · refine (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) u).congr ?_
      filter_upwards [Ioi_mem_nhds hub] with v hv
      rw [ite_eq_right (fun h => absurd h.2 (not_lt.2 hv.le))]

/-- The sieve weight `H` is continuous away from the cell endpoints `t_0, …, t_m`. -/
lemma continuousAt_sieveH {u : ℝ} (hu : ∀ k ≤ D.m, u ≠ D.t k) : ContinuousAt D.sieveH u := by
  show ContinuousAt
    (fun v => ∑ k ∈ Finset.range D.m, if D.t k ≤ v ∧ v < D.t (k + 1) then D.h k else 0) u
  exact tendsto_finsetSum (f := fun k v => if D.t k ≤ v ∧ v < D.t (k + 1) then D.h k else 0) _
    (fun k hk => continuousAt_ite_Ico (hu k (by simp at hk; omega))
      (hu (k + 1) (by simp at hk; omega)))

/-- `φ` is continuous at every `u > 0` that is not a cell endpoint. -/
lemma continuousAt_phi (hD : D.Valid) {u : ℝ} (hu0 : 0 < u) (hu : ∀ k ≤ D.m, u ≠ D.t k) :
    ContinuousAt (phi D) u := by
  obtain ⟨c, hc, hcω⟩ := hD.omega_lb
  have hf : ContinuousAt D.f u := hD.f_cond.cont.continuousAt (Ici_mem_nhds hu0)
  have hg : ContinuousAt D.g u := hD.g_cond1.cont.continuousAt (Ici_mem_nhds hu0)
  have hH := continuousAt_sieveH D hu
  have hexp : ∀ a : ℝ, ContinuousAt (fun v : ℝ => Real.exp (a * v)) u := fun a => by
    fun_prop
  have hω : ContinuousAt D.omega u := by
    show ContinuousAt (fun v => D.g v * Real.exp (D.s₁ * v) + D.sieveH v) u
    exact (hg.mul (hexp D.s₁)).add hH
  have hnum : ContinuousAt (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2) u :=
    (hexp (2 * D.s)).mul (hf.pow 2)
  by_cases hωu : D.omega u = 0
  · have hfu : D.f u = 0 := by
      by_contra hne
      have := hcω u hu0.le hne
      linarith
    have hφu : phi D u = 0 := by simp [phi, hfu]
    have ha : Tendsto (fun v => Real.exp (2 * D.s * v) * D.f v ^ 2 / c) (𝓝 u) (𝓝 0) := by
      have := (hnum.div_const c).tendsto
      simpa [hfu] using this
    show Tendsto (phi D) (𝓝 u) (𝓝 (phi D u))
    rw [hφu]
    apply squeeze_zero_norm' _ ha
    filter_upwards [Ioi_mem_nhds hu0] with v hv
    rw [Real.norm_eq_abs]
    exact abs_phi_le D hc hcω (le_of_lt hv)
  · exact hnum.div hω hωu

/-- `∫₀^{x_f} φ = I_B`. -/
lemma integral_phi_eq (hD : D.Valid) : ∫ u in (0 : ℝ)..D.xf, phi D u = D.IB := by
  rw [intervalIntegral.integral_of_le hD.f_cond.pos.le]
  show ∫ u in Set.Ioc 0 D.xf, phi D u = ∫ u in Set.Ioi (0 : ℝ), phi D u
  symm
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    Set.Ioc_subset_Ioi_self
  intro v hv
  have hv' : D.xf ≤ v := by
    rcases hv with ⟨hv1, hv2⟩
    simp only [Set.mem_Ioi] at hv1
    simp only [Set.mem_Ioc, not_and, not_le] at hv2
    exact (hv2 hv1).le
  simp [phi, hD.f_cond.vanish v hv']

end FirstPart

theorem first_factor_bound (D : NearData) (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ D.xf⌋₊, Λ n / n *
          (Real.exp (2 * D.s * tn q n) * D.f (tn q n) ^ 2 / D.omega (tn q n))) /
        Real.log q ≤ D.IB + ε := by
  obtain ⟨M, hM⟩ := FirstPart.exists_bound D hD
  obtain ⟨q₀, hq₀⟩ := riemann_upper (FirstPart.phi D) D.xf M
    (insert D.xg ((Finset.range (D.m + 1)).image D.t)) hD.f_cond.pos hM
    (fun u hu huP => FirstPart.continuousAt_phi D hD hu.1 (fun k hk hEq => huP (by
      rw [Finset.mem_insert, Finset.mem_image]
      exact Or.inr ⟨k, Finset.mem_range.2 (by omega), hEq.symm⟩))) hε
  refine ⟨q₀, fun q hq => ?_⟩
  have h := hq₀ q hq
  rw [FirstPart.integral_phi_eq D hD] at h
  exact h

end GradedNear
