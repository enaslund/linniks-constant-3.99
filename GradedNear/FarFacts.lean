module

public import GradedNear.Far

/-!
# Facts about the far weight (paper §6)

For a far profile `P` with `c₁, c₂ > 0` (`GradedNear.Kernel.FarProfile`):
* `FarProfile.profileCondition`: the profile
  `w₀ = √(w₀²) = e^{−θt/2} (min(t − u, c₂) + ε)^{1/4}` satisfies the printed conditions of
  [X, Lemma 5.1] on `[u, x]`;
* `FarProfile.winv_pos`, `FarProfile.w_pos`, `FarProfile.w_antitone`: `w(λ) > 0`, and `w`
  decreases on all of `ℝ`;
* `FarProfile.tail_antitone`: if `2x ≤ A`, then `e^{−Aλ} w(λ)⁻¹` decreases (the tail column);
* `FarProfile.far_bound`: [X, Lemma 5.1] with `M = 10` and `ε = 100η` gives
  `Σ_χ w(λ(χ)) ≤ (1 + η) V`.

The concrete profiles `inherited` and `retuned` satisfy all hypotheses, and both have
`2x < 3.156342 = 3.99 − 2T` (`FarProfile.corpus_facts`); the `*_corpus` statements and
`FarProfile.tail_antitone_of_L` specialize the results to them.
-/

@[expose] public section

noncomputable section

namespace GradedNear.Kernel

open MeasureTheory Set Filter Topology

namespace FarProfile

variable (P : FarProfile)

lemma eps_pos : (0 : ℝ) < FarProfile.eps := by norm_num [FarProfile.eps]

lemma u_pos (hc₁ : 0 < P.c₁) : 0 < P.u := by
  have h1 : (0 : ℝ) < P.c₁ := by exact_mod_cast hc₁
  unfold FarProfile.u; linarith

lemma u_lt_x (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) : P.u < P.x := by
  have h1 : (0 : ℝ) < P.c₁ := by exact_mod_cast hc₁
  have h2 : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  unfold FarProfile.u FarProfile.x; linarith

lemma continuous_w0sq : Continuous P.w0sq := by
  unfold FarProfile.w0sq; fun_prop

lemma w0sq_nonneg (t : ℝ) : 0 ≤ P.w0sq t :=
  mul_nonneg (Real.exp_pos _).le (Real.sqrt_nonneg _)

lemma w0sq_pos (hc₂ : 0 < P.c₂) {t : ℝ} (ht : P.u ≤ t) : 0 < P.w0sq t := by
  have h2 : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have hm : 0 ≤ min (t - P.u) (P.c₂ : ℝ) := le_min (by linarith) h2.le
  exact mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 (by linarith [eps_pos]))

/-! ### The printed profile conditions -/

/-- Left of `v`, the profile is `√(e^{−θs} √(s − u + ε))`. -/
lemma sqrt_w0sq_of_le_v {s : ℝ} (hs : s ≤ P.v) :
    Real.sqrt (P.w0sq s) =
      Real.sqrt (Real.exp (-((P.θ : ℝ) * s)) * Real.sqrt (s - P.u + FarProfile.eps)) := by
  unfold FarProfile.w0sq
  rw [min_eq_left (by unfold FarProfile.v at hs; linarith)]

/-- Right of `v`, the profile is `√(e^{−θs} √(c₂ + ε))`. -/
lemma sqrt_w0sq_of_v_le {s : ℝ} (hs : P.v ≤ s) :
    Real.sqrt (P.w0sq s) =
      Real.sqrt (Real.exp (-((P.θ : ℝ) * s)) * Real.sqrt (P.c₂ + FarProfile.eps)) := by
  unfold FarProfile.w0sq
  rw [min_eq_right (by unfold FarProfile.v at hs; linarith)]

/-- **The printed conditions of [X, Lemma 5.1]** hold for `w₀ = √(w₀²)` on `[u, x]`: it is
continuous, `C¹` off `{v}`, bounded above and below by positive constants (as `ε > 0`), and its
derivative is bounded on `(u, x)`. -/
theorem profileCondition (hc₂ : 0 < P.c₂) :
    ProfileCondition (fun t => Real.sqrt (P.w0sq t)) P.u P.x := by
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have he := eps_pos
  set F₁ : ℝ → ℝ := fun s =>
    Real.sqrt (Real.exp (-((P.θ : ℝ) * s)) * Real.sqrt (s - P.u + FarProfile.eps)) with hF₁def
  set F₂ : ℝ → ℝ := fun s =>
    Real.sqrt (Real.exp (-((P.θ : ℝ) * s)) * Real.sqrt (P.c₂ + FarProfile.eps)) with hF₂def
  have hcont : Continuous (fun t => Real.sqrt (P.w0sq t)) := P.continuous_w0sq.sqrt
  -- `F₁` is `C¹` on `(u − ε, ∞)`.
  have hF₁ : ∀ s, P.u - FarProfile.eps < s → ContDiffAt ℝ 1 F₁ s := by
    intro s hs
    have h1 : 0 < s - P.u + FarProfile.eps := by linarith
    have hin : ContDiffAt ℝ 1 (fun s : ℝ => s - P.u + FarProfile.eps) s := by fun_prop
    have h2 : ContDiffAt ℝ 1 (fun s : ℝ => Real.sqrt (s - P.u + FarProfile.eps)) s :=
      hin.sqrt h1.ne'
    have h3 : ContDiffAt ℝ 1 (fun s : ℝ => Real.exp (-((P.θ : ℝ) * s))) s := by fun_prop
    exact (h3.mul h2).sqrt (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 h1)).ne'
  -- `F₂` is `C¹` everywhere.
  have hF₂ : ContDiff ℝ 1 F₂ := by
    have h1 : 0 < (P.c₂ : ℝ) + FarProfile.eps := by linarith
    have h3 : ContDiff ℝ 1 (fun s : ℝ => Real.exp (-((P.θ : ℝ) * s)) *
        Real.sqrt (P.c₂ + FarProfile.eps)) := by fun_prop
    exact h3.sqrt fun s => (mul_pos (Real.exp_pos _) (Real.sqrt_pos.2 h1)).ne'
  -- Local agreement with `F₁` left of `v` and with `F₂` right of `v`.
  have hleft : ∀ t, t < P.v → (fun t => Real.sqrt (P.w0sq t)) =ᶠ[𝓝 t] F₁ := fun t ht =>
    Filter.eventually_of_mem (Iio_mem_nhds ht) fun s hs => P.sqrt_w0sq_of_le_v (le_of_lt hs)
  have hright : ∀ t, P.v < t → (fun t => Real.sqrt (P.w0sq t)) =ᶠ[𝓝 t] F₂ := fun t ht =>
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun s hs => P.sqrt_w0sq_of_v_le (le_of_lt hs)
  refine ⟨hcont.continuousOn, ⟨{P.v}, ?_⟩, ?_, ?_⟩
  · intro t ht htv
    rcases lt_or_gt_of_ne (Finset.notMem_singleton.1 htv) with h | h
    · exact (hF₁ t (by linarith [ht.1])).congr_of_eventuallyEq (hleft t h)
    · exact hF₂.contDiffAt.congr_of_eventuallyEq (hright t h)
  · obtain ⟨m, hm, hmle⟩ := isCompact_Icc.exists_forall_le' hcont.continuousOn
      (a := 0) fun t ht => Real.sqrt_pos.2 (P.w0sq_pos hc₂ ht.1)
    obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
      (s := Icc P.u P.x)
    refine ⟨m, K, hm, fun t ht => ⟨hmle t ht, ?_⟩⟩
    have := hK t ht
    rw [Real.norm_eq_abs] at this
    exact (le_abs_self _).trans this
  · have hd₁ : ContinuousOn (deriv F₁) (Icc P.u P.v) :=
      (ContDiffOn.continuousOn_deriv_of_isOpen (fun s hs => (hF₁ s hs).contDiffWithinAt)
        isOpen_Ioi le_rfl).mono fun s hs => show P.u - FarProfile.eps < s by linarith [hs.1]
    obtain ⟨K₁, hK₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hd₁
    obtain ⟨K₂, hK₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
      ((hF₂.continuous_deriv le_rfl).continuousOn (s := Icc P.v P.x))
    refine ⟨max (max K₁ K₂) |deriv (fun t => Real.sqrt (P.w0sq t)) P.v|, fun t ht => ?_⟩
    rcases lt_trichotomy t P.v with h | h | h
    · rw [(hleft t h).deriv_eq]
      have := hK₁ t ⟨ht.1.le, h.le⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
    · rw [h]
      exact le_max_right _ _
    · rw [(hright t h).deriv_eq]
      have := hK₂ t ⟨h.le, ht.2.le⟩
      rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_right _ _).trans (le_max_left _ _))

/-! ### Positivity and monotonicity of the far weight -/

lemma intervalIntegrable_winv (lam a b : ℝ) :
    IntervalIntegrable (fun t => P.w0sq t * Real.exp (2 * lam * t)) volume a b :=
  (P.continuous_w0sq.mul (by fun_prop)).intervalIntegrable a b

/-- `w(λ)⁻¹ = ∫_u^x w₀² e^{2λt} dt > 0`. -/
theorem winv_pos (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℝ) : 0 < P.winv lam := by
  unfold FarProfile.winv
  refine intervalIntegral.intervalIntegral_pos_of_pos_on (P.intervalIntegrable_winv lam _ _)
    (fun t ht => ?_) (P.u_lt_x hc₁ hc₂)
  exact mul_pos (P.w0sq_pos hc₂ ht.1.le) (Real.exp_pos _)

/-- `w(λ) > 0`. -/
theorem w_pos (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℝ) : 0 < P.w lam :=
  inv_pos.2 (P.winv_pos hc₁ hc₂ lam)

/-- `λ ↦ w(λ)⁻¹` increases, since `t ≥ u > 0` on `[u, x]`. -/
theorem winv_monotone (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) : Monotone P.winv := by
  intro l₁ l₂ hl
  unfold FarProfile.winv
  refine intervalIntegral.integral_mono_on (P.u_lt_x hc₁ hc₂).le
    (P.intervalIntegrable_winv _ _ _) (P.intervalIntegrable_winv _ _ _) fun t ht => ?_
  have ht0 : 0 ≤ t := (P.u_pos hc₁).le.trans ht.1
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by nlinarith)) (P.w0sq_nonneg t)

/-- **The far weight `w` decreases** on all of `ℝ`. -/
theorem w_antitone (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) : Antitone P.w := fun _ _ hl =>
  inv_anti₀ (P.winv_pos hc₁ hc₂ _) (P.winv_monotone hc₁ hc₂ hl)

/-- **Tail monotonicity.** If `2x ≤ A`, then `λ ↦ e^{−Aλ} w(λ)⁻¹` decreases: its integrand
`w₀(t)² e^{(2t − A)λ}` decreases in `λ` since `2t ≤ 2x ≤ A`. -/
theorem tail_antitone (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) {A : ℝ} (hA : 2 * P.x ≤ A) :
    Antitone fun lam => Real.exp (-(A * lam)) * P.winv lam := by
  intro l₁ l₂ hl
  simp only [FarProfile.winv, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (P.u_lt_x hc₁ hc₂).le
    ((continuous_const.mul (P.continuous_w0sq.mul (by fun_prop))).intervalIntegrable _ _)
    ((continuous_const.mul (P.continuous_w0sq.mul (by fun_prop))).intervalIntegrable _ _)
    fun t ht => ?_
  have h2t : 2 * t ≤ A := by linarith [ht.2]
  have key : -(A * l₂) + 2 * l₂ * t ≤ -(A * l₁) + 2 * l₁ * t := by nlinarith
  calc Real.exp (-(A * l₂)) * (P.w0sq t * Real.exp (2 * l₂ * t))
      = P.w0sq t * Real.exp (-(A * l₂) + 2 * l₂ * t) := by rw [Real.exp_add]; ring
    _ ≤ P.w0sq t * Real.exp (-(A * l₁) + 2 * l₁ * t) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 key) (P.w0sq_nonneg t)
    _ = Real.exp (-(A * l₁)) * (P.w0sq t * Real.exp (2 * l₁ * t)) := by rw [Real.exp_add]; ring

/-- Tail monotonicity in the form `e^{−Aλ}/w(λ)` decreases. -/
theorem tail_antitone' (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) {A : ℝ} (hA : 2 * P.x ≤ A) :
    Antitone fun lam => Real.exp (-(A * lam)) / P.w lam := by
  simpa only [FarProfile.w, div_inv_eq_mul] using P.tail_antitone hc₁ hc₂ hA

/-! ### The far bound from [X, Lemma 5.1] -/

/-- The `i`-th integral of the printed right side of [X, (5.19)] (with `M = 10`,
`u_i = u + i c₂/10`) is the `i`-th integral of `V`: the integrand of `V` vanishes on
`[u, u_i]`. -/
lemma printed_integral_eq (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (i : Fin 10) :
    (∫ t in (P.u + (i.val : ℝ) * P.c₂ / 10)..P.x,
      (Real.sqrt (P.w0sq t))⁻¹ ^ 2 * min (t - (P.u + (i.val : ℝ) * P.c₂ / 10)) (P.c₂ / 10)) =
    ∫ t in P.u..P.x,
      (P.w0sq t)⁻¹ * min (max 0 (t - P.u - (i.val : ℝ) * (P.c₂ / 10))) (P.c₂ / 10) := by
  have hc₁' : (0 : ℝ) < P.c₁ := by exact_mod_cast hc₁
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have hi : (i.val : ℝ) ≤ 9 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
  have hi0 : (0 : ℝ) ≤ i.val := Nat.cast_nonneg _
  set ui : ℝ := P.u + (i.val : ℝ) * P.c₂ / 10 with hui
  have hu_ui : P.u ≤ ui := by
    have : 0 ≤ (i.val : ℝ) * P.c₂ := mul_nonneg hi0 hc₂'.le
    rw [hui]; linarith
  have hui_x : ui ≤ P.x := by
    have : (i.val : ℝ) * P.c₂ ≤ 9 * P.c₂ := mul_le_mul_of_nonneg_right hi hc₂'.le
    rw [hui]; unfold FarProfile.u FarProfile.x; linarith
  have hsub : ∀ t : ℝ, t - P.u - (i.val : ℝ) * (P.c₂ / 10) = t - ui := fun t => by
    rw [hui]; ring
  set f : ℝ → ℝ := fun t =>
    (P.w0sq t)⁻¹ * min (max 0 (t - P.u - (i.val : ℝ) * (P.c₂ / 10))) (P.c₂ / 10) with hfdef
  have hf : ContinuousOn f (Icc P.u P.x) :=
    (P.continuous_w0sq.continuousOn.inv₀ fun t ht => (P.w0sq_pos hc₂ ht.1).ne').mul
      (Continuous.continuousOn (by fun_prop))
  have hfi : ∀ a b, a ∈ Icc P.u P.x → b ∈ Icc P.u P.x → IntervalIntegrable f volume a b :=
    fun a b ha hb => (hf.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hxmem : P.x ∈ Icc P.u P.x := ⟨(P.u_lt_x hc₁ hc₂).le, le_rfl⟩
  have humem : P.u ∈ Icc P.u P.x := ⟨le_rfl, (P.u_lt_x hc₁ hc₂).le⟩
  have huimem : ui ∈ Icc P.u P.x := ⟨hu_ui, hui_x⟩
  show _ = ∫ t in P.u..P.x, f t
  rw [← intervalIntegral.integral_add_adjacent_intervals (hfi _ _ humem huimem)
    (hfi _ _ huimem hxmem)]
  have h0 : ∫ t in P.u..ui, f t = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
    · simp
    · rw [uIcc_of_le hu_ui] at ht
      simp only [f, hsub]
      rw [max_eq_left (by linarith [ht.2]), min_eq_left (by linarith), mul_zero]
  rw [h0, zero_add]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hui_x] at ht
  simp only [f, hsub]
  rw [inv_pow, Real.sq_sqrt (P.w0sq_nonneg t), max_eq_right (by linarith [ht.1])]

/-- **The far bound** from [X, Lemma 5.1, (5.19)] with `M = 10`, `α = P.α`, `w₀ = √(w₀²)` and
`ε = 100η`: for `q ≥ q₀`, any set of characters mod `q` with one chosen zero each in the region
`σ ≥ 1 − (log log log q)/(3 log q)`, `|t| ≤ 1`, has `Σ_χ w(λ(χ)) ≤ (1 + η) V`, where
`λ(χ) = (1 − β(χ)) log q`. -/
theorem far_bound (hX : XylourisLemma51) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂)
    (hα : ∀ i, 0 ≤ P.α i) (hαsum : ∑ i, P.α i = 1) {η : ℝ} (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ (s : Finset (DirichletCharacter ℂ q)) (ρ : DirichletCharacter ℂ q → ℂ),
        (∀ χ ∈ s, χ ≠ 1 ∧ DirichletCharacter.LFunction χ (ρ χ) = 0 ∧
          1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (ρ χ).re ∧
          |(ρ χ).im| ≤ 1) →
        ∑ χ ∈ s, P.w ((1 - (ρ χ).re) * Real.log q) ≤ (1 + η) * P.V := by
  have hc₁' : (0 : ℝ) < P.c₁ := by exact_mod_cast hc₁
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have hα' : ∀ i, (0 : ℝ) ≤ (P.α i : ℝ) := fun i => by exact_mod_cast hα i
  have hαsum' : ∑ i, (P.α i : ℝ) = 1 := by exact_mod_cast hαsum
  obtain ⟨q₀, hq₀⟩ := hX (P.c₁ : ℝ) (P.c₂ : ℝ) hc₁' hc₂' 10 (fun i => (P.α i : ℝ)) hα' hαsum'
    (fun t => Real.sqrt (P.w0sq t)) (P.profileCondition hc₂) (100 * η) (by positivity)
  refine ⟨q₀, fun q _ hq s ρ hρ => ?_⟩
  have h := hq₀ q hq s ρ hρ
  simp only [Nat.cast_ofNat] at h
  calc ∑ χ ∈ s, P.w ((1 - (ρ χ).re) * Real.log q)
      = ∑ χ ∈ s, (∫ t in P.u..P.x, Real.sqrt (P.w0sq t) ^ 2 *
          Real.exp (2 * ((1 - (ρ χ).re) * Real.log q) * t))⁻¹ := by
        refine Finset.sum_congr rfl fun χ _ => ?_
        rw [FarProfile.w, FarProfile.winv]
        congr 1
        refine intervalIntegral.integral_congr fun t _ => ?_
        simp only [Real.sq_sqrt (P.w0sq_nonneg t)]
    _ ≤ _ := h
    _ = (10 ^ 2 + 100 * η) / ((P.c₁ : ℝ) * (P.c₂ : ℝ) ^ 2) * ∑ i : Fin 10, (P.α i : ℝ) ^ 2 *
          ∫ t in P.u..P.x,
            (P.w0sq t)⁻¹ * min (max 0 (t - P.u - (i.val : ℝ) * (P.c₂ / 10))) (P.c₂ / 10) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        exact P.printed_integral_eq hc₁ hc₂ i
    _ = (1 + η) * P.V := by
        rw [FarProfile.V]
        field_simp
        ring

end FarProfile

/-! ### The two profiles of the corpus -/

lemma inherited_c₁_pos : 0 < inherited.c₁ := by norm_num [inherited]
lemma inherited_c₂_pos : 0 < inherited.c₂ := by norm_num [inherited]
lemma inherited_α_nonneg : ∀ i, 0 ≤ inherited.α i := by
  intro i; fin_cases i <;> norm_num [inherited]
lemma inherited_α_sum : ∑ i, inherited.α i = 1 := by
  norm_num [inherited, Fin.sum_univ_succ]

lemma retuned_c₁_pos : 0 < retuned.c₁ := by norm_num [retuned]
lemma retuned_c₂_pos : 0 < retuned.c₂ := by norm_num [retuned]
lemma retuned_α_nonneg : ∀ i, 0 ≤ retuned.α i := by
  intro i; fin_cases i <;> norm_num [retuned]
lemma retuned_α_sum : ∑ i, retuned.α i = 1 := by
  norm_num [retuned, Fin.sum_univ_succ]

/-- `2x < 3.156342 = 3.99 − 2T` for the inherited profile. -/
lemma inherited_two_x_lt : 2 * inherited.x < 3.156342 := by
  norm_num [FarProfile.x, inherited]

/-- `2x < 3.156342 = 3.99 − 2T` for the retuned profile. -/
lemma retuned_two_x_lt : 2 * retuned.x < 3.156342 := by
  norm_num [FarProfile.x, retuned]

/-- `3.99 − 2T = 3.156342`. -/
lemma three_point_nine_nine_sub_two_T : (3.99 : ℝ) - 2 * (T : ℝ) = 3.156342 := by
  norm_num [T]

namespace FarProfile

/-- The data hypotheses used above hold for both profiles of the corpus, and `2x < 3.156342`. -/
lemma corpus_facts {P : FarProfile} (hP : P = inherited ∨ P = retuned) :
    0 < P.c₁ ∧ 0 < P.c₂ ∧ (∀ i, 0 ≤ P.α i) ∧ ∑ i, P.α i = 1 ∧ 2 * P.x < 3.156342 := by
  rcases hP with rfl | rfl
  · exact ⟨inherited_c₁_pos, inherited_c₂_pos, inherited_α_nonneg, inherited_α_sum,
      inherited_two_x_lt⟩
  · exact ⟨retuned_c₁_pos, retuned_c₂_pos, retuned_α_nonneg, retuned_α_sum, retuned_two_x_lt⟩

variable {P : FarProfile}

/-- The printed conditions of [X, Lemma 5.1] for the corpus profiles. -/
theorem profileCondition_corpus (hP : P = inherited ∨ P = retuned) :
    ProfileCondition (fun t => Real.sqrt (P.w0sq t)) P.u P.x :=
  P.profileCondition (corpus_facts hP).2.1

theorem winv_pos_corpus (hP : P = inherited ∨ P = retuned) (lam : ℝ) : 0 < P.winv lam :=
  P.winv_pos (corpus_facts hP).1 (corpus_facts hP).2.1 lam

theorem w_pos_corpus (hP : P = inherited ∨ P = retuned) (lam : ℝ) : 0 < P.w lam :=
  P.w_pos (corpus_facts hP).1 (corpus_facts hP).2.1 lam

theorem w_antitone_corpus (hP : P = inherited ∨ P = retuned) : Antitone P.w :=
  P.w_antitone (corpus_facts hP).1 (corpus_facts hP).2.1

/-- Tail monotonicity for the corpus profiles and `A ≥ 3.156342`. -/
theorem tail_antitone_corpus (hP : P = inherited ∨ P = retuned) {A : ℝ} (hA : 3.156342 ≤ A) :
    Antitone fun lam => Real.exp (-(A * lam)) * P.winv lam :=
  P.tail_antitone (corpus_facts hP).1 (corpus_facts hP).2.1
    (by linarith [(corpus_facts hP).2.2.2.2])

/-- Tail monotonicity for the corpus profiles at exponent `L ≥ 3.99` (`A = L − 2T`):
`λ ↦ e^{−Aλ}/w(λ)` decreases. -/
theorem tail_antitone_of_L (hP : P = inherited ∨ P = retuned) {L : ℝ} (hL : 3.99 ≤ L) :
    Antitone fun lam => Real.exp (-((L - 2 * T) * lam)) / P.w lam :=
  P.tail_antitone' (corpus_facts hP).1 (corpus_facts hP).2.1
    (by linarith [(corpus_facts hP).2.2.2.2, three_point_nine_nine_sub_two_T])

/-- **The far bound for the corpus profiles**: assuming [X, Lemma 5.1], for every `η > 0` and
`q ≥ q₀(η)`, `Σ_χ w(λ(χ)) ≤ (1 + η) V` over any set of characters mod `q` with one chosen zero
each in `σ ≥ 1 − (log log log q)/(3 log q)`, `|t| ≤ 1`. -/
theorem far_bound_corpus (hX : XylourisLemma51) (hP : P = inherited ∨ P = retuned) {η : ℝ}
    (hη : 0 < η) :
    ∃ q₀ : ℕ, ∀ q : ℕ, [NeZero q] → q₀ ≤ q →
      ∀ (s : Finset (DirichletCharacter ℂ q)) (ρ : DirichletCharacter ℂ q → ℂ),
        (∀ χ ∈ s, χ ≠ 1 ∧ DirichletCharacter.LFunction χ (ρ χ) = 0 ∧
          1 - Real.log (Real.log (Real.log q)) / 3 / Real.log q ≤ (ρ χ).re ∧
          |(ρ χ).im| ≤ 1) →
        ∑ χ ∈ s, P.w ((1 - (ρ χ).re) * Real.log q) ≤ (1 + η) * P.V :=
  have h := corpus_facts hP
  P.far_bound hX h.1 h.2.1 h.2.2.1 h.2.2.2.1 hη

end FarProfile

end GradedNear.Kernel
