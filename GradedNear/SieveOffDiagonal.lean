module

public import GradedNear.SieveBasic

/-!
# (C) The off-diagonal of the sieve part: Burgess's bound and Abel summation

For a non-principal `ψ` mod `q`, a cell `[q^t, q^{t'})` with `t > 1/3 + 2ε'`, and the level
`V = q^{(t - 1/3)/2 - ε'}`, open `ν_V(n) = Σ_{d,e ≤ V} ψ_d ψ_e [d ∣ n][e ∣ n]`. Each inner sum
runs over `m ≥ M₀ = q^t/[d,e] ≥ q^{1/3 + 2ε'}`. Abel summation against the pointwise Burgess
bound `|Σ_{M₀ ≤ m ≤ u} ψ(m)| ≪ u^{2/3} q^{1/9 + ε}`, together with
`Σ_{d,e ≤ V} [d,e]^{-2/3} ≪ V^{2/3}`, gives a total of `≪ (log q)^2 q^{ε - 2ε'/3}`.

Formalized route: the sum over `Ico ⌈q^t⌉ ⌈q^{t'}⌉` is rewritten over `Ioc a b`; the square is
opened over `d, e ≤ ⌊V⌋` (`sum_sieveNu_mul`); each inner sum over multiples of `l = [d,e]` is
handled by discrete summation by parts in `n` (`sum_Ioc_by_parts`), with partial sums bounded
by Burgess for any length (`burgess_any_length`, `norm_sum_Ioc_dvd_le`) and
`|W(n) - W(n+1)| ≤ (1 + |s| log(n+1))/n²` from the mean value theorem (`norm_wt_sub_le`),
which gives `≪ q^{1/9+ε} l^{-2/3} (q^t)^{-1/3} (1 + log q)^3` (`norm_T_le`). The lcm sum is
bounded by `9 V^{2/3} (1 + log V)` (`lcm_sum_le`). With `ε = ε'/3` the total is
`≪ (1 + log q)^4 q^{-ε'/3} ≪ q^{-ε'/6}`, so `κ = ε'/6` and `q₀ = 2`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.Moebius

namespace GradedNear

/-! ### The Selberg weights -/

/-- The weights satisfy `|ψ_d| ≤ 1`. -/
lemma abs_grahamWeight_le_one (V : ℝ) (d : ℕ) : |grahamWeight V d| ≤ 1 := by
  unfold grahamWeight
  split_ifs with h
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd
      have hV1 : 1 ≤ V := le_trans hd1 h
      have hVpos : 0 < V := by linarith
      have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV1
      have h1 : 0 ≤ Real.log (V / d) :=
        Real.log_nonneg (by rw [le_div_iff₀ (by linarith)]; linarith)
      have h2 : Real.log (V / d) ≤ Real.log V :=
        Real.log_le_log (by positivity) (div_le_self hVpos.le hd1)
      have hmu : |(μ d : ℝ)| ≤ 1 := by
        have := ArithmeticFunction.abs_moebius_le_one (n := d)
        exact_mod_cast this
      rw [abs_div, abs_mul, abs_of_nonneg h1, abs_of_nonneg hlogV]
      apply div_le_one_of_le₀ _ hlogV
      calc |(μ d : ℝ)| * Real.log (V / d) ≤ 1 * Real.log V := by gcongr
        _ = Real.log V := one_mul _
  · simp

/-- The weight `ψ_d` vanishes for `d > ⌊V⌋`. -/
lemma grahamWeight_eq_zero_of_floor_lt {V : ℝ} {d : ℕ} (h : ⌊V⌋₊ < d) :
    grahamWeight V d = 0 := by
  unfold grahamWeight
  exact ite_eq_right (not_le.2 (Nat.lt_of_floor_lt h))

/-! ### Character sums over intervals and over multiples -/

/-- A sum over the multiples of `l` in `(a, b]`, after the substitution `k = l m`. -/
lemma sum_Ioc_ite_dvd {M : Type*} [AddCommMonoid M] (f : ℕ → M) {l : ℕ} (hl : 0 < l)
    (a b : ℕ) :
    ∑ k ∈ Finset.Ioc a b, (if l ∣ k then f k else 0) =
      ∑ m ∈ Finset.Ioc (a / l) (b / l), f (l * m) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_nbij (fun m => l * m)
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right l m⟩
    · have := (Nat.div_lt_iff_lt_mul hl).1 hm.1
      rw [Nat.mul_comm]; exact this
    · have := (Nat.le_div_iff_mul_le hl).1 hm.2
      rw [Nat.mul_comm]; exact this
  · intro m _ m' _ h
    exact Nat.eq_of_mul_eq_mul_left hl h
  · intro k hk
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hk
    obtain ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩ := hk
    refine ⟨m, ?_, rfl⟩
    simp only [Finset.coe_Ioc, Set.mem_Ioc]
    constructor
    · exact (Nat.div_lt_iff_lt_mul hl).2 (by rw [Nat.mul_comm]; exact h1)
    · exact (Nat.le_div_iff_mul_le hl).2 (by rw [Nat.mul_comm]; exact h2)
  · intro m _
    rfl

/-- A non-principal character sums to zero over `q` consecutive integers. -/
lemma sum_range_char_eq_zero {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (c : ℕ) : ∑ k ∈ Finset.range q, χ ((c + k : ℕ) : ZMod q) = 0 := by
  have : NeZero q := ⟨hq.ne'⟩
  rw [← MulChar.sum_eq_zero_of_ne_one hχ]
  apply Finset.sum_nbij (fun k : ℕ => ((c + k : ℕ) : ZMod q))
  · intro k _; exact Finset.mem_univ _
  · intro k hk k' hk' h
    simp only [Finset.coe_range, Set.mem_Iio] at hk hk'
    simp only [Nat.cast_add, add_right_inj] at h
    rw [ZMod.natCast_eq_natCast_iff'] at h
    rwa [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt hk'] at h
  · intro x _
    refine ⟨(x - (c : ZMod q)).val, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]; exact ZMod.val_lt _
    · simp only [Nat.cast_add, ZMod.natCast_zmod_val]; ring
  · intro k _; rfl

/-- A non-principal character sums to zero over a complete period `(N, N + q]`. -/
lemma sum_Ioc_period_eq_zero {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (N : ℕ) : ∑ n ∈ Finset.Ioc N (N + q), χ n = 0 := by
  rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range]
  rw [show N + q + 1 - (N + 1) = q by omega]
  exact sum_range_char_eq_zero hq χ hχ (N + 1)

/-- Burgess's bound for intervals of any length: split off complete periods, on which the
character sums to zero, and apply the bound for `H ≤ q` to the remainder. -/
lemma burgess_any_length {q : ℕ} (hq : 0 < q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, 1 ≤ H → H ≤ q →
      ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3)) :
    ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  intro N H
  induction H using Nat.strong_induction_on generalizing N with
  | _ H ih =>
    rcases Nat.eq_zero_or_pos H with rfl | hH
    · simp
    by_cases hHq : H ≤ q
    · exact h N H hH hHq
    · replace hHq := Nat.lt_of_not_le hHq
      have hsplit : ∑ n ∈ Finset.Ioc N (N + H), χ n =
          ∑ n ∈ Finset.Ioc N (N + q), χ n +
            ∑ n ∈ Finset.Ioc (N + q) (N + q + (H - q)), χ n := by
        rw [Finset.sum_Ioc_consecutive _ (by omega) (by omega)]
        congr 2; omega
      rw [hsplit, sum_Ioc_period_eq_zero hq χ hχ, zero_add]
      calc _ ≤ K * ((H - q : ℕ) : ℝ) ^ ((2 : ℝ) / 3) := ih (H - q) (by omega) (N + q)
        _ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3) := by
          gcongr
          exact_mod_cast Nat.sub_le H q

/-! ### Summation by parts -/

/-- Discrete summation by parts, with partial sums `P(x) = Σ_{a < k ≤ x} f(k)`. -/
lemma sum_Ioc_by_parts (f W : ℕ → ℂ) (a b : ℕ) :
    ∑ n ∈ Finset.Ioc a b, f n * W n =
      (∑ k ∈ Finset.Ioc a b, f k) * W (b + 1) +
        ∑ n ∈ Finset.Ioc a b, (∑ k ∈ Finset.Ioc a n, f k) * (W n - W (n + 1)) := by
  induction b with
  | zero => simp
  | succ b ih =>
    by_cases hab : a ≤ b
    · simp only [Finset.sum_Ioc_succ_top hab, ih]
      ring
    · have : Finset.Ioc a (b + 1) = ∅ := Finset.Ioc_eq_empty (by omega)
      simp [this]

/-- A harmonic-sum bound. -/
lemma sum_Ioc_inv_le (a b : ℕ) : ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n ≤ 1 + Real.log b := by
  calc ∑ n ∈ Finset.Ioc a b, (1 : ℝ) / n ≤ ∑ n ∈ Finset.Ioc 0 b, (1 : ℝ) / n := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro x hx
          simp only [Finset.mem_Ioc] at hx ⊢
          omega
        · intros; positivity
    _ = (harmonic b : ℝ) := by
        rw [harmonic_eq_sum_Icc, show Finset.Ioc 0 b = Finset.Icc 1 b by ext; simp; omega]
        push_cast
        simp [one_div]
    _ ≤ 1 + Real.log b := harmonic_le_one_add_log b

/-! ### The weight `W(n) = log n · n^{-s}` -/

/-- The weight `W(n) = log n · n^{-s}`. -/
noncomputable def wt (s : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) * (n : ℂ) ^ (-s)

/-- `|W(n)| ≤ log n / n` for `Re s ≥ 1`. -/
lemma norm_wt_le (s : ℂ) (hs : 1 ≤ s.re) (n : ℕ) : ‖wt s n‖ ≤ Real.log n / n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [wt]
  · unfold wt
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn]
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
    rw [Complex.norm_real, Real.norm_of_nonneg hlog, div_eq_mul_inv]
    gcongr
    rw [Complex.neg_re]
    calc (n:ℝ) ^ (-s.re) ≤ (n:ℝ) ^ (-1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) (by linarith)
      _ = (n:ℝ)⁻¹ := Real.rpow_neg_one _

/-- `W(n) = G(log n)` with `G(u) = u e^{-su}`. -/
lemma wt_eq_exp (s : ℂ) {n : ℕ} (hn : 0 < n) :
    wt s n = (Real.log n : ℂ) * cexp ((Real.log n : ℂ) * (-s)) := by
  unfold wt
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn.ne'), ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg n)]

/-- `G'(u) = e^{-su} (1 - s u)`. -/
lemma hasDerivAt_G (s : ℂ) (u : ℝ) :
    HasDerivAt (fun u : ℝ => (u : ℂ) * cexp ((u : ℂ) * (-s)))
      (cexp ((u : ℂ) * (-s)) * (1 - u * s)) u := by
  have h1 : HasDerivAt (fun u : ℝ => (u : ℂ)) 1 u := by
    simpa using (hasDerivAt_id u).ofReal_comp
  have h2 : HasDerivAt (fun u : ℝ => (u : ℂ) * (-s)) (1 * (-s)) u := h1.mul_const (-s)
  have h3 : HasDerivAt (fun u : ℝ => cexp ((u : ℂ) * (-s)))
      (cexp ((u : ℂ) * (-s)) * (1 * (-s))) u := h2.cexp
  have h4 := h1.mul h3
  convert h4 using 1
  ring

/-- `|W(n) - W(n+1)| ≤ (1 + |s| log(n+1)) / n²` for `Re s ≥ 1`, by the mean value theorem
applied to `G` on `[log n, log(n+1)]`. -/
lemma norm_wt_sub_le (s : ℂ) (hs : 1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖wt s n - wt s (n + 1)‖ ≤ (1 + ‖s‖ * Real.log (n + 1)) / (n : ℝ) ^ 2 := by
  set G : ℝ → ℂ := fun u => (u : ℂ) * cexp ((u : ℂ) * (-s)) with hG
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hwn : wt s n = G (Real.log n) := wt_eq_exp s hn
  have hwn1 : wt s (n + 1) = G (Real.log ((n:ℝ) + 1)) := by
    rw [wt_eq_exp s (Nat.succ_pos n)]; push_cast; rfl
  set u₀ := Real.log n with hu₀
  set u₁ := Real.log ((n:ℝ) + 1) with hu₁
  have hu : u₀ ≤ u₁ := Real.log_le_log hn0 (by linarith)
  have hu0 : 0 ≤ u₀ := Real.log_nonneg (by exact_mod_cast hn)
  have hbound : ∀ u ∈ Set.Icc u₀ u₁,
      ‖cexp ((u : ℂ) * (-s)) * (1 - u * s)‖ ≤ (1 + ‖s‖ * u₁) / n := by
    intro u hu'
    obtain ⟨hu'0, hu'1⟩ := hu'
    have hu'nn : 0 ≤ u := le_trans hu0 hu'0
    rw [norm_mul, Complex.norm_exp, div_eq_mul_inv, mul_comm]
    have e1 : ((u : ℂ) * (-s)).re = -(u * s.re) := by
      rw [Complex.re_ofReal_mul, Complex.neg_re]; ring
    rw [e1]
    have e2 : Real.exp (-(u * s.re)) ≤ (n:ℝ)⁻¹ := by
      calc Real.exp (-(u * s.re)) ≤ Real.exp (-u₀) := by
            apply Real.exp_le_exp.2
            nlinarith
        _ = (n:ℝ)⁻¹ := by rw [Real.exp_neg, hu₀, Real.exp_log hn0]
    have e3 : ‖1 - (u:ℂ) * s‖ ≤ 1 + ‖s‖ * u₁ := by
      calc ‖1 - (u:ℂ) * s‖ ≤ ‖(1:ℂ)‖ + ‖(u:ℂ) * s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ * u := by
            rw [norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu'nn, mul_comm]
        _ ≤ 1 + ‖s‖ * u₁ := by gcongr
    have hu₁0 : 0 ≤ u₁ := le_trans hu0 hu
    exact mul_le_mul e3 e2 (by positivity) (by positivity)
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := G) (f' := fun u => cexp ((u : ℂ) * (-s)) * (1 - u * s)) (s := Set.Icc u₀ u₁)
    (C := (1 + ‖s‖ * u₁) / n)
    (fun u _ => (hasDerivAt_G s u).hasDerivWithinAt) hbound
    (convex_Icc u₀ u₁) (Set.left_mem_Icc.2 hu) (Set.right_mem_Icc.2 hu)
  have hdiff : u₁ - u₀ ≤ 1 / n := by
    have h := Real.log_le_sub_one_of_pos (x := ((n:ℝ) + 1) / n) (by positivity)
    rw [Real.log_div (by positivity) hn0.ne'] at h
    have : ((n:ℝ) + 1) / n - 1 = 1 / n := by field_simp; ring
    linarith
  rw [hwn, hwn1, norm_sub_rev]
  calc ‖G u₁ - G u₀‖ ≤ (1 + ‖s‖ * u₁) / n * ‖u₁ - u₀‖ := key
    _ ≤ (1 + ‖s‖ * u₁) / n * (1 / n) := by
        have hC0 : 0 ≤ (1 + ‖s‖ * u₁) / n :=
          div_nonneg (add_nonneg zero_le_one (mul_nonneg (norm_nonneg _) (le_trans hu0 hu)))
            hn0.le
        apply mul_le_mul_of_nonneg_left _ hC0
        rw [Real.norm_of_nonneg (by linarith)]
        exact hdiff
    _ = (1 + ‖s‖ * u₁) / (n:ℝ) ^ 2 := by ring

/-! ### The bound for one pair `(d, e)` -/

/-- `(x/l)^{2/3} ≤ l^{-2/3} c^{-1/3} x` for `0 < c ≤ x`. -/
lemma rpow_two_thirds_div_le {x l c : ℝ} (hc : 0 < c) (hcx : c ≤ x) (hl : 0 < l) :
    (x / l) ^ ((2 : ℝ) / 3) ≤ l ^ (-((2 : ℝ) / 3)) * c ^ (-((1 : ℝ) / 3)) * x := by
  have hx : 0 < x := lt_of_lt_of_le hc hcx
  rw [Real.div_rpow hx.le hl.le, div_eq_mul_inv, ← Real.rpow_neg hl.le]
  have h1 : x ^ ((2 : ℝ) / 3) = x * x ^ (-((1 : ℝ) / 3)) := by
    rw [show (2 : ℝ) / 3 = 1 + (-((1 : ℝ) / 3)) by norm_num, Real.rpow_add hx, Real.rpow_one]
  rw [h1]
  have h2 : x ^ (-((1 : ℝ) / 3)) ≤ c ^ (-((1 : ℝ) / 3)) :=
    Real.rpow_le_rpow_of_nonpos hc hcx (by norm_num)
  have h3 : 0 ≤ l ^ (-((2 : ℝ) / 3)) := Real.rpow_nonneg hl.le _
  calc x * x ^ (-((1 : ℝ) / 3)) * l ^ (-((2 : ℝ) / 3))
      ≤ x * c ^ (-((1 : ℝ) / 3)) * l ^ (-((2 : ℝ) / 3)) := by gcongr
    _ = l ^ (-((2 : ℝ) / 3)) * c ^ (-((1 : ℝ) / 3)) * x := by ring

/-- Partial sums of `χ` over the multiples of `l` in `(a, x]`, from Burgess's bound. -/
lemma norm_sum_Ioc_dvd_le {q : ℕ} (χ : DirichletCharacter ℂ q) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3))
    {l : ℕ} (hl : 0 < l) (a x : ℕ) :
    ‖∑ k ∈ Finset.Ioc a x, (if l ∣ k then χ k else 0)‖ ≤
      K * ((x : ℝ) / l) ^ ((2 : ℝ) / 3) := by
  rw [sum_Ioc_ite_dvd (f := fun k => χ k) hl]
  simp only [Nat.cast_mul, map_mul]
  rw [← Finset.mul_sum, norm_mul]
  have hχl : ‖χ (l : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  by_cases hax : a / l ≤ x / l
  · obtain ⟨H, hH⟩ : ∃ H, x / l = a / l + H := ⟨x / l - a / l, by omega⟩
    rw [hH]
    have hHx : (H : ℝ) ≤ (x : ℝ) / l := by
      calc (H : ℝ) ≤ ((x / l : ℕ) : ℝ) := by
            exact_mod_cast (show H ≤ x / l by rw [hH]; exact Nat.le_add_left _ _)
        _ ≤ (x : ℝ) / l := Nat.cast_div_le
    calc ‖χ (l : ZMod q)‖ * ‖∑ m ∈ Finset.Ioc (a / l) (a / l + H), χ m‖
        ≤ 1 * (K * (H : ℝ) ^ ((2 : ℝ) / 3)) := by
          gcongr
          exact h _ _
      _ ≤ K * ((x : ℝ) / l) ^ ((2 : ℝ) / 3) := by
          rw [one_mul]
          gcongr
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, norm_zero, mul_zero]
    positivity

/-- The inner sum for one `l = [d, e]`: by summation by parts against the partial sums,
`|Σ_{a < n ≤ b, l ∣ n} χ(n) W(n)| ≤ K l^{-2/3} (a+1)^{-1/3} Λ`, where
`Λ = log(b+1) + (1 + |s| log(b+1))(1 + log(b+1))`. -/
lemma norm_T_le {q : ℕ} (χ : DirichletCharacter ℂ q) {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ K * (H : ℝ) ^ ((2 : ℝ) / 3))
    (s : ℂ) (hs : 1 ≤ s.re) {l : ℕ} (hl : 0 < l) (a b : ℕ) :
    ‖∑ n ∈ Finset.Ioc a b, (if l ∣ n then χ n * wt s n else 0)‖ ≤
      K * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) *
        (Real.log (b + 1) + (1 + ‖s‖ * Real.log (b + 1)) * (1 + Real.log (b + 1))) := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  have ha1 : (0 : ℝ) < (a : ℝ) + 1 := by positivity
  have hE0 : 0 ≤ K * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) := by
    positivity
  have hL0 : 0 ≤ Real.log ((b : ℝ) + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg b : (0:ℝ) ≤ b)])
  generalize hE : K * (l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) = E at hE0
  generalize hL : Real.log ((b : ℝ) + 1) = L at hL0
  have hsum : ∑ n ∈ Finset.Ioc a b, (if l ∣ n then χ n * wt s n else 0) =
      ∑ n ∈ Finset.Ioc a b, (fun n => if l ∣ n then χ n else 0) n * wt s n := by
    apply Finset.sum_congr rfl
    intro n _
    by_cases hd : l ∣ n <;> simp [hd]
  rw [hsum, sum_Ioc_by_parts]
  have hkey : ∀ x : ℕ, a < x →
      ‖∑ k ∈ Finset.Ioc a x, (fun n => if l ∣ n then χ n else 0) k‖ ≤ E * x := by
    intro x hx
    have hcx : (a : ℝ) + 1 ≤ x := by exact_mod_cast hx
    calc ‖∑ k ∈ Finset.Ioc a x, (fun n => if l ∣ n then χ n else 0) k‖
        ≤ K * ((x : ℝ) / l) ^ ((2 : ℝ) / 3) := norm_sum_Ioc_dvd_le χ hK h hl a x
      _ ≤ K * ((l : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * x) := by
          gcongr
          exact rpow_two_thirds_div_le ha1 hcx hlpos
      _ = E * x := by rw [← hE]; ring
  have hΛ0 : 0 ≤ L + (1 + ‖s‖ * L) * (1 + L) :=
    add_nonneg hL0 (mul_nonneg (by nlinarith [norm_nonneg s]) (by linarith))
  rcases le_or_gt b a with hab | hab
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp only [Finset.sum_empty, zero_mul, zero_add, norm_zero]
    exact mul_nonneg hE0 hΛ0
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  -- the boundary term
  have hT1 : ‖(∑ k ∈ Finset.Ioc a b, (fun n => if l ∣ n then χ n else 0) k) * wt s (b + 1)‖ ≤
      E * L := by
    rw [norm_mul]
    have hw := norm_wt_le s hs (b + 1)
    push_cast at hw
    rw [hL] at hw
    calc ‖∑ k ∈ Finset.Ioc a b, (fun n => if l ∣ n then χ n else 0) k‖ * ‖wt s (b + 1)‖
        ≤ (E * b) * (L / ((b : ℝ) + 1)) :=
          mul_le_mul (hkey b hab) hw (norm_nonneg _) (mul_nonneg hE0 hb0.le)
      _ = E * L * (b / ((b : ℝ) + 1)) := by ring
      _ ≤ E * L * 1 := by
          apply mul_le_mul_of_nonneg_left _ (mul_nonneg hE0 hL0)
          rw [div_le_one (by positivity)]
          linarith
      _ = E * L := mul_one _
  -- the interior terms
  have hT2 : ∀ n ∈ Finset.Ioc a b,
      ‖(∑ k ∈ Finset.Ioc a n, (fun n => if l ∣ n then χ n else 0) k) *
        (wt s n - wt s (n + 1))‖ ≤ E * (1 + ‖s‖ * L) * (1 / (n : ℝ)) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn1 : 1 ≤ n := by omega
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_mul]
    have hlog : Real.log ((n : ℝ) + 1) ≤ L := by
      rw [← hL]
      apply Real.log_le_log (by positivity)
      have : (n : ℝ) ≤ b := by exact_mod_cast hn.2
      linarith
    have hw : ‖wt s n - wt s (n + 1)‖ ≤ (1 + ‖s‖ * L) / (n : ℝ) ^ 2 := by
      refine (norm_wt_sub_le s hs hn1).trans ?_
      gcongr
    calc ‖∑ k ∈ Finset.Ioc a n, (fun n => if l ∣ n then χ n else 0) k‖ *
          ‖wt s n - wt s (n + 1)‖
        ≤ (E * n) * ((1 + ‖s‖ * L) / (n : ℝ) ^ 2) :=
          mul_le_mul (hkey n hn.1) hw (norm_nonneg _) (mul_nonneg hE0 hn0.le)
      _ = E * (1 + ‖s‖ * L) * (1 / (n : ℝ)) := by field_simp
  have hharm : ∑ n ∈ Finset.Ioc a b, (1 / (n : ℝ)) ≤ 1 + L := by
    calc ∑ n ∈ Finset.Ioc a b, (1 / (n : ℝ)) ≤ 1 + Real.log b := sum_Ioc_inv_le a b
      _ ≤ 1 + L := by
          rw [← hL]
          gcongr
          linarith
  calc ‖(∑ k ∈ Finset.Ioc a b, (fun n => if l ∣ n then χ n else 0) k) * wt s (b + 1) +
        ∑ n ∈ Finset.Ioc a b, (∑ k ∈ Finset.Ioc a n, (fun n => if l ∣ n then χ n else 0) k) *
          (wt s n - wt s (n + 1))‖
      ≤ ‖(∑ k ∈ Finset.Ioc a b, (fun n => if l ∣ n then χ n else 0) k) * wt s (b + 1)‖ +
        ∑ n ∈ Finset.Ioc a b, ‖(∑ k ∈ Finset.Ioc a n, (fun n => if l ∣ n then χ n else 0) k) *
          (wt s n - wt s (n + 1))‖ :=
        (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ E * L + ∑ n ∈ Finset.Ioc a b, E * (1 + ‖s‖ * L) * (1 / (n : ℝ)) :=
        add_le_add hT1 (Finset.sum_le_sum hT2)
    _ = E * L + E * (1 + ‖s‖ * L) * ∑ n ∈ Finset.Ioc a b, (1 / (n : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ E * L + E * (1 + ‖s‖ * L) * (1 + L) := by
        gcongr
    _ = E * (L + (1 + ‖s‖ * L) * (1 + L)) := by ring

/-! ### The lcm sum -/

/-- `Σ_{j ≤ Y} j^{-2/3} ≤ 3 Y^{1/3}`, by telescoping. -/
lemma sum_rpow_neg_two_thirds_le (Y : ℕ) :
    ∑ j ∈ Finset.Ioc 0 Y, (j : ℝ) ^ (-((2 : ℝ) / 3)) ≤ 3 * (Y : ℝ) ^ ((1 : ℝ) / 3) := by
  induction Y with
  | zero => simp
  | succ Y ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le Y)]
    have hY0 : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y
    have hY1 : (0 : ℝ) < (Y : ℝ) + 1 := by linarith
    have key : ((Y : ℝ) + 1) ^ (-((2 : ℝ) / 3)) ≤
        3 * (((Y : ℝ) + 1) ^ ((1 : ℝ) / 3) - (Y : ℝ) ^ ((1 : ℝ) / 3)) := by
      have ha3 : (((Y : ℝ) + 1) ^ ((1 : ℝ) / 3)) ^ 3 = (Y : ℝ) + 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY1.le]; norm_num
      have hb3 : ((Y : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (Y : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hY0]; norm_num
      have hlhs : ((Y : ℝ) + 1) ^ (-((2 : ℝ) / 3)) = 1 / (((Y : ℝ) + 1) ^ ((1 : ℝ) / 3)) ^ 2 := by
        rw [Real.rpow_neg hY1.le, ← Real.rpow_natCast, ← Real.rpow_mul hY1.le, one_div]
        norm_num
      have ha0 : 0 < ((Y : ℝ) + 1) ^ ((1 : ℝ) / 3) := Real.rpow_pos_of_pos hY1 _
      have hb0 : 0 ≤ (Y : ℝ) ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hY0 _
      have hba : (Y : ℝ) ^ ((1 : ℝ) / 3) ≤ ((Y : ℝ) + 1) ^ ((1 : ℝ) / 3) :=
        Real.rpow_le_rpow hY0 (by linarith) (by norm_num)
      rw [hlhs]
      generalize ((Y : ℝ) + 1) ^ ((1 : ℝ) / 3) = a at *
      generalize (Y : ℝ) ^ ((1 : ℝ) / 3) = b at *
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hba) (sub_nonneg.2 hba))
        (by positivity : (0 : ℝ) ≤ 2 * a + b)]
    push_cast
    linarith

/-- `[d, e]^{-2/3} = (d, e)^{2/3} d^{-2/3} e^{-2/3}`. -/
lemma lcm_rpow_eq {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) =
      ((Nat.gcd d e : ℕ) : ℝ) ^ ((2 : ℝ) / 3) *
        ((d : ℝ) ^ (-((2 : ℝ) / 3)) * (e : ℝ) ^ (-((2 : ℝ) / 3))) := by
  have hg : (0 : ℝ) < (Nat.gcd d e : ℕ) := by exact_mod_cast Nat.gcd_pos_of_pos_left e hd
  have hl : (0 : ℝ) < (Nat.lcm d e : ℕ) := by exact_mod_cast Nat.lcm_pos hd he
  have hprod : ((Nat.gcd d e : ℕ) : ℝ) * (Nat.lcm d e : ℕ) = (d : ℝ) * e := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have h1 : ((d : ℝ) * e) ^ (-((2 : ℝ) / 3)) =
      (d : ℝ) ^ (-((2 : ℝ) / 3)) * (e : ℝ) ^ (-((2 : ℝ) / 3)) :=
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  rw [← h1, ← hprod, Real.mul_rpow hg.le hl.le, ← mul_assoc, ← Real.rpow_add hg]
  norm_num

/-- `Σ_{d ≤ K, g ∣ d} d^{-2/3} ≤ 3 K^{1/3} / g`. -/
lemma sum_dvd_rpow_le (K : ℕ) {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ Finset.Ioc 0 K, (if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0) ≤
      3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ := by
  rw [sum_Ioc_ite_dvd (f := fun d => (d : ℝ) ^ (-((2 : ℝ) / 3))) hg, Nat.zero_div]
  have hg0 : (0 : ℝ) < g := by exact_mod_cast hg
  simp only [Nat.cast_mul]
  have hsplit : ∀ m ∈ Finset.Ioc 0 (K / g), ((g : ℝ) * m) ^ (-((2 : ℝ) / 3)) =
      (g : ℝ) ^ (-((2 : ℝ) / 3)) * (m : ℝ) ^ (-((2 : ℝ) / 3)) :=
    fun m _ => Real.mul_rpow hg0.le (Nat.cast_nonneg _)
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum]
  have hgg : (g : ℝ) ^ (-((2 : ℝ) / 3)) / (g : ℝ) ^ ((1 : ℝ) / 3) = (g : ℝ)⁻¹ := by
    rw [← Real.rpow_sub hg0, show (-((2 : ℝ) / 3) - 1 / 3) = -1 by norm_num, Real.rpow_neg_one]
  calc (g : ℝ) ^ (-((2 : ℝ) / 3)) * ∑ m ∈ Finset.Ioc 0 (K / g), (m : ℝ) ^ (-((2 : ℝ) / 3))
      ≤ (g : ℝ) ^ (-((2 : ℝ) / 3)) * (3 * ((K : ℝ) / g) ^ ((1 : ℝ) / 3)) := by
        gcongr
        calc _ ≤ 3 * ((K / g : ℕ) : ℝ) ^ ((1 : ℝ) / 3) := sum_rpow_neg_two_thirds_le _
          _ ≤ 3 * ((K : ℝ) / g) ^ ((1 : ℝ) / 3) := by
              gcongr
              exact Nat.cast_div_le
    _ = 3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ := by
        rw [Real.div_rpow (Nat.cast_nonneg _) hg0.le, ← hgg]
        ring

/-- `Σ_{d, e ≤ K} [d, e]^{-2/3} ≤ 9 K^{2/3} (1 + log K)`. -/
lemma lcm_sum_le (K : ℕ) :
    ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤
      9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log K) := by
  let F : ℕ → ℕ → ℝ := fun g d => if g ∣ d then (d : ℝ) ^ (-((2 : ℝ) / 3)) else 0
  have hF0 : ∀ g d, 0 ≤ F g d := by
    intro g d
    simp only [F]
    split_ifs <;> positivity
  let X : ℕ → ℕ → ℕ → ℝ := fun g d e => (g : ℝ) ^ ((2 : ℝ) / 3) * (F g d * F g e)
  have hX0 : ∀ g d e, 0 ≤ X g d e := fun g d e =>
    mul_nonneg (by positivity) (mul_nonneg (hF0 g d) (hF0 g e))
  have h1 : ∀ d ∈ Finset.Ioc 0 K, ∀ e ∈ Finset.Ioc 0 K,
      ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) ≤ ∑ g ∈ Finset.Ioc 0 K, X g d e := by
    intro d hd e he
    rw [Finset.mem_Ioc] at hd he
    have hgS : Nat.gcd d e ∈ Finset.Ioc 0 K := by
      rw [Finset.mem_Ioc]
      exact ⟨Nat.gcd_pos_of_pos_left e hd.1, le_trans (Nat.gcd_le_left e hd.1) hd.2⟩
    have hval : ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) = X (Nat.gcd d e) d e := by
      rw [lcm_rpow_eq hd.1 he.1]
      simp only [X, F, Nat.gcd_dvd_left d e, Nat.gcd_dvd_right d e, ite_true]
    rw [hval]
    exact Finset.single_le_sum (f := fun g => X g d e) (fun g _ => hX0 g d e) hgS
  have hswap : ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K, X g d e =
      ∑ g ∈ Finset.Ioc 0 K, ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e := by
    calc ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K, X g d e
        = ∑ d ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e := by
          apply Finset.sum_congr rfl
          intro d _
          exact Finset.sum_comm
      _ = ∑ g ∈ Finset.Ioc 0 K, ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e :=
          Finset.sum_comm
  have hfactor : ∀ g, ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, X g d e =
      (g : ℝ) ^ ((2 : ℝ) / 3) *
        ((∑ d ∈ Finset.Ioc 0 K, F g d) * (∑ e ∈ Finset.Ioc 0 K, F g e)) := by
    intro g
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.mul_sum]
  have hK13 : ((K : ℝ) ^ ((1 : ℝ) / 3)) * ((K : ℝ) ^ ((1 : ℝ) / 3)) =
      (K : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_add' (Nat.cast_nonneg _) (by norm_num)]
    norm_num
  calc ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3))
      ≤ ∑ d ∈ Finset.Ioc 0 K, ∑ e ∈ Finset.Ioc 0 K, ∑ g ∈ Finset.Ioc 0 K, X g d e :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => h1 d hd e he
    _ = ∑ g ∈ Finset.Ioc 0 K, (g : ℝ) ^ ((2 : ℝ) / 3) *
          ((∑ d ∈ Finset.Ioc 0 K, F g d) * (∑ e ∈ Finset.Ioc 0 K, F g e)) := by
        rw [hswap]
        exact Finset.sum_congr rfl fun g _ => hfactor g
    _ ≤ ∑ g ∈ Finset.Ioc 0 K, 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 / (g : ℝ)) := by
        apply Finset.sum_le_sum
        intro g hg
        have hg1' : 0 < g := (Finset.mem_Ioc.1 hg).1
        have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg1'
        have hg0 : (0 : ℝ) < g := by linarith
        have hU : ∑ d ∈ Finset.Ioc 0 K, F g d ≤ 3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹ :=
          sum_dvd_rpow_le K hg1'
        have hU0 : 0 ≤ ∑ d ∈ Finset.Ioc 0 K, F g d := Finset.sum_nonneg fun d _ => hF0 g d
        have hgg : (g : ℝ) ^ ((2 : ℝ) / 3) * (g : ℝ)⁻¹ ≤ 1 := by
          rw [mul_inv_le_iff₀ hg0, one_mul]
          calc (g : ℝ) ^ ((2 : ℝ) / 3) ≤ (g : ℝ) ^ (1 : ℝ) :=
                Real.rpow_le_rpow_of_exponent_le hg1 (by norm_num)
            _ = g := Real.rpow_one _
        calc (g : ℝ) ^ ((2 : ℝ) / 3) *
              ((∑ d ∈ Finset.Ioc 0 K, F g d) * (∑ e ∈ Finset.Ioc 0 K, F g e))
            ≤ (g : ℝ) ^ ((2 : ℝ) / 3) * ((3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹) *
                (3 * (K : ℝ) ^ ((1 : ℝ) / 3) * (g : ℝ)⁻¹)) :=
              mul_le_mul_of_nonneg_left (mul_self_le_mul_self hU0 hU) (by positivity)
          _ = 9 * ((K : ℝ) ^ ((1 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 3)) *
                ((g : ℝ) ^ ((2 : ℝ) / 3) * (g : ℝ)⁻¹) * (g : ℝ)⁻¹ := by ring
          _ ≤ 9 * ((K : ℝ) ^ ((1 : ℝ) / 3) * (K : ℝ) ^ ((1 : ℝ) / 3)) * 1 * (g : ℝ)⁻¹ := by
              gcongr
          _ = 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 / (g : ℝ)) := by rw [hK13]; ring
    _ = 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * ∑ g ∈ Finset.Ioc 0 K, 1 / (g : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ 9 * (K : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log K) := by
        gcongr
        exact sum_Ioc_inv_le 0 K

/-! ### Opening the square -/

/-- `Σ_{d ∣ n} ψ_d = Σ_{d ≤ ⌊V⌋} [d ∣ n] ψ_d` for `n ≠ 0`. -/
lemma sum_divisors_grahamWeight (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ d ∈ n.divisors, grahamWeight V d =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, (if d ∣ n then grahamWeight V d else 0) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_subset
  · intro d hd
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hd
    exact Nat.mem_divisors.2 ⟨hd.2, hn⟩
  · intro d hd hnot
    apply grahamWeight_eq_zero_of_floor_lt
    simp only [Finset.mem_filter, Finset.mem_Ioc, not_and] at hnot
    by_contra hle
    exact hnot ⟨Nat.pos_of_mem_divisors hd, not_lt.1 hle⟩ (Nat.dvd_of_mem_divisors hd)

/-- `ν_V(n) = Σ_{d, e ≤ ⌊V⌋} [[d, e] ∣ n] ψ_d ψ_e` for `n ≠ 0`. -/
lemma sieveNu_eq (V : ℝ) {n : ℕ} (hn : n ≠ 0) :
    sieveNu V n = ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
      (if Nat.lcm d e ∣ n then grahamWeight V d * grahamWeight V e else 0) := by
  unfold sieveNu
  rw [sum_divisors_grahamWeight V hn, sq, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  by_cases hd : d ∣ n <;> by_cases he : e ∣ n <;> simp [hd, he, Nat.lcm_dvd_iff]

/-- Opening the square and swapping the sums. -/
lemma sum_sieveNu_mul (V : ℝ) (R : Finset ℕ) (hR : ∀ n ∈ R, n ≠ 0) (F : ℕ → ℂ) :
    ∑ n ∈ R, (sieveNu V n : ℂ) * F n =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ R, (if Nat.lcm d e ∣ n then F n else 0) := by
  have hpt : ∀ n ∈ R, (sieveNu V n : ℂ) * F n =
      ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          (if Nat.lcm d e ∣ n then F n else 0) := by
    intro n hn
    rw [sieveNu_eq V (hR n hn), Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d _
    rw [Complex.ofReal_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro e _
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hpt, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]

/-! ### Assembly -/

/-- Collecting the logarithmic factors. -/
lemma Lambda_bound {L σ c P : ℝ} (hL0 : 0 ≤ L) (hL : L ≤ c * P) (hσ0 : 0 ≤ σ)
    (hσ : σ ≤ 2 * P) (hc : 1 ≤ c) (hP : 1 ≤ P) :
    L + (1 + σ * L) * (1 + L) ≤ 7 * c ^ 2 * P ^ 3 := by
  have hcP : 1 ≤ c * P := by nlinarith
  have h0 : 1 ≤ c * P * P := by nlinarith
  have h1 : σ * L ≤ 2 * P * (c * P) := mul_le_mul hσ hL hL0 (by linarith)
  have h2 : 1 + σ * L ≤ 3 * (c * P) * P := by nlinarith
  have h3 : 1 + L ≤ 2 * (c * P) := by linarith
  have h4 : (1 + σ * L) * (1 + L) ≤ (3 * (c * P) * P) * (2 * (c * P)) :=
    mul_le_mul h2 h3 (by linarith) (by nlinarith)
  have h5 : L ≤ (c * P) * (c * P) * P := by nlinarith
  nlinarith

theorem sieve_offdiag (hBur : BurgessBound) {ε' tmax : ℝ} (hε' : 0 < ε') :
    ∃ C κ : ℝ, 0 < κ ∧ ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, 1 / 3 + 2 * ε' < t → t ≤ t' → t' ≤ tmax → 0 ≤ β → β ≤ 1 →
        |τ| ≤ Real.log q →
        ‖∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu ((q : ℝ) ^ ((t - 1 / 3) / 2 - ε')) n : ℂ) * ψ n * (Real.log n : ℂ) *
              (n : ℂ) ^ (-((1 + β : ℝ) + (τ : ℂ) * I))‖ ≤ C * (q : ℝ) ^ (-κ) := by
  obtain ⟨CB, hCB⟩ := hBur (ε' / 3) (by positivity)
  obtain ⟨C₀, hCBC₀, hC₀0⟩ : ∃ C₀ : ℝ, CB ≤ C₀ ∧ 0 ≤ C₀ :=
    ⟨max CB 0, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨c₁, hc₁1, hc₁t⟩ : ∃ c₁ : ℝ, 1 ≤ c₁ ∧ tmax ≤ c₁ :=
    ⟨max 1 tmax, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 1 + 24 / ε' := ⟨_, rfl⟩
  have hM1 : 1 ≤ M := by
    rw [hM]
    have : 0 < 24 / ε' := by positivity
    linarith
  refine ⟨C₀ * (63 * c₁ ^ 3 * M ^ 4), ε' / 6, by positivity, 2, ?_⟩
  intro q hq ψ hψ t t' β τ ht htt' ht'max hβ0 hβ1 hτ
  have hqpos : 0 < q := by omega
  have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hℓ0 : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht0 : 0 < t := by linarith
  -- Burgess's bound for intervals of any length
  have hKq0 : 0 ≤ C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) := by positivity
  have hBurq : ∀ N H : ℕ, ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
      C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
    apply burgess_any_length hqpos ψ hψ hKq0
    intro N H hH1 hHq
    calc _ ≤ CB * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) :=
          hCB q ψ hψ N H hH1 hHq
      _ ≤ C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
          gcongr
  generalize hKq : C₀ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) = Kq at hKq0 hBurq
  -- the exponent `s = 1 + β + iτ`
  have hs : 1 ≤ (((1 + β : ℝ) : ℂ) + (τ : ℂ) * I).re := by
    simp
    linarith
  have hsn : ‖((1 + β : ℝ) : ℂ) + (τ : ℂ) * I‖ ≤ 2 * (1 + Real.log q) := by
    calc ‖((1 + β : ℝ) : ℂ) + (τ : ℂ) * I‖ ≤ ‖((1 + β : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ :=
          norm_add_le _ _
      _ = |1 + β| + |τ| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 2 * (1 + Real.log q) := by
          rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + β)]
          linarith
  generalize hsdef : ((1 + β : ℝ) : ℂ) + (τ : ℂ) * I = s at hs hsn ⊢
  -- the level `V = q^δ`
  have hδ0 : 0 < (t - 1 / 3) / 2 - ε' := by linarith
  generalize hδ : (t - 1 / 3) / 2 - ε' = δ at hδ0 ⊢
  have hV1 : 1 ≤ (q : ℝ) ^ δ := Real.one_le_rpow hq1 hδ0.le
  have hlogV : Real.log ((q : ℝ) ^ δ) = δ * Real.log q := Real.log_rpow hq0 δ
  have hexp : (q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) * ((q : ℝ) ^ t) ^ (-((1 : ℝ) / 3)) *
      ((q : ℝ) ^ δ) ^ ((2 : ℝ) / 3) = (q : ℝ) ^ (-(ε' / 3)) := by
    rw [← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le, ← Real.rpow_add hq0,
      ← Real.rpow_add hq0]
    congr 1
    rw [← hδ]
    ring
  generalize hV : (q : ℝ) ^ δ = V at hV1 hlogV hexp ⊢
  have hA1 : 1 ≤ (q : ℝ) ^ t := Real.one_le_rpow hq1 ht0.le
  have hB1 : 1 ≤ (q : ℝ) ^ t' := Real.one_le_rpow hq1 (by linarith)
  have hlogB : Real.log ((q : ℝ) ^ t') = t' * Real.log q := Real.log_rpow hq0 t'
  generalize hA : (q : ℝ) ^ t = A at hA1 hexp ⊢
  generalize hB : (q : ℝ) ^ t' = B at hB1 hlogB ⊢
  have hA0 : 0 < A := by linarith
  have hB0 : 0 < B := by linarith
  have hN₀ : 1 ≤ ⌈A⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hA0).ne'
  have hN₁ : 1 ≤ ⌈B⌉₊ := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hB0).ne'
  -- rewrite the sum over `Ioc`, and open the square
  have hIco : Finset.Ico ⌈A⌉₊ ⌈B⌉₊ = Finset.Ioc (⌈A⌉₊ - 1) (⌈B⌉₊ - 1) := by
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hsummand : ∀ n : ℕ, (sieveNu V n : ℂ) * ψ n * (Real.log n : ℂ) * (n : ℂ) ^ (-s) =
      (sieveNu V n : ℂ) * (ψ n * wt s n) := by
    intro n
    unfold wt
    ring
  simp_rw [hsummand]
  rw [hIco]
  have hexpand := sum_sieveNu_mul V (Finset.Ioc (⌈A⌉₊ - 1) (⌈B⌉₊ - 1))
    (fun n hn => by simp only [Finset.mem_Ioc] at hn; omega) (fun n => ψ n * wt s n)
  beta_reduce at hexpand
  rw [hexpand]
  have ha1 : ((⌈A⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈A⌉₊ : ℝ) := by
    rw [Nat.cast_sub hN₀, Nat.cast_one]; ring
  have hb1 : ((⌈B⌉₊ - 1 : ℕ) : ℝ) + 1 = (⌈B⌉₊ : ℝ) := by
    rw [Nat.cast_sub hN₁, Nat.cast_one]; ring
  generalize ha : ⌈A⌉₊ - 1 = a at ha1 ⊢
  generalize hb : ⌈B⌉₊ - 1 = b at hb1 ⊢
  -- each `(d, e)` term
  have hT : ∀ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∀ e ∈ Finset.Ioc 0 ⌊V⌋₊,
      ‖((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0)‖ ≤
        Kq * ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) *
          (Real.log (b + 1) + (1 + ‖s‖ * Real.log (b + 1)) * (1 + Real.log (b + 1))) := by
    intro d hd e he
    rw [Finset.mem_Ioc] at hd he
    have hl : 0 < Nat.lcm d e := Nat.lcm_pos hd.1 he.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    calc |grahamWeight V d| * |grahamWeight V e| *
          ‖∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0)‖
        ≤ 1 * 1 * (Kq * ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) *
            ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) *
            (Real.log (b + 1) + (1 + ‖s‖ * Real.log (b + 1)) * (1 + Real.log (b + 1)))) :=
          mul_le_mul (mul_le_mul (abs_grahamWeight_le_one V d) (abs_grahamWeight_le_one V e)
            (abs_nonneg _) zero_le_one) (norm_T_le ψ hKq0 hBurq s hs hl a b) (norm_nonneg _)
            (by norm_num)
      _ = _ := by ring
  -- bounds on the logarithmic factors
  have hL0 : 0 ≤ Real.log ((b : ℝ) + 1) :=
    Real.log_nonneg (by have := (Nat.cast_nonneg b : (0 : ℝ) ≤ b); linarith)
  have hLle : Real.log ((b : ℝ) + 1) ≤ c₁ * (1 + Real.log q) := by
    rw [hb1]
    have h1 : (⌈B⌉₊ : ℝ) ≤ 2 * B := by
      have := Nat.ceil_lt_add_one hB0.le
      linarith
    have h2 : Real.log (⌈B⌉₊ : ℝ) ≤ Real.log (2 * B) :=
      Real.log_le_log (by exact_mod_cast (show 0 < ⌈B⌉₊ by omega)) h1
    rw [Real.log_mul (by norm_num) hB0.ne', hlogB] at h2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (x := 2) (by norm_num)
      linarith
    have h3 : t' * Real.log q ≤ c₁ * Real.log q :=
      mul_le_mul_of_nonneg_right (by linarith) hℓ0
    linarith
  have hK1 : 1 ≤ ⌊V⌋₊ := Nat.floor_pos.2 hV1
  have hlogK0 : 0 ≤ Real.log (⌊V⌋₊ : ℝ) := Real.log_nonneg (by exact_mod_cast hK1)
  have hlogK : 1 + Real.log (⌊V⌋₊ : ℝ) ≤ c₁ * (1 + Real.log q) := by
    have h1 : Real.log (⌊V⌋₊ : ℝ) ≤ Real.log V :=
      Real.log_le_log (by exact_mod_cast hK1) (Nat.floor_le (by linarith))
    rw [hlogV] at h1
    have hδt : δ ≤ c₁ := by rw [← hδ]; linarith
    have h3 : δ * Real.log q ≤ c₁ * Real.log q := mul_le_mul_of_nonneg_right hδt hℓ0
    linarith
  have hK23 : (⌊V⌋₊ : ℝ) ^ ((2 : ℝ) / 3) ≤ V ^ ((2 : ℝ) / 3) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by linarith)) (by norm_num)
  have hA13 : ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) ≤ A ^ (-((1 : ℝ) / 3)) := by
    rw [ha1]
    exact Real.rpow_le_rpow_of_nonpos hA0 (Nat.le_ceil A) (by norm_num)
  have hPq : (1 + Real.log q) ^ 4 ≤ M ^ 4 * (q : ℝ) ^ (ε' / 6) := by
    have hlog := Real.log_le_rpow_div hq0.le (show 0 < ε' / 24 by positivity)
    have hq24 : 1 ≤ (q : ℝ) ^ (ε' / 24) := Real.one_le_rpow hq1 (by positivity)
    have hP : 1 + Real.log q ≤ M * (q : ℝ) ^ (ε' / 24) := by
      rw [hM]
      have : (q : ℝ) ^ (ε' / 24) / (ε' / 24) = 24 / ε' * (q : ℝ) ^ (ε' / 24) := by
        field_simp
      linarith
    have hpow : ((q : ℝ) ^ (ε' / 24)) ^ 4 = (q : ℝ) ^ (ε' / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hq0.le]
      congr 1
      push_cast
      ring
    calc (1 + Real.log q) ^ 4 ≤ (M * (q : ℝ) ^ (ε' / 24)) ^ 4 := by
          gcongr
      _ = M ^ 4 * (q : ℝ) ^ (ε' / 6) := by rw [mul_pow, hpow]
  generalize hLdef : Real.log ((b : ℝ) + 1) = L at hT hL0 hLle
  generalize hPdef : 1 + Real.log q = P at hLle hlogK hsn hPq
  have hP1 : 1 ≤ P := by rw [← hPdef]; linarith
  have hΛ0 : 0 ≤ L + (1 + ‖s‖ * L) * (1 + L) :=
    add_nonneg hL0 (mul_nonneg (by nlinarith [norm_nonneg s]) (by linarith))
  have hΛ : L + (1 + ‖s‖ * L) * (1 + L) ≤ 7 * c₁ ^ 2 * P ^ 3 :=
    Lambda_bound hL0 hLle (norm_nonneg s) hsn hc₁1 hP1
  have hAr0 : 0 ≤ A ^ (-((1 : ℝ) / 3)) := Real.rpow_nonneg hA0.le _
  have hVr0 : 0 ≤ V ^ ((2 : ℝ) / 3) := Real.rpow_nonneg (by linarith) _
  have hc0 : 0 ≤ c₁ := by linarith
  have hP0 : 0 ≤ P := by linarith
  calc ‖∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        ((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0)‖
      ≤ ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        ‖((grahamWeight V d * grahamWeight V e : ℝ) : ℂ) *
          ∑ n ∈ Finset.Ioc a b, (if Nat.lcm d e ∣ n then ψ n * wt s n else 0)‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun d _ => norm_sum_le _ _)
    _ ≤ ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
        Kq * ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) *
          (L + (1 + ‖s‖ * L) * (1 + L)) :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e he => hT d hd e he
    _ = Kq * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * (L + (1 + ‖s‖ * L) * (1 + L)) *
        ∑ d ∈ Finset.Ioc 0 ⌊V⌋₊, ∑ e ∈ Finset.Ioc 0 ⌊V⌋₊,
          ((Nat.lcm d e : ℕ) : ℝ) ^ (-((2 : ℝ) / 3)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e _
        ring
    _ ≤ Kq * ((a : ℝ) + 1) ^ (-((1 : ℝ) / 3)) * (L + (1 + ‖s‖ * L) * (1 + L)) *
        (9 * (⌊V⌋₊ : ℝ) ^ ((2 : ℝ) / 3) * (1 + Real.log ⌊V⌋₊)) :=
        mul_le_mul_of_nonneg_left (lcm_sum_le _)
          (mul_nonneg (mul_nonneg hKq0 (Real.rpow_nonneg (by positivity) _)) hΛ0)
    _ ≤ Kq * A ^ (-((1 : ℝ) / 3)) * (7 * c₁ ^ 2 * P ^ 3) *
        (9 * V ^ ((2 : ℝ) / 3) * (c₁ * P)) := by
        apply mul_le_mul
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hA13 hKq0) hΛ hΛ0
            (mul_nonneg hKq0 hAr0)
        · exact mul_le_mul (mul_le_mul_of_nonneg_left hK23 (by norm_num)) hlogK (by linarith)
            (by positivity)
        · exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by positivity) _))
            (by linarith)
        · exact mul_nonneg (mul_nonneg hKq0 hAr0) (by positivity)
    _ = 63 * c₁ ^ 3 * P ^ 4 * (C₀ * ((q : ℝ) ^ ((1 : ℝ) / 9 + ε' / 3) *
        A ^ (-((1 : ℝ) / 3)) * V ^ ((2 : ℝ) / 3))) := by
        rw [← hKq]
        ring
    _ = 63 * c₁ ^ 3 * P ^ 4 * (C₀ * (q : ℝ) ^ (-(ε' / 3))) := by rw [hexp]
    _ ≤ 63 * c₁ ^ 3 * (M ^ 4 * (q : ℝ) ^ (ε' / 6)) * (C₀ * (q : ℝ) ^ (-(ε' / 3))) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hC₀0 (Real.rpow_nonneg hq0.le _))
        exact mul_le_mul_of_nonneg_left hPq (by positivity)
    _ = C₀ * (63 * c₁ ^ 3 * M ^ 4) * ((q : ℝ) ^ (-(ε' / 3)) * (q : ℝ) ^ (ε' / 6)) := by ring
    _ = C₀ * (63 * c₁ ^ 3 * M ^ 4) * (q : ℝ) ^ (-(ε' / 6)) := by
        rw [← Real.rpow_add hq0]
        congr 2
        ring

end GradedNear
