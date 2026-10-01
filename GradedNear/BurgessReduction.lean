module

public import GradedNear.Defs

/-!
# Burgess's bound: from the printed primitive statement to all non-principal characters

`GradedNear.BurgessBound` (in `GradedNear/Defs.lean`) is Burgess's bound with `r = 3` for every
non-principal Dirichlet character and every `N ≥ 0`. The printed source, [HB, Lemma 2.1, p. 7],
states it for primitive characters and `N ≥ 1` only. `BurgessPrimitive` (in `GradedNear/Defs.lean`)
states the printed form, and this file proves `BurgessPrimitive → BurgessBound`
(`burgessBound_of_primitive`), so that the hypothesis is a statement matching the print.

The reduction is the standard one. If `χ` mod `q` is induced by the primitive `χ*` mod `q*`, then
`χ(n) = χ*(n)` for `(n, q) = 1` and `χ(n) = 0` otherwise, and Möbius inversion gives
`Σ_{N < n ≤ N+H} χ(n) = Σ_{d ∣ q} μ(d) χ*(d) Σ_{⌊N/d⌋ < m ≤ ⌊(N+H)/d⌋} χ*(m)`.
Each inner sum has length at most `H`; complete periods of `χ*` are removed (they vanish since
`χ* ≠ 1`) and the interval is shifted by `q*`, which lands in the printed range `N ≥ 1`,
`1 ≤ H ≤ q*`. Finally `q* ≤ q` and the number of divisors costs `τ(q) ≪_ε q^ε`
(`card_divisors_le_rpow`, proved here).

References: [HB] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least
prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338 (Lemma 2.1 is on
p. 7 of the preprint `literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf`).
-/

@[expose] public section

open Finset
open scoped ArithmeticFunction.Moebius

noncomputable section

namespace GradedNear

/-! ## The divisor bound -/

/-- One prime-power factor of the divisor bound: `a + 1 ≤ M_p (p^ε)^a`, where `M_p = 1` for
`p ≥ K ≥ 2^{1/ε}` and `M_p = max 1 (1/(2^ε - 1))` for `p < K`. -/
private lemma divisor_factor_le {ε : ℝ} (hε : 0 < ε) {K : ℕ} (hK : (2 : ℝ) ^ (1 / ε) ≤ K)
    {p : ℕ} (hp : p.Prime) (a : ℕ) :
    (a : ℝ) + 1 ≤
      (if p < K then max 1 (1 / ((2 : ℝ) ^ ε - 1)) else 1) * ((p : ℝ) ^ ε) ^ a := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  split_ifs with hpK
  · set b : ℝ := (2 : ℝ) ^ ε with hb
    have hb1 : 1 < b := Real.one_lt_rpow (by norm_num) hε
    have hbp : b ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by norm_num) hp2 hε.le
    set M := max 1 (1 / (b - 1)) with hM
    have hM1 : 1 ≤ M := le_max_left _ _
    have hb' : 0 < b - 1 := by linarith
    have hMb : 1 ≤ M * (b - 1) := by
      have h1 : 1 / (b - 1) ≤ M := le_max_right _ _
      calc (1 : ℝ) = 1 / (b - 1) * (b - 1) := by field_simp
        _ ≤ M * (b - 1) := by gcongr
    have hbern : 1 + (a : ℝ) * (b - 1) ≤ b ^ a := by
      have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ b - 1 by linarith) a
      simpa using h
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc (a : ℝ) + 1 ≤ M * (1 + a * (b - 1)) := by
          nlinarith [mul_nonneg ha (sub_nonneg.mpr hMb)]
      _ ≤ M * b ^ a := by gcongr
      _ ≤ M * ((p : ℝ) ^ ε) ^ a := by gcongr
  · have hpK' : K ≤ p := not_lt.mp hpK
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := by
            apply Real.rpow_le_rpow (by positivity) _ hε.le
            exact hK.trans (by exact_mod_cast hpK')
    calc (a : ℝ) + 1 ≤ 2 ^ a := by
          have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 by norm_num) a
          norm_num at h
          linarith
      _ ≤ ((p : ℝ) ^ ε) ^ a := by gcongr
      _ = 1 * ((p : ℝ) ^ ε) ^ a := (one_mul _).symm

/-- The divisor bound `τ(n) ≪_ε n^ε`. -/
theorem card_divisors_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  set K : ℕ := ⌈(2 : ℝ) ^ (1 / ε)⌉₊
  have hK : (2 : ℝ) ^ (1 / ε) ≤ K := Nat.le_ceil _
  set M : ℝ := max 1 (1 / ((2 : ℝ) ^ ε - 1)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  refine ⟨M ^ K, by positivity, fun n hn => ?_⟩
  set g : ℕ → ℝ := fun p => if p < K then M else 1 with hg
  have hτ : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn]
    push_cast
    rfl
  have hn' : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ (n.factorization p) := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [Real.rpow_pow_comm (by positivity)]
  have hgK : ∏ p ∈ n.primeFactors, g p ≤ M ^ K := by
    have h1 : ∏ p ∈ n.primeFactors, g p = M ^ (n.primeFactors.filter (· < K)).card := by
      simp only [hg]
      rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
    rw [h1]
    apply pow_le_pow_right₀ hM1
    calc (n.primeFactors.filter (· < K)).card ≤ (Finset.range K).card := by
          apply Finset.card_le_card
          intro p hp
          simp only [Finset.mem_filter] at hp
          simpa using hp.2
      _ = K := Finset.card_range K
  calc (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := hτ
    _ ≤ ∏ p ∈ n.primeFactors, (g p * ((p : ℝ) ^ ε) ^ (n.factorization p)) := by
        apply Finset.prod_le_prod₀ (fun p _ => by positivity)
        intro p hp
        exact divisor_factor_le hε hK (Nat.prime_of_mem_primeFactors hp) _
    _ = (∏ p ∈ n.primeFactors, g p) * (n : ℝ) ^ ε := by rw [Finset.prod_mul_distrib, hn']
    _ ≤ M ^ K * (n : ℝ) ^ ε := by gcongr

/-! ## Complete periods -/

/-- Summing over `ZMod q` is summing over the residues `0, …, q - 1`. -/
private lemma sum_zmod_eq_sum_range {q : ℕ} [NeZero q] (f : ZMod q → ℂ) :
    ∑ x : ZMod q, f x = ∑ i ∈ range q, f i := by
  refine Finset.sum_nbij' (fun x => x.val) (fun i => (i : ZMod q)) ?_ ?_ ?_ ?_ ?_
  · intro x _
    simpa using ZMod.val_lt x
  · intro i _
    simp
  · intro x _
    simp
  · intro i hi
    exact ZMod.val_cast_of_lt (Finset.mem_range.mp hi)
  · intro x _
    simp

/-- For a function of period `q` on `ℕ`, the sums over `q` consecutive integers agree. -/
private lemma sum_range_add_of_periodic {q : ℕ} (f : ℕ → ℂ) (hf : ∀ n, f (n + q) = f n)
    (a : ℕ) : ∑ i ∈ range q, f (a + i) = ∑ i ∈ range q, f i := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [← ih]
    have h1 : ∑ i ∈ range (q + 1), f (a + i) = ∑ i ∈ range q, f (a + (i + 1)) + f (a + 0) :=
      Finset.sum_range_succ' (fun i => f (a + i)) q
    have h2 : ∑ i ∈ range (q + 1), f (a + i) = ∑ i ∈ range q, f (a + i) + f (a + q) :=
      Finset.sum_range_succ (fun i => f (a + i)) q
    have h3 : f (a + q) = f (a + 0) := by rw [hf, add_zero]
    have h4 : ∑ i ∈ range q, f (a + 1 + i) = ∑ i ∈ range q, f (a + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [add_assoc, add_comm 1 i]
    rw [h4]
    rw [h3] at h2
    exact add_right_cancel (h1.symm.trans h2)

/-- A non-principal character sums to zero over any `q` consecutive integers. -/
private lemma sum_Ioc_period_eq_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (a : ℕ) : ∑ n ∈ Ioc a (a + q), ψ n = 0 := by
  have hper : ∀ n : ℕ, (fun n : ℕ => ψ n) (n + q) = (fun n : ℕ => ψ n) n := by
    intro n
    simp [Nat.cast_add]
  rw [← Finset.Ico_add_one_add_one_eq_Ioc, Finset.sum_Ico_eq_sum_range,
    show a + q + 1 - (a + 1) = q by omega]
  have h := sum_range_add_of_periodic (fun n : ℕ => ψ n) hper (a + 1)
  rw [h, ← sum_zmod_eq_sum_range (fun x => ψ x)]
  exact MulChar.sum_eq_zero_of_ne_one hψ

/-- A non-principal character sums to zero over any `q k` consecutive integers. -/
private lemma sum_Ioc_mul_period_eq_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q)
    (hψ : ψ ≠ 1) (a k : ℕ) : ∑ n ∈ Ioc a (a + q * k), ψ n = 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have e : a + q * (k + 1) = a + q * k + q := by ring
    rw [e, ← Finset.sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a (q * k))
      (Nat.le_add_right (a + q * k) q), ih, zero_add]
    exact sum_Ioc_period_eq_zero ψ hψ _

/-- Shifting an interval by the period does not change the sum of a non-principal character. -/
private lemma sum_Ioc_add_period {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1)
    (a h : ℕ) : ∑ n ∈ Ioc (a + q) (a + q + h), ψ n = ∑ n ∈ Ioc a (a + h), ψ n := by
  have e1 := Finset.sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a q)
    (Nat.le_add_right (a + q) h)
  have e2 := Finset.sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right a h)
    (Nat.le_add_right (a + h) q)
  rw [sum_Ioc_period_eq_zero ψ hψ a, zero_add] at e1
  rw [sum_Ioc_period_eq_zero ψ hψ (a + h), add_zero] at e2
  rw [e1, e2, show a + q + h = a + h + q by ring]

/-- The primitive bound on every interval `(N, N + H]`: complete periods are removed and the
interval is shifted by the modulus, which reaches the printed range `N ≥ 1`, `1 ≤ H ≤ q`. -/
private lemma primitive_bound_all {ε C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ N H : ℕ, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3))
    {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (N H : ℕ) :
    ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
      C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hH : H % q + q * (H / q) = H := Nat.mod_add_div H q
  have hsplit : ∑ n ∈ Ioc N (N + H), ψ n = ∑ n ∈ Ioc (N + q) (N + q + H % q), ψ n := by
    rw [← Finset.sum_Ioc_consecutive (fun n : ℕ => ψ n) (Nat.le_add_right N (H % q))
      (show N + H % q ≤ N + H by omega), show N + H = N + H % q + q * (H / q) by omega,
      sum_Ioc_mul_period_eq_zero ψ hψ, add_zero, sum_Ioc_add_period ψ hψ]
  rw [hsplit]
  have hRHS : 0 ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by positivity
  rcases Nat.eq_zero_or_pos (H % q) with hr | hr
  · rw [hr, add_zero, Finset.Ioc_self, Finset.sum_empty, norm_zero]
    exact hRHS
  · calc ‖∑ n ∈ Ioc (N + q) (N + q + H % q), ψ n‖
        ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * ((H % q : ℕ) : ℝ) ^ ((2 : ℝ) / 3) :=
          hB q hq ψ hprim (N + q) (H % q) (by omega) hr (Nat.mod_lt H hq).le
      _ ≤ C * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
          gcongr
          exact_mod_cast Nat.mod_le H q

/-! ## Reduction to the primitive character -/

/-- A character agrees with its primitive character on integers prime to the level and vanishes
on the others. -/
private lemma apply_eq_ite_primitive {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    χ n = if n.Coprime q then χ.primitiveCharacter n else 0 := by
  split_ifs with h
  · have h' : IsCoprime (n : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr h
    have := χ.primitiveCharacter_apply_of_isCoprime h'
    simpa using this.symm
  · exact χ.map_nonunit (by rwa [ZMod.isUnit_iff_coprime])

/-- `Σ_{d ∣ m} μ(d) = [m = 1]`. -/
private lemma sum_moebius_divisors (m : ℕ) :
    ∑ d ∈ m.divisors, (μ d : ℂ) = if m = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f m) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  have h2 : ∑ d ∈ m.divisors, (μ d : ℂ) = ((∑ d ∈ m.divisors, μ d : ℤ) : ℂ) := by push_cast; rfl
  rw [h2, h]
  split_ifs <;> simp

/-- Möbius inversion over the divisors of the level:
`Σ_{n ∈ s} χ(n) = Σ_{d ∣ q} μ(d) Σ_{n ∈ s, d ∣ n} χ*(n)`. -/
private lemma sum_eq_sum_divisors {q : ℕ} (hq : q ≠ 0) (χ : DirichletCharacter ℂ q)
    (s : Finset ℕ) :
    ∑ n ∈ s, χ n =
      ∑ d ∈ q.divisors, (μ d : ℂ) * ∑ n ∈ s.filter (d ∣ ·), χ.primitiveCharacter n := by
  have key : ∀ n : ℕ, χ n =
      ∑ d ∈ q.divisors, if d ∣ n then (μ d : ℂ) * χ.primitiveCharacter n else 0 := by
    intro n
    rw [← Finset.sum_filter]
    have hfilt : q.divisors.filter (· ∣ n) = (Nat.gcd n q).divisors := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff, ne_eq,
        Nat.gcd_eq_zero_iff, hq, and_false, not_false_eq_true, and_true]
      tauto
    rw [hfilt, ← Finset.sum_mul, sum_moebius_divisors, apply_eq_ite_primitive]
    by_cases h : n.Coprime q
    · rw [ite_eq_left h, ite_eq_left (Nat.coprime_iff_gcd_eq_one.mp h), one_mul]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Nat.coprime_iff_gcd_eq_one.mpr h')),
        zero_mul]
  rw [Finset.sum_congr rfl (fun n _ => key n), Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_filter, Finset.mul_sum]
  simp only [mul_ite, mul_zero]

/-- The multiples of `d` in `(N, N + H]` are the `d m` with `⌊N/d⌋ < m ≤ ⌊(N + H)/d⌋`. -/
private lemma filter_dvd_Ioc {d : ℕ} (hd : 0 < d) (N H : ℕ) :
    (Ioc N (N + H)).filter (d ∣ ·) = (Ioc (N / d) ((N + H) / d)).image (d * ·) := by
  ext n
  simp only [mem_filter, mem_Ioc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨m, rfl⟩⟩
    refine ⟨m, ⟨?_, ?_⟩, rfl⟩
    · rw [Nat.div_lt_iff_lt_mul hd]
      linarith [mul_comm d m]
    · rw [Nat.le_div_iff_mul_le hd]
      linarith [mul_comm d m]
  · rintro ⟨m, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
    · rw [Nat.div_lt_iff_lt_mul hd] at h1
      linarith [mul_comm d m]
    · rw [Nat.le_div_iff_mul_le hd] at h2
      linarith [mul_comm d m]

/-- `Σ_{N < n ≤ N + H, d ∣ n} ψ(n) = ψ(d) Σ_{⌊N/d⌋ < m ≤ ⌊(N + H)/d⌋} ψ(m)`. -/
private lemma sum_filter_dvd_Ioc {q : ℕ} (ψ : DirichletCharacter ℂ q) {d : ℕ} (hd : 0 < d)
    (N H : ℕ) :
    ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), ψ n =
      ψ d * ∑ m ∈ Ioc (N / d) ((N + H) / d), ψ m := by
  rw [filter_dvd_Ioc hd, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  exact map_mul ψ _ _

/-- The number of multiples of `d ≥ 1` in `(N, N + H]` is at most `H`. -/
private lemma div_sub_div_le {d : ℕ} (hd : 0 < d) (N H : ℕ) : (N + H) / d - N / d ≤ H := by
  have h1 : (N + H) / d ≤ (N + H * d) / d :=
    Nat.div_le_div_right (by nlinarith)
  rw [Nat.add_mul_div_right N H hd] at h1
  omega

/-- **Burgess's bound for all non-principal characters** (`BurgessBound`, with `N ≥ 0`) follows
from the printed primitive statement [HB, Lemma 2.1, k = 3] (`BurgessPrimitive`). -/
theorem burgessBound_of_primitive (hB : BurgessPrimitive) : BurgessBound := by
  intro ε hε
  obtain ⟨C₁, hC₁⟩ := hB (ε / 2) (by positivity)
  obtain ⟨C₂, hC₂, hτ⟩ := card_divisors_le_rpow (show 0 < ε / 2 by positivity)
  set C₁' := max C₁ 0 with hC₁'def
  have hC₁'0 : 0 ≤ C₁' := le_max_right _ _
  have hC₁' : ∀ q : ℕ, 1 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ.IsPrimitive →
      ∀ N H : ℕ, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C₁' * (q : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
    intro q hq χ hχ N H hN hH hHq
    refine (hC₁ q hq χ hχ N H hN hH hHq).trans ?_
    gcongr
    exact le_max_left _ _
  refine ⟨C₁' * C₂, ?_⟩
  intro q χ hχ N H hH hHq
  have hq1 : 1 ≤ q := hH.trans hHq
  have hq0 : q ≠ 0 := by omega
  have : NeZero q := ⟨hq0⟩
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hψ1 : χ.primitiveCharacter ≠ 1 := by
    intro h
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, h, map_one]
  have hψprim : χ.primitiveCharacter.IsPrimitive := χ.primitiveCharacter_isPrimitive
  have hcond : (χ.conductor : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) χ.conductor_dvd_level
  set B : ℝ := C₁' * (q : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) * (H : ℝ) ^ ((2 : ℝ) / 3) with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hinner : ∀ d ∈ q.divisors,
      ‖(μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), χ.primitiveCharacter n‖ ≤ B := by
    intro d hd
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    rw [sum_filter_dvd_Ioc _ hd0]
    have hle : N / d ≤ (N + H) / d := Nat.div_le_div_right (by omega)
    have hH' : (N + H) / d - N / d ≤ H := div_sub_div_le hd0 N H
    have heq : (N + H) / d = N / d + ((N + H) / d - N / d) := by omega
    rw [heq]
    have hμ : ‖(μ d : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    have hψd : ‖χ.primitiveCharacter d‖ ≤ 1 := χ.primitiveCharacter.norm_le_one _
    set S := ∑ m ∈ Ioc (N / d) (N / d + ((N + H) / d - N / d)), χ.primitiveCharacter m
    calc ‖(μ d : ℂ) * (χ.primitiveCharacter d * S)‖
        = ‖(μ d : ℂ)‖ * (‖χ.primitiveCharacter d‖ * ‖S‖) := by rw [norm_mul, norm_mul]
      _ ≤ 1 * (1 * ‖S‖) := by gcongr
      _ = ‖S‖ := by ring
      _ ≤ C₁' * (χ.conductor : ℝ) ^ ((1 : ℝ) / 9 + ε / 2) *
            (((N + H) / d - N / d : ℕ) : ℝ) ^ ((2 : ℝ) / 3) :=
          primitive_bound_all hC₁'0 hC₁' _ hψprim hψ1 _ _
      _ ≤ B := by
          rw [hBdef]
          gcongr
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq1
  calc ‖∑ n ∈ Ioc N (N + H), χ n‖
      = ‖∑ d ∈ q.divisors,
          (μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), χ.primitiveCharacter n‖ := by
        rw [sum_eq_sum_divisors hq0]
    _ ≤ ∑ d ∈ q.divisors,
          ‖(μ d : ℂ) * ∑ n ∈ (Ioc N (N + H)).filter (d ∣ ·), χ.primitiveCharacter n‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _d ∈ q.divisors, B := Finset.sum_le_sum hinner
    _ = (q.divisors.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C₂ * (q : ℝ) ^ (ε / 2)) * B := by
        gcongr
        exact hτ q hq0
    _ = C₁' * C₂ * (q : ℝ) ^ ((1 : ℝ) / 9 + ε) * (H : ℝ) ^ ((2 : ℝ) / 3) := by
        rw [hBdef, show (1 : ℝ) / 9 + ε = ε / 2 + ((1 : ℝ) / 9 + ε / 2) by ring,
          Real.rpow_add hqpos (ε / 2) ((1 : ℝ) / 9 + ε / 2)]
        ring

end GradedNear
