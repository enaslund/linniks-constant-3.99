module

public import GradedNear.SieveBasic

/-!
# The Selberg majorant of `Λ` and the small prime powers

* For `V > 1` and `n ≥ 1`: `Λ(n) ≤ log n · ν_V(n) + [n = p^e, p ≤ V] Λ(n)`. For a prime power
  with `p > V`, every divisor `p^i > 1` has weight `0`, so `ν_V(p^e) = 1`.
* The prime powers `n ≥ A` of primes `p ≤ V` contribute `Σ Λ(n)/n ≤ 2 V log V / A`, by the
  geometric series in `e` for each `p ≤ V`.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace Majorant

/-- If every prime factor of `n ≠ 0` exceeds `V > 1`, then `ν_V(n) = 1`: every divisor `d > 1`
of `n` satisfies `d ≥ minFac n > V`, so only `d = 1` has a nonzero weight, and `ψ_1 = 1`. -/
lemma sieveNu_eq_one_of_lt_minFac {V : ℝ} (hV : 1 < V) {n : ℕ} (hn : n ≠ 0)
    (hmin : V < ((Nat.minFac n : ℕ) : ℝ)) : sieveNu V n = 1 := by
  have hsum : ∑ d ∈ n.divisors, grahamWeight V d = 1 := by
    rw [Finset.sum_eq_single 1]
    · have hlog : Real.log V ≠ 0 := (Real.log_pos hV).ne'
      simp [grahamWeight, hV.le, hlog]
    · intro d hd hd1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
      have hd2 : 2 ≤ d := by omega
      have hle : Nat.minFac n ≤ d := Nat.minFac_le_of_dvd hd2 (Nat.dvd_of_mem_divisors hd)
      have hle' : ((Nat.minFac n : ℕ) : ℝ) ≤ d := by exact_mod_cast hle
      have hnot : ¬ ((d : ℝ) ≤ V) := fun h => by linarith
      simp [grahamWeight, hnot]
    · intro h
      exact absurd (Nat.one_mem_divisors.mpr hn) h
  simp [sieveNu, hsum]

/-- Geometric tail: for `p ≥ 2` and a finite set `F` of exponents with `p^k ≥ A > 0` for all
`k ∈ F`, `Σ_{k ∈ F} p^{-k} ≤ 2/A`. -/
lemma geom_tail {p : ℕ} (hp : 2 ≤ p) {A : ℝ} (hA : 0 < A) (F : Finset ℕ)
    (hF : ∀ k ∈ F, A ≤ (p : ℝ) ^ k) :
    ∑ k ∈ F, 1 / (p : ℝ) ^ k ≤ 2 / A := by
  rcases F.eq_empty_or_nonempty with h | hne
  · rw [h, Finset.sum_empty]
    exact div_nonneg (by norm_num) hA.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hm : F.min' hne ∈ F := F.min'_mem hne
  have hsub : F ⊆ Finset.Ico (F.min' hne) (F.max' hne + 1) := by
    intro k hk
    exact Finset.mem_Ico.mpr ⟨F.min'_le k hk, Nat.lt_succ_of_le (F.le_max' k hk)⟩
  have hx0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hx1 : 1 / (p : ℝ) ≤ 1 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
  calc ∑ k ∈ F, 1 / (p : ℝ) ^ k = ∑ k ∈ F, (1 / (p : ℝ)) ^ k :=
        Finset.sum_congr rfl (fun k _ => (one_div_pow (p : ℝ) k).symm)
    _ ≤ ∑ k ∈ Finset.Ico (F.min' hne) (F.max' hne + 1), (1 / (p : ℝ)) ^ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => pow_nonneg hx0 k)
    _ ≤ (1 / (p : ℝ)) ^ (F.min' hne) / (1 - 1 / (p : ℝ)) :=
        geom_sum_Ico_le_of_lt_one hx0 (by linarith)
    _ ≤ 2 * (1 / (p : ℝ)) ^ (F.min' hne) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [pow_nonneg hx0 (F.min' hne)]
    _ = 2 / (p : ℝ) ^ (F.min' hne) := by
        rw [one_div_pow]
        ring
    _ ≤ 2 / A := div_le_div_of_nonneg_left (by norm_num) hA (hF _ hm)

/-- The contribution of the powers of a single prime `p`: if every `n ∈ T` is a prime power
with `minFac n = p` and `n ≥ A > 0`, then `Σ_{n ∈ T} Λ(n)/n ≤ 2 log p / A`. -/
lemma fiber_bound {A : ℝ} (hA : 0 < A) (p : ℕ) (T : Finset ℕ)
    (hT : ∀ n ∈ T, IsPrimePow n ∧ Nat.minFac n = p ∧ A ≤ n) :
    ∑ n ∈ T, Λ n / n ≤ 2 * Real.log p / A := by
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rcases T.eq_empty_or_nonempty with h | ⟨n₀, hn₀⟩
  · rw [h, Finset.sum_empty]
    exact div_nonneg (mul_nonneg (by norm_num) hlogp) hA.le
  have hp : p.Prime := by
    obtain ⟨hpp, hmin, _⟩ := hT n₀ hn₀
    rw [← hmin]
    exact Nat.minFac_prime hpp.ne_one
  have hpow : ∀ n ∈ T, p ^ (n.factorization p) = n := by
    intro n hn
    obtain ⟨hpp, hmin, _⟩ := hT n hn
    rw [← hmin]
    exact hpp.minFac_pow_factorization_eq
  have hcast : ∀ n ∈ T, (n : ℝ) = (p : ℝ) ^ (n.factorization p) := by
    intro n hn
    exact_mod_cast (hpow n hn).symm
  have hterm : ∀ n ∈ T, Λ n / n = Real.log p * (1 / (p : ℝ) ^ (n.factorization p)) := by
    intro n hn
    obtain ⟨hpp, hmin, _⟩ := hT n hn
    rw [ArithmeticFunction.vonMangoldt_apply, ite_eq_left hpp, hmin, hcast n hn]
    ring
  have hinj : Set.InjOn (fun n : ℕ => n.factorization p) T := by
    intro n hn m hm h
    have h' : n.factorization p = m.factorization p := h
    calc n = p ^ (n.factorization p) := (hpow n hn).symm
      _ = p ^ (m.factorization p) := by rw [h']
      _ = m := hpow m hm
  have hF : ∀ k ∈ T.image (fun n : ℕ => n.factorization p), A ≤ (p : ℝ) ^ k := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    rw [← hcast n hn]
    exact (hT n hn).2.2
  calc ∑ n ∈ T, Λ n / n = ∑ n ∈ T, Real.log p * (1 / (p : ℝ) ^ (n.factorization p)) :=
        Finset.sum_congr rfl hterm
    _ = Real.log p * ∑ k ∈ T.image (fun n : ℕ => n.factorization p), 1 / (p : ℝ) ^ k := by
        rw [Finset.sum_image hinj, Finset.mul_sum]
    _ ≤ Real.log p * (2 / A) :=
        mul_le_mul_of_nonneg_left (geom_tail hp.two_le hA _ hF) hlogp
    _ = 2 * Real.log p / A := by ring

end Majorant

theorem vonMangoldt_le_sieve {V : ℝ} (hV : 1 < V) (n : ℕ) :
    Λ n ≤ Real.log n * sieveNu V n +
      (if IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V then Λ n else 0) := by
  have hprod : 0 ≤ Real.log n * sieveNu V n :=
    mul_nonneg (Real.log_natCast_nonneg n) (sieveNu_nonneg V n)
  by_cases hpp : IsPrimePow n
  · by_cases hmin : ((Nat.minFac n : ℕ) : ℝ) ≤ V
    · rw [ite_eq_left ⟨hpp, hmin⟩]
      linarith
    · rw [ite_eq_right (fun h => hmin h.2), add_zero,
        Majorant.sieveNu_eq_one_of_lt_minFac hV hpp.ne_zero (not_le.mp hmin), mul_one]
      exact ArithmeticFunction.vonMangoldt_le_log
  · rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hpp, ite_eq_right (fun h => hpp h.1),
      add_zero]
    exact hprod

theorem small_primepow_sum {V A B : ℝ} (hV : 1 ≤ V) (hA : 1 ≤ A) :
    ∑ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V),
      Λ n / n ≤ 2 * V * Real.log V / A := by
  have hA0 : 0 < A := by linarith
  have hlogV : 0 ≤ Real.log V := Real.log_nonneg hV
  have hmaps : ∀ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter
      (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V),
      Nat.minFac n ∈ Finset.Icc 1 ⌊V⌋₊ := by
    intro n hn
    rw [Finset.mem_filter] at hn
    exact Finset.mem_Icc.mpr ⟨Nat.minFac_pos n, Nat.le_floor hn.2.2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc _ ≤ ∑ p ∈ Finset.Icc 1 ⌊V⌋₊, 2 * Real.log p / A := by
        apply Finset.sum_le_sum
        intro p _
        apply Majorant.fiber_bound hA0 p
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Ico] at hn
        exact ⟨hn.1.2.1, hn.2, Nat.ceil_le.mp hn.1.1.1⟩
    _ ≤ ∑ p ∈ Finset.Icc 1 ⌊V⌋₊, 2 * Real.log V / A := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_Icc] at hp
        have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1
        have hpV : (p : ℝ) ≤ V := (Nat.cast_le.mpr hp.2).trans (Nat.floor_le (by linarith))
        have := Real.log_le_log hp0 hpV
        apply div_le_div_of_nonneg_right _ hA0.le
        linarith
    _ = (⌊V⌋₊ : ℝ) * (2 * Real.log V / A) := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        simp
    _ ≤ V * (2 * Real.log V / A) := by
        apply mul_le_mul_of_nonneg_right (Nat.floor_le (by linarith))
        exact div_nonneg (mul_nonneg (by norm_num) hlogV) hA0.le
    _ = 2 * V * Real.log V / A := by ring

end GradedNear
