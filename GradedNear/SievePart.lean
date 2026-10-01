module

public import GradedNear.SieveCell
public import GradedNear.SieveDiagonal
public import GradedNear.SieveOffDiagonal
public import GradedNear.SieveMajorant
public import GradedNear.SieveError

/-!
# The sieve part of the second Cauchy–Schwarz factor

`𝓛⁻¹ Σ_{n ≤ N} (Λ(n)/n) H(t_n) |Y_n|² ≤ Σ_j S(δ_j) a_j² + ε (Σ a)²` for all large `q`, where
`S(δ) = Σ_k h_k e^{-2δ t_k} (t_{k+1}² - t_k²)/(2 λ_k)` is the sieve part of `D(δ)`.
-/

@[expose] public section

open Complex
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GradedNear

open NearData

/-- The sieve part of `D(δ)`. -/
def sieveDiag (D : NearData) (δ : ℝ) : ℝ :=
  ∑ k ∈ Finset.range D.m,
    D.h k * Real.exp (-2 * δ * D.t k) * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)

lemma Dδ_eq (D : NearData) (δ : ℝ) :
    D.Dδ δ = (∫ u in Set.Ioi (0 : ℝ), D.g u * Real.exp ((D.s₁ - 2 * δ) * u)) +
      sieveDiag D δ := rfl

/-- The sieve weight at `t_n` as a sum over the cells containing it. -/
lemma sieve_sum_cells (D : NearData) {q : ℕ} {ι : Type*} [Fintype ι] (E : Entries q ι)
    (a : ι → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2 =
      ∑ k ∈ Finset.range D.m, D.h k * ∑ n ∈ (Finset.Icc 1 N).filter
        (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)), Λ n / n * ‖Yn E a n‖ ^ 2 := by
  unfold NearData.sieveH
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  split_ifs <;> ring

lemma rpow_le_natCast_iff_tn {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) (t : ℝ) :
    (q : ℝ) ^ t ≤ n ↔ t ≤ tn q n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hℓ := log_q_pos hq
  rw [← Real.log_le_log_iff (Real.rpow_pos_of_pos hq0 t) hn0, Real.log_rpow hq0, tn,
    le_div_iff₀ hℓ]

lemma natCast_lt_rpow_iff_tn {q n : ℕ} (hq : 2 ≤ q) (hn : 1 ≤ n) (t : ℝ) :
    (n : ℝ) < (q : ℝ) ^ t ↔ tn q n < t := by
  have := rpow_le_natCast_iff_tn hq hn t
  constructor
  · intro h; by_contra h'; linarith [this.2 (not_lt.1 h')]
  · intro h; by_contra h'; linarith [this.1 (not_lt.1 h')]

/-- The integers of a cell lie in `[⌈q^t⌉, ⌈q^{t'}⌉)`. -/
lemma cell_filter_subset {q : ℕ} (hq : 2 ≤ q) (N : ℕ) (t t' : ℝ) :
    (Finset.Icc 1 N).filter (fun n => t ≤ tn q n ∧ tn q n < t') ⊆
      Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊ := by
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hn1, -⟩, ht, ht'⟩ := hn
  rw [Finset.mem_Ico]
  refine ⟨Nat.ceil_le.2 ((rpow_le_natCast_iff_tn hq hn1 t).2 ht), ?_⟩
  exact Nat.lt_ceil.2 ((natCast_lt_rpow_iff_tn hq hn1 t').2 ht')

lemma cell_mem {q : ℕ} (hq : 2 ≤ q) {t t' : ℝ} {n : ℕ}
    (hn : n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊) : 1 ≤ n ∧ t ≤ tn q n := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Finset.mem_Ico] at hn
  have h1 : 1 ≤ n := by
    have : 0 < ⌈(q : ℝ) ^ t⌉₊ := Nat.ceil_pos.2 (Real.rpow_pos_of_pos hq0 t)
    omega
  refine ⟨h1, (rpow_le_natCast_iff_tn hq h1 t).1 ?_⟩
  exact (Nat.ceil_le.1 hn.1)

lemma Ico_ceil_subset_Icc {A B : ℝ} :
    Finset.Ico ⌈A⌉₊ ⌈B⌉₊ ⊆ Finset.Icc ⌈A⌉₊ ⌊B⌋₊ := by
  intro n hn
  rw [Finset.mem_Ico] at hn
  rw [Finset.mem_Icc]
  refine ⟨hn.1, Nat.le_floor ?_⟩
  exact (Nat.lt_ceil.1 hn.2).le

/-- **One cell of the sieve part**, with all analytic inputs plugged in. -/
lemma cell_k_bound {V₀ CB CC κ : ℝ}
    (hdiagG : ∀ V A B : ℝ, V₀ ≤ V → V ≤ A → A ≤ B →
      ∑ n ∈ Finset.Icc ⌈A⌉₊ ⌊B⌋₊, Real.log n / n * sieveNu V n ≤
        (Real.log B ^ 2 - Real.log A ^ 2) / (2 * Real.log V) +
          CB * (Real.log B ^ 2 + 1) / Real.log V ^ 2)
    (D : NearData) (hD : D.Valid) {q : ℕ} (hq : 2 ≤ q)
    (hoffC : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 →
      ∀ t t' β τ : ℝ, 1 / 3 + 2 * D.ε' < t → t ≤ t' → t' ≤ D.t D.m → 0 ≤ β → β ≤ 1 →
        |τ| ≤ Real.log q →
        ‖∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ t⌉₊ ⌈(q : ℝ) ^ t'⌉₊,
            (sieveNu ((q : ℝ) ^ ((t - 1 / 3) / 2 - D.ε')) n : ℂ) * ψ n * (Real.log n : ℂ) *
              (n : ℂ) ^ (-((1 + β : ℝ) + (τ : ℂ) * I))‖ ≤ CC * (q : ℝ) ^ (-κ))
    {ι : Type*} [Fintype ι] (E : Entries q ι) (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j)
    (hδ : ∀ j, 0 ≤ E.δ j) (hinj : Function.Injective E.χ)
    (hβ : ∀ j j', (E.δ j + E.δ j') / Real.log q ≤ 1) (hτ : ∀ j j', |E.γ j - E.γ j'| ≤ Real.log q)
    {k : ℕ} (hk : k < D.m) (ht0 : 1 / 3 + 2 * D.ε' < D.t k) (htk : D.t (k + 1) ≤ D.t D.m)
    (hlev : 0 < D.level k) (hV : V₀ ≤ (q : ℝ) ^ D.level k) :
    ∑ n ∈ Finset.Ico ⌈(q : ℝ) ^ D.t k⌉₊ ⌈(q : ℝ) ^ D.t (k + 1)⌉₊, Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      ∑ j, Real.exp (-2 * E.δ j * D.t k) *
          (Real.log q * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k) +
            |CB| * (D.t (k + 1) ^ 2 * Real.log q ^ 2 + 1) / (D.level k ^ 2 * Real.log q ^ 2)) *
          a j ^ 2 +
        (|CC| * (q : ℝ) ^ (-κ) + 2 * (q : ℝ) ^ D.level k * (D.level k * Real.log q) /
          (q : ℝ) ^ D.t k) * (∑ j, a j) ^ 2 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show 1 ≤ q by omega)
  have hℓ := log_q_pos hq
  have htk_lt := hD.t_lt k hk
  set V : ℝ := (q : ℝ) ^ D.level k with hVdef
  set A : ℝ := (q : ℝ) ^ D.t k with hAdef
  set B : ℝ := (q : ℝ) ^ D.t (k + 1) with hBdef
  have hVpos : 1 < V := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by omega)) hlev
  have hlev_lt : D.level k < D.t k := by
    unfold NearData.level; linarith [hD.ε'_pos]
  have hVA : V ≤ A := Real.rpow_le_rpow_of_exponent_le hq1 hlev_lt.le
  have hAB : A ≤ B := Real.rpow_le_rpow_of_exponent_le hq1 htk_lt.le
  have hA1 : 1 ≤ A := Real.one_le_rpow hq1 (by linarith [hlev_lt])
  have hlogV : Real.log V = D.level k * Real.log q := Real.log_rpow hq0 _
  have hlogA : Real.log A = D.t k * Real.log q := Real.log_rpow hq0 _
  have hlogB : Real.log B = D.t (k + 1) * Real.log q := Real.log_rpow hq0 _
  -- apply the cell bound
  refine cell_bound E a ha hδ hq V (D.t k) _ (|CC| * (q : ℝ) ^ (-κ)) _ _
    (fun n hn => (cell_mem hq hn).1) (fun n hn => (cell_mem hq hn).2)
    (fun n => if IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V then Λ n else 0)
    (fun n => by split_ifs <;> simp [ArithmeticFunction.vonMangoldt_nonneg])
    (fun n _ => vonMangoldt_le_sieve hVpos n) ?_ ?_ ?_
    (mul_nonneg (abs_nonneg _) (Real.rpow_nonneg hq0.le _))
  · -- diagonal
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Ico_ceil_subset_Icc) ?_).trans
      ((hdiagG V A B hV hVA hAB).trans ?_)
    · intro n _ _
      exact mul_nonneg (div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n))
        (sieveNu_nonneg V n)
    · rw [hlogV, hlogA, hlogB]
      have hlv : 0 < D.level k * Real.log q := mul_pos hlev hℓ
      have e1 : ((D.t (k + 1) * Real.log q) ^ 2 - (D.t k * Real.log q) ^ 2) /
          (2 * (D.level k * Real.log q)) =
          Real.log q * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k) := by
        field_simp
      have e2 : CB * ((D.t (k + 1) * Real.log q) ^ 2 + 1) / (D.level k * Real.log q) ^ 2 ≤
          |CB| * (D.t (k + 1) ^ 2 * Real.log q ^ 2 + 1) / (D.level k ^ 2 * Real.log q ^ 2) := by
        rw [show (D.level k * Real.log q) ^ 2 = D.level k ^ 2 * Real.log q ^ 2 by ring,
          show (D.t (k + 1) * Real.log q) ^ 2 = D.t (k + 1) ^ 2 * Real.log q ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (le_abs_self CB) (by positivity)
      rw [e1]; linarith
  · -- off-diagonal
    intro j j' hjj'
    have hψ : E.χ j * (E.χ j')⁻¹ ≠ 1 := fun h => hjj' (hinj (mul_inv_eq_one.1 h))
    have hb := hoffC _ hψ (D.t k) (D.t (k + 1)) ((E.δ j + E.δ j') / Real.log q)
      (E.γ j - E.γ j') ht0 htk_lt.le htk (div_nonneg (add_nonneg (hδ j) (hδ j')) hℓ.le)
      (hβ j j') (hτ j j')
    have hV' : (q : ℝ) ^ ((D.t k - 1 / 3) / 2 - D.ε') = V := by
      rw [hVdef]; rfl
    rw [hV'] at hb
    refine le_trans (le_of_eq ?_) (hb.trans ?_)
    · congr 1
      refine Finset.sum_congr rfl fun n _ => ?_
      push_cast
      ring
    · exact mul_le_mul_of_nonneg_right (le_abs_self CC) (Real.rpow_nonneg hq0.le _)
  · -- small prime powers
    have h := small_primepow_sum (V := V) (A := A) (B := B) hVpos.le hA1
    have e : ∑ n ∈ Finset.Ico ⌈A⌉₊ ⌈B⌉₊,
        (if IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V then Λ n else 0) / n =
        ∑ n ∈ (Finset.Ico ⌈A⌉₊ ⌈B⌉₊).filter
          (fun n => IsPrimePow n ∧ ((Nat.minFac n : ℕ) : ℝ) ≤ V), Λ n / n := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun n _ => ?_
      split_ifs <;> simp
    rw [e, ← hlogV]
    exact h

/-- The final algebra of the sieve part. -/
lemma sieve_final_algebra {ι : Type*} [Fintype ι] (m : ℕ) (h : ℕ → ℝ)
    (hh : ∀ k ∈ Finset.range m, 0 ≤ h k) (e : ι → ℕ → ℝ)
    (he1 : ∀ j, ∀ k ∈ Finset.range m, e j k ≤ 1) (main err1 Dk O P : ℕ → ℝ)
    (herr : ∀ k ∈ Finset.range m, 0 ≤ err1 k)
    (a : ι → ℝ) (ha : ∀ j, 0 ≤ a j) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hDk : ∀ k ∈ Finset.range m, Dk k / ℓ = main k + err1 k) :
    (∑ k ∈ Finset.range m, h k * (∑ j, e j k * Dk k * a j ^ 2 +
        (O k + P k) * (∑ j, a j) ^ 2)) / ℓ ≤
      ∑ j, (∑ k ∈ Finset.range m, h k * e j k * main k) * a j ^ 2 +
        (∑ k ∈ Finset.range m, h k * (err1 k + (O k + P k) / ℓ)) * (∑ j, a j) ^ 2 := by
  have hA2 : ∑ j, a j ^ 2 ≤ (∑ j, a j) ^ 2 := by
    rw [sq, Finset.sum_mul_sum]
    calc ∑ j, a j ^ 2 = ∑ j, a j * a j := by simp [sq]
      _ ≤ ∑ j, ∑ j', a j * a j' := Finset.sum_le_sum fun j _ =>
          Finset.single_le_sum (f := fun j' => a j * a j') (fun j' _ => mul_nonneg (ha j) (ha j'))
            (Finset.mem_univ j)
  have hDk' : ∀ k ∈ Finset.range m, Dk k = ℓ * (main k + err1 k) := fun k hk => by
    rw [← hDk k hk]; field_simp
  -- expand, cell by cell
  have hk : ∀ k ∈ Finset.range m, h k * (∑ j, e j k * Dk k * a j ^ 2 +
      (O k + P k) * (∑ j, a j) ^ 2) / ℓ =
      (∑ j, h k * e j k * main k * a j ^ 2) + (∑ j, h k * e j k * err1 k * a j ^ 2) +
        h k * ((O k + P k) / ℓ) * (∑ j, a j) ^ 2 := by
    intro k hk
    have e1 : h k * (∑ j, e j k * Dk k * a j ^ 2) / ℓ =
        ∑ j, h k * e j k * main k * a j ^ 2 + ∑ j, h k * e j k * err1 k * a j ^ 2 := by
      rw [Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hDk' k hk]; field_simp
    rw [mul_add, add_div, e1]
    ring
  have hmain : ∑ j, (∑ k ∈ Finset.range m, h k * e j k * main k) * a j ^ 2 =
      ∑ k ∈ Finset.range m, ∑ j, h k * e j k * main k * a j ^ 2 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  have herr' : ∑ j, (∑ k ∈ Finset.range m, h k * e j k * err1 k) * a j ^ 2 =
      ∑ k ∈ Finset.range m, ∑ j, h k * e j k * err1 k * a j ^ 2 := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hsplit : (∑ k ∈ Finset.range m, h k * (∑ j, e j k * Dk k * a j ^ 2 +
        (O k + P k) * (∑ j, a j) ^ 2)) / ℓ =
      ∑ j, (∑ k ∈ Finset.range m, h k * e j k * main k) * a j ^ 2 +
        ∑ j, (∑ k ∈ Finset.range m, h k * e j k * err1 k) * a j ^ 2 +
        (∑ k ∈ Finset.range m, h k * ((O k + P k) / ℓ)) * (∑ j, a j) ^ 2 := by
    rw [Finset.sum_div, Finset.sum_congr rfl hk, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hmain, herr', Finset.sum_mul]
  have herr_le : ∑ j, (∑ k ∈ Finset.range m, h k * e j k * err1 k) * a j ^ 2 ≤
      (∑ k ∈ Finset.range m, h k * err1 k) * (∑ j, a j) ^ 2 := by
    have hE0 : 0 ≤ ∑ k ∈ Finset.range m, h k * err1 k :=
      Finset.sum_nonneg fun k hk => mul_nonneg (hh k hk) (herr k hk)
    calc ∑ j, (∑ k ∈ Finset.range m, h k * e j k * err1 k) * a j ^ 2
        ≤ ∑ j, (∑ k ∈ Finset.range m, h k * err1 k) * a j ^ 2 := by
          refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          refine Finset.sum_le_sum fun k hk => ?_
          have := mul_le_mul_of_nonneg_left (he1 j k hk) (mul_nonneg (hh k hk) (herr k hk))
          nlinarith [hh k hk, herr k hk]
      _ = (∑ k ∈ Finset.range m, h k * err1 k) * ∑ j, a j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ (∑ k ∈ Finset.range m, h k * err1 k) * (∑ j, a j) ^ 2 :=
          mul_le_mul_of_nonneg_left hA2 hE0
  have hlast : (∑ k ∈ Finset.range m, h k * err1 k) * (∑ j, a j) ^ 2 +
      (∑ k ∈ Finset.range m, h k * ((O k + P k) / ℓ)) * (∑ j, a j) ^ 2 =
      (∑ k ∈ Finset.range m, h k * (err1 k + (O k + P k) / ℓ)) * (∑ j, a j) ^ 2 := by
    rw [← add_mul, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  linarith [herr_le, hlast]

lemma t_mono_le (D : NearData) (hD : D.Valid) {k l : ℕ} (hkl : k ≤ l) (hl : l ≤ D.m) :
    D.t k ≤ D.t l := by
  induction l with
  | zero => have : k = 0 := by omega
            subst this; exact le_rfl
  | succ l ih =>
    rcases Nat.lt_or_ge k (l + 1) with h | h
    · have h1 := ih (by omega) (by omega)
      have h2 := hD.t_lt l (by omega)
      linarith
    · have : k = l + 1 := by omega
      subst this; exact le_rfl

/-- **The sieve part of the second factor.** -/
theorem sieve_part_bound (hGr : GrahamEstimate) (hBur : BurgessBound) (D : NearData)
    (hD : D.Valid) {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q → ∀ T : ℝ, 0 ≤ T → T ≤ Real.log q / 3 →
      ∀ (ι : Type) [Fintype ι] (E : Entries q ι), (∀ j, |E.γ j| ≤ T) → (∀ j, E.δ j ∈ D.Δ) →
      ((∃ k < D.m, D.h k ≠ 0) → Function.Injective E.χ) →
      ∀ a : ι → ℝ, (∀ j, 0 ≤ a j) → ∀ N : ℕ,
        (∑ n ∈ Finset.Icc 1 N, Λ n / n * D.sieveH (tn q n) * ‖Yn E a n‖ ^ 2) / Real.log q ≤
          ∑ j, sieveDiag D (E.δ j) * a j ^ 2 + ε * (∑ j, a j) ^ 2 := by
  obtain ⟨CB, V₀, -, hdiagG⟩ := sieve_diagonal hGr
  obtain ⟨CC, κ, hκ, qC, hoffC⟩ := sieve_offdiag hBur (tmax := D.t D.m) hD.ε'_pos
  have ht0k : ∀ k < D.m, 1 / 3 + 2 * D.ε' < D.t k := fun k hk =>
    lt_of_lt_of_le hD.t_zero (t_mono_le D hD (Nat.zero_le k) hk.le)
  have hlev_pos : ∀ k < D.m, 0 < D.level k := fun k hk => by
    unfold NearData.level; linarith [ht0k k hk]
  have hlev_lt : ∀ k < D.m, D.level k < D.t k := fun k hk => by
    unfold NearData.level; linarith [ht0k k hk, hD.ε'_pos]
  obtain ⟨qE, hqE⟩ := sieve_error_eventually D.m D.h D.t D.level hlev_pos hlev_lt |CB| CC κ hκ hε
  obtain ⟨qV, hqV⟩ : ∃ qV : ℕ, ∀ q : ℕ, qV ≤ q → ∀ k < D.m, V₀ ≤ (q : ℝ) ^ D.level k := by
    have hev : ∀ k ∈ Finset.range D.m,
        ∀ᶠ q : ℕ in Filter.atTop, V₀ ≤ (q : ℝ) ^ D.level k := by
      intro k hk
      have hl := hlev_pos k (Finset.mem_range.1 hk)
      exact ((tendsto_rpow_atTop hl).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop V₀
    obtain ⟨qV, hqV⟩ := Filter.eventually_atTop.1 ((Finset.eventually_all _).2 hev)
    exact ⟨qV, fun q hq k hk => hqV q hq k (Finset.mem_range.2 hk)⟩
  obtain ⟨qβ, hqβ⟩ := Filter.eventually_atTop.1
    (tendsto_log_nat_atTop.eventually_ge_atTop (2 * ∑ δ ∈ D.Δ, δ))
  refine ⟨max (max (max qC qE) (max qV qβ)) 2,
    fun q hq T hT hTq ι _ E hγ hΔ hinj a ha N => ?_⟩
  have hq2 : 2 ≤ q := le_trans (le_max_right _ _) hq
  have hqC : qC ≤ q := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hq
  have hqE' : qE ≤ q := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hq
  have hqV' : qV ≤ q := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hq
  have hqβ' : qβ ≤ q := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hq
  have hℓ := log_q_pos hq2
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hδ : ∀ j, 0 ≤ E.δ j := fun j => hD.Δ_nonneg _ (hΔ j)
  have hA : 0 ≤ ∑ j, a j := Finset.sum_nonneg fun j _ => ha j
  by_cases hH : ∃ k < D.m, D.h k ≠ 0
  swap
  · -- the sieve weight vanishes
    have hH' : ∀ k < D.m, D.h k = 0 := fun k hk => by
      by_contra h; exact hH ⟨k, hk, h⟩
    have hS0 : ∀ u, D.sieveH u = 0 := by
      intro u; unfold NearData.sieveH
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hH' k (Finset.mem_range.1 hk)]; simp
    have hD0 : ∀ δ, sieveDiag D δ = 0 := by
      intro δ; unfold sieveDiag
      refine Finset.sum_eq_zero fun k hk => ?_
      rw [hH' k (Finset.mem_range.1 hk)]; simp
    simp only [hS0, hD0, mul_zero, zero_mul, Finset.sum_const_zero, zero_div, zero_add]
    positivity
  have hinj' := hinj hH
  have hβ : ∀ j j', (E.δ j + E.δ j') / Real.log q ≤ 1 := by
    intro j j'
    rw [div_le_one hℓ]
    have h1 : E.δ j ≤ ∑ δ ∈ D.Δ, δ := Finset.single_le_sum hD.Δ_nonneg (hΔ j)
    have h2 : E.δ j' ≤ ∑ δ ∈ D.Δ, δ := Finset.single_le_sum hD.Δ_nonneg (hΔ j')
    linarith [hqβ q hqβ']
  have hτ : ∀ j j', |E.γ j - E.γ j'| ≤ Real.log q := by
    intro j j'
    have := abs_sub (E.γ j) (E.γ j')
    linarith [hγ j, hγ j']
  rw [sieve_sum_cells]
  set Dk : ℕ → ℝ := fun k => Real.log q * (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k) +
    |CB| * (D.t (k + 1) ^ 2 * Real.log q ^ 2 + 1) / (D.level k ^ 2 * Real.log q ^ 2) with hDk
  set Pk : ℕ → ℝ := fun k => 2 * (q : ℝ) ^ D.level k * (D.level k * Real.log q) /
    (q : ℝ) ^ D.t k with hPk
  have hcell : ∀ k ∈ Finset.range D.m,
      D.h k * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => D.t k ≤ tn q n ∧ tn q n < D.t (k + 1)),
        Λ n / n * ‖Yn E a n‖ ^ 2 ≤
      D.h k * (∑ j, Real.exp (-2 * E.δ j * D.t k) * Dk k * a j ^ 2 +
        (|CC| * (q : ℝ) ^ (-κ) + Pk k) * (∑ j, a j) ^ 2) := by
    intro k hk
    have hk' := Finset.mem_range.1 hk
    refine mul_le_mul_of_nonneg_left ?_ (hD.h_nonneg k hk')
    refine (Finset.sum_le_sum_of_subset_of_nonneg (cell_filter_subset hq2 N _ _) ?_).trans ?_
    · intro n _ _
      exact mul_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
        (sq_nonneg _)
    · exact cell_k_bound hdiagG D hD hq2 (hoffC q hqC) E a ha hδ hinj' hβ hτ hk' (ht0k k hk')
        (t_mono_le D hD (by omega) le_rfl) (hlev_pos k hk') (hqV q hqV' k hk')
  refine (div_le_div_of_nonneg_right (Finset.sum_le_sum hcell) hℓ.le).trans ?_
  have halg := sieve_final_algebra D.m D.h (fun k hk => hD.h_nonneg k (Finset.mem_range.1 hk))
    (fun j k => Real.exp (-2 * E.δ j * D.t k))
    (fun j k hk => by
      rw [Real.exp_le_one_iff]
      have htk : 0 < D.t k := by
        have := ht0k k (Finset.mem_range.1 hk); linarith [hD.ε'_pos]
      nlinarith [hδ j])
    (fun k => (D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k))
    (fun k => |CB| * D.t (k + 1) ^ 2 / (D.level k ^ 2 * Real.log q) +
      |CB| / (D.level k ^ 2 * Real.log q ^ 3))
    Dk (fun _ => |CC| * (q : ℝ) ^ (-κ)) Pk
    (fun k hk => by
      have := hlev_pos k (Finset.mem_range.1 hk)
      positivity)
    a ha hℓ ?_
  · refine halg.trans ?_
    have hmain : ∀ j, ∑ k ∈ Finset.range D.m, D.h k * Real.exp (-2 * E.δ j * D.t k) *
        ((D.t (k + 1) ^ 2 - D.t k ^ 2) / (2 * D.level k)) = sieveDiag D (E.δ j) := by
      intro j; unfold sieveDiag
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    have herr : ∑ k ∈ Finset.range D.m, D.h k *
        ((|CB| * D.t (k + 1) ^ 2 / (D.level k ^ 2 * Real.log q) +
          |CB| / (D.level k ^ 2 * Real.log q ^ 3)) +
          (|CC| * (q : ℝ) ^ (-κ) + Pk k) / Real.log q) ≤ ε := by
      refine le_trans (le_of_eq ?_) (hqE q hqE')
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      simp only [hPk]
      have hPq : 2 * (q : ℝ) ^ D.level k * (D.level k * Real.log q) / (q : ℝ) ^ D.t k /
          Real.log q = 2 * D.level k * (q : ℝ) ^ (D.level k - D.t k) := by
        rw [Real.rpow_sub hq0]
        field_simp
      rw [add_div, hPq]
      ring
    simp_rw [hmain]
    have hA2 : 0 ≤ (∑ j, a j) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right herr hA2]
  · intro k hk
    have hl := hlev_pos k (Finset.mem_range.1 hk)
    simp only [hDk]
    field_simp

end GradedNear
