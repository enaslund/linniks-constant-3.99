module

public import Mathlib

/-!
# (A) The first Cauchy–Schwarz factor: a Mertens-type upper Riemann sum

For `φ` bounded on `[0, X]` and continuous at every point of `(0, X)` outside a finite set,
`𝓛⁻¹ Σ_{1 ≤ n ≤ q^X} Λ(n)/n · φ(log n / 𝓛) ≤ ∫₀^X φ + ε` for all large `q`, where `𝓛 = log q`.
The proof uses Mertens' estimate `Σ_{n ≤ x} Λ(n)/n = log x + O(1)`.

## Proof outline

* `FirstFactor.abs_mertensSum_sub_log_le`: `|Σ_{n ≤ x} Λ(n)/n - log x| ≤ 6` for `x ≥ 1`, from
  `log N! = Σ_{n ≤ N} Λ(n) ⌊N/n⌋`, Chebyshev's bound `ψ(N) ≤ (log 4 + 4) N` and
  `N log N - N ≤ log N! ≤ N log N`.
* `FirstFactor.sum_le_partition`: if `φ ≤ c_i` on `(u_i, u_{i+1}]`, then the weighted sum up to
  `q^{u_j}` is at most `Σ_{i < j} c_i (S(q^{u_{i+1}}) - S(q^{u_i}))`, `S` the Mertens sum.
* `FirstFactor.tendsto_integral_stepFn`: the upper step functions of `φ` on the uniform mesh
  `X / K` converge to `φ` at every continuity point, so by dominated convergence their integrals
  tend to `∫₀^X φ`.
* `riemann_upper`: fix `K` with `∫ stepFn ≤ ∫ φ + ε/2`; Mertens on each of the `K` cells costs
  `12 M` per cell, which is `≤ ε/2` after division by `log q` for `q` large.
-/

@[expose] public section

open scoped ArithmeticFunction.vonMangoldt

namespace GradedNear

namespace FirstFactor

open Filter Topology MeasureTheory

/-! ### Mertens' first theorem -/

/-- The Mertens partial sum `Σ_{1 ≤ n ≤ y} Λ(n)/n`. -/
noncomputable def mertensSum (y : ℝ) : ℝ := ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, Λ n / n

/-- `log N! = Σ_{n ≤ N} Λ(n) ⌊N/n⌋`. -/
lemma sum_log_eq_sum_vonMangoldt (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
  have h := ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum (R := ℝ) Λ N
  rw [ArithmeticFunction.vonMangoldt_mul_zeta] at h
  simpa [ArithmeticFunction.log_apply] using h

/-- Mertens lower bound at an integer: `Σ_{n ≤ N} Λ(n)/n ≥ log N - 1`. -/
lemma mertens_nat_lower (N : ℕ) (hN : 1 ≤ N) :
    Real.log N - 1 ≤ ∑ n ∈ Finset.Ioc 0 N, Λ n / n := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Real.le_sum_log_nat N
  rw [sum_log_eq_sum_vonMangoldt] at h1
  have h2 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) ≤
      ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n) := by
    apply Finset.sum_le_sum
    intro n _
    exact mul_le_mul_of_nonneg_left Nat.cast_div_le ArithmeticFunction.vonMangoldt_nonneg
  have h3 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n) =
      N * ∑ n ∈ Finset.Ioc 0 N, Λ n / n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [h3] at h2
  have h4 : (N : ℝ) * (Real.log N - 1) ≤ N * ∑ n ∈ Finset.Ioc 0 N, Λ n / n := by
    linarith
  exact le_of_mul_le_mul_left h4 hNR

/-- Mertens upper bound at an integer: `Σ_{n ≤ N} Λ(n)/n ≤ log N + log 4 + 4`. -/
lemma mertens_nat_upper (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, Λ n / n ≤ Real.log N + (Real.log 4 + 4) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 := Real.sum_log_le' (x := (N : ℝ)) (by exact_mod_cast hN)
  rw [Nat.floor_natCast, sum_log_eq_sum_vonMangoldt] at h1
  have h2 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n - 1) ≤
      ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N / n : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Ioc.1 hn).1
    apply mul_le_mul_of_nonneg_left _ ArithmeticFunction.vonMangoldt_nonneg
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have h5 : N < N / n * n + n := Nat.lt_div_mul_add hn0
    have h6 : (N : ℝ) < ((N / n : ℕ) : ℝ) * n + n := by exact_mod_cast h5
    rw [div_sub_one hnR.ne', div_le_iff₀ hnR]
    linarith
  have h3 : ∑ n ∈ Finset.Ioc 0 N, Λ n * ((N : ℝ) / n - 1) =
      N * ∑ n ∈ Finset.Ioc 0 N, Λ n / n - Chebyshev.psi N := by
    rw [Chebyshev.psi, Nat.floor_natCast, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    ring
  rw [h3] at h2
  have h4 := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) hNR.le
  have h5 : (N : ℝ) * ∑ n ∈ Finset.Ioc 0 N, Λ n / n ≤ N * (Real.log N + (Real.log 4 + 4)) := by
    nlinarith
  exact le_of_mul_le_mul_left h5 hNR

/-- **Mertens' first theorem**: `|Σ_{n ≤ x} Λ(n)/n - log x| ≤ 6` for `x ≥ 1`. -/
lemma abs_mertensSum_sub_log_le (x : ℝ) (hx : 1 ≤ x) :
    |mertensSum x - Real.log x| ≤ 6 := by
  have hN : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  have hNR : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN
  have hlo := mertens_nat_lower _ hN
  have hup := mertens_nat_upper _ hN
  have hfl : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hfl2 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
  have hlog1 : Real.log ⌊x⌋₊ ≤ Real.log x := Real.log_le_log (by linarith) hfl
  have hlog2 : Real.log x ≤ Real.log 2 + Real.log ⌊x⌋₊ := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have hl2 := Real.log_two_lt_d9
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  unfold mertensSum
  rw [abs_le]
  constructor <;> linarith

/-- Short-interval form: `Σ_{q^a < n ≤ q^b} Λ(n)/n = (b - a) log q + O(1)`, with error `≤ 12`. -/
lemma mertensSum_short (q : ℕ) (hq : 1 < q) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |mertensSum ((q : ℝ) ^ b) - mertensSum ((q : ℝ) ^ a) - (b - a) * Real.log q| ≤ 12 := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
  have hqpos : (0 : ℝ) < q := by linarith
  have h1 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR hb)
  have h2 := abs_mertensSum_sub_log_le _ (Real.one_le_rpow hqR ha)
  rw [Real.log_rpow hqpos] at h1 h2
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-! ### Summation over a partition -/

/-- If `φ ≤ c i` on each cell `(u i, u (i + 1)]` of a partition starting at `u 0 = 0`, then the
weighted sum over `n ≤ q ^ u j` is bounded by the Mertens masses of the cells weighted by `c`. -/
lemma sum_le_partition (φ : ℝ → ℝ) (q : ℕ) (hq : 1 < q) (u c : ℕ → ℝ) (hu0 : u 0 = 0)
    (hmono : ∀ i, u i ≤ u (i + 1)) (j : ℕ)
    (hφ : ∀ i < j, ∀ t, u i < t → t ≤ u (i + 1) → φ t ≤ c i) :
    ∑ n ∈ Finset.Ioc 0 ⌊(q : ℝ) ^ u j⌋₊, Λ n / n * φ (Real.log n / Real.log q) ≤
      ∑ i ∈ Finset.range j,
        c i * (mertensSum ((q : ℝ) ^ u (i + 1)) - mertensSum ((q : ℝ) ^ u i)) := by
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := by linarith
  have hℓ : 0 < Real.log q := Real.log_pos hqR
  induction j with
  | zero =>
    simp only [hu0, Real.rpow_zero, Nat.floor_one, Finset.range_zero, Finset.sum_empty]
    rw [show Finset.Ioc 0 1 = {1} from rfl, Finset.sum_singleton]
    simp
  | succ j ih =>
    have ih' := ih (fun i hi => hφ i (by omega))
    rw [Finset.sum_range_succ]
    have hmonoF : ⌊(q : ℝ) ^ u j⌋₊ ≤ ⌊(q : ℝ) ^ u (j + 1)⌋₊ :=
      Nat.floor_le_floor (Real.rpow_le_rpow_of_exponent_le hqR.le (hmono j))
    rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF]
    have hS : mertensSum ((q : ℝ) ^ u (j + 1)) - mertensSum ((q : ℝ) ^ u j) =
        ∑ n ∈ Finset.Ioc ⌊(q : ℝ) ^ u j⌋₊ ⌊(q : ℝ) ^ u (j + 1)⌋₊, Λ n / n := by
      unfold mertensSum
      rw [← Finset.sum_Ioc_consecutive _ (Nat.zero_le _) hmonoF]
      ring
    rw [hS, Finset.mul_sum]
    apply add_le_add ih'
    apply Finset.sum_le_sum
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn.1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have h1 : (q : ℝ) ^ u j < n := (Nat.floor_lt (Real.rpow_pos_of_pos hqpos _).le).1 hn.1
    have h2 : (n : ℝ) ≤ (q : ℝ) ^ u (j + 1) :=
      (Nat.le_floor_iff (Real.rpow_pos_of_pos hqpos _).le).1 hn.2
    have h1' : u j * Real.log q < Real.log n := by
      rw [← Real.log_rpow hqpos]; exact Real.log_lt_log (Real.rpow_pos_of_pos hqpos _) h1
    have h2' : Real.log n ≤ u (j + 1) * Real.log q := by
      rw [← Real.log_rpow hqpos]; exact Real.log_le_log hnR h2
    have ht1 : u j < Real.log n / Real.log q := by rw [lt_div_iff₀ hℓ]; exact h1'
    have ht2 : Real.log n / Real.log q ≤ u (j + 1) := by rw [div_le_iff₀ hℓ]; exact h2'
    have hφn := hφ j (by omega) _ ht1 ht2
    have hΛ : 0 ≤ Λ n / n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg hnR.le
    rw [mul_comm (c j)]
    exact mul_le_mul_of_nonneg_left hφn hΛ

/-! ### Step-function majorants -/

/-- The supremum of `φ` on `[a, b]`. -/
noncomputable def supOn (φ : ℝ → ℝ) (a b : ℝ) : ℝ := sSup (φ '' Set.Icc a b)

/-- The supremum of `φ` on the `i`-th cell `[i h, (i + 1) h]`. -/
noncomputable def cell (φ : ℝ → ℝ) (h : ℝ) (i : ℕ) : ℝ := supOn φ (i * h) ((i + 1) * h)

/-- The step function equal to `cell φ h i` on `(i h, (i + 1) h]`. -/
noncomputable def stepFn (φ : ℝ → ℝ) (h : ℝ) (t : ℝ) : ℝ := cell φ h (⌈t / h⌉₊ - 1)

/-- `supOn` majorizes a function that is bounded above on `[a, b]`. -/
lemma le_supOn {φ : ℝ → ℝ} {a b t M : ℝ} (hbd : ∀ v ∈ Set.Icc a b, φ v ≤ M)
    (ht : t ∈ Set.Icc a b) : φ t ≤ supOn φ a b :=
  le_csSup ⟨M, by rintro _ ⟨v, hv, rfl⟩; exact hbd v hv⟩ ⟨t, ht, rfl⟩

/-- `supOn` on a nonempty interval is at most any upper bound. -/
lemma supOn_le {φ : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b) (h : ∀ v ∈ Set.Icc a b, φ v ≤ B) :
    supOn φ a b ≤ B :=
  csSup_le ⟨φ a, a, ⟨le_rfl, hab⟩, rfl⟩ (by rintro _ ⟨v, hv, rfl⟩; exact h v hv)

/-- On the cell `(i h, (i + 1) h]` the step function equals `cell φ h i`. -/
lemma stepFn_eq (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (i : ℕ) {t : ℝ} (ht1 : (i : ℝ) * h < t)
    (ht2 : t ≤ (i + 1) * h) : stepFn φ h t = cell φ h i := by
  have hc : ⌈t / h⌉₊ = i + 1 := by
    rw [Nat.ceil_eq_iff (Nat.succ_ne_zero i)]
    constructor
    · rw [Nat.succ_sub_one, lt_div_iff₀ hh]; exact ht1
    · rw [div_le_iff₀ hh]; push_cast; exact ht2
  unfold stepFn
  rw [hc, Nat.add_sub_cancel]

lemma measurable_stepFn (φ : ℝ → ℝ) (h : ℝ) : Measurable (stepFn φ h) := by
  have : stepFn φ h = (fun k : ℕ => cell φ h (k - 1)) ∘ (fun t : ℝ => ⌈t / h⌉₊) := rfl
  rw [this]
  exact measurable_from_nat.comp (measurable_id.div_const h).nat_ceil

/-- `∫₀^{j h} stepFn φ h = Σ_{i < j} cell φ h i · h`, with interval integrability. -/
lemma integral_stepFn (φ : ℝ → ℝ) {h : ℝ} (hh : 0 < h) (j : ℕ) :
    IntervalIntegrable (stepFn φ h) volume 0 (j * h) ∧
      ∫ t in (0 : ℝ)..(j * h), stepFn φ h t = ∑ i ∈ Finset.range j, cell φ h i * h := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hEq : ∀ t ∈ Set.Ioc ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h),
        stepFn φ h t = cell φ h j := by
      intro t ht
      exact stepFn_eq φ hh j ht.1 (by push_cast at ht; exact ht.2)
    have hle : (j : ℝ) * h ≤ ((j + 1 : ℕ) : ℝ) * h := by push_cast; nlinarith
    have hII : IntervalIntegrable (stepFn φ h) volume ((j : ℝ) * h) (((j + 1 : ℕ) : ℝ) * h) := by
      rw [intervalIntegrable_iff, Set.uIoc_of_le hle]
      exact (integrableOn_const (C := cell φ h j) (hs := by rw [Real.volume_Ioc]; exact
        ENNReal.ofReal_ne_top)).congr_fun (fun t ht => (hEq t ht).symm) measurableSet_Ioc
    have hI : ∫ t in ((j : ℝ) * h)..(((j + 1 : ℕ) : ℝ) * h), stepFn φ h t = cell φ h j * h := by
      rw [intervalIntegral.integral_congr_ae (g := fun _ => cell φ h j)]
      · rw [intervalIntegral.integral_const, smul_eq_mul]; push_cast; ring
      · refine Filter.Eventually.of_forall (fun t ht => ?_)
        rw [Set.uIoc_of_le hle] at ht
        exact hEq t ht
    refine ⟨ih.1.trans hII, ?_⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals ih.1 hII, ih.2, hI,
      Finset.sum_range_succ]

/-- For `t ∈ (0, X]` and the uniform mesh `h = X / K`, the cell index of `t` is `< K`
and `t` lies in the corresponding cell. -/
lemma ceil_index {X : ℝ} (hX : 0 < X) {K : ℕ} (hK : 0 < K) {t : ℝ} (ht0 : 0 < t)
    (htX : t ≤ X) :
    ⌈t / (X / K)⌉₊ - 1 < K ∧ ((⌈t / (X / K)⌉₊ - 1 : ℕ) : ℝ) * (X / K) < t ∧
      t ≤ (((⌈t / (X / K)⌉₊ - 1 : ℕ) : ℝ) + 1) * (X / K) := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hh : 0 < X / K := div_pos hX hKR
  have hpos : 0 < t / (X / K) := div_pos ht0 hh
  have hKh : (K : ℝ) * (X / K) = X := by field_simp
  have hle : t / (X / K) ≤ K := by rw [div_le_iff₀ hh, hKh]; exact htX
  set m := ⌈t / (X / K)⌉₊ with hm
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (Nat.ceil_pos.2 hpos).ne'
  have hmK : m ≤ K := Nat.ceil_le.2 hle
  have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by rw [Nat.cast_sub hm1, Nat.cast_one]
  refine ⟨by omega, ?_, ?_⟩
  · rw [hcast]
    have h1 := Nat.ceil_lt_add_one hpos.le
    rw [← hm] at h1
    have h2 : (m : ℝ) - 1 < t / (X / K) := by linarith
    rwa [lt_div_iff₀ hh] at h2
  · rw [hcast, sub_add_cancel]
    have h1 := Nat.le_ceil (t / (X / K))
    rw [← hm] at h1
    rwa [div_le_iff₀ hh] at h1

/-- For `i < K` the `i`-th cell of the mesh `X / K` lies in `[0, X]`. -/
lemma cell_subset {X : ℝ} (hX : 0 < X) {K : ℕ} (hK : 0 < K) {i : ℕ} (hi : i < K) {v : ℝ}
    (hv : v ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K))) : v ∈ Set.Icc 0 X := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hh : 0 < X / K := div_pos hX hKR
  have hiK : (i : ℝ) + 1 ≤ K := by exact_mod_cast Nat.succ_le_of_lt hi
  have hKh : (K : ℝ) * (X / K) = X := by field_simp
  constructor
  · have : 0 ≤ (i : ℝ) * (X / K) := by positivity
    linarith [hv.1]
  · have : ((i : ℝ) + 1) * (X / K) ≤ K * (X / K) := mul_le_mul_of_nonneg_right hiK hh.le
    linarith [hv.2]

/-- The cell supremum majorizes `φ` on the closed cell. -/
lemma le_cell {φ : ℝ → ℝ} {X M : ℝ} (hX : 0 < X) (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    {K : ℕ} (hK : 0 < K) {i : ℕ} (hi : i < K) {t : ℝ}
    (ht : t ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K))) :
    φ t ≤ cell φ (X / K) i := by
  unfold cell
  exact le_supOn (M := M) (fun v hv => (abs_le.1 (hbd v (cell_subset hX hK hi hv))).2) ht

/-- The cell suprema inherit the bound `|φ| ≤ M`. -/
lemma abs_cell_le {φ : ℝ → ℝ} {X M : ℝ} (hX : 0 < X) (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    {K : ℕ} (hK : 0 < K) {i : ℕ} (hi : i < K) : |cell φ (X / K) i| ≤ M := by
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  have hh : 0 < X / K := div_pos hX hKR
  have hab : (i : ℝ) * (X / K) ≤ ((i : ℝ) + 1) * (X / K) := by nlinarith
  have hmem : (i : ℝ) * (X / K) ∈ Set.Icc ((i : ℝ) * (X / K)) ((i + 1) * (X / K)) :=
    ⟨le_rfl, hab⟩
  rw [abs_le]
  constructor
  · have h1 := le_cell hX hbd hK hi hmem
    have h2 := (abs_le.1 (hbd _ (cell_subset hX hK hi hmem))).1
    linarith
  · unfold cell
    exact supOn_le hab (fun v hv => (abs_le.1 (hbd v (cell_subset hX hK hi hv))).2)

/-- At a continuity point `t ∈ (0, X)`, the step majorants on the mesh `X / K` converge to
`φ t` as `K → ∞`. -/
lemma tendsto_stepFn {φ : ℝ → ℝ} {X M : ℝ} (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M) {t : ℝ} (ht : t ∈ Set.Ioo 0 X)
    (hc : ContinuousAt φ t) :
    Tendsto (fun K : ℕ => stepFn φ (X / K) t) atTop (𝓝 (φ t)) := by
  rw [Metric.tendsto_atTop]
  intro η hη
  obtain ⟨δ, hδ, hδφ⟩ := Metric.continuousAt_iff.1 hc (η / 2) (by linarith)
  refine ⟨⌈X / δ⌉₊ + 1, fun K hK => ?_⟩
  have hK0 : 0 < K := by omega
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK0
  have hh : 0 < X / K := div_pos hX hKR
  have hhδ : X / K < δ := by
    rw [div_lt_iff₀ hKR]
    have h1 := Nat.le_ceil (X / δ)
    have h2 : ((⌈X / δ⌉₊ : ℕ) : ℝ) + 1 ≤ K := by exact_mod_cast hK
    have h3 : X / δ < K := by linarith
    rw [div_lt_iff₀ hδ] at h3
    linarith
  obtain ⟨hiK, hi1, hi2⟩ := ceil_index hX hK0 ht.1 ht.2.le
  set i := ⌈t / (X / K)⌉₊ - 1 with hidef
  have hstep : stepFn φ (X / K) t = cell φ (X / K) i := stepFn_eq φ hh i hi1 hi2
  rw [hstep, Real.dist_eq, abs_lt]
  have hlow : φ t ≤ cell φ (X / K) i := le_cell hX hbd hK0 hiK ⟨hi1.le, hi2⟩
  have hexp : ((i : ℝ) + 1) * (X / K) = (i : ℝ) * (X / K) + X / K := by ring
  have hup : cell φ (X / K) i ≤ φ t + η / 2 := by
    unfold cell
    apply supOn_le (by linarith)
    intro v hv
    have hdist : dist v t < δ := by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hv.1, hv.2]
    have := hδφ hdist
    rw [Real.dist_eq, abs_lt] at this
    linarith [this.2]
  constructor <;> linarith

/-- Dominated convergence: the integrals of the step majorants tend to `∫₀^X φ`. -/
lemma tendsto_integral_stepFn (φ : ℝ → ℝ) (X M : ℝ) (P : Finset ℝ) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    (hcont : ∀ u ∈ Set.Ioo 0 X, u ∉ P → ContinuousAt φ u) :
    Tendsto (fun K : ℕ => ∫ t in (0 : ℝ)..X, stepFn φ (X / K) t) atTop
      (𝓝 (∫ u in (0 : ℝ)..X, φ u)) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => M)
  · exact Filter.Eventually.of_forall (fun K => (measurable_stepFn φ _).aestronglyMeasurable)
  · refine eventually_atTop.2 ⟨1, fun K hK => Filter.Eventually.of_forall (fun t ht => ?_)⟩
    have hK0 : 0 < K := by omega
    rw [Set.uIoc_of_le hX.le] at ht
    obtain ⟨hiK, hi1, hi2⟩ := ceil_index hX hK0 ht.1 ht.2
    rw [Real.norm_eq_abs, stepFn_eq φ (div_pos hX (Nat.cast_pos.2 hK0)) _ hi1 hi2]
    exact abs_cell_le hX hbd hK0 hiK
  · exact intervalIntegrable_const
  · have hnull : ∀ᵐ t ∂(volume : Measure ℝ), t ∉ ((P : Set ℝ) ∪ {X}) := by
      apply measure_eq_zero_iff_ae_notMem.1
      exact ((P.finite_toSet).union (Set.finite_singleton X)).measure_zero _
    filter_upwards [hnull] with t ht htI
    rw [Set.uIoc_of_le hX.le] at htI
    simp only [Set.mem_union, Set.mem_singleton_iff, not_or, Finset.mem_coe] at ht
    have htIoo : t ∈ Set.Ioo 0 X := ⟨htI.1, lt_of_le_of_ne htI.2 ht.2⟩
    exact tendsto_stepFn hX hbd htIoo (hcont t htIoo ht.1)

/-- The statement of `GradedNear.riemann_upper`, proved inside the helper namespace. -/
theorem riemann_upper_aux (φ : ℝ → ℝ) (X M : ℝ) (P : Finset ℝ) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    (hcont : ∀ u ∈ Set.Ioo 0 X, u ∉ P → ContinuousAt φ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊, Λ n / n * φ (Real.log n / Real.log q)) /
          Real.log q ≤ (∫ u in (0 : ℝ)..X, φ u) + ε := by
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hbd 0 ⟨le_rfl, hX.le⟩)
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 (tendsto_integral_stepFn φ X M P hX hbd hcont)).2 _
      (lt_add_of_pos_right _ hε2))
  set K : ℕ := K₁ + 1 with hKdef
  have hK : 0 < K := Nat.succ_pos _
  have hKint := hK₁ K (Nat.le_succ _)
  have hKR : (0 : ℝ) < K := Nat.cast_pos.2 hK
  set h : ℝ := X / K with hhdef
  have hh : 0 < h := div_pos hX hKR
  have hKh : (K : ℝ) * h = X := by rw [hhdef]; field_simp
  refine ⟨⌈Real.exp (24 * K * M / ε)⌉₊ + 2, fun q hq => ?_⟩
  have hq1 : 1 < q := by omega
  have hqR : (1 : ℝ) < q := by exact_mod_cast hq1
  have hℓ : 0 < Real.log q := Real.log_pos hqR
  have hℓbig : 24 * K * M < ε * Real.log q := by
    have h1 : 24 * K * M / ε < Real.log q := by
      rw [Real.lt_log_iff_exp_lt (by linarith)]
      have := Nat.le_ceil (Real.exp (24 * K * M / ε))
      have : (⌈Real.exp (24 * K * M / ε)⌉₊ : ℝ) + 2 ≤ q := by exact_mod_cast hq
      linarith
    rw [div_lt_iff₀ hε] at h1
    linarith
  -- the partition `u i = i h`
  have hpart := sum_le_partition φ q hq1 (fun i => (i : ℝ) * h) (cell φ h) (by simp)
    (fun i => by push_cast; nlinarith) K
    (fun i hi t ht1 ht2 => le_cell hX hbd hK hi ⟨ht1.le, by push_cast at ht2 ⊢; linarith⟩)
  simp only [hKh] at hpart
  have hIcc : Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊ = Finset.Ioc 0 ⌊(q : ℝ) ^ X⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hIcc]
  -- each cell contributes `c_i h 𝓛 + 12 M`
  have hterm : ∀ i ∈ Finset.range K,
      cell φ h i * (mertensSum ((q : ℝ) ^ (((i + 1 : ℕ) : ℝ) * h)) -
        mertensSum ((q : ℝ) ^ ((i : ℝ) * h))) ≤ cell φ h i * h * Real.log q + 12 * M := by
    intro i hi
    have hi' : i < K := Finset.mem_range.1 hi
    have hs := mertensSum_short q hq1 (a := (i : ℝ) * h) (b := ((i + 1 : ℕ) : ℝ) * h)
      (by positivity) (by positivity)
    have hc := abs_cell_le hX hbd hK hi'
    rw [← hhdef] at hc
    have hdiff : ((i + 1 : ℕ) : ℝ) * h - (i : ℝ) * h = h := by push_cast; ring
    rw [hdiff] at hs
    set D := mertensSum ((q : ℝ) ^ (((i + 1 : ℕ) : ℝ) * h)) -
      mertensSum ((q : ℝ) ^ ((i : ℝ) * h))
    have h1 : cell φ h i * (D - h * Real.log q) ≤ |cell φ h i| * |D - h * Real.log q| := by
      rw [← abs_mul]; exact le_abs_self _
    have h2 : |cell φ h i| * |D - h * Real.log q| ≤ M * 12 :=
      mul_le_mul hc hs (abs_nonneg _) hM
    nlinarith
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.sum_mul] at hsum
  have hint := (integral_stepFn φ hh K).2
  rw [hKh] at hint
  rw [← hint] at hsum
  rw [div_le_iff₀ hℓ]
  have hlt := mul_lt_mul_of_pos_right hKint hℓ
  nlinarith

end FirstFactor

theorem riemann_upper (φ : ℝ → ℝ) (X M : ℝ) (P : Finset ℝ) (hX : 0 < X)
    (hbd : ∀ u ∈ Set.Icc 0 X, |φ u| ≤ M)
    (hcont : ∀ u ∈ Set.Ioo 0 X, u ∉ P → ContinuousAt φ u)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q₀ : ℕ, ∀ q : ℕ, q₀ ≤ q →
      (∑ n ∈ Finset.Icc 1 ⌊(q : ℝ) ^ X⌋₊, Λ n / n * φ (Real.log n / Real.log q)) /
          Real.log q ≤ (∫ u in (0 : ℝ)..X, φ u) + ε :=
  FirstFactor.riemann_upper_aux φ X M P hX hbd hcont hε

end GradedNear
