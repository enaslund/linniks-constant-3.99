module

public import GradedNear.Parabolic

/-!
# The near rows of the leaves: a concrete instance of the graded near lemma

A near row of a leaf (paper §§9.1–9.4; `computations/sieve_near/sieve_inputs.py` in the research repository,
`SieveNearTest`) fixes rational parameters: the detector `f = f_{2γ}` and the short Gram test
`g = f_{2g₁}` (the parabolic tests of `Parabolic.lean`, normalized so that `f(0) = g(0) = 1`), the
anchors `s ≥ s₁ ≥ 0`, and a Selberg-sieve weight with heights `h_k ≥ 0` on the `m` cells
`[t_k, t_{k+1})`, `t_k = t₀ + (2γ - t₀) k/m`, with level margin `ε' = 1/2000`. `Params.near` is
the corresponding `NearData`.

* `Params.valid`: the standing hypotheses `NearData.Valid` follow from checkable conditions on the
  rationals (`Params.Good`) and positive lower bounds `L_k` of `ω` on the cells;
* `Params.IB_le`: `I_B ≤ Σ_{j<n} (t₀/n) e^{(2s-s₁)b_j} f(a_j)²/g(b_j) +
  Σ_{k<m} (t_{k+1}-t_k) e^{2s t_{k+1}} f(t_k)²/L_k`, the upper Riemann sum of the builders
  (`n` short cells `[a_j, b_j)` of `[0, t₀)`, where the sieve weight vanishes);
* `Params.Dδ_eq`, `Params.Dδ_anti`: `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + Σ_k c_k e^{-2δ t_k}` with
  `c_k = h_k (t_{k+1}² - t_k²)/(2δ_k)`, and `D` decreases in `δ ≥ 0`.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Filter
open scoped Interval

namespace GradedNear

namespace Row

open Parabolic

/-- The rational parameters of a near row. -/
structure Params where
  /-- The detector is `f_{2γ}`. -/
  γ : ℚ
  /-- The short Gram test is `f_{2g₁}`. -/
  g1 : ℚ
  /-- The first sieve cell starts at `t₀`. -/
  t0 : ℚ
  /-- The reference anchor. -/
  s : ℚ
  /-- The safe anchor. -/
  s1 : ℚ
  /-- The sieve heights `h_k`, one per cell. -/
  h : List ℚ

/-- The level margin `ε' = 1/2000` (`EPS_LEVEL`). -/
def epsLev : ℚ := 1 / 2000

namespace Params

variable (p : Params)

/-- The number of sieve cells. -/
def m : ℕ := p.h.length

/-- The cell ends `t_k = t₀ + (2γ - t₀) k / m`. -/
def tk (k : ℕ) : ℚ := p.t0 + (2 * p.γ - p.t0) * k / p.m

/-- The sieve height of cell `k` (`0` beyond the list). -/
def hk (k : ℕ) : ℚ := p.h.getD k 0

/-- The `NearData` of the row, with the finite set `Δ` of anchor offsets of its entries. -/
def near (Δ : Finset ℝ) : NearData where
  f := fpar (2 * (p.γ : ℝ))
  xf := 2 * (p.γ : ℝ)
  Bf := 10 / (2 * (p.γ : ℝ)) ^ 2
  g := fpar (2 * (p.g1 : ℝ))
  xg := 2 * (p.g1 : ℝ)
  Bg := 10 / (2 * (p.g1 : ℝ)) ^ 2
  s₁ := p.s1
  s := p.s
  m := p.m
  t := fun k => (p.tk k : ℝ)
  h := fun k => (p.hk k : ℝ)
  ε' := (epsLev : ℝ)
  Δ := Δ

@[simp] lemma near_f (Δ : Finset ℝ) : (p.near Δ).f = fpar (2 * (p.γ : ℝ)) := rfl
@[simp] lemma near_g (Δ : Finset ℝ) : (p.near Δ).g = fpar (2 * (p.g1 : ℝ)) := rfl
@[simp] lemma near_s (Δ : Finset ℝ) : (p.near Δ).s = p.s := rfl
@[simp] lemma near_s₁ (Δ : Finset ℝ) : (p.near Δ).s₁ = p.s1 := rfl
@[simp] lemma near_m (Δ : Finset ℝ) : (p.near Δ).m = p.m := rfl
@[simp] lemma near_t (Δ : Finset ℝ) (k : ℕ) : (p.near Δ).t k = (p.tk k : ℝ) := rfl
@[simp] lemma near_h (Δ : Finset ℝ) (k : ℕ) : (p.near Δ).h k = (p.hk k : ℝ) := rfl
@[simp] lemma near_ε' (Δ : Finset ℝ) : (p.near Δ).ε' = (epsLev : ℝ) := rfl

/-- The conditions on the rationals under which the row's data are valid: `γ, g₁ > 0`,
`s ≥ s₁ ≥ 0`, `1/3 + 2ε' < t₀ < min(2γ, 2g₁)`, at least one cell, and `h_k ≥ 0`. -/
structure Good : Prop where
  γ_pos : 0 < p.γ
  g1_pos : 0 < p.g1
  s1_nonneg : 0 ≤ p.s1
  s1_le : p.s1 ≤ p.s
  t0_gt : 1 / 3 + 2 * epsLev < p.t0
  t0_lt : p.t0 < 2 * p.γ
  t0_lt_g : p.t0 < 2 * p.g1
  m_pos : 0 < p.m
  h_nonneg : ∀ k < p.m, 0 ≤ p.hk k

/-- The lower bound `L_k = g(t_{k+1}) e^{s₁ t_k} + h_k` of `ω` on cell `k`. -/
def Lk (k : ℕ) : ℝ :=
  fpar (2 * (p.g1 : ℝ)) (p.tk (k + 1)) * Real.exp (p.s1 * p.tk k) + p.hk k

variable {p}

lemma tk_zero : p.tk 0 = p.t0 := by simp [tk]

lemma tk_m (hg : p.Good) : p.tk p.m = 2 * p.γ := by
  have : (p.m : ℚ) ≠ 0 := by exact_mod_cast hg.m_pos.ne'
  simp only [tk]
  field_simp
  ring

lemma tk_lt (hg : p.Good) {j k : ℕ} (h : j < k) : p.tk j < p.tk k := by
  simp only [tk]
  have hm : (0 : ℚ) < p.m := by exact_mod_cast hg.m_pos
  have hw : 0 < 2 * p.γ - p.t0 := by linarith [hg.t0_lt]
  have : (j : ℚ) < k := by exact_mod_cast h
  have := mul_lt_mul_of_pos_left this hw
  linarith [div_lt_div_of_pos_right this hm]

lemma tk_mono (hg : p.Good) {j k : ℕ} (h : j ≤ k) : p.tk j ≤ p.tk k := by
  rcases eq_or_lt_of_le h with h | h
  · rw [h]
  · exact (tk_lt hg h).le

lemma t0_le_tk (hg : p.Good) (k : ℕ) : p.t0 ≤ p.tk k := by
  have := tk_mono hg (Nat.zero_le k)
  rwa [tk_zero] at this

lemma t0_pos (hg : p.Good) : 0 < p.t0 := by
  have := hg.t0_gt
  unfold epsLev at this
  linarith

lemma γ_pos' (hg : p.Good) : (0 : ℝ) < 2 * (p.γ : ℝ) := by
  have := hg.γ_pos; positivity

lemma g1_pos' (hg : p.Good) : (0 : ℝ) < 2 * (p.g1 : ℝ) := by
  have := hg.g1_pos; positivity

/-- A point of `[t₀, 2γ)` lies in some cell `[t_k, t_{k+1})`, `k < m`. -/
lemma exists_cell (hg : p.Good) {u : ℝ} (h0 : (p.t0 : ℝ) ≤ u) (h1 : u < 2 * (p.γ : ℝ)) :
    ∃ k < p.m, (p.tk k : ℝ) ≤ u ∧ u < p.tk (k + 1) := by
  have hm : (0 : ℝ) < p.m := by exact_mod_cast hg.m_pos
  have hw : (0 : ℝ) < 2 * p.γ - p.t0 := by
    have := hg.t0_lt; have : (p.t0 : ℝ) < 2 * p.γ := by exact_mod_cast this
    linarith
  set y := (u - p.t0) * p.m / (2 * p.γ - p.t0) with hy
  have hy0 : 0 ≤ y := by positivity
  have hym : y < p.m := by
    rw [hy, div_lt_iff₀ hw]
    nlinarith
  set k := ⌊y⌋₊ with hk
  have hk1 : (k : ℝ) ≤ y := Nat.floor_le hy0
  have hk2 : y < k + 1 := Nat.lt_floor_add_one y
  have hkm : k < p.m := by
    have : (k : ℝ) < p.m := lt_of_le_of_lt hk1 hym
    exact_mod_cast this
  refine ⟨k, hkm, ?_, ?_⟩
  · simp only [tk]
    push_cast
    rw [hy, le_div_iff₀ hw] at hk1
    have : (2 * (p.γ : ℝ) - p.t0) * k / p.m ≤ u - p.t0 := by
      rw [div_le_iff₀ hm]; nlinarith
    linarith
  · simp only [tk]
    push_cast
    rw [hy, div_lt_iff₀ hw] at hk2
    have : u - p.t0 < (2 * (p.γ : ℝ) - p.t0) * ((k : ℝ) + 1) / p.m := by
      rw [lt_div_iff₀ hm]; nlinarith
    linarith

/-! ## The weight `ω` -/

lemma sieveH_term_nonneg (hg : p.Good) (Δ : Finset ℝ) (u : ℝ) {j : ℕ} (hj : j < p.m) :
    0 ≤ (if (p.near Δ).t j ≤ u ∧ u < (p.near Δ).t (j + 1) then (p.near Δ).h j else 0) := by
  split_ifs
  · rw [near_h]; exact_mod_cast hg.h_nonneg j hj
  · exact le_rfl

lemma sieveH_nonneg (hg : p.Good) (Δ : Finset ℝ) (u : ℝ) : 0 ≤ (p.near Δ).sieveH u := by
  unfold NearData.sieveH
  exact Finset.sum_nonneg fun k hk => sieveH_term_nonneg hg Δ u (Finset.mem_range.1 hk)

/-- On cell `k` the sieve weight is at least `h_k`. -/
lemma hk_le_sieveH (hg : p.Good) (Δ : Finset ℝ) {k : ℕ} (hk : k < p.m) {u : ℝ}
    (hu : (p.tk k : ℝ) ≤ u ∧ u < p.tk (k + 1)) : (p.hk k : ℝ) ≤ (p.near Δ).sieveH u := by
  unfold NearData.sieveH
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j => if (p.near Δ).t j ≤ u ∧ u < (p.near Δ).t (j + 1) then (p.near Δ).h j else 0)
    (fun j hj => sieveH_term_nonneg hg Δ u (Finset.mem_range.1 hj)) (Finset.mem_range.2 hk))
  split_ifs with h
  · rw [near_h]
  · exact absurd hu h

lemma omega_eq (Δ : Finset ℝ) (u : ℝ) :
    (p.near Δ).omega u = fpar (2 * (p.g1 : ℝ)) u * Real.exp (p.s1 * u) + (p.near Δ).sieveH u :=
  rfl

lemma omega_nonneg (hg : p.Good) (Δ : Finset ℝ) {u : ℝ} (hu : 0 ≤ u) : 0 ≤ (p.near Δ).omega u := by
  rw [omega_eq]
  have := fpar_nonneg (g1_pos' hg) hu
  have := sieveH_nonneg hg Δ u
  positivity

/-- On `[0, t₀]`: `ω(u) ≥ g(b) e^{s₁ u}` for `u ≤ b`. -/
lemma omega_ge_short (hg : p.Good) (Δ : Finset ℝ) {u b : ℝ} (hu : 0 ≤ u) (hub : u ≤ b) :
    fpar (2 * (p.g1 : ℝ)) b * Real.exp (p.s1 * u) ≤ (p.near Δ).omega u := by
  rw [omega_eq]
  have h1 := fpar_anti (g1_pos' hg) hu hub
  have h2 := sieveH_nonneg hg Δ u
  have h3 := Real.exp_pos (p.s1 * u)
  nlinarith

/-- On cell `k`: `ω(u) ≥ L_k`. -/
lemma Lk_le_omega (hg : p.Good) (Δ : Finset ℝ) {k : ℕ} (hk : k < p.m) {u : ℝ}
    (hu : (p.tk k : ℝ) ≤ u ∧ u < p.tk (k + 1)) : p.Lk k ≤ (p.near Δ).omega u := by
  rw [omega_eq, Lk]
  have ht0 : (0 : ℝ) ≤ p.tk k := by
    have := t0_le_tk hg k; have := t0_pos hg
    have : (0 : ℚ) ≤ p.tk k := by linarith
    exact_mod_cast this
  have hu0 : 0 ≤ u := ht0.trans hu.1
  have h1 := fpar_anti (g1_pos' hg) hu0 hu.2.le
  have h2 := hk_le_sieveH hg Δ hk hu
  have h3 : Real.exp (p.s1 * p.tk k) ≤ Real.exp (p.s1 * u) := by
    have : (0 : ℝ) ≤ p.s1 := by exact_mod_cast hg.s1_nonneg
    exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hu.1 this)
  have h4 := fpar_nonneg (g1_pos' hg) (show (0 : ℝ) ≤ p.tk (k + 1) from ht0.trans (by
    have := tk_mono hg (Nat.le_succ k); exact_mod_cast this))
  have h5 := Real.exp_pos (p.s1 * p.tk k)
  nlinarith [mul_le_mul h1 h3 h5.le (fpar_nonneg (g1_pos' hg) hu0)]

/-! ## The integral `I_B` -/

/-- The integrand `e^{2su} f(u)² / ω(u)` of `I_B`. -/
def ibIntegrand (Δ : Finset ℝ) (u : ℝ) : ℝ :=
  Real.exp (2 * (p.s : ℝ) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 / (p.near Δ).omega u

lemma IB_eq (Δ : Finset ℝ) : (p.near Δ).IB = ∫ u in Ioi (0 : ℝ), p.ibIntegrand Δ u := rfl

/-- The short cell ends `a_j = t₀ j / n`. -/
def aj (n j : ℕ) : ℝ := p.t0 * j / n

/-- The bound of the integrand on the short cell `[a_j, a_{j+1})`:
`e^{(2s-s₁) a_{j+1}} f(a_j)² / g(a_{j+1})`. -/
def cS (n j : ℕ) : ℝ :=
  Real.exp ((2 * p.s - p.s1) * p.aj n (j + 1)) * fpar (2 * (p.γ : ℝ)) (p.aj n j) ^ 2 /
    fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1))

/-- The bound of the integrand on cell `k`: `e^{2s t_{k+1}} f(t_k)² / L_k`. -/
def cL (k : ℕ) : ℝ :=
  Real.exp (2 * p.s * p.tk (k + 1)) * fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 / p.Lk k

/-- **The builders' upper Riemann sum** of `I_B`, with `n` short cells on `[0, t₀)`. -/
def riemann (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, (p.t0 / n : ℝ) * p.cS n j +
    ∑ k ∈ Finset.range p.m, ((p.tk (k + 1) : ℝ) - p.tk k) * p.cL k

/-- The step majorant of the integrand: the cell bounds on the cells. -/
def stepMaj (n : ℕ) (u : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, (Ico (p.aj n j) (p.aj n (j + 1))).indicator (fun _ => p.cS n j) u +
    ∑ k ∈ Finset.range p.m, (Ico (p.tk k : ℝ) (p.tk (k + 1))).indicator (fun _ => p.cL k) u

lemma aj_mono {n : ℕ} (hn : 0 < n) (hg : p.Good) {i j : ℕ} (h : i ≤ j) : p.aj n i ≤ p.aj n j := by
  have ht : (0 : ℝ) ≤ p.t0 := by exact_mod_cast (t0_pos hg).le
  unfold aj
  gcongr

lemma aj_le_t0 {n : ℕ} (hn : 0 < n) (hg : p.Good) {j : ℕ} (h : j ≤ n) : p.aj n j ≤ p.t0 := by
  have ht : (0 : ℝ) ≤ p.t0 := by exact_mod_cast (t0_pos hg).le
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold aj
  rw [div_le_iff₀ hn']
  have : (j : ℝ) ≤ n := by exact_mod_cast h
  nlinarith

lemma aj_nonneg {n : ℕ} (hg : p.Good) (j : ℕ) : 0 ≤ p.aj n j := by
  have ht : (0 : ℝ) ≤ p.t0 := by exact_mod_cast (t0_pos hg).le
  unfold aj; positivity

lemma cS_nonneg (n j : ℕ) (hg : p.Good) : 0 ≤ p.cS n j := by
  unfold cS
  have := fpar_nonneg (g1_pos' hg) (aj_nonneg hg (n := n) (j + 1))
  positivity

lemma cL_nonneg (hL : ∀ k < p.m, 0 < p.Lk k) {k : ℕ} (hk : k < p.m) : 0 ≤ p.cL k := by
  unfold cL
  have := hL k hk
  positivity

lemma stepMaj_nonneg (hg : p.Good) (hL : ∀ k < p.m, 0 < p.Lk k) (n : ℕ) (u : ℝ) :
    0 ≤ p.stepMaj n u := by
  unfold stepMaj
  refine add_nonneg (Finset.sum_nonneg fun j _ => ?_) (Finset.sum_nonneg fun k hk => ?_)
  · exact Set.indicator_nonneg (fun _ _ => cS_nonneg n j hg) u
  · exact Set.indicator_nonneg (fun _ _ => cL_nonneg hL (Finset.mem_range.1 hk)) u

lemma ibIntegrand_nonneg (hg : p.Good) (Δ : Finset ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ p.ibIntegrand Δ u := by
  unfold ibIntegrand
  have := omega_nonneg hg Δ hu
  positivity

/-- The integrand is below the short-cell bound on `[a_j, a_{j+1})`. -/
lemma ibIntegrand_le_cS (hg : p.Good) (Δ : Finset ℝ) {n : ℕ} (hn : 0 < n) {j : ℕ} (hj : j < n)
    {u : ℝ} (hu : p.aj n j ≤ u ∧ u < p.aj n (j + 1)) : p.ibIntegrand Δ u ≤ p.cS n j := by
  have hγ := γ_pos' hg
  have hg1 := g1_pos' hg
  have hu0 : 0 ≤ u := (aj_nonneg hg j).trans hu.1
  have hb : p.aj n (j + 1) ≤ p.t0 := aj_le_t0 hn hg (by omega)
  have ht0g : (p.t0 : ℝ) < 2 * p.g1 := by exact_mod_cast hg.t0_lt_g
  have hgb : 0 < fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1)) :=
    fpar_pos hg1 (aj_nonneg hg _) (hb.trans_lt ht0g)
  have hω := omega_ge_short hg Δ hu0 hu.2.le
  have hpos : 0 < fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1)) * Real.exp (p.s1 * u) :=
    mul_pos hgb (Real.exp_pos _)
  have hss : (0 : ℝ) ≤ 2 * p.s - p.s1 := by
    have h1 : (p.s1 : ℝ) ≤ p.s := by exact_mod_cast hg.s1_le
    have h2 : (0 : ℝ) ≤ p.s1 := by exact_mod_cast hg.s1_nonneg
    linarith
  unfold ibIntegrand cS
  calc Real.exp (2 * (p.s : ℝ) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 / (p.near Δ).omega u
      ≤ Real.exp (2 * (p.s : ℝ) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 /
          (fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1)) * Real.exp (p.s1 * u)) :=
        div_le_div_of_nonneg_left (by positivity) hpos hω
    _ = Real.exp ((2 * p.s - p.s1) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 /
          fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1)) := by
        rw [show (2 * (p.s : ℝ) - p.s1) * u = 2 * p.s * u - p.s1 * u by ring, Real.exp_sub]
        field_simp
    _ ≤ Real.exp ((2 * p.s - p.s1) * p.aj n (j + 1)) * fpar (2 * (p.γ : ℝ)) (p.aj n j) ^ 2 /
          fpar (2 * (p.g1 : ℝ)) (p.aj n (j + 1)) := by
        refine div_le_div_of_nonneg_right (mul_le_mul (Real.exp_le_exp.2
          (mul_le_mul_of_nonneg_left hu.2.le hss)) (pow_le_pow_left₀ (fpar_nonneg hγ hu0)
          (fpar_anti hγ (aj_nonneg hg j) hu.1) 2) (by positivity) (Real.exp_pos _).le) hgb.le

/-- The integrand is below the bound of cell `k` on `[t_k, t_{k+1})`. -/
lemma ibIntegrand_le_cL (hg : p.Good) (Δ : Finset ℝ) (hL : ∀ k < p.m, 0 < p.Lk k) {k : ℕ}
    (hk : k < p.m) {u : ℝ} (hu : (p.tk k : ℝ) ≤ u ∧ u < p.tk (k + 1)) :
    p.ibIntegrand Δ u ≤ p.cL k := by
  have hγ := γ_pos' hg
  have htk : (0 : ℝ) ≤ p.tk k := by
    have := t0_le_tk hg k; have := t0_pos hg
    have : (0 : ℚ) ≤ p.tk k := by linarith
    exact_mod_cast this
  have hu0 : 0 ≤ u := htk.trans hu.1
  have hω := Lk_le_omega hg Δ hk hu
  have hLk := hL k hk
  have hs : (0 : ℝ) ≤ p.s := by
    have h1 : (p.s1 : ℝ) ≤ p.s := by exact_mod_cast hg.s1_le
    have h2 : (0 : ℝ) ≤ p.s1 := by exact_mod_cast hg.s1_nonneg
    linarith
  unfold ibIntegrand cL
  calc Real.exp (2 * (p.s : ℝ) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 / (p.near Δ).omega u
      ≤ Real.exp (2 * (p.s : ℝ) * u) * fpar (2 * (p.γ : ℝ)) u ^ 2 / p.Lk k :=
        div_le_div_of_nonneg_left (by positivity) hLk hω
    _ ≤ Real.exp (2 * p.s * p.tk (k + 1)) * fpar (2 * (p.γ : ℝ)) (p.tk k) ^ 2 / p.Lk k := by
        refine div_le_div_of_nonneg_right (mul_le_mul (Real.exp_le_exp.2 ?_)
          (pow_le_pow_left₀ (fpar_nonneg hγ hu0) (fpar_anti hγ htk hu.1) 2) (by positivity)
          (Real.exp_pos _).le) hLk.le
        have := mul_le_mul_of_nonneg_left hu.2.le hs
        linarith

/-- The integrand is below the step majorant on `(0, ∞)`. -/
lemma ibIntegrand_le_stepMaj (hg : p.Good) (Δ : Finset ℝ) (hL : ∀ k < p.m, 0 < p.Lk k) {n : ℕ}
    (hn : 0 < n) {u : ℝ} (hu : 0 < u) : p.ibIntegrand Δ u ≤ p.stepMaj n u := by
  have hγ := γ_pos' hg
  have hS := fun j (_ : j ∈ Finset.range n) =>
    Set.indicator_nonneg (fun _ _ => cS_nonneg n j hg) (s := Ico (p.aj n j) (p.aj n (j + 1))) u
  have hLn := fun k (hk : k ∈ Finset.range p.m) =>
    Set.indicator_nonneg (fun _ _ => cL_nonneg hL (Finset.mem_range.1 hk))
      (s := Ico (p.tk k : ℝ) (p.tk (k + 1))) u
  have ht0 : (0 : ℝ) < p.t0 := by exact_mod_cast t0_pos hg
  rcases lt_or_ge u p.t0 with hut | hut
  · -- a short cell
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set y := u * n / p.t0 with hy
    have hy0 : 0 ≤ y := by positivity
    have hyn : y < n := by rw [hy, div_lt_iff₀ ht0]; nlinarith
    set j := ⌊y⌋₊
    have hj1 : (j : ℝ) ≤ y := Nat.floor_le hy0
    have hj2 : y < j + 1 := Nat.lt_floor_add_one y
    have hjn : j < n := by exact_mod_cast lt_of_le_of_lt hj1 hyn
    have hcell : p.aj n j ≤ u ∧ u < p.aj n (j + 1) := by
      unfold aj
      constructor
      · rw [div_le_iff₀ hn']
        rw [hy, le_div_iff₀ ht0] at hj1
        linarith
      · rw [lt_div_iff₀ hn']
        rw [hy, div_lt_iff₀ ht0] at hj2
        push_cast
        linarith
    calc p.ibIntegrand Δ u ≤ p.cS n j := ibIntegrand_le_cS hg Δ hn hjn hcell
      _ = (Ico (p.aj n j) (p.aj n (j + 1))).indicator (fun _ => p.cS n j) u :=
          (Set.indicator_of_mem (show u ∈ Ico (p.aj n j) (p.aj n (j + 1)) from hcell)
            (fun _ => p.cS n j)).symm
      _ ≤ ∑ i ∈ Finset.range n,
            (Ico (p.aj n i) (p.aj n (i + 1))).indicator (fun _ => p.cS n i) u :=
          Finset.single_le_sum (f := fun i => (Ico (p.aj n i) (p.aj n (i + 1))).indicator
            (fun _ => p.cS n i) u) hS (Finset.mem_range.2 hjn)
      _ ≤ p.stepMaj n u := le_add_of_nonneg_right (Finset.sum_nonneg hLn)
  · rcases lt_or_ge u (2 * (p.γ : ℝ)) with hu2 | hu2
    · obtain ⟨k, hk, hcell⟩ := exists_cell hg hut hu2
      calc p.ibIntegrand Δ u ≤ p.cL k := ibIntegrand_le_cL hg Δ hL hk hcell
        _ = (Ico (p.tk k : ℝ) (p.tk (k + 1))).indicator (fun _ => p.cL k) u :=
            (Set.indicator_of_mem (show u ∈ Ico (p.tk k : ℝ) (p.tk (k + 1)) from hcell)
              (fun _ => p.cL k)).symm
        _ ≤ ∑ i ∈ Finset.range p.m,
              (Ico (p.tk i : ℝ) (p.tk (i + 1))).indicator (fun _ => p.cL i) u :=
            Finset.single_le_sum (f := fun i => (Ico (p.tk i : ℝ) (p.tk (i + 1))).indicator
              (fun _ => p.cL i) u) hLn (Finset.mem_range.2 hk)
        _ ≤ p.stepMaj n u := le_add_of_nonneg_left (Finset.sum_nonneg hS)
    · have hf0 : fpar (2 * (p.γ : ℝ)) u = 0 := (fpar_condition1 hγ).vanish u hu2
      have : p.ibIntegrand Δ u = 0 := by unfold ibIntegrand; rw [hf0]; simp
      rw [this]
      exact stepMaj_nonneg hg hL n u

lemma measurable_omega (hg : p.Good) (Δ : Finset ℝ) : Measurable (p.near Δ).omega := by
  have hg1 := g1_pos' hg
  refine Measurable.add ((continuous_fpar hg1).measurable.mul (by fun_prop)) ?_
  unfold NearData.sieveH
  refine Finset.measurable_sum _ fun k _ => ?_
  exact Measurable.ite measurableSet_Ico measurable_const measurable_const

lemma measurable_ibIntegrand (hg : p.Good) (Δ : Finset ℝ) : Measurable (p.ibIntegrand Δ) := by
  unfold ibIntegrand
  exact ((by fun_prop : Measurable fun u : ℝ => Real.exp (2 * (p.s : ℝ) * u)).mul
    ((continuous_fpar (γ_pos' hg)).measurable.pow_const 2)).div (measurable_omega hg Δ)

lemma integrable_stepMaj (n : ℕ) :
    Integrable (p.stepMaj n) (volume.restrict (Ioi (0 : ℝ))) := by
  unfold stepMaj
  refine Integrable.add (integrable_finsetSum _ fun j _ => ?_)
    (integrable_finsetSum _ fun k _ => ?_)
  · exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact (measure_mono inter_subset_left).trans_lt measure_Ico_lt_top |>.ne))
  · exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact (measure_mono inter_subset_left).trans_lt measure_Ico_lt_top |>.ne))

lemma real_restrict_Ico_le {a b : ℝ} (hab : a ≤ b) :
    (volume.restrict (Ioi (0 : ℝ))).real (Ico a b) ≤ b - a := by
  rw [measureReal_def, Measure.restrict_apply measurableSet_Ico]
  have h : volume (Ico a b ∩ Ioi (0 : ℝ)) ≤ ENNReal.ofReal (b - a) :=
    (measure_mono inter_subset_left).trans (Real.volume_Ico).le
  calc (volume (Ico a b ∩ Ioi (0 : ℝ))).toReal ≤ (ENNReal.ofReal (b - a)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    _ = b - a := ENNReal.toReal_ofReal (by linarith)

lemma integral_stepMaj_le (hg : p.Good) (hL : ∀ k < p.m, 0 < p.Lk k) {n : ℕ} (hn : 0 < n) :
    ∫ u in Ioi (0 : ℝ), p.stepMaj n u ≤ p.riemann n := by
  unfold stepMaj riemann
  have hi1 : ∀ j ∈ Finset.range n, Integrable ((Ico (p.aj n j) (p.aj n (j + 1))).indicator
      fun _ => p.cS n j) (volume.restrict (Ioi (0 : ℝ))) := fun j _ =>
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact (measure_mono inter_subset_left).trans_lt measure_Ico_lt_top |>.ne))
  have hi2 : ∀ k ∈ Finset.range p.m, Integrable ((Ico (p.tk k : ℝ) (p.tk (k + 1))).indicator
      fun _ => p.cL k) (volume.restrict (Ioi (0 : ℝ))) := fun k _ =>
    (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by
      rw [Measure.restrict_apply measurableSet_Ico]
      exact (measure_mono inter_subset_left).trans_lt measure_Ico_lt_top |>.ne))
  rw [integral_add (integrable_finsetSum _ hi1) (integrable_finsetSum _ hi2),
    integral_finsetSum _ hi1, integral_finsetSum _ hi2]
  refine add_le_add (Finset.sum_le_sum fun j _ => ?_) (Finset.sum_le_sum fun k hk => ?_)
  · rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul]
    have hw : p.aj n (j + 1) - p.aj n j = (p.t0 / n : ℝ) := by
      unfold aj; push_cast; field_simp; ring
    rw [← hw]
    exact mul_le_mul_of_nonneg_right (real_restrict_Ico_le (aj_mono hn hg (Nat.le_succ j)))
      (cS_nonneg n j hg)
  · rw [integral_indicator_const _ measurableSet_Ico, smul_eq_mul]
    refine mul_le_mul_of_nonneg_right (real_restrict_Ico_le ?_)
      (cL_nonneg hL (Finset.mem_range.1 hk))
    exact_mod_cast tk_mono hg (Nat.le_succ k)

/-- **`I_B` is at most the builders' Riemann sum.** -/
theorem IB_le (hg : p.Good) (Δ : Finset ℝ) (hL : ∀ k < p.m, 0 < p.Lk k) {n : ℕ} (hn : 0 < n) :
    (p.near Δ).IB ≤ p.riemann n := by
  rw [IB_eq]
  refine le_trans ?_ (integral_stepMaj_le hg hL hn)
  refine integral_mono_of_nonneg ?_ (integrable_stepMaj (p := p) n) ?_
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ibIntegrand_nonneg hg Δ (le_of_lt hu)
  · exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu =>
      ibIntegrand_le_stepMaj hg Δ hL hn hu

/-- **`I_B > 0`.** -/
theorem IB_pos (hg : p.Good) (Δ : Finset ℝ) (hL : ∀ k < p.m, 0 < p.Lk k) : 0 < (p.near Δ).IB := by
  have hγ := γ_pos' hg
  have hg1 := g1_pos' hg
  have ht0 : (0 : ℝ) < p.t0 := by exact_mod_cast t0_pos hg
  have ht0γ : (p.t0 : ℝ) < 2 * p.γ := by exact_mod_cast hg.t0_lt
  have ht0g : (p.t0 : ℝ) < 2 * p.g1 := by exact_mod_cast hg.t0_lt_g
  rw [IB_eq]
  have hint : Integrable (p.ibIntegrand Δ) (volume.restrict (Ioi (0 : ℝ))) := by
    refine (integrable_stepMaj (p := p) 1).mono' (measurable_ibIntegrand hg Δ).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ibIntegrand_nonneg hg Δ (le_of_lt hu))]
      exact ibIntegrand_le_stepMaj hg Δ hL one_pos hu
  -- the integrand is positive on `(0, t₀)`
  have hsupp : Ioo 0 (p.t0 : ℝ) ⊆ Function.support (p.ibIntegrand Δ) := fun u hu => by
    have hf := fpar_pos hγ hu.1.le (hu.2.trans ht0γ)
    have hω : 0 < (p.near Δ).omega u :=
      lt_of_lt_of_le (mul_pos (fpar_pos hg1 hu.1.le (hu.2.trans ht0g)) (Real.exp_pos _))
        (omega_ge_short hg Δ hu.1.le le_rfl)
    exact (show 0 < p.ibIntegrand Δ u by unfold ibIntegrand; positivity).ne'
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] p.ibIntegrand Δ :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u hu => ibIntegrand_nonneg hg Δ (le_of_lt hu)
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  calc (0 : ENNReal) < volume (Ioo 0 (p.t0 : ℝ)) := by
        rw [Real.volume_Ioo, sub_zero]; exact ENNReal.ofReal_pos.2 ht0
    _ = (volume.restrict (Ioi (0 : ℝ))) (Ioo 0 (p.t0 : ℝ)) := by
        rw [Measure.restrict_apply measurableSet_Ioo, inter_eq_left.2 Ioo_subset_Ioi_self]
    _ ≤ (volume.restrict (Ioi (0 : ℝ))) (Function.support (p.ibIntegrand Δ)) := measure_mono hsupp

/-! ## The diagonal `D(δ)` -/

/-- The level exponent `δ_k = (t_k - 1/3)/2 - ε'` of cell `k`. -/
def lev (k : ℕ) : ℝ := ((p.tk k : ℝ) - 1 / 3) / 2 - epsLev

/-- The sieve coefficients `c_k = h_k (t_{k+1}² - t_k²) / (2 δ_k)` of `D(δ)`. -/
def ck (k : ℕ) : ℝ := (p.hk k : ℝ) * ((p.tk (k + 1) : ℝ) ^ 2 - (p.tk k : ℝ) ^ 2) / (2 * p.lev k)

lemma lev_pos (hg : p.Good) (k : ℕ) : 0 < p.lev k := by
  have h1 := t0_le_tk hg k
  have h2 := hg.t0_gt
  unfold lev epsLev at *
  have : (1 / 3 + 2 * (1 / 2000) : ℝ) < p.tk k := by
    have h3 : (1 / 3 + 2 * (1 / 2000) : ℚ) < p.tk k := lt_of_lt_of_le h2 h1
    have h4 : ((1 / 3 + 2 * (1 / 2000) : ℚ) : ℝ) < p.tk k := by exact_mod_cast h3
    push_cast at h4
    exact h4
  linarith

lemma ck_nonneg (hg : p.Good) {k : ℕ} (hk : k < p.m) : 0 ≤ p.ck k := by
  unfold ck
  have hh : (0 : ℝ) ≤ p.hk k := by exact_mod_cast hg.h_nonneg k hk
  have ht : (p.tk k : ℝ) ≤ p.tk (k + 1) := by exact_mod_cast tk_mono hg (Nat.le_succ k)
  have ht0 : (0 : ℝ) ≤ p.tk k := by
    have := t0_le_tk hg k; have := t0_pos hg
    have : (0 : ℚ) ≤ p.tk k := by linarith
    exact_mod_cast this
  have := lev_pos hg k
  have : (0 : ℝ) ≤ (p.tk (k + 1) : ℝ) ^ 2 - (p.tk k : ℝ) ^ 2 := by nlinarith
  positivity

lemma d₁_eq (hg : p.Good) (Δ : Finset ℝ) : (p.near Δ).d₁ = 1 / 6 := by
  simp only [NearData.d₁, near_g, fpar_zero (g1_pos' hg)]

/-- The Gram integral `∫₀^∞ g(u) e^{(s₁-2δ)u} du` is the transform of `g` at `2δ - s₁`. -/
lemma gram_integral_eq (hg : p.Good) (δ : ℝ) :
    ∫ u in Ioi (0 : ℝ), fpar (2 * (p.g1 : ℝ)) u * Real.exp ((p.s1 - 2 * δ) * u) =
      2 * p.g1 * Phi (2 * p.g1 * (2 * δ - p.s1)) := by
  have hg1 := g1_pos' hg
  have hc := fpar_condition1 hg1
  rw [← laplace_fpar_real hg1, laplace_re_real hc, intervalIntegral.integral_of_le hg1.le]
  have hf : ∀ u : ℝ, fpar (2 * (p.g1 : ℝ)) u * Real.exp ((p.s1 - 2 * δ) * u) =
      fpar (2 * (p.g1 : ℝ)) u * Real.exp (-((2 * δ - p.s1) * u)) := fun u => by ring_nf
  simp_rw [hf]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioc_subset_Ioi_self : Ioc (0 : ℝ) (2 * p.g1) ⊆ Ioi 0) (fun u hu => ?_)
  have hu' : 2 * (p.g1 : ℝ) ≤ u := by
    by_contra h
    exact hu.2 ⟨hu.1, (not_le.1 h).le⟩
  simp [hc.vanish u hu']

/-- **`D(δ)` in closed form**: `D(δ) = 2g₁ Φ(2g₁(2δ - s₁)) + Σ_k c_k e^{-2δ t_k}`. -/
theorem Dδ_eq (hg : p.Good) (Δ : Finset ℝ) (δ : ℝ) :
    (p.near Δ).Dδ δ = 2 * p.g1 * Phi (2 * p.g1 * (2 * δ - p.s1)) +
      ∑ k ∈ Finset.range p.m, p.ck k * Real.exp (-2 * δ * p.tk k) := by
  unfold NearData.Dδ
  simp only [near_g, near_s₁, near_m, near_h, near_t]
  rw [gram_integral_eq hg δ]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold ck lev NearData.level
  simp only [near_t, near_ε']
  ring

/-- **`D` decreases** in the offset `δ`. -/
theorem Dδ_anti (hg : p.Good) (Δ : Finset ℝ) {δ δ' : ℝ} (h : δ ≤ δ') :
    (p.near Δ).Dδ δ' ≤ (p.near Δ).Dδ δ := by
  have hg1 := g1_pos' hg
  rw [Dδ_eq hg, Dδ_eq hg]
  refine add_le_add (mul_le_mul_of_nonneg_left (Phi_anti ?_) hg1.le)
    (Finset.sum_le_sum fun k hk => ?_)
  · nlinarith
  · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (ck_nonneg hg (Finset.mem_range.1 hk))
    have ht0 : (0 : ℝ) ≤ p.tk k := by
      have := t0_le_tk hg k; have := t0_pos hg
      have : (0 : ℚ) ≤ p.tk k := by linarith
      exact_mod_cast this
    nlinarith

/-! ## Validity -/

/-- **The row's data are valid** when the rationals are `Good`, every offset is `≥ 0` and every
cell bound `L_k` is positive. -/
theorem valid (hg : p.Good) (Δ : Finset ℝ) (hΔ : ∀ δ ∈ Δ, 0 ≤ δ) (hL : ∀ k < p.m, 0 < p.Lk k) :
    (p.near Δ).Valid := by
  have hγ := γ_pos' hg
  have hg1 := g1_pos' hg
  -- a uniform lower bound for ω where f ≠ 0
  set c := min (fpar (2 * (p.g1 : ℝ)) p.t0)
    ((Finset.range p.m).inf' (Finset.nonempty_range_iff.2 hg.m_pos.ne') p.Lk) with hc
  have ht0γ : (p.t0 : ℝ) < 2 * p.γ := by exact_mod_cast hg.t0_lt
  have ht0g : (p.t0 : ℝ) < 2 * p.g1 := by exact_mod_cast hg.t0_lt_g
  have ht0 : (0 : ℝ) < p.t0 := by exact_mod_cast t0_pos hg
  have hc0 : 0 < c := by
    refine lt_min (fpar_pos hg1 ht0.le ht0g) ?_
    rw [Finset.lt_inf'_iff]
    exact fun k hk => hL k (Finset.mem_range.1 hk)
  refine ⟨fpar_condition1 hγ, fpar_condition1 hg1, fpar_condition2 hg1, ?_, ?_, ?_, ?_, hΔ, ?_,
    ?_⟩
  · show (0 : ℝ) < (epsLev : ℝ); norm_num [epsLev]
  · intro k _
    show (p.tk k : ℝ) < p.tk (k + 1)
    exact_mod_cast tk_lt hg (Nat.lt_succ_self k)
  · show 1 / 3 + 2 * (epsLev : ℝ) < p.tk 0
    rw [tk_zero]
    have h := hg.t0_gt
    have h' : ((1 / 3 + 2 * epsLev : ℚ) : ℝ) < p.t0 := by exact_mod_cast h
    push_cast at h'
    exact h'
  · intro k hk
    rw [near_h]
    exact_mod_cast hg.h_nonneg k hk
  · refine ⟨c, hc0, fun u hu hfu => ?_⟩
    rw [near_f] at hfu
    have hu2 : u < 2 * (p.γ : ℝ) := by
      by_contra h
      exact hfu (fpar_of_lt (lt_of_le_of_ne (not_lt.1 h) fun e => by
        rw [← e] at hfu; exact hfu (by rw [fpar_of_le le_rfl, div_self hγ.ne', P_one])))
    rcases lt_or_ge u p.t0 with hut | hut
    · -- the short range: ω(u) ≥ g(t₀) e^{s₁ u} ≥ g(t₀)
      calc c ≤ fpar (2 * (p.g1 : ℝ)) p.t0 := min_le_left _ _
        _ ≤ fpar (2 * (p.g1 : ℝ)) p.t0 * Real.exp (p.s1 * u) := by
            refine le_mul_of_one_le_right (fpar_nonneg hg1 ht0.le) (Real.one_le_exp ?_)
            have : (0 : ℝ) ≤ p.s1 := by exact_mod_cast hg.s1_nonneg
            positivity
        _ ≤ (p.near Δ).omega u := omega_ge_short hg Δ hu hut.le
    · obtain ⟨k, hk, hcell⟩ := exists_cell hg hut hu2
      calc c ≤ (Finset.range p.m).inf' _ p.Lk := min_le_right _ _
        _ ≤ p.Lk k := Finset.inf'_le _ (Finset.mem_range.2 hk)
        _ ≤ (p.near Δ).omega u := Lk_le_omega hg Δ hk hcell
  · exact IB_pos hg Δ hL

end Params

end Row

end GradedNear

end
