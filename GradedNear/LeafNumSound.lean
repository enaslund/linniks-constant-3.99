module

public import LeafNumCore
public import GradedNear.KernelFacts
public import GradedNear.FarFacts
public import GradedNear.Interval.Sound

/-!
# Soundness of the leaf enclosures `LeafNumCore`

Every enclosure of `LeafNumCore` contains the value of the corresponding real function of
`GradedNear/Functions.lean` (`x ∈ₗ I` is `I.lo ≤ x ≤ I.hi`, `IntervalCore.Mem`):

* the constants: `T_eq`, `kappa_eq`, `beta_eq`, `cast_H0` (`(H0 : ℝ) = GradedNear.Kernel.H0`);
* `benv_sound`, `gphi_sound`, `G_sound`, `hratio_sound` (`λ ≠ 0`), `cpa_sound` (`a ≠ 0`),
  `jold_sound` (`a ≠ 0`), `jnew_sound` (`a ≠ 0`, `p ≠ 0`), from the closed forms `Benv_eq`,
  `hRatio_eq`, `Cpa_closed` of `GradedNear.KernelFacts`;
* `winv_sound` (`c₁, c₂ > 0`), `w_sound` (when the enclosure of `w⁻¹` is positive), `w_lo_le`
  (the lower end is always a lower bound), `V_mem`, `V_le_vUpper`, and their instances for the
  profiles `inherited` and `retuned`.

**The far weight.** `winv_eq` splits `w(λ)⁻¹ = ∫_u^x w₀² e^{2λt} dt` at `v` and substitutes
`t = u − ε + r²` on `[u, v]` (`integral_subst_sq`, from
`intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg`), which gives
`2 e^{a(u−ε)} ∫_{√ε}^{√(c₂+ε)} r² e^{a r²} dr + √(c₂+ε) ∫_v^x e^{at} dt`. `rInt_sound` encloses
`∫_{√y_a}^{√y_b} (r² − D) e^{c r²} dr` (`rIntR`): the Taylor polynomial integrates exactly
(`integral_poly`), and `|e^x − Σ_{m<N} x^m/m!| ≤ 2|x|^N/N!` for `2|x| ≤ N + 1`
(`abs_exp_sub_sum_le`, from `Complex.exp_bound'`).

**Fixed point.** `Fx.mem_add`, `Fx.mem_mulRat`, `Fx.mem_mul`, `Fx.mem_ofRat`, `Fx.mem_ofIval`: the
fixed-point operations (ends `lo/2^w`, `hi/2^w`) are sound; `mem_horner` and `mem_serPhi` follow.

**The constant `V`.** With `h = c₂/10`, `min((s − ih)₊, h) = (s − ih)₊ − (s − (i+1)h)₊`, so
`J_i = K(ih) − K((i+1)h)` with `K(d) = ∫_u^x w₀⁻² (t − u − d)₊ dt` (`V_eq`); `K_eq` computes `K(d)`
for `0 ≤ d ≤ c₂` by the same substitution on `[u + d, v]` and the closed form
`∫_v^x e^{θt}(t − c) dt` (`integral_exp_affine`) on `[v, x]`.
-/

@[expose] public section

open IntervalCore MeasureTheory Set

namespace LeafNumCore

open GradedNear

/-! ## The constants -/

theorem T_eq : T = Kernel.T := rfl

theorem kappa_eq : kappa = Kernel.kappa := rfl

theorem beta_eq (i : Fin 16) : beta i = Kernel.beta i := by fin_cases i <;> rfl

theorem cast_sumQ (f : ℕ → ℚ) : ∀ n, ((sumQ f n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, (f i : ℝ)
  | 0 => by simp [sumQ]
  | n + 1 => by rw [sumQ, Finset.sum_range_succ, Rat.cast_add, cast_sumQ f n]

/-- `Σ_{i<16} g(β_i) = Σ_{i : Fin 16} g(β_i)`. -/
theorem sum_range_beta (g : ℕ → ℚ → ℝ) :
    ∑ i ∈ Finset.range 16, g i (beta i) = ∑ i : Fin 16, g i (Kernel.beta i) := by
  rw [← Fin.sum_univ_eq_sum_range (fun i => g i (beta i)) 16]
  exact Finset.sum_congr rfl fun i _ => by rw [beta_eq]

theorem cast_H0 : ((H0 : ℚ) : ℝ) = Kernel.H0 := by
  rw [H0, Kernel.H0, Rat.cast_pow, Rat.cast_mul, cast_sumQ, kappa_eq,
    sum_range_beta (fun _ b => (b : ℝ))]

theorem cast_betaTail (i : Fin 16) :
    ((betaTail i : ℚ) : ℝ) = ∑ j ∈ Finset.Ioi i, (Kernel.beta j : ℝ) := by
  rw [betaTail, cast_sumQ]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (((if (i : ℕ) < j then beta j else 0 : ℚ)) : ℝ)) 16,
    Kernel.Ioi_eq_filter i, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : i < j
  · have h' : (i : ℕ) < j := h
    rw [ite_eq_left h', ite_eq_left h, beta_eq]
  · have h' : ¬ (i : ℕ) < j := h
    rw [ite_eq_right h', ite_eq_right h, Rat.cast_zero]

theorem cross_eq {i : ℕ} (hi : i < 16) : cross i = beta i * betaTail i := by
  simp [cross, crossList, List.getD_eq_getElem?_getD, hi]

theorem cast_cross (i : Fin 16) :
    ((cross i : ℚ) : ℝ) = Kernel.beta i * ∑ j ∈ Finset.Ioi i, (Kernel.beta j : ℝ) := by
  rw [cross_eq i.isLt, Rat.cast_mul, cast_betaTail, beta_eq]

/-! ## Interval helpers -/

theorem mem_expI (q : ℚ) (prec : ℕ) : Real.exp q ∈ₗ expI q prec :=
  Ival.mem_exp prec (Ival.mem_ofRat q)

theorem mem_max0 {x : ℝ} {I : Ival} (hx : x ∈ₗ I) : max 0 x ∈ₗ max0 I := by
  refine ⟨?_, ?_⟩
  · simp only [max0, cast_rmax, Rat.cast_zero]; exact max_le_max le_rfl hx.1
  · simp only [max0, cast_rmax, Rat.cast_zero]; exact max_le_max le_rfl hx.2

theorem mem_ofRat_zero : (0 : ℝ) ∈ₗ Ival.ofRat 0 := by
  simpa using Ival.mem_ofRat 0

theorem mem_sumI {f : ℕ → Ival} {x : ℕ → ℝ} (prec : ℕ) :
    ∀ n, (∀ i < n, x i ∈ₗ f i) → (∑ i ∈ Finset.range n, x i) ∈ₗ sumI f prec n
  | 0, _ => by simpa [sumI] using mem_ofRat_zero
  | n + 1, h => by
    rw [Finset.sum_range_succ]
    exact Ival.mem_add prec (mem_sumI prec n fun i hi => h i (by omega)) (h n (by omega))

/-! ### Fixed-point intervals -/

namespace Fx

theorem mem_iff {x : ℝ} {A : Fx} {w : ℕ} :
    x ∈ₗ A.toIval w ↔ (A.lo : ℝ) / 2 ^ w ≤ x ∧ x ≤ (A.hi : ℝ) / 2 ^ w := by
  simp only [Mem, toIval, cast_mkRat_two_pow]

theorem fdivI_le (n : ℤ) {d : ℕ} (hd : 0 < d) : ((fdivI n d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  unfold fdivI
  have hd' : ((d : ℤ)) ≠ 0 := by exact_mod_cast hd.ne'
  have h := Int.ediv_mul_le n hd'
  rw [le_div_iff₀ (by exact_mod_cast hd)]
  exact_mod_cast h

theorem le_cdivI (n : ℤ) {d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ ((cdivI n d : ℤ) : ℝ) := by
  have h := fdivI_le (-n) hd
  unfold fdivI at h
  unfold cdivI
  rw [Int.cast_neg]
  rw [Int.cast_neg, neg_div] at h
  linarith

theorem mem_ofRat (q : ℚ) (w : ℕ) : (q : ℝ) ∈ₗ (Fx.ofRat q w).toIval w := by
  rw [mem_iff]
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := Rat.cast_def q
  have hw : (0 : ℝ) < 2 ^ w := by positivity
  have h1 := fdivI_le (q.num * ((2 ^ w : ℕ) : ℤ)) q.den_pos
  have h2 := le_cdivI (q.num * ((2 ^ w : ℕ) : ℤ)) q.den_pos
  have e : ((q.num * ((2 ^ w : ℕ) : ℤ) : ℤ) : ℝ) / q.den = (q : ℝ) * 2 ^ w := by
    rw [hq]; push_cast; ring
  rw [e] at h1 h2
  unfold ofRat
  exact ⟨by rw [div_le_iff₀ hw]; exact h1, by rw [le_div_iff₀ hw]; exact h2⟩

theorem mem_ofIval {x : ℝ} {I : Ival} (hx : x ∈ₗ I) (w : ℕ) : x ∈ₗ (Fx.ofIval I w).toIval w := by
  have h1 := (mem_iff.mp (mem_ofRat I.lo w)).1
  have h2 := (mem_iff.mp (mem_ofRat I.hi w)).2
  exact mem_iff.mpr ⟨h1.trans hx.1, hx.2.trans h2⟩

theorem mem_zero (w : ℕ) : (0 : ℝ) ∈ₗ (⟨0, 0⟩ : Fx).toIval w := by
  rw [mem_iff]; simp

theorem mem_add {x y : ℝ} {A B : Fx} {w : ℕ} (hx : x ∈ₗ A.toIval w) (hy : y ∈ₗ B.toIval w) :
    x + y ∈ₗ (A.add B).toIval w := by
  rw [mem_iff] at hx hy ⊢
  simp only [add, Int.cast_add, add_div]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_mulRat {x : ℝ} {A : Fx} {w : ℕ} (hx : x ∈ₗ A.toIval w) (q : ℚ) :
    x * q ∈ₗ (A.mulRat q).toIval w := by
  rw [mem_iff] at hx ⊢
  have hw : (0 : ℝ) < 2 ^ w := by positivity
  have hq : (q : ℝ) = (q.num : ℝ) / q.den := Rat.cast_def q
  have e : ∀ m : ℤ, ((m * q.num : ℤ) : ℝ) / q.den / 2 ^ w = (m : ℝ) / 2 ^ w * q := by
    intro m; rw [hq]; push_cast; ring
  unfold mulRat
  split_ifs with h
  · have hq0 : (0 : ℝ) ≤ q := by exact_mod_cast h
    constructor
    · calc ((fdivI (A.lo * q.num) q.den : ℤ) : ℝ) / 2 ^ w
          ≤ ((A.lo * q.num : ℤ) : ℝ) / q.den / 2 ^ w := by
            gcongr; exact fdivI_le _ q.den_pos
        _ = (A.lo : ℝ) / 2 ^ w * q := e _
        _ ≤ x * q := mul_le_mul_of_nonneg_right hx.1 hq0
    · calc x * q ≤ (A.hi : ℝ) / 2 ^ w * q := mul_le_mul_of_nonneg_right hx.2 hq0
        _ = ((A.hi * q.num : ℤ) : ℝ) / q.den / 2 ^ w := (e _).symm
        _ ≤ ((cdivI (A.hi * q.num) q.den : ℤ) : ℝ) / 2 ^ w := by
            gcongr; exact le_cdivI _ q.den_pos
  · have hq0 : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (not_le.mp h))
    constructor
    · calc ((fdivI (A.hi * q.num) q.den : ℤ) : ℝ) / 2 ^ w
          ≤ ((A.hi * q.num : ℤ) : ℝ) / q.den / 2 ^ w := by
            gcongr; exact fdivI_le _ q.den_pos
        _ = (A.hi : ℝ) / 2 ^ w * q := e _
        _ ≤ x * q := mul_le_mul_of_nonpos_right hx.2 hq0
    · calc x * q ≤ (A.lo : ℝ) / 2 ^ w * q := mul_le_mul_of_nonpos_right hx.1 hq0
        _ = ((A.lo * q.num : ℤ) : ℝ) / q.den / 2 ^ w := (e _).symm
        _ ≤ ((cdivI (A.lo * q.num) q.den : ℤ) : ℝ) / 2 ^ w := by
            gcongr; exact le_cdivI _ q.den_pos

theorem mem_mul {x y : ℝ} {A B : Fx} {w : ℕ} (hx : x ∈ₗ A.toIval w) (hy : y ∈ₗ B.toIval w) :
    x * y ∈ₗ (A.mul B w).toIval w := by
  rw [mem_iff] at hx hy ⊢
  have hw : (0 : ℝ) < 2 ^ w := by positivity
  have hw' : 0 < 2 ^ w := by positivity
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hmin := Ival.min4_le_mul hx1 hx2 hy1 hy2
  have hmax := Ival.mul_le_max4 hx1 hx2 hy1 hy2
  have e : ∀ m n : ℤ, (m : ℝ) / 2 ^ w * ((n : ℝ) / 2 ^ w) = ((m * n : ℤ) : ℝ) / 2 ^ w / 2 ^ w := by
    intro m n; push_cast; ring
  rw [e, e, e, e] at hmin hmax
  have hc : ∀ m : ℤ, ((m : ℝ) / ((2 ^ w : ℕ) : ℝ)) = (m : ℝ) / 2 ^ w := by
    intro m; push_cast; ring
  unfold mul
  dsimp only
  constructor
  · set M := min (min (A.lo * B.lo) (A.lo * B.hi)) (min (A.hi * B.lo) (A.hi * B.hi)) with hM
    have h1 : ((M : ℤ) : ℝ) / 2 ^ w / 2 ^ w ≤ min (min (((A.lo * B.lo : ℤ) : ℝ) / 2 ^ w / 2 ^ w)
        (((A.lo * B.hi : ℤ) : ℝ) / 2 ^ w / 2 ^ w)) (min (((A.hi * B.lo : ℤ) : ℝ) / 2 ^ w / 2 ^ w)
        (((A.hi * B.hi : ℤ) : ℝ) / 2 ^ w / 2 ^ w)) := by
      refine le_min (le_min ?_ ?_) (le_min ?_ ?_) <;> gcongr <;> exact_mod_cast (by omega)
    calc ((fdivI M (2 ^ w) : ℤ) : ℝ) / 2 ^ w ≤ (M : ℝ) / 2 ^ w / 2 ^ w := by
          gcongr; rw [← hc]; exact fdivI_le M hw'
      _ ≤ _ := h1
      _ ≤ x * y := hmin
  · set M := max (max (A.lo * B.lo) (A.lo * B.hi)) (max (A.hi * B.lo) (A.hi * B.hi)) with hM
    have h1 : max (max (((A.lo * B.lo : ℤ) : ℝ) / 2 ^ w / 2 ^ w)
        (((A.lo * B.hi : ℤ) : ℝ) / 2 ^ w / 2 ^ w)) (max (((A.hi * B.lo : ℤ) : ℝ) / 2 ^ w / 2 ^ w)
        (((A.hi * B.hi : ℤ) : ℝ) / 2 ^ w / 2 ^ w)) ≤ ((M : ℤ) : ℝ) / 2 ^ w / 2 ^ w := by
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> gcongr <;> exact_mod_cast (by omega)
    calc x * y ≤ _ := hmax
      _ ≤ (M : ℝ) / 2 ^ w / 2 ^ w := h1
      _ ≤ ((cdivI M (2 ^ w) : ℤ) : ℝ) / 2 ^ w := by
          gcongr; rw [← hc]; exact le_cdivI M hw'

end Fx

theorem mem_hornerFx (c : ℕ → ℚ) {x : ℝ} {X : Fx} {w : ℕ} (hx : x ∈ₗ X.toIval w) :
    ∀ m k, (∑ i ∈ Finset.range m, (c (k + i) : ℝ) * x ^ i) ∈ₗ (hornerFx c X w k m).toIval w
  | 0, k => by simpa [hornerFx] using Fx.mem_zero w
  | m + 1, k => by
    show _ ∈ₗ ((X.mul (hornerFx c X w (k + 1) m) w).add (Fx.ofRat (c k) w)).toIval w
    have ih := mem_hornerFx c hx m (k + 1)
    have h := Fx.mem_add (Fx.mem_mul hx ih) (Fx.mem_ofRat (c k) w)
    convert h using 1
    rw [Finset.sum_range_succ', Finset.mul_sum]
    simp only [add_zero, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k + (i + 1) = k + 1 + i by ring, pow_succ]
    ring

theorem mem_horner (c : ℕ → ℚ) (n : ℕ) {x : ℝ} {X : Ival} (prec : ℕ) (hx : x ∈ₗ X) :
    (∑ i ∈ Finset.range n, (c i : ℝ) * x ^ i) ∈ₗ horner c n X prec := by
  have h := mem_hornerFx c (Fx.mem_ofIval hx (prec + 16)) n 0
  simp only [zero_add] at h
  exact h

theorem cast_rabs (q : ℚ) : ((rabs q : ℚ) : ℝ) = |(q : ℝ)| := by
  unfold rabs
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast h)]
  · push_cast
    rw [abs_of_neg (by exact_mod_cast (lt_of_not_ge h))]

theorem lt_natCeil {q : ℚ} (hq : 0 ≤ q) : (q : ℝ) < natCeil q := by
  unfold natCeil
  have key := Nat.lt_mul_div_succ q.num.toNat q.den_pos
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  rw [cast_eq_of_nonneg hq, div_lt_iff₀ hd]
  have : ((q.num.toNat : ℕ) : ℝ) < (q.den : ℝ) * ((q.num.toNat / q.den : ℕ) + 1 : ℕ) := by
    exact_mod_cast key
  push_cast at this ⊢
  linarith

theorem fact_eq (n : ℕ) : fact n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fact, ih, Nat.factorial_succ]

theorem mem_sqrtI {y : ℚ} (hy : 0 ≤ y) (prec : ℕ) : Real.sqrt y ∈ₗ sqrtI y prec := by
  have hy' : (0 : ℝ) ≤ y := by exact_mod_cast hy
  unfold sqrtI
  dsimp only
  generalize Nat.sqrt (y.num.toNat * 2 ^ (2 * prec) / y.den) = m
  split_ifs with h
  · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨h1, h2⟩ := h
    have hlo : (0 : ℚ) ≤ mkRat (m : ℤ) (2 ^ prec) := by rw [Rat.mkRat_eq_div]; positivity
    have hhi : (0 : ℚ) ≤ mkRat ((m + 1 : ℕ) : ℤ) (2 ^ prec) := by
      rw [Rat.mkRat_eq_div]; positivity
    refine ⟨?_, ?_⟩
    · rw [Real.le_sqrt (by exact_mod_cast hlo) hy', sq]
      exact_mod_cast h1
    · rw [Real.sqrt_le_iff, sq]
      exact ⟨by exact_mod_cast hhi, by exact_mod_cast h2⟩
  · refine ⟨by simp, ?_⟩
    simp only [cast_rmax, Rat.cast_one]
    rw [Real.sqrt_le_iff]
    have h1 : (1 : ℝ) ≤ max 1 (y : ℝ) := le_max_left _ _
    have h2 : (y : ℝ) ≤ max 1 (y : ℝ) := le_max_right _ _
    exact ⟨by linarith, by nlinarith⟩

/-- **Taylor remainder of `exp`**: `|e^x − Σ_{m<n} x^m/m!| ≤ 2|x|^n/n!` for `2|x| ≤ n + 1`
(`Complex.exp_bound'`). -/
theorem abs_exp_sub_sum_le {x : ℝ} {n : ℕ} (hx : 2 * |x| ≤ n + 1) :
    |Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial| ≤ 2 * |x| ^ n / n.factorial := by
  have hxc : ‖(x : ℂ)‖ / (n.succ : ℝ) ≤ 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have h := Complex.exp_bound' hxc
  have e : Complex.exp (x : ℂ) - ∑ m ∈ Finset.range n, (x : ℂ) ^ m / (m.factorial : ℂ) =
      ((Real.exp x - ∑ m ∈ Finset.range n, x ^ m / m.factorial : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [e, Complex.norm_real, Real.norm_eq_abs, Complex.norm_real, Real.norm_eq_abs] at h
  calc _ ≤ |x| ^ n / n.factorial * 2 := h
    _ = 2 * |x| ^ n / n.factorial := by ring

/-! ## The envelope, `G_φ`, `h`, `C(p, a)`, `J_old` and `J_new` -/

/-- The closed form `Benv_eq` in the shape computed by `benv`. -/
theorem Benv_eq' (φ : ℝ) {lam : ℝ} (hlam : lam ≠ 0) :
    Kernel.Benv φ lam =
      (((1 - Kernel.envE lam) * (φ / (2 * lam) - 1 / (2 * lam * lam)) + (kappa : ℝ) / lam) *
          ∑ i ∈ Finset.range 16, ((beta i * beta i : ℚ) : ℝ) * Kernel.envE lam ^ i +
        (1 - Kernel.envE lam) * ((kappa : ℝ) / lam) *
          ∑ i ∈ Finset.range 16, ((cross i : ℚ) : ℝ) * Kernel.envE lam ^ i) / Kernel.H0 := by
  rw [Kernel.Benv_eq φ hlam]
  congr 1
  rw [sum_range_beta (fun i b => ((b * b : ℚ) : ℝ) * Kernel.envE lam ^ i),
    ← Fin.sum_univ_eq_sum_range (fun i => ((cross i : ℚ) : ℝ) * Kernel.envE lam ^ i) 16,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cast_cross i]
  unfold Kernel.envQ0 Kernel.envU
  rw [kappa_eq]
  push_cast
  field_simp
  ring

/-- **The envelope.** `B_φ(λ) ∈ benv φ λ` for `λ ≠ 0`. -/
theorem benv_sound (φ lam : ℚ) (prec : ℕ) (hlam : lam ≠ 0) :
    Kernel.Benv φ lam ∈ₗ benv φ lam prec := by
  have hlam' : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam
  have hE : Kernel.envE lam ∈ₗ expI (-(2 * kappa * lam)) prec := by
    have := mem_expI (-(2 * kappa * lam)) prec
    rw [Kernel.envE, ← kappa_eq]
    push_cast at this
    exact this
  have hM := Ival.mem_sub prec (Ival.mem_ofRat 1) hE
  rw [Rat.cast_one] at hM
  have hA1 := Ival.mem_addRat (kappa / lam) prec
    (Ival.mem_mulRat (φ / (2 * lam) - 1 / (2 * lam * lam)) prec hM)
  have hA2 := Ival.mem_mulRat (kappa / lam) prec hM
  have hP1 := mem_horner (fun i => beta i * beta i) 16 prec hE
  have hP2 := mem_horner cross 16 prec hE
  have key := Ival.mem_divRat H0 prec
    (Ival.mem_add prec (Ival.mem_mul prec hA1 hP1) (Ival.mem_mul prec hA2 hP2))
  unfold benv
  convert key using 1
  rw [Benv_eq' φ hlam', cast_H0]
  push_cast
  ring

/-- **The objective.** `G_φ(λ) = e^{−(L−2T)λ} B_φ(λ) ∈ gphi L φ λ` for `λ ≠ 0`. -/
theorem gphi_sound (L φ lam : ℚ) (prec : ℕ) (hlam : lam ≠ 0) :
    Kernel.Gphi L φ lam ∈ₗ gphi L φ lam prec := by
  have h := Ival.mem_mul prec (mem_expI (-((L - 2 * T) * lam)) prec) (benv_sound φ lam prec hlam)
  unfold gphi
  convert h using 1
  rw [Kernel.Gphi, T_eq]
  push_cast
  ring_nf

/-- The ordinary objective `G(λ) = G_{1/3}(λ) ∈ gphi L (1/3) λ` for `λ ≠ 0`. -/
theorem G_sound (L lam : ℚ) (prec : ℕ) (hlam : lam ≠ 0) :
    Kernel.G L lam ∈ₗ gphi L (1 / 3) lam prec := by
  have h := gphi_sound L (1 / 3) lam prec hlam
  rw [show (((1 / 3 : ℚ)) : ℝ) = 1 / 3 by norm_num] at h
  exact h

/-- **`h`.** `h(λ) ∈ hratio λ` for `λ ≠ 0`. -/
theorem hratio_sound (lam : ℚ) (prec : ℕ) (hlam : lam ≠ 0) :
    Kernel.hRatio lam ∈ₗ hratio lam prec := by
  have hlam' : (lam : ℝ) ≠ 0 := by exact_mod_cast hlam
  have he := mem_expI (-(kappa * lam)) prec
  have hS := mem_horner beta 16 prec he
  have hM := Ival.mem_sub prec (Ival.mem_ofRat 1) he
  rw [Rat.cast_one] at hM
  have key := Ival.mem_divRat H0 prec
    (Ival.mem_sqr prec (Ival.mem_divRat lam prec (Ival.mem_mul prec hS hM)))
  unfold hratio
  convert key using 1
  rw [Kernel.hRatio_eq hlam', cast_H0]
  congr 2
  rw [sum_range_beta (fun i b => (b : ℝ) * Real.exp ((-(kappa * lam) : ℚ) : ℝ) ^ i),
    Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kappa_eq]
  push_cast
  rw [← Real.exp_nat_mul]
  congr 3
  ring_nf

/-- The cell integral `X(r, j)`. -/
theorem mem_cellI (r : ℚ) {er : Ival} (her : Real.exp (-(r * kappa)) ∈ₗ er) (j : ℕ)
    (prec : ℕ) : Kernel.cellExp r j ∈ₗ cellI r er j prec := by
  unfold cellI Kernel.cellExp
  by_cases hr : r = 0
  · have hr' : (r : ℝ) = 0 := by exact_mod_cast hr
    rw [ite_eq_left hr, ite_eq_left hr', ← kappa_eq]
    exact Ival.mem_ofRat _
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr
    rw [ite_eq_right hr, ite_eq_right hr']
    have h := Ival.mem_divRat r prec (Ival.mem_mul prec (Ival.mem_pow j prec her)
      (Ival.mem_sub prec (Ival.mem_ofRat 1) her))
    convert h using 1
    rw [← kappa_eq, Rat.cast_one, ← Real.exp_nat_mul]
    have e1 : ((j : ℝ) * -((r : ℝ) * kappa)) = -((r : ℝ) * ((j : ℝ) * kappa)) := by ring
    have e2 : Real.exp (-((r : ℝ) * (((j : ℝ) + 1) * kappa))) =
        Real.exp ((j : ℝ) * -((r : ℝ) * kappa)) * Real.exp (-((r : ℝ) * kappa)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e2, e1]
    ring

/-- **The cross term.** `C(p, a) ∈ cpa p a` for `a ≠ 0`. -/
theorem cpa_sound (p a : ℚ) (prec : ℕ) (ha : a ≠ 0) : Kernel.Cpa p a ∈ₗ cpa p a prec := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hea := mem_expI (-(a * kappa)) prec
  have he2p := mem_expI (-(2 * p * kappa)) prec
  have he2pa := mem_expI (-((2 * p - a) * kappa)) prec
  push_cast at hea he2p he2pa
  have hX2p : ∀ j, Kernel.cellExp ((2 * p : ℚ) : ℝ) j ∈ₗ
      cellI (2 * p) (expI (-(2 * p * kappa)) prec) j prec := fun j =>
    mem_cellI (2 * p) (by push_cast; exact he2p) j prec
  have hX2pa : ∀ j, Kernel.cellExp ((2 * p - a : ℚ) : ℝ) j ∈ₗ
      cellI (2 * p - a) (expI (-((2 * p - a) * kappa)) prec) j prec := fun j =>
    mem_cellI (2 * p - a) (by push_cast; exact he2pa) j prec
  have hXa : ∀ k, Kernel.cellExp (a : ℝ) k * (beta k : ℝ) ∈ₗ
      (cellI a (expI (-(a * kappa)) prec) k prec).mulRat (beta k) prec := fun k =>
    Ival.mem_mulRat _ prec (mem_cellI a hea k prec)
  -- the tails `Σ_{k>j} β_k X(a, k)`
  set xa := (List.range 16).map fun k =>
    (cellI a (expI (-(a * kappa)) prec) k prec).mulRat (beta k) prec with hxa
  have hxa_get : ∀ k < 16, xa.getD k (Ival.ofRat 0) =
      (cellI a (expI (-(a * kappa)) prec) k prec).mulRat (beta k) prec := by
    intro k hk
    simp [hxa, List.getD_eq_getElem?_getD, hk]
  have htail : ∀ j : ℕ, (∑ k ∈ Finset.range 16,
      (if j < k then Kernel.cellExp (a : ℝ) k * (beta k : ℝ) else 0)) ∈ₗ
      sumI (fun k => if j < k then xa.getD k (Ival.ofRat 0) else Ival.ofRat 0) prec 16 := by
    intro j
    refine mem_sumI prec 16 fun k hk => ?_
    by_cases hjk : j < k
    · rw [ite_eq_left hjk, ite_eq_left hjk, hxa_get k hk]; exact hXa k
    · rw [ite_eq_right hjk, ite_eq_right hjk]; exact mem_ofRat_zero
  have hterm : ∀ j < 16, ((Kernel.cellExp ((2 * p : ℚ) : ℝ) j * ((beta j / a : ℚ) : ℝ) +
      ((∑ k ∈ Finset.range 16, (if j < k then Kernel.cellExp (a : ℝ) k * (beta k : ℝ) else 0)) -
        Real.exp (-((a : ℝ) * kappa)) ^ (j + 1) * ((beta j / a : ℚ) : ℝ)) *
        Kernel.cellExp ((2 * p - a : ℚ) : ℝ) j) * (beta j : ℝ)) ∈ₗ
      ((((cellI (2 * p) (expI (-(2 * p * kappa)) prec) j prec).mulRat (beta j / a) prec).add
        (((sumI (fun k => if j < k then xa.getD k (Ival.ofRat 0) else Ival.ofRat 0) prec 16).sub
          (((expI (-(a * kappa)) prec).pow (j + 1) prec).mulRat (beta j / a) prec) prec).mul
          (cellI (2 * p - a) (expI (-((2 * p - a) * kappa)) prec) j prec) prec) prec).mulRat
        (beta j) prec) := by
    intro j _
    exact Ival.mem_mulRat _ prec (Ival.mem_add prec (Ival.mem_mulRat _ prec (hX2p j))
      (Ival.mem_mul prec (Ival.mem_sub prec (htail j)
        (Ival.mem_mulRat _ prec (Ival.mem_pow (j + 1) prec hea))) (hX2pa j)))
  have key := Ival.mem_mulRat (2 / H0) prec (mem_sumI prec 16 hterm)
  unfold cpa
  convert key using 1
  rw [Kernel.Cpa_closed p ha', Finset.sum_range, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have htail' : ∑ k ∈ Finset.range 16,
      (if (j : ℕ) < k then Kernel.cellExp (a : ℝ) k * (beta k : ℝ) else 0) =
      ∑ k ∈ Finset.Ioi j, (Kernel.beta k : ℝ) * Kernel.cellExp a k := by
    rw [← Fin.sum_univ_eq_sum_range (fun k => (if (j : ℕ) < k then
      Kernel.cellExp (a : ℝ) k * (beta k : ℝ) else 0)) 16, Kernel.Ioi_eq_filter j,
      Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : j < k
    · have h' : (j : ℕ) < k := h
      rw [ite_eq_left h', ite_eq_left h, beta_eq, mul_comm]
    · have h' : ¬ (j : ℕ) < k := h
      rw [ite_eq_right h', ite_eq_right h]
  rw [htail', ← Real.exp_nat_mul]
  push_cast
  rw [cast_H0, beta_eq, ← kappa_eq]
  have e : Real.exp (-((a : ℝ) * ((((j : ℕ) : ℝ) + 1) * kappa))) =
      Real.exp ((((j : ℕ) : ℝ) + 1) * -((a : ℝ) * kappa)) := by
    congr 1; ring
  rw [e]
  ring

/-- **`J_old`.** `J_old ∈ jold L n α φ a p` for `a ≠ 0`. -/
theorem jold_sound (L : ℚ) (n α : ℕ) (φ a p : ℚ) (prec : ℕ) (ha : a ≠ 0) :
    Kernel.Jold L n α φ a p ∈ₗ jold L n α φ a p prec := by
  have hh := hratio_sound a prec ha
  have hd := mem_max0 (Ival.mem_sub prec (benv_sound φ a prec ha) (Ival.mem_mulRat α prec hh))
  have key := Ival.mem_mulRat n prec (Ival.mem_add prec
    (Ival.mem_mul prec (mem_expI (-((L - 2 * T) * p)) prec) hd)
    (Ival.mem_mulRat α prec (Ival.mem_mul prec (mem_expI (-((L - 2 * T) * a)) prec) hh)))
  unfold jold
  convert key using 1
  rw [Kernel.Jold, T_eq]
  push_cast
  rw [mul_comm (Kernel.hRatio a) (α : ℝ)]
  ring_nf

/-- **`J_new`.** `J_new ∈ jnew L n α φ a p` for `a ≠ 0` and `p ≠ 0`. -/
theorem jnew_sound (L : ℚ) (n α : ℕ) (φ a p : ℚ) (prec : ℕ) (ha : a ≠ 0) (hp : p ≠ 0) :
    Kernel.Jnew L n α φ a p ∈ₗ jnew L n α φ a p prec := by
  have key := Ival.mem_mulRat n prec (Ival.mem_add prec
    (Ival.mem_mulRat α prec (Ival.mem_mul prec (mem_expI (-((L - 2 * T) * a)) prec)
      (hratio_sound a prec ha)))
    (Ival.mem_mul prec (mem_expI (-((L - 2 * T) * p)) prec)
      (Ival.mem_sub prec (benv_sound φ p prec hp)
        (Ival.mem_mulRat α prec (cpa_sound p a prec ha)))))
  unfold jnew
  convert key using 1
  rw [Kernel.Jnew, T_eq]
  push_cast
  ring_nf

/-! ## The integrals `∫ (r² − D) e^{c r²} dr` -/

/-- `∫_{√y_a}^{√y_b} (r² − D) e^{c r²} dr`. -/
noncomputable def rIntR (c D ya yb : ℝ) : ℝ :=
  ∫ r in Real.sqrt ya..Real.sqrt yb, (r ^ 2 - D) * Real.exp (c * r ^ 2)

/-- `Φ(y) = Σ_{k<N} (cy)^k/k! (y/(2k+3) − D/(2k+1))`. -/
noncomputable def phiR (c D y : ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (c * y) ^ k / k.factorial * (y / (2 * k + 3) - D / (2 * k + 1))

theorem mem_serStep (z y D : ℚ) (w : ℕ) : ∀ k,
    (∑ j ∈ Finset.range k, (z : ℝ) ^ j / j.factorial * ((y : ℝ) / (2 * j + 3) - D / (2 * j + 1)))
        ∈ₗ (serStep z y D w k).1.toIval w ∧
      (z : ℝ) ^ k / k.factorial ∈ₗ (serStep z y D w k).2.toIval w
  | 0 => by
    refine ⟨by simpa [serStep] using Fx.mem_zero w, ?_⟩
    simpa [serStep] using Fx.mem_ofRat 1 w
  | k + 1 => by
    obtain ⟨h1, h2⟩ := mem_serStep z y D w k
    refine ⟨?_, ?_⟩
    · show _ ∈ₗ ((serStep z y D w k).1.add (((serStep z y D w k).2).mulRat
        (y / (2 * k + 3) - D / (2 * k + 1)))).toIval w
      rw [Finset.sum_range_succ]
      have h := Fx.mem_add h1 (Fx.mem_mulRat h2 (y / (2 * k + 3) - D / (2 * k + 1)))
      convert h using 2
      push_cast
      ring
    · show _ ∈ₗ (((serStep z y D w k).2).mulRat (z / (k + 1))).toIval w
      have h := Fx.mem_mulRat h2 (z / (k + 1))
      convert h using 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp
      ring

theorem mem_serPhi (c D y : ℚ) (N prec : ℕ) : phiR c D y N ∈ₗ serPhi c D y N prec := by
  have h := (mem_serStep (c * y) y D prec N).1
  unfold serPhi phiR
  push_cast at h
  exact h

/-- Substitution `t = s + r²`: `∫_{s+y_a}^{s+y_b} g = ∫_{√y_a}^{√y_b} g(s + r²) 2r dr`
(no integrability hypothesis is needed, since `r ↦ s + r²` is monotone on `r ≥ 0`). -/
theorem integral_subst_sq (g : ℝ → ℝ) (s : ℝ) {ya yb : ℝ} (ha : 0 ≤ ya) (hb : 0 ≤ yb) :
    ∫ t in (s + ya)..(s + yb), g t =
      ∫ r in Real.sqrt ya..Real.sqrt yb, g (s + r ^ 2) * (2 * r) := by
  have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt ya) (b := Real.sqrt yb) (f := fun r => s + r ^ 2) (f' := fun r => 2 * r)
    (g := g) (by fun_prop : Continuous fun r : ℝ => s + r ^ 2).continuousOn
    (fun r _ => by simpa using (hasDerivAt_pow 2 r).const_add s)
    (fun r hr => by
      have : 0 ≤ min (Real.sqrt ya) (Real.sqrt yb) :=
        le_min (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      linarith [hr.1])
  simp only [Function.comp_def, Real.sq_sqrt ha, Real.sq_sqrt hb] at h
  exact h.symm

/-- The integral of the Taylor polynomial part. -/
theorem integral_poly (c D ra rb : ℝ) (N : ℕ) :
    ∫ r in ra..rb, (r ^ 2 - D) * ∑ k ∈ Finset.range N, (c * r ^ 2) ^ k / k.factorial =
      ∑ k ∈ Finset.range N, c ^ k / k.factorial *
        ((rb ^ (2 * k + 3) - ra ^ (2 * k + 3)) / (2 * k + 3) -
          D * (rb ^ (2 * k + 1) - ra ^ (2 * k + 1)) / (2 * k + 1)) := by
  have e : ∀ r : ℝ, (r ^ 2 - D) * ∑ k ∈ Finset.range N, (c * r ^ 2) ^ k / k.factorial =
      ∑ k ∈ Finset.range N, (c ^ k / k.factorial * r ^ (2 * k + 2) -
        c ^ k / k.factorial * D * r ^ (2 * k)) := by
    intro r
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow, ← pow_mul]
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_pow,
    integral_pow]
  push_cast
  ring

theorem rabs_nonneg (q : ℚ) : 0 ≤ rabs q := by
  unfold rabs; split_ifs with h
  · exact h
  · linarith [lt_of_not_ge h]

/-- Widening an enclosure `M` of `m` by `err ≥ |x − m|`. -/
theorem mem_widen {x m e : ℝ} {M : Ival} (hm : m ∈ₗ M) (hxm : |x - m| ≤ e) {err : ℚ}
    (herr : e ≤ err) (prec : ℕ) :
    x ∈ₗ (⟨roundDown prec (M.lo - err), roundUp prec (M.hi + err)⟩ : Ival) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hxm
  refine ⟨(roundDown_le_real prec _).trans ?_, le_trans ?_ (le_roundUp_real prec _)⟩
  · push_cast; linarith [hm.1]
  · push_cast; linarith [hm.2]

/-- **The integrals `∫_{√y_a}^{√y_b} (r² − D) e^{c r²} dr`**, for `0 ≤ D ≤ y_a ≤ y_b`. -/
theorem rInt_sound (c D ya yb : ℚ) (prec : ℕ) (hD : 0 ≤ D) (hDa : D ≤ ya) (hab : ya ≤ yb) :
    rIntR c D ya yb ∈ₗ rInt c D ya yb prec := by
  have hD' : (0 : ℝ) ≤ D := by exact_mod_cast hD
  have hDa' : (D : ℝ) ≤ ya := by exact_mod_cast hDa
  have hab' : (ya : ℝ) ≤ yb := by exact_mod_cast hab
  have hya : (0 : ℝ) ≤ ya := hD'.trans hDa'
  have hyb : (0 : ℝ) ≤ yb := hya.trans hab'
  set N := nTerms c yb with hN
  set ra := Real.sqrt (ya : ℝ) with hra_def
  set rb := Real.sqrt (yb : ℝ) with hrb_def
  have hra : 0 ≤ ra := Real.sqrt_nonneg _
  have hrab : ra ≤ rb := Real.sqrt_le_sqrt hab'
  have hrb2 : rb ^ 2 = yb := Real.sq_sqrt hyb
  have hra2 : ra ^ 2 = ya := Real.sq_sqrt hya
  -- `N` is large enough for the Taylor remainder bound
  have hNbig : 2 * (|(c : ℝ)| * yb) ≤ N + 1 := by
    have h0 : (0 : ℚ) ≤ rabs c * yb := mul_nonneg (rabs_nonneg c) (hD.trans (hDa.trans hab))
    have h1 := lt_natCeil h0
    rw [Rat.cast_mul, cast_rabs] at h1
    have h2 : (N : ℝ) = seriesTerms + 4 * (natCeil (rabs c * yb) : ℝ) := by
      rw [hN, nTerms]; push_cast; ring
    have h3 : (0 : ℝ) ≤ seriesTerms := Nat.cast_nonneg _
    rw [h2]
    linarith
  set P : ℝ → ℝ := fun r => ∑ k ∈ Finset.range N, ((c : ℝ) * r ^ 2) ^ k / k.factorial with hP
  set E0 : ℝ := 2 * (|(c : ℝ)| * yb) ^ N / N.factorial with hE0
  have hE0nn : 0 ≤ E0 := by positivity
  have hpt : ∀ r ∈ Icc ra rb, |Real.exp (c * r ^ 2) - P r| ≤ E0 := by
    intro r hr
    have hr0 : 0 ≤ r := hra.trans hr.1
    have hr2 : r ^ 2 ≤ yb := by rw [← hrb2]; exact pow_le_pow_left₀ hr0 hr.2 2
    have habs : |(c : ℝ) * r ^ 2| ≤ |(c : ℝ)| * yb := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg r)]
      exact mul_le_mul_of_nonneg_left hr2 (abs_nonneg _)
    calc _ ≤ 2 * |(c : ℝ) * r ^ 2| ^ N / N.factorial :=
          abs_exp_sub_sum_le (by linarith)
      _ ≤ E0 := by
          rw [hE0]
          gcongr
  have hq : ∀ r ∈ Icc ra rb, 0 ≤ r ^ 2 - D ∧ r ^ 2 - D ≤ yb - D := by
    intro r hr
    have hr0 : 0 ≤ r := hra.trans hr.1
    have h1 : ya ≤ r ^ 2 := by rw [← hra2]; exact pow_le_pow_left₀ hra hr.1 2
    have h2 : r ^ 2 ≤ yb := by rw [← hrb2]; exact pow_le_pow_left₀ hr0 hr.2 2
    constructor <;> linarith
  have hPc : Continuous P := by
    rw [hP]
    exact continuous_finsetSum _ fun k _ => by fun_prop
  -- the polynomial part integrates exactly
  have hint_poly : ∫ r in ra..rb, (r ^ 2 - D) * P r =
      rb * phiR c D yb N - ra * phiR c D ya N := by
    rw [hP, integral_poly, phiR, phiR, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    have e1 : rb ^ (2 * k + 3) = (yb : ℝ) ^ (k + 1) * rb := by rw [← hrb2]; ring
    have e2 : ra ^ (2 * k + 3) = (ya : ℝ) ^ (k + 1) * ra := by rw [← hra2]; ring
    have e3 : rb ^ (2 * k + 1) = (yb : ℝ) ^ k * rb := by rw [← hrb2]; ring
    have e4 : ra ^ (2 * k + 1) = (ya : ℝ) ^ k * ra := by rw [← hra2]; ring
    rw [e1, e2, e3, e4]
    ring
  have hIq : IntervalIntegrable (fun r : ℝ => r ^ 2 - (D : ℝ)) volume ra rb := by
    apply Continuous.intervalIntegrable; fun_prop
  have hint_q : ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) ≤ rb * (yb - D) := by
    have h := intervalIntegral.integral_mono_on hrab hIq
      (intervalIntegrable_const (c := ((yb : ℝ) - D))) fun r hr => (hq r hr).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at h
    have : (rb - ra) * ((yb : ℝ) - D) ≤ rb * (yb - D) := by nlinarith
    linarith
  have hint_q0 : 0 ≤ ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) :=
    intervalIntegral.integral_nonneg hrab fun r hr => (hq r hr).1
  have hIf : IntervalIntegrable (fun r : ℝ => (r ^ 2 - D) * Real.exp (c * r ^ 2)) volume ra rb := by
    apply Continuous.intervalIntegrable; fun_prop
  have hIP : IntervalIntegrable (fun r : ℝ => (r ^ 2 - D) * P r) volume ra rb :=
    ((continuous_pow 2).sub continuous_const |>.mul hPc).intervalIntegrable _ _
  have hIE : IntervalIntegrable (fun r : ℝ => E0 * (r ^ 2 - D)) volume ra rb :=
    hIq.const_mul E0
  have hup : rIntR c D ya yb ≤
      (rb * phiR c D yb N - ra * phiR c D ya N) + E0 * ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) := by
    rw [← hint_poly, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hIP hIE]
    refine intervalIntegral.integral_mono_on hrab hIf (hIP.add hIE) fun r hr => ?_
    have h1 := (abs_le.mp (hpt r hr)).2
    calc (r ^ 2 - D) * Real.exp (c * r ^ 2) ≤ (r ^ 2 - D) * (P r + E0) :=
          mul_le_mul_of_nonneg_left (by linarith) (hq r hr).1
      _ = (r ^ 2 - D) * P r + E0 * (r ^ 2 - D) := by ring
  have hlo : (rb * phiR c D yb N - ra * phiR c D ya N) - E0 * ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) ≤
      rIntR c D ya yb := by
    rw [← hint_poly, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hIP hIE]
    refine intervalIntegral.integral_mono_on hrab (hIP.sub hIE) hIf fun r hr => ?_
    have h1 := (abs_le.mp (hpt r hr)).1
    calc (r ^ 2 - D) * P r - E0 * (r ^ 2 - D) = (r ^ 2 - D) * (P r - E0) := by ring
      _ ≤ (r ^ 2 - D) * Real.exp (c * r ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (hq r hr).1
  -- the interval part
  have hsa := mem_sqrtI (hD.trans hDa) (prec + 32)
  have hsb := mem_sqrtI (hD.trans (hDa.trans hab)) (prec + 32)
  have hM := Ival.mem_sub (prec + 32)
    (Ival.mem_mul (prec + 32) hsb (mem_serPhi c D yb N (prec + 32)))
    (Ival.mem_mul (prec + 32) hsa (mem_serPhi c D ya N (prec + 32)))
  set e0 : ℚ := roundUp (prec + 32) (2 * (rabs c * yb) ^ N / (fact N : ℚ)) with he0
  have hE0e0 : E0 ≤ e0 := by
    refine le_trans ?_ (le_roundUp_real (prec + 32) _)
    rw [hE0, fact_eq]
    push_cast
    rw [cast_rabs]
  have herr : E0 * ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) ≤
      ((roundUp (prec + 32) (e0 * (sqrtI yb (prec + 32)).hi * (yb - D)) : ℚ) : ℝ) := by
    refine le_trans ?_ (le_roundUp_real (prec + 32) _)
    push_cast
    have hsbhi : rb ≤ ((sqrtI yb (prec + 32)).hi : ℝ) := hsb.2
    have hyD : (0 : ℝ) ≤ yb - D := by linarith
    calc E0 * ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) ≤ E0 * (rb * (yb - D)) :=
          mul_le_mul_of_nonneg_left hint_q hE0nn
      _ ≤ (e0 : ℝ) * (((sqrtI yb (prec + 32)).hi : ℝ) * (yb - D)) :=
          mul_le_mul hE0e0 (mul_le_mul_of_nonneg_right hsbhi hyD)
            (mul_nonneg (Real.sqrt_nonneg _) hyD) (hE0nn.trans hE0e0)
      _ = (e0 : ℝ) * ((sqrtI yb (prec + 32)).hi : ℝ) * (yb - D) := by ring
  have hxm : |rIntR c D ya yb - (rb * phiR c D yb N - ra * phiR c D ya N)| ≤
      E0 * ∫ r in ra..rb, (r ^ 2 - (D : ℝ)) := by
    rw [abs_le]; constructor <;> linarith
  unfold rInt
  dsimp only
  exact mem_widen hM hxm herr prec

/-! ## The far weight -/

theorem cast_epsQ : ((epsQ : ℚ) : ℝ) = Kernel.FarProfile.eps := by
  norm_num [epsQ, Kernel.FarProfile.eps]

/-- `∫_v^x e^{at} dt = (e^{ax} − e^{av})/a` for `a ≠ 0`. -/
theorem integral_exp_mul {a : ℝ} (ha : a ≠ 0) (v x : ℝ) :
    ∫ t in v..x, Real.exp (a * t) = (Real.exp (a * x) - Real.exp (a * v)) / a := by
  have h := Kernel.integral_exp_neg_mul (neg_ne_zero.mpr ha) v x
  simp only [neg_mul, neg_neg] at h
  rw [h]
  field_simp
  ring

theorem expIntI_sound (a v x : ℚ) (prec : ℕ) :
    (∫ t in (v : ℝ)..(x : ℝ), Real.exp (a * t)) ∈ₗ expIntI a v x prec := by
  unfold expIntI
  by_cases ha : a = 0
  · rw [ite_eq_left ha]
    subst ha
    have h := Ival.mem_ofRat (x - v)
    push_cast at h ⊢
    simpa using h
  · rw [ite_eq_right ha]
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    rw [integral_exp_mul ha']
    have h := Ival.mem_divRat a prec (Ival.mem_sub (prec + 64) (mem_expI (a * x) (prec + 64))
      (mem_expI (a * v) (prec + 64)))
    push_cast at h
    exact h

namespace FarProfileFacts

variable (P : Kernel.FarProfile)

theorem u_le_v (hc₂ : 0 < P.c₂) : P.u ≤ P.v := by
  have : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  unfold Kernel.FarProfile.v; linarith

theorem v_le_x (hc₁ : 0 < P.c₁) : P.v ≤ P.x := by
  have : (0 : ℝ) < P.c₁ := by exact_mod_cast hc₁
  unfold Kernel.FarProfile.v Kernel.FarProfile.x Kernel.FarProfile.u; linarith

/-- On `[u, v]` after the substitution `t = u − ε + r²`: `w₀(t)² = e^{−θt} r`. -/
theorem w0sq_subst {r : ℝ} (hr0 : 0 ≤ r) (hr : r ^ 2 ≤ P.c₂ + Kernel.FarProfile.eps) :
    P.w0sq (P.u - Kernel.FarProfile.eps + r ^ 2) =
      Real.exp (-(P.θ * (P.u - Kernel.FarProfile.eps + r ^ 2))) * r := by
  unfold Kernel.FarProfile.w0sq
  rw [show P.u - Kernel.FarProfile.eps + r ^ 2 - P.u = r ^ 2 - Kernel.FarProfile.eps by ring,
    min_eq_left (by linarith), sub_add_cancel, Real.sqrt_sq hr0]

/-- On `[v, x]`: `w₀(t)² = e^{−θt} √(c₂ + ε)`. -/
theorem w0sq_right {t : ℝ} (ht : P.v ≤ t) :
    P.w0sq t = Real.exp (-(P.θ * t)) * Real.sqrt (P.c₂ + Kernel.FarProfile.eps) := by
  unfold Kernel.FarProfile.w0sq
  rw [min_eq_right (by unfold Kernel.FarProfile.v at ht; linarith)]

end FarProfileFacts

/-- **The far weight in closed-ish form**: with `a = 2λ − θ`,
`w(λ)⁻¹ = 2 e^{a(u−ε)} ∫_{√ε}^{√(c₂+ε)} r² e^{a r²} dr + √(c₂+ε) ∫_v^x e^{at} dt`. -/
theorem winv_eq (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℝ) :
    P.winv lam = rIntR (2 * lam - P.θ) 0 Kernel.FarProfile.eps (P.c₂ + Kernel.FarProfile.eps) *
        Real.exp ((2 * lam - P.θ) * (P.u - Kernel.FarProfile.eps)) * 2 +
      Real.sqrt (P.c₂ + Kernel.FarProfile.eps) *
        ∫ t in P.v..P.x, Real.exp ((2 * lam - P.θ) * t) := by
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have he := Kernel.FarProfile.eps_pos
  set ε := Kernel.FarProfile.eps with hε
  unfold Kernel.FarProfile.winv
  rw [← intervalIntegral.integral_add_adjacent_intervals (P.intervalIntegrable_winv lam P.u P.v)
    (P.intervalIntegrable_winv lam P.v P.x)]
  congr 1
  · have hs := integral_subst_sq (fun t => P.w0sq t * Real.exp (2 * lam * t)) (P.u - ε) he.le
      (by positivity : (0 : ℝ) ≤ P.c₂ + ε)
    rw [show P.u - ε + ε = P.u by ring,
      show P.u - ε + ((P.c₂ : ℝ) + ε) = P.v by unfold Kernel.FarProfile.v; ring] at hs
    rw [hs, rIntR, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (Real.sqrt_le_sqrt (by linarith))] at hr
    have hr0 : 0 ≤ r := (Real.sqrt_nonneg _).trans hr.1
    have hr2 : r ^ 2 ≤ P.c₂ + ε := by
      rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ P.c₂ + ε)]
      exact pow_le_pow_left₀ hr0 hr.2 2
    rw [FarProfileFacts.w0sq_subst P hr0 hr2]
    have e : Real.exp (-(P.θ * (P.u - ε + r ^ 2))) * Real.exp (2 * lam * (P.u - ε + r ^ 2)) =
        Real.exp ((2 * lam - P.θ) * r ^ 2) * Real.exp ((2 * lam - P.θ) * (P.u - ε)) := by
      rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
    linear_combination (2 * r ^ 2) * e
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le (FarProfileFacts.v_le_x P hc₁)] at ht
    rw [FarProfileFacts.w0sq_right P ht.1,
      show (2 * lam - P.θ) * t = -(P.θ * t) + 2 * lam * t by ring, Real.exp_add]
    ring

/-- **The far weight** `w(λ)⁻¹ ∈ winv c₁ c₂ θ λ` for a profile with `c₁, c₂ > 0`. -/
theorem winv_sound (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℚ)
    (prec : ℕ) : P.winv lam ∈ₗ winv P.c₁ P.c₂ P.θ lam prec := by
  have hε : (0 : ℚ) ≤ epsQ := by norm_num [epsQ]
  have hR := rInt_sound (2 * lam - P.θ) 0 epsQ (P.c₂ + epsQ) prec le_rfl hε (by linarith)
  have key := Ival.mem_add prec
    (Ival.mem_mulRat 2 prec (Ival.mem_mul prec hR
      (mem_expI ((2 * lam - P.θ) * (1 / 3 + 2 * P.c₁ - epsQ)) prec)))
    (Ival.mem_mul prec (mem_sqrtI (by linarith : (0 : ℚ) ≤ P.c₂ + epsQ) prec)
      (expIntI_sound (2 * lam - P.θ) (1 / 3 + 2 * P.c₁ + P.c₂) (2 / 3 + 3 * P.c₁ + P.c₂) prec))
  unfold winv
  dsimp only
  convert key using 1
  rw [winv_eq P hc₁ hc₂]
  simp only [Kernel.FarProfile.v, Kernel.FarProfile.x, Kernel.FarProfile.u]
  push_cast
  rw [cast_epsQ]

/-- **The far weight** `w(λ) ∈ w c₁ c₂ θ λ`, when the enclosure of `w(λ)⁻¹` is positive. -/
theorem w_sound (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℚ) (prec : ℕ)
    (hpos : 0 < (winv P.c₁ P.c₂ P.θ lam prec).lo) : P.w lam ∈ₗ w P.c₁ P.c₂ P.θ lam prec := by
  have hI := winv_sound P hc₁ hc₂ lam prec
  unfold w
  dsimp only
  rw [ite_eq_left hpos]
  exact Ival.mem_inv (p := prec) (by simp [Ival.inv, hpos]) hI

/-- The lower end of `w c₁ c₂ θ λ` is always a lower bound for `w(λ)`. -/
theorem w_lo_le (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (lam : ℚ)
    (prec : ℕ) : ((w P.c₁ P.c₂ P.θ lam prec).lo : ℝ) ≤ P.w lam := by
  by_cases hpos : 0 < (winv P.c₁ P.c₂ P.θ lam prec).lo
  · exact (w_sound P hc₁ hc₂ lam prec hpos).1
  · unfold w
    dsimp only
    rw [ite_eq_right hpos]
    simpa using (P.w_pos hc₁ hc₂ lam).le

/-! ## The constant `V` -/

/-- `K(d) = ∫_u^x w₀(t)⁻² (t − u − d)₊ dt`. -/
noncomputable def Kd (P : Kernel.FarProfile) (d : ℝ) : ℝ :=
  ∫ t in P.u..P.x, (P.w0sq t)⁻¹ * max 0 (t - P.u - d)

theorem min_max_zero (s h : ℝ) (hh : 0 ≤ h) : min (max 0 s) h = max 0 s - max 0 (s - h) := by
  rcases le_total s 0 with h1 | h1
  · rw [max_eq_left h1, max_eq_left (by linarith), min_eq_left hh]; ring
  · rcases le_total s h with h2 | h2
    · rw [max_eq_right h1, max_eq_left (by linarith), min_eq_left h2]; ring
    · rw [max_eq_right h1, max_eq_right (by linarith), min_eq_right (by linarith)]; ring

theorem intervalIntegrable_K (P : Kernel.FarProfile) (hc₂ : 0 < P.c₂) (d : ℝ)
    {a b : ℝ} (ha : a ∈ Icc P.u P.x) (hb : b ∈ Icc P.u P.x) :
    IntervalIntegrable (fun t => (P.w0sq t)⁻¹ * max 0 (t - P.u - d)) volume a b := by
  have hf : ContinuousOn (fun t => (P.w0sq t)⁻¹ * max 0 (t - P.u - d)) (Icc P.u P.x) :=
    (P.continuous_w0sq.continuousOn.inv₀ fun t ht => (P.w0sq_pos hc₂ ht.1).ne').mul
      (Continuous.continuousOn (by fun_prop))
  exact (hf.mono (uIcc_subset_Icc ha hb)).intervalIntegrable

/-- `J_i = K(ih) − K((i+1)h)`, `h = c₂/10`. -/
theorem V_eq (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) :
    P.V = 100 / ((P.c₁ : ℝ) * (P.c₂ : ℝ) ^ 2) * ∑ i : Fin 10, ((P.α i : ℝ)) ^ 2 *
      (Kd P ((i : ℕ) * (P.c₂ / 10)) - Kd P (((i : ℕ) + 1) * (P.c₂ / 10))) := by
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have hux : P.u ≤ P.x := (P.u_lt_x hc₁ hc₂).le
  have hu : P.u ∈ Icc P.u P.x := ⟨le_rfl, hux⟩
  have hx : P.x ∈ Icc P.u P.x := ⟨hux, le_rfl⟩
  unfold Kernel.FarProfile.V
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold Kd
  rw [← intervalIntegral.integral_sub (intervalIntegrable_K P hc₂ _ hu hx)
    (intervalIntegrable_K P hc₂ _ hu hx)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [← mul_sub, show t - P.u - (((i : ℕ) : ℝ) + 1) * (P.c₂ / 10) =
    (t - P.u - ((i : ℕ) : ℝ) * (P.c₂ / 10)) - P.c₂ / 10 by ring,
    min_max_zero _ _ (by positivity)]

/-- `∫_v^x e^{θt}(t − c) dt` in closed form, for `θ ≠ 0`. -/
theorem integral_exp_affine {θ : ℝ} (hθ : θ ≠ 0) (c v x : ℝ) :
    ∫ t in v..x, Real.exp (θ * t) * (t - c) =
      Real.exp (θ * x) * ((x - c) / θ - 1 / (θ * θ)) -
        Real.exp (θ * v) * ((v - c) / θ - 1 / (θ * θ)) := by
  have h := Kernel.integral_exp_mul_affine (neg_ne_zero.mpr hθ) (-c) 1 v x
  simp only [neg_mul, neg_neg, one_mul] at h
  have e : ∀ t : ℝ, Real.exp (θ * t) * (t - c) = Real.exp (θ * t) * (-c + t) := fun t => by ring
  simp_rw [e]
  rw [h]
  field_simp
  ring

theorem affExpI_sound (θ c v x : ℚ) (prec : ℕ) :
    (∫ t in (v : ℝ)..(x : ℝ), Real.exp (θ * t) * (t - c)) ∈ₗ affExpI θ c v x prec := by
  unfold affExpI
  by_cases hθ : θ = 0
  · rw [ite_eq_left hθ]
    subst hθ
    have h := Ival.mem_ofRat (((x - c) ^ 2 - (v - c) ^ 2) / 2)
    convert h using 1
    simp only [Rat.cast_zero, zero_mul, Real.exp_zero, one_mul]
    rw [intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
      intervalIntegrable_const, integral_id, intervalIntegral.integral_const, smul_eq_mul]
    push_cast
    ring
  · rw [ite_eq_right hθ]
    have hθ' : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ
    rw [integral_exp_affine hθ']
    dsimp only
    have h := Ival.mem_sub prec
      (Ival.mem_mulRat ((x - c) / θ - 1 / (θ * θ)) (prec + 64) (mem_expI (θ * x) (prec + 64)))
      (Ival.mem_mulRat ((v - c) / θ - 1 / (θ * θ)) (prec + 64) (mem_expI (θ * v) (prec + 64)))
    push_cast at h
    exact h

/-- **`K(d)` for `0 ≤ d ≤ c₂`**:
`K(d) = 2 e^{θ(u−ε)} ∫_{√(d+ε)}^{√(c₂+ε)} (r² − d − ε) e^{θ r²} dr`
`+ (c₂+ε)^{−1/2} ∫_v^x e^{θt}(t − u − d) dt`. -/
theorem K_eq (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) {d : ℝ} (hd0 : 0 ≤ d)
    (hd : d ≤ P.c₂) :
    Kd P d = rIntR P.θ (d + Kernel.FarProfile.eps) (d + Kernel.FarProfile.eps)
        (P.c₂ + Kernel.FarProfile.eps) * Real.exp (P.θ * (P.u - Kernel.FarProfile.eps)) * 2 +
      Real.sqrt (1 / (P.c₂ + Kernel.FarProfile.eps)) *
        ∫ t in P.v..P.x, Real.exp (P.θ * t) * (t - (P.u + d)) := by
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have he := Kernel.FarProfile.eps_pos
  set ε := Kernel.FarProfile.eps with hε
  have huv := FarProfileFacts.u_le_v P hc₂
  have hvx := FarProfileFacts.v_le_x P hc₁
  have hud : P.u ≤ P.u + d := by linarith
  have hdv : P.u + d ≤ P.v := by unfold Kernel.FarProfile.v; linarith
  have mem : ∀ t, P.u ≤ t → t ≤ P.x → t ∈ Icc P.u P.x := fun t h1 h2 => ⟨h1, h2⟩
  have hI := fun a b (ha : a ∈ Icc P.u P.x) (hb : b ∈ Icc P.u P.x) =>
    intervalIntegrable_K P hc₂ d ha hb
  unfold Kd
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hI P.u P.v (mem _ le_rfl (huv.trans hvx)) (mem _ huv hvx))
      (hI P.v P.x (mem _ huv hvx) (mem _ (huv.trans hvx) le_rfl)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hI P.u (P.u + d) (mem _ le_rfl (huv.trans hvx)) (mem _ hud (hdv.trans hvx)))
      (hI (P.u + d) P.v (mem _ hud (hdv.trans hvx)) (mem _ huv hvx))]
  have h0 : ∫ t in P.u..(P.u + d), (P.w0sq t)⁻¹ * max 0 (t - P.u - d) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun t ht => ?_]
    · simp
    · rw [uIcc_of_le hud] at ht
      rw [max_eq_left (by linarith [ht.2]), mul_zero]
  rw [h0, zero_add]
  congr 1
  · have hs := integral_subst_sq (fun t => (P.w0sq t)⁻¹ * max 0 (t - P.u - d)) (P.u - ε)
      (by positivity : (0 : ℝ) ≤ d + ε) (by positivity : (0 : ℝ) ≤ P.c₂ + ε)
    rw [show P.u - ε + (d + ε) = P.u + d by ring,
      show P.u - ε + ((P.c₂ : ℝ) + ε) = P.v by unfold Kernel.FarProfile.v; ring] at hs
    rw [hs, rIntR, ← intervalIntegral.integral_mul_const, ← intervalIntegral.integral_mul_const]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le (Real.sqrt_le_sqrt (by linarith))] at hr
    have hdε : 0 < d + ε := by positivity
    have hr0 : 0 < r := (Real.sqrt_pos.2 hdε).trans_le hr.1
    have hr1 : d + ε ≤ r ^ 2 := by
      rw [← Real.sq_sqrt hdε.le]; exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hr.1 2
    have hr2 : r ^ 2 ≤ P.c₂ + ε := by
      rw [← Real.sq_sqrt (by positivity : (0 : ℝ) ≤ P.c₂ + ε)]
      exact pow_le_pow_left₀ hr0.le hr.2 2
    rw [FarProfileFacts.w0sq_subst P hr0.le hr2,
      max_eq_right (by linarith : (0 : ℝ) ≤ P.u - ε + r ^ 2 - P.u - d)]
    have e : (Real.exp (-(P.θ * (P.u - ε + r ^ 2))))⁻¹ =
        Real.exp (P.θ * r ^ 2) * Real.exp (P.θ * (P.u - ε)) := by
      rw [← Real.exp_neg, ← Real.exp_add]; congr 1; ring
    rw [mul_inv, e]
    field_simp
    ring
  · rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hvx] at ht
    have hsq : 0 < Real.sqrt (P.c₂ + ε) := Real.sqrt_pos.2 (by positivity)
    rw [FarProfileFacts.w0sq_right P ht.1,
      max_eq_right (by unfold Kernel.FarProfile.v at ht; linarith [ht.1] :
        (0 : ℝ) ≤ t - P.u - d),
      one_div, Real.sqrt_inv, mul_inv, ← Real.exp_neg]
    rw [show -(-(P.θ * t)) = P.θ * t by ring]
    ring

theorem kI_sound (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (d : ℚ)
    (hd0 : 0 ≤ d) (hd : d ≤ P.c₂) (prec : ℕ) : Kd P d ∈ₗ kI P.c₁ P.c₂ P.θ d prec := by
  have hε : (0 : ℚ) ≤ epsQ := by norm_num [epsQ]
  have hR := rInt_sound P.θ (d + epsQ) (d + epsQ) (P.c₂ + epsQ) prec (by linarith) le_rfl
    (by linarith)
  have key := Ival.mem_add prec
    (Ival.mem_mulRat 2 prec (Ival.mem_mul prec hR
      (mem_expI (P.θ * (1 / 3 + 2 * P.c₁ - epsQ)) prec)))
    (Ival.mem_mul prec (mem_sqrtI (by positivity : (0 : ℚ) ≤ 1 / (P.c₂ + epsQ)) prec)
      (affExpI_sound P.θ (1 / 3 + 2 * P.c₁ + d) (1 / 3 + 2 * P.c₁ + P.c₂)
        (2 / 3 + 3 * P.c₁ + P.c₂) prec))
  unfold kI
  dsimp only
  convert key using 1
  rw [K_eq P hc₁ hc₂ (by exact_mod_cast hd0) (by exact_mod_cast hd)]
  simp only [Kernel.FarProfile.v, Kernel.FarProfile.x, Kernel.FarProfile.u]
  push_cast
  rw [cast_epsQ]

/-- **The constant `V`**: `V ∈ vI c₁ c₂ θ α` for a profile with `c₁, c₂ > 0`. -/
theorem V_mem (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (prec : ℕ) :
    P.V ∈ₗ vI P.c₁ P.c₂ P.θ (List.ofFn P.α) prec := by
  have hc₂' : (0 : ℝ) < P.c₂ := by exact_mod_cast hc₂
  have hterm : ∀ i < 10, (Kd P ((i : ℕ) * (P.c₂ / 10)) - Kd P (((i : ℕ) + 1) * (P.c₂ / 10))) *
      (((List.ofFn P.α).getD i 0 ^ 2 : ℚ) : ℝ) ∈ₗ
      ((kI P.c₁ P.c₂ P.θ (i * (P.c₂ / 10)) prec).sub
        (kI P.c₁ P.c₂ P.θ ((i + 1) * (P.c₂ / 10)) prec) prec).mulRat
        ((List.ofFn P.α).getD i 0 ^ 2) prec := by
    intro i hi
    have hi' : (i : ℚ) ≤ 9 := by exact_mod_cast Nat.le_of_lt_succ hi
    have h1 := kI_sound P hc₁ hc₂ (i * (P.c₂ / 10)) (by positivity) (by nlinarith) prec
    have h2 := kI_sound P hc₁ hc₂ ((i + 1) * (P.c₂ / 10)) (by positivity) (by nlinarith) prec
    push_cast at h1 h2
    exact Ival.mem_mulRat _ prec (Ival.mem_sub prec h1 h2)
  have key := Ival.mem_mulRat (100 / (P.c₁ * P.c₂ ^ 2)) prec (mem_sumI prec 10 hterm)
  unfold vI
  dsimp only
  convert key using 1
  rw [V_eq P hc₁ hc₂, Finset.sum_range (fun i => (Kd P ((i : ℕ) * (P.c₂ / 10)) -
      Kd P (((i : ℕ) + 1) * (P.c₂ / 10))) * (((List.ofFn P.α).getD i 0 ^ 2 : ℚ) : ℝ)),
    Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hget : (List.ofFn P.α).getD (i : ℕ) 0 = P.α i := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp
  rw [hget]
  push_cast
  ring

/-- **`V ≤ vUpper`** for a profile with `c₁, c₂ > 0`. -/
theorem V_le_vUpper (P : Kernel.FarProfile) (hc₁ : 0 < P.c₁) (hc₂ : 0 < P.c₂) (prec : ℕ) :
    P.V ≤ vUpper P.c₁ P.c₂ P.θ (List.ofFn P.α) prec :=
  (V_mem P hc₁ hc₂ prec).2

/-! ## The two profiles of the corpus -/

theorem inherited_eq : inherited.c₁ = Kernel.inherited.c₁ ∧ inherited.c₂ = Kernel.inherited.c₂ ∧
    inherited.θ = Kernel.inherited.θ ∧ inherited.α = List.ofFn Kernel.inherited.α :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem retuned_eq : retuned.c₁ = Kernel.retuned.c₁ ∧ retuned.c₂ = Kernel.retuned.c₂ ∧
    retuned.θ = Kernel.retuned.θ ∧ retuned.α = List.ofFn Kernel.retuned.α :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem winv_inherited (lam : ℚ) (prec : ℕ) :
    Kernel.inherited.winv lam ∈ₗ winv inherited.c₁ inherited.c₂ inherited.θ lam prec :=
  winv_sound Kernel.inherited Kernel.inherited_c₁_pos Kernel.inherited_c₂_pos lam prec

theorem winv_retuned (lam : ℚ) (prec : ℕ) :
    Kernel.retuned.winv lam ∈ₗ winv retuned.c₁ retuned.c₂ retuned.θ lam prec :=
  winv_sound Kernel.retuned Kernel.retuned_c₁_pos Kernel.retuned_c₂_pos lam prec

theorem w_lo_le_inherited (lam : ℚ) (prec : ℕ) :
    ((w inherited.c₁ inherited.c₂ inherited.θ lam prec).lo : ℝ) ≤ Kernel.inherited.w lam :=
  w_lo_le Kernel.inherited Kernel.inherited_c₁_pos Kernel.inherited_c₂_pos lam prec

theorem w_lo_le_retuned (lam : ℚ) (prec : ℕ) :
    ((w retuned.c₁ retuned.c₂ retuned.θ lam prec).lo : ℝ) ≤ Kernel.retuned.w lam :=
  w_lo_le Kernel.retuned Kernel.retuned_c₁_pos Kernel.retuned_c₂_pos lam prec

theorem V_inherited_le (prec : ℕ) :
    Kernel.inherited.V ≤ vUpper inherited.c₁ inherited.c₂ inherited.θ inherited.α prec :=
  V_le_vUpper Kernel.inherited Kernel.inherited_c₁_pos Kernel.inherited_c₂_pos prec

theorem V_retuned_le (prec : ℕ) :
    Kernel.retuned.V ≤ vUpper retuned.c₁ retuned.c₂ retuned.θ retuned.α prec :=
  V_le_vUpper Kernel.retuned Kernel.retuned_c₁_pos Kernel.retuned_c₂_pos prec

end LeafNumCore
