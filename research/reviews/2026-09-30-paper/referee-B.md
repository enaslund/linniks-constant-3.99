# Referee report B: near rows (§9), leaf programs and certificates (§10), leaf model, subdivision and realization (§11)

**Version reviewed.** `paper/sections/09-rows.tex` (md5 `3b244651…`, 03:40 UTC), `10-lp.tex` (md5 `a04bcb13…`, 03:40),
`11-casetree.tex` (md5 `a85ae32e…`, 03:40). These three files had not changed again by 03:50. I also read `08-near.tex`,
`05-costs.tex`, `06-far.tex`, `13-join.tex`, `14-verification.tex` and the relevant parts of `07-location.tex`.

The paper was being edited while I worked, and three of my findings were fixed during the review:

* **03:40.** The variant count now reads "31 … once on each" (09:335–336), where it used to say "32 … one root uses both".
* **03:46.** (S4) in 13-join now chooses `M` with `η''_min`, which resolves M2 below.
* **03:47.** A parenthesis in §14 now states the Lean positivity hypothesis, which resolves minor item 20.

Line numbers below refer to the 03:40 files for §§9–11.

**Code checked.** `sieve_near/sieve_inputs.py`, `sieve_near/leaf_driver.py` (`graded_row`, `_family_term`, `safe_anchor`),
`graded/graded_leaves.py` (`old_row`, `second_columns`, `_columns_for_second`, `reserve_specs`), `graded/graded_cert.py`,
`graded/graded_driver.py` (splits and verifier), `core/code/two_test_enclosures.py`, `extension_enclosures.py`,
`published_single_inputs.py`, `triple_inputs.py` (`input_with_third`, `use_shifted`), `sieve_near/third_refine.py`,
`near/code/first_outside_blocks.py`, `core/code/base_enclosures.py` (`RigorousTest.F`, `exponential_moment`, `C_upper`),
`vector_intervals.py`, `pair_bounds.real_tail`. I also looked at the Lean files `ZeroForm.lean` and `Cert/Semantics.lean`.

---

## Summary verdict

I found **no blocking error** in my scope. I re-derived each result independently:

* the entry catalogue (a)–(g): kept sets, response-lemma hypotheses, the multiplicities, and each `r`;
* the two-test theorem: Hilbert-space setup, norms, the exceptional-quotient graph count and hence the `D_o`/`D_f` table, `κ=3/4`, `E·C_Z`;
* the mixture proposition (`N_ε`, `C_Z+εC_G`) and the paired proposition (the derivative argument);
* Prop `rowsvalid`, the relaxation lemmas, the rounding directions, the exclusion rule, weak duality, the root-box end, and Prop `realization`.

All of these are correct, and they match the code, with the exceptions listed below. There are **three MAJOR items**; M2 was
fixed in the 03:46 edit of (S4), so **two remain open (M1, M3)**. Each is a gap between a stated result and the way it is used or
checked. Each can be fixed in a few lines, and I found **no numerical consequence for any certificate**. There are 20 minor items;
item 20 was fixed at 03:47.

**Independent checks (read-only, run from my scratchpad).**

1. **Where the two-test row is used.** I scanned all three corpora. The `old` row occurs in exactly 37 leaves, all inside (0 in
   `nodes`, 0 in `outside`), one per root: 10, 11, 15–18, 20–36, 1198–1201, 1212–1215, 1218, 1219, 2603, 2608, 2613, 2633.
   * Roots 1218 and 1219 use it in a *reserved* child: reservation split at 0.8959 and 0.8934, nonreal pair, lowest ninth of
     a 9-way second-family split, with `second_columns=400`.
   * I regenerated the source leaves of 10 roots (10, 36, 1198, 1215, 1218, 1219, 2603, 2608, 2613, 2633). Root 2633 is
     **paired only**.
   * Tally: 23 rr/single, 8 complex/single, 2 complex/mixture, 4 complex/pair. So the current text "31/2/4, once on each" is right.
   * Every paired use has a nonreal `χ₁`, so Prop `paired` (stated for nonreal `χ₁`) covers every use. However,
     `extension_enclosures.paired_first` also accepts `kind='rc'` (`make_extended` then uses `pa,ph=a,b`). That path is unused;
     remove it or state that variant.
2. **Independent recomputation of the two-test data** for those 10 of the 37 leaves. I used mpmath at 60 digits with the closed
   form of `F`, sampled suprema for `C_G`, `C_Z`, and a sampled `𝓑` over a 3×3 grid of `(λ₁,λ')` and `Δ∈[0,30]` at step 1/40.
   I compared `d`, `D_o`, `D_f`, `v_f`, three bin features `V_i` per leaf, `v₂`, and for the paired roots `𝓑`, `e`, `D_*`, `m`
   and `2D_*−κ_*m`.
   * Every stored integer is on the safe side. Features are below the true values by about 1e-7; diagonals are equal or above.
   * Stored `𝓑` is about 7e-4, against a sampled supremum of about −5e-4 (conservative, because of the floor at 0 and the
     interpolation slack).
   * The paired margins `2D_*−κ_*m` are 0.184, 0.186, 0.187 and 0.295.
   * This closes part of the gap noted in §14 (those 37 rows are not covered by the Lean row checker).
3. **All 4,046 distinct family and shifted parameter sets** have `μ=10⁹`, `g₁>γ`, and computed sieve heights all 0, so `H≡0`.
   The graded anchors in use are exactly {1.5, 1.6, 1.9, 2.1, 2.3}. Family anchors are at most 1.48 and shifted anchors at most 1.9.
4. **`η''=η'` for every row.** For all 4,193 distinct near-row parameter sets, `min(1,√(I_B D_u),D_u)=1` in a floating estimate
   (smallest `D_u≈1.088`). This matters for MAJOR-2.
5. **Reservation splits.** There are 4 in the inside corpus and 6 records in 5 node roots (1501 twice), matching 11:236–237.

---

## BLOCKING

None found.

---

## MAJOR

### M1. `lem:noright` is applied outside its stated hypothesis `|γ|≤l`

* **Where.** The statement is at 09-rows.tex:95–99: "Let χ be nonprincipal, $|\gamma|\le l$ …". It is used in the two-test
  off-diagonal step at 09:269: "If $\psi\notin\{\chi_1,\bchi_1\}$ there are none, by \cref{lem:noright}(b)". It is used
  implicitly in the paired proof at 09:314–315: "Averaging does not create new quotient characters, so the off-diagonal
  estimates are unchanged".
* **Why it is a problem.** The inner product ⟨A_j,A_k⟩ is an X3.2 sum at height `γ_j−γ_k`.
  * Ordinary and reserved entries have height at most 1, so `|γ_j−γ_k|` can reach 2.
  * In Prop `paired`, the second half of `A_f` sits at `γ'` with `|γ'|≤l`, so the heights reach `l+1`.
  * Inp. `rectangle` only gives `1≤l≤𝓛/10`. With `l=1`, height 2 exceeds `l`, so the lemma as stated does not apply.
* **Proposed fix.** The proof of the lemma works verbatim for `|γ|≤9l−δ₀`. State `lem:noright` for `|γ|≤2l`; its proof then
  reads "`|Im ρ|≤2l+δ₀<10l`". Then add one sentence in each of the two proofs: `|γ_j−γ_k|≤2≤2l` in the two-test proof, and
  `|γ'−γ_k|≤l+1≤2l` in the paired proof. The same remark covers the claim at 09:311 that `ρ₁` is the only zero of `χ₁` below `s`
  in the disc about `1+iγ'`.

### M2. The separation `M` from (S4) does not match what Cor. `zeroform` now requires (**resolved at 03:46**)

The 03:46 version of 13-join (S4) chooses `M` with `η''_min` over all rows, which is the first fix proposed below. The
description that follows refers to the 03:40 text.

* **Where.**
  * 08-near.tex:317–319 now reads: "apply … with $\eta''$ in place of $\eta'$ (so the kept sets are assumed to satisfy the
    hypotheses of \cref{lem:response} with the separation and radius that it provides for $\eta''$)", where
    `η''=η'min(1,√(I_B D_u),D_u)`.
  * 13-join.tex:21–22 (S4) chooses `M` with "$|\Re F(x+iY)|\le\eta'/(2K_0+2)$".
  * `lem:Tstar` (06-far) and `lem:strip` (09:107–118) supply exactly this `M` to every ordinary entry (a) whose anchor exceeds `l₂`.
* **Why it is a problem.** If `η''<η'` for some row, the strip lemma delivers a separation that is too small for the response
  lemma at `η''`. The rows' validity (Prop `rowsvalid`) then does not follow as written.
* **Numerical consequence.** None. On all 4,193 parameter sets `η''=η'` (independent check 4 above).
* **Proposed fix.** Either
  * in (S4), choose `M` with `|Re F(x+iY)|≤η''_k/(2K₀+2)` for every row `k`, where `η''_k=η'min(1,√(I_{B,k}D_{u,k}),D_{u,k})`;
    there are finitely many rows, so this is allowed; or
  * state and check `D_u≥1` and `I_uD_u≥1` for every row, so that `η''=η'`, and say so in §9 ("Row data").

### M3. Prop `paired`: the hypothesis that is checked is not the hypothesis that is stated

* **Where.** The hypotheses are at 09-rows.tex:299–305: "Let $e\ge C_Z/(2N)$ … If $D_*>0$ and $2D_*\ge\kappa_*\max(m,0)$, then …".
  The proof is at 09:316–323. The code is in `extension_enclosures.paired_first`:
  `di,fi=upper(D),lower(mf) … assert di>0 and 2*Q(di,S)>=kap*max(Q(fi,S),Q(0))`, and it then stores `v_first=fi`, `Df=di`.
* **Why it is a problem.**
  * The code checks the monotonicity condition for the **rounded** pair `(fi,di)`, with `fi≤m` and `di≥D_*`. That does not imply
    the stated condition `2D_*≥κ_*max(m,0)`, because the implication runs the wrong way.
  * The proposition, as stated, therefore does not cover the numbers that were certified. It does become valid once combined
    with monotonicity of (T) *after* the exact hypothesis is known.
  * The proof has a related loose end. The "actual diagonal" `k{(1+P)/2−d₀+c_G}` is not shown to be positive, so
    Prop `threshold` must be applied with the larger diagonal `D_*+κ_*U>0`. The text only says the actual diagonal is "at most"
    that, and then speaks of "the threshold inequality with the actual first-family data".
* **Proposed fix.** State the proposition for any `m'≤m` and `D'≥D_*` with `D'>0` and `2D'≥κ_*max(m',0)`. In the proof, put
  `U'=U+(m−m')≥0`. Then the actual feature is at least `m'+U'`, and the diagonal used is `D'+κ_*U'≥D_*+κ_*U`, which is positive
  and at least the actual diagonal. Apply Prop `threshold` with `(m'+U', D'+κ_*U')`, then the displayed monotonicity with
  `(m',D')`. The certified margins (0.18–0.29) show that no leaf is affected.

---

## MINOR

1. **09:176–178, entry (g), type rc.** The paper has "Global entries $(\chi_1,\gamma_1,0)$ and $(\bchi_1,-\gamma_1,0)$ (for type
   $\mathrm{rc}$, $(\chi_1,\pm\gamma_1,0)$)". The code has one global entry per first-family character:
   `graded_row(…, families='outside_first')` → `_family_term(test, inp['n'], b, min(a,s), D)`, with `n=1` for rc. Both are valid,
   but the paper should describe what the code does. Fix: "for type rc, the single entry $(\chi_1,\gamma_1,0)$ with
   $\mathcal S=\{\rho_1\}$".
2. **09:142–146 (entry (d)) and 09:309–311 (paired proof).** "Let $\rho'$ be the zero realizing $\lambda'$". By 11:22–23,
   `λ'` is taken over occurrences in both `χ₁` and `χ̄₁`, so `ρ'` may be a zero of `χ̄₁`, and then the entry `(χ₁,γ',0)` is
   meaningless. Fix: add "after replacing $\rho'$ by $\overline{\rho'}$ if necessary, $\rho'$ is a non-distinguished zero of
   $\chi_1$ (possibly a second copy of $\rho_1$)". The same sentence is needed where the second-zero split is defined
   (11:242–245), since `y` depends on this choice.
3. **09:236–238, statement of the two-test theorem.** "consider the entries: each ordinary character at one of its zeros … of
   height at most 1".
   * Not every ordinary character has such a zero, and the row uses only the characters of `O` outside the tail.
   * Fix: "for any finite set of ordinary characters, each at one of its zeros of height at most 1". The proof already works for
     any subset.
   * "the $n$ characters of the first family at $\rho_1$ and $\overline{\rho_1}$" is ambiguous for type rc, where the single entry
     keeps both zeros. Say so explicitly.
4. **09:326, "after division by $D_o$".** No undivided form appears in the paper, so this phrase refers to the repository's
   formula `Σx_i(V_i−τ)²≤D(1−τ²/d)−…`. Drop it, or display the undivided form. Also say that the 2-tuple reserved term in
   `graded_leaves.old_row` receives the row's `D=D_o` by default (`graded_cert.Leaf._fam`). That is what the display shows, but
   the data format hides it.
5. **09:62–65, row data.**
   * `κ_k` is undefined. The code uses `κ_k=(t_{k+1}²−t_k²)/(2δ_k(t_{k+1}−t_k))`.
   * "When $\mu=10^9$ all heights vanish and $H\equiv0$" is not a general fact; it depends on `γ_f`, `γ_g`, `s`, `s₁`. It is true
     for every stored family and shifted row (I checked all 4,046).
   * The heights `h_k` are computed in binary64 (`np.exp`, `np.sqrt`) and then rationalized with `limit_denominator(10**12)`.
     They are not stored in the certificates, so replay depends on the platform's libm. Soundness is unaffected, but
     reproducibility is not guaranteed.
   * Fix: define `κ_k`; write "in every stored row with μ=10⁹ the computed heights are 0"; and store the `h_k`, or a digest of
     each row's integers, in the records.
6. **09:364–368, grid claims.** "the suprema over heights are enclosed on grids of step at most $\frac1{50}$". This holds for
   `R_lo`, `c^hi`, `R_p`, `R_q` (`pair_bounds`, `second_zero_bounds`). It does not hold for `C_Z`: `RigorousTest.C_upper` starts
   from 200 cells of width 1/10 on `[0,20]` and bisects only where the interval bound is not within tolerance. It is rigorous
   (second-derivative slack plus the tail beyond 20), but "step ≤ 1/50" is false. Describe the adaptive cover.
7. **09:354–356, proof of Prop `rowsvalid`.** "each column's diagonal is at least theirs". This fails for a column whose entries
   were omitted because `D(⌊δ⌋)−d₁` is not safely positive. `graded_row` then sets `v=0` and `Dv=D`, the offset-0 diagonal. It is
   harmless, since a feature-0 column contributes nothing for `τ≥0`. Say "or the column has feature 0 and contributes nothing".
8. **09:131–133, 171–181.** The diagonal numerators of (b), (f) and (g) are not stated. They are `D(s−σ)−d₁`, `D(s−σ₂)−d₁`
   (per column: `D(s−σ)−d₁`), and `D(0)−d₁` with pair excess 0. State them as for (a) and (e).
9. **09:168–170, entry (e).** "otherwise the entry's feature is negative and it contributes nothing". This relies on the
   builder's replacement of negative features by 0 (`max(0, shifted_first_feature)`) and on the last clause of Cor. `zeroform`
   (`v'_j≤max(v_j,0)`, `v'_j≤0`). The true `r_j` can be *below* the displayed `r` when `m≥2` and `F(b−s)<C_Z`. Cite that clause.
10. **09:116–117, proof of Lemma `strip`.** "so $|\Im\rho|>T^*$ by the minimality of the representative". This needs the zero to
    lie in `R(l)`: `λ_ρ<3` and `|Im ρ|<2≤10l`, then Inp. `rectangle`. Add the half-sentence.
11. **09:197–198.** "In every row the safe-anchor hypothesis holds". The two-test row has no safe anchor, since its Gram form is
    at `s`. Say "in every family, shifted and graded row". Likewise, 09:59 "Every graded row fixes …" should cover the family and
    shifted rows too.
12. **09:335–338, check of (8).** Add three points:
    * `Re G(−s+iΔ)` and `Re F(x+iΔ)` are even in `Δ`, so `Δ≥0` suffices;
    * the corner values are completed by the second-derivative slack in `λ₁` and `λ'`, namely
      `ζ/(2N)((b−a)²∫t²fe^{(s−a)₊t}/8+(h−p*)²∫t²fe^{(s−p*)₊t}/8)` (the code's `param_err`), which is what makes corners sufficient;
    * `𝓑` is floored at 0.
13. **11:186–187, rounding list** "(far weights and features down, objective coefficients up)". It is incomplete:
    * diagonals and radii are rounded up;
    * `F` is rounded up and the subtracted `n⌊Sw(b)⌋` down;
    * the hidden-tail count coefficient `1/w(end)` must be rounded **down**. The code does this: `lower(w.winv(end))` in
      `first_outside_blocks.first_out_input`, line 26. The hidden-count step of the realization (11:278–279) needs it.
14. **11:196–197 against 11:261–262.** The tail is defined "over the ordinary characters with $\nu_{T^*}(\chi)\ge R$" in the model,
    but "over $\chi\in O$" in the realization. Use `O` in both places: characters without a zero in `R_P` may have no
    `T*`-representative.
15. **11:260–262, notation.** "Put $x_i$ equal to the number of $\chi\in O$ with $\nu_{T^*}(\chi)\in[x_i,x_{i+1})$". Here `x_i`
    denotes both a column value and a grid point. Rename the grid points (for example `ξ_i`). Also, `σ` means a specification in
    §11, an anchor in §9 (a)–(g), and `1−s/𝓛` in the two-test proof.
16. **11:284–285, "Value" step.** "the monotonicity of $G$, $G_{\phi_2}$ and $G/w$". The hidden columns also need two facts:
    * `e^{−Aλ}` is decreasing (bins) and `e^{−Aλ}/w` is decreasing (hidden tail; Lemma `decay`);
    * Prop `firstoutside` is applied with the anchor `p°=max(a,p,g⁻)`, not `p`, which is valid since `λ'≥p°`.

    Say both.
17. **11:252, 239–247.** The configuration sets of the sub-cases (rc height split, second-zero split) are not defined. Define
    `C(σ)∩{μ₁∈I}` and `C(σ)∩{|y|∈I}` for the chosen `ρ'`, and note that the pieces are exhaustive.
18. **10:21–22, 42.** `E_c` is called a "second-family indicator", but in `Σ_cE_cx_c=n₂S` it must equal `S` (code: `_S_all`).
    Likewise `C_c∈{0,S}` and `N_c∈{S,⌊S/w(end)⌋}`. State the scaled values.
19. **10:132–133.** "the budgets are … rounded up". The first-order budget is `S−⌊S²a²/(T_S²d)⌋−Σ⌊n(v−bS/T_S)²₊/D⌋`, which is at
    least the exact value but is not `⌈·⌉` of it. Say "rounded upward (each subtracted term rounded down)".
20. **08:7–8 and 14 (a) — resolved at 03:47 by a parenthesis in §14.** "All three are formally verified". The Lean `graded_near_threshold` (`ZeroForm.lean`) assumes
    `0<D(δ_j)−d₁+e_j` for the **true** numerators. Cor. `zeroform` (08) needs only `D_j^+>0`, and the builders test positivity
    at `⌊δ⌋` (the row checker compensates with the grid point above the offset). Say that the formal version carries this extra
    hypothesis and that the row checker verifies it.

---

## Checked and found correct

* **Entries.**
  * (a) The strip lemma gives separation `M` and count `K₀` whenever `σ=min(lo,s)>l₂`; otherwise there is no zero to the right.
  * (b) The kept zero `ρ₁` (resp. `ρ̄₁`); `r=F(b−σ)−f(0)/6`.
  * (c) `ρ̄₁` lies in the disc because the leaf is inside; `R_lo≥0` since `x≥0`; the pair excess bound is right. The code's
    Lipschitz and curvature slacks match (`4∫t²f`, `∫tf`).
  * (d) Both `r`'s; the double-zero case; `R_p,R_q≥0` (the code floors them at 0, valid since `x≥0`); the last piece covers
    zeros outside the disc.
  * (e) Equal multiplicities; `C_Z=C_c(s−a)`.
  * (f) `σ₂` (the code uses `sec_anchor='l2'`, and `source_l2` is the leaf's `l₂`, raised by location updates).
  * (g) Separations `C_B−C_P>M`; features at `hi_h`; the code uses `D` with no excess.
* **Two-test theorem.** `−Re⟨A_j,B⟩=𝓛R_j`; `‖B‖²` via `f²/g`, which satisfies Condition 1 (order-6 zero); the graph count and
  the `D_o`/`D_f` table (including cubic `χ₁`, where `χ₁²=χ̄₁` is the partner); `κ=3/4` for real characters; `E=1` only for rc.
  The code (`constants`, `feat`, `norm_bounds`, `single_rows`) matches the formulas exactly.
* **Mixture.** `f_ε²/g=f²/g+2εf+ε²g`, `N_ε`, `C_Z+εC_G`, and `ε=t(γ_Z/γ_G)⁵` in the unnormalized scaling.
* **Paired.** `U≥0`, the diagonal bound through (8), the derivative identity, and the rigor of `correlation_bound`:
  sequential interpolation in `Δ` and in the separable real parts; tail at 30 through `real_tail` and `tailbox`.
* **Builder normalization.** `I_up` is a rigorous upper Riemann sum (`(1+2⁻⁴⁰)` covers the summation error of 2,000 positive
  terms); `D_up≥D(0)`; `D(⌊δ⌋_{1/200})≥D(δ)`; `diag_norm` omits entries at `≤D_up/1000`; `gram()` gives `d=(1+η)(d₁/D_u+η)`.
  The parabolic closed form and its Taylor branch agree with Lemma `parabolic`(iv) after normalization, term by term.
* **§10 against `graded_cert.py`.**
  * first-order and tangent costs (double floor, including negative case-1 costs);
  * budgets;
  * `e_k=⌈√(⌊d_kT_S²/S⌋+1)⌉` and the containment;
  * enumeration of relaxation cases;
  * exclusion only with all costs `≥0` and budget `<0`;
  * dual feasibility with free `P−M` and `U` only when hidden columns exist;
  * case value `⌈tot/D_S⌉+first+final<S`.

  All match. Lemmas `firstorder` and `tangent` and Theorem `certificate` are correct.
* **§11.**
  * Bins are half-open, with features at the right end, objective at the left end, and far weight at the right end.
  * The count rule (count 1 if `x_{i+1}≤λ₃^lo`) and deletion in reserved leaves (`input_with_third`, `refine_third`).
  * Tail far weight is `S`, and its objective `G(R)/w(R)` is rounded up.
  * Second-family columns: grid 1/400, the `first` and `F` adjustments, the anchor rule, feature 0 in the old row.
  * Hidden columns: `p°`, `B_{φ₁}(p°)`, count `S` / `⌊S/w(end)⌋`, `n_g=n`.
  * The far budget; `first=min(J_old,J_new)` (`use_shifted`, with `J_new` only if `p*≥b`).
  * The reservation split and the rc and second-zero splits as verified by `graded_driver._verify_record`: the family row must
    come first in each part, and the parts must be exactly `RC_MU_SPLIT` and `DZ_SPLIT`.
