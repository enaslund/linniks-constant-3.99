# What the graded-leaf LP data mean

Date: 2026-09-29. This specification was traced from the code, not from
[PROOF.md](../PROOF.md), by an independent agent. It checked the analytic
formulas (`B_φ`, `C(p,a)`, `h`, `w⁻¹`, `J_i`, `V`, `f_γ`, `F`) against direct
mpmath quadrature at 30 digits, and regenerated one outside leaf (root 1193)
and one inside leaf (spec 1220, reserved family as columns) to confirm the
field layouts. It is the reference for the Lean definitions in
[`lean-graded/GradedNear/Functions.lean`](../../GradedNear/Functions.lean).

**Path abbreviations** (all under `computations/`):

| Tag | Path |
|---|---|
| GC | graded/graded_cert.py |
| GL | graded/graded_leaves.py |
| GD | graded/graded_driver.py |
| LD | sieve_near/leaf_driver.py |
| SI | sieve_near/sieve_inputs.py |
| TR | sieve_near/third_refine.py |
| FR | sieve_near/family_row.py |
| PP | sieve_near/propose_params.py |
| BE | core/code/base_enclosures.py |
| EN | core/code/enclosures.py |
| CF | core/code/config_v4.py |
| PS | core/code/published_single_inputs.py |
| TI | core/code/triple_inputs.py |
| EG | core/code/endgame.py |
| TT | core/code/two_test_enclosures.py |
| EX | core/code/extension_enclosures.py |
| FE | frontier/far_enclosures.py |
| FO | near/code/first_outside_blocks.py |

**Conventions.**
* `S = 10¹⁶`.
* `⌊X⌋_S` and `⌈X⌉_S` are the exact floor and ceiling of `S·X`, taken at the
  lower or upper endpoint of an outward interval enclosure of `X`
  (`lower`/`upper`, BE:19-28).
* `η = 10⁻⁶` (CF:3). It serves as both the far `η` and the near lemma's `η′`.

## 0. Where the leaf input comes from

**Inside leaves** are built by GL:92-101, in this order:
1. `make_endgame` (EG:42-49):
   * `reduced_spec` (EG:15-40) applies location rows, which may raise `lp`,
     `gap.lo`, `source_l2`, `ordinary_lower` and `second.lo`;
   * `make_extended`/`make_single` (EX:114-133, PS:15-29);
   * `input_with_third` (TI:43-64);
   * `use_shifted` (TI:102-105).
2. `replace_far(src['far_parameters'])` (FE:51-71), only when the source has
   `far_parameters` and no `hidden_rows`.
3. `refine_third` (TR:86-112).

**Outside leaves** use `first_out_input(spec, L, 'outside_buffer', par, den)`
(FO:6-28, GL:104-118). They never go through `replace_far` or
`refine_third`.

**Second-family columns.** When the record has `second_columns: 400`,
`second_columns` is applied (GL:121-146, GD:319-323).

**Which far weight each leaf uses:**
* All 2,027 `far_parameters` in `frontier/collective_full_4.30/roots.jsonl.gz`,
  and 508 in `far_full_4.30.jsonl.gz`, equal `CANDIDATE` (FE:18-21).
* The 1,642 outside sources have `lambda_den = 200` and no far parameters.
* Identities-node templates use `den = 200` and no far parameters.
* So the retuned weight appears only on inside scenario leaves whose source
  records it.

## 1. The functions

**Kernel** (CF:5-8, EN:14-18):
* `T = .416829` and `κ = T/16`.
* `β₀…β₁₅` as in `config_v4.py`, and `ψ = Σβᵢ·1_{[iκ,(i+1)κ)}`.
* `Ψ(z) = Σβᵢ e^{−iκz}(1−e^{−κz})/z` and `H₀ = Ψ(0)² = .0374973375696671475`.
* `A = L − 2T`, `H(z) = e^{−Az}Ψ(z)²` and `h(λ) = Ψ(λ)²/H₀`.

**Envelope** `B_φ` and `G` (EN:28-35, 44). The code implements an exact closed
form of PROOF.md's
`B_φ = H₀⁻¹[F_λ(−λ) + (φ/2)f_λ(0)]`. Put `E = e^{−2κλ}`, `U = (1−E)/λ` and
`Q₀ = κ/λ − U/(2λ)`, with `U = 2κ` and `Q₀ = κ²` at `λ = 0`. Then

`H₀B_φ(λ) = Σ_{i=0}^{15} Eⁱ[βᵢ²(Q₀ + (φ/2)U) + κUβᵢΣ_{j>i}βⱼ]`,

with `φ/2 = 1/6` (non-real) or `1/8` (real).
* `G(λ) = e^{−Aλ}B_{1/3}(λ)` is used for every ordinary bin, real characters
  included.
* `G_real(λ) = e^{−Aλ}B_{1/4}(λ)`.

**First family** (inside). Notation:
* `n = 2` for type complex, otherwise 1;
* `α = 2` for type rc, otherwise 1;
* `B_t = B_{1/4}` for types rr and rc, otherwise `B_{1/3}`;
* `a, b` are `case.lo` and `case.hi`;
* `p` is `gap.lo` if there is a gap, otherwise `case.lp`.

The bounds:
* `J_old = n[e^{−Ap}(⌈B_t(a) − αh(a)⌉_S/S)₊ + αe^{−Aa}h(a)]` (EN:45-51).
* `C(p,a) = (2/H₀)∫₀^Tψ(u)e^{−2pu}∫_u^Tψ(v)e^{−a(v−u)}dv du`, computed as exact
  step-cell sums (TI:72-89).
* `J_new`, only when `p ≥ b`: `n{αe^{−Aa}h(a) + e^{−Ap}[B_t(p) − αC(p,a)]}`
  (TI:91-100).
* The inside charge is `min(⌈J_old⌉_S, ⌈J_new⌉_S)` (TI:58, 103-104).

**Reserved second family.** `G_{φ₂} = e^{−Aλ}B_{φ₂}`, with `φ₂ = 1/4` exactly
when `n₂ = 1` (TI:61; GL:138, 143).

**Hidden-column objective** (outside): `e^{−A·lo_h}·B_φ(p_h)`, where
`p_h = max(a, lp, gap.lo)` and `φ = 1/4` for rc or `1/3` for complex
(FO:9-11, 19, 25).

**Far weight** (BE:124-157; EN:19-26; FE:23-40). The profile, on
`t∈[u,x]`, is
`w₀(t)² = e^{−θt}√(min(t−u,c₂) + ε)`, with `u = 1/3+2c₁`, `v = u+c₂`,
`x = 2/3+3c₁+c₂` and `ε = 10⁻⁷`.
* `w(λ)⁻¹ = ∫_u^x w₀²e^{2λt}dt = 2e^{a(u−ε)}∫_{√ε}^{√(c₂+ε)}r²e^{ar²}dr + √(c₂+ε)∫_v^xe^{at}dt`,
  where `a = 2λ−θ`.
* `V = (100/(c₁c₂²))Σ_{i=0}^{9}αᵢ²Jᵢ`, where
  `Jᵢ = ∫_u^x e^{θt}min((t−u−ih)₊, h)/√(min(t−u,c₂)+ε)dt` and `h = c₂/10`.

| | c₁ | c₂ | θ | V | w(0) |
|---|---|---|---|---|---|
| inherited (CF:9-12) | .09035 | .235968 | 1.28683 | 175.26640331471829 | 10.7055 |
| retuned `CANDIDATE` | .0821922 | .2170903 | 1.4964274 | 243.32098105220588 | 13.1730 |

**Budget.**
`F = ⌈(1+η)V⌉_S − [inside]·n·⌊w(b)⌋_S − [reserved]·n₂·⌊w(hi₂)⌋_S`
(PS:22-27; FE:61-64). With second-family columns, `n₂⌊w(hi₂)⌋_S` is added back
(GL:145).

**Tail column.**
* It covers `[R,∞)` with `R = 3`.
* Far cost `S`, count cost 0, feature 0 in every row.
* Objective `⌈G(R)·w(R)⁻¹⌉_S`.
* It is valid only if `e^{−Aλ}/w(λ)` decreases, which needs `A > 2x`. That
  is asserted only in `replace_far` (FE:58-59).

**Detector and Gram tests** (SI:33-37; BE:36-61).
* `f_γ(t) = ∫(γ²−y²)₊(γ²−(y+t)²)₊dy = (16γ⁵/15)(1−u)³(1+3u+u²)`, with
  `u = |t|/(2γ)` and support `|t| ≤ 2γ`.
* Rows use the normalized `f = f_γ/f_γ(0)` and `g = f_{g₁}/f_{g₁}(0)`.
* `F(z)` has a closed form for `|z| ≥ 1/2`, and a 42-term Taylor series with
  an explicit remainder for `|z| < 1/2`.

**How each enclosure is computed.**
* mpmath `iv` at 50 digits: the kernel, `B`, `G`, `h`, `C`, `J`, `w`, `w⁻¹`, `V`
  and `F`. The integrals `∫rⁿe^{ar²}` use a 64-term series with an explicit
  remainder.
* Binary64 directed rounding: `I_up` and the sum part of `D(δ)`.
* Exact rationals: `D₂` and all integer and rational data.

## 2. The fields of `graded_cert.Leaf` (GC:72-124)

| Field | Quantity it bounds | Rounding | Code |
|---|---|---|---|
| `rows[i][0..1]` | Bin ends `lo_i`, `hi_i`; `hi = 'infinity'` for the tail | exact | PS:7-13 |
| `rows[i][2] = W_i` | `w(hi_i)`, a lower bound; tail: `S` | `⌊⌋_S` | PS:12; FE:65-69 |
| `rows[i][3] = G_i` | `G(lo_i)`, an upper bound; tail: `G(R)/w(R)` | `⌈⌉_S` | TI:54; FE:68 |
| `rows[i][4]` | The two-test feature, used only by the `old` row | `⌊⌋_S` | PS:12 |
| `count_cost[i]` | `S` iff there is no reserved family and `hi_i ≤ λ₃^{lo}` | exact | TI:56; TR:105 |
| `far_budget` | The formula above | as above | PS:22-27 |
| `first` | Inside: `min(⌈J_old⌉,⌈J_new⌉) + J₂`. Outside: `J₂` only (FO:17). `J₂ = n₂⌈G_{φ₂}(lo₂)⌉_S`, removed when second-family columns are used | ceilings | TI:57-62 |
| `final` | `5η·S = 5·10¹⁰` | exact | PS:29 |
| hidden rows | `[lo_h, hi_h, ⌊w(hi_h)⌋, ⌈e^{−A·lo_h}B_φ(p_h)⌉, −, NH = S]`. The hidden tail has `NH = ⌊w(R_h)⁻¹⌋` and objective `⌈e^{−A·R_h}B_φ(p_h)/w(R_h)⌉`; its weight is the inherited one | as shown | FO:19-27 |
| second columns | `[l_j, r_j, ⌊w(r_j)⌋, ⌈G_{φ₂}(l_j)⌉]` with `Σz_j = n₂` | as shown | GL:139-143 |

**Bins** (PS:7-13).
* The points are `[r₀] ∪ {j/den : ⌊r₀·den⌋ < j ≤ ⌊R·den⌋} ∪ {R}`, with
  `r₀ = ordinary_lower` and `R = 3`.
* `den` is 200, 400, 500, 800 or 2000 on inside leaves, and 200 on node and
  outside leaves.
* With a reserved family, bins with `hi ≤ λ₃^{lo}` are deleted.
* An ordinary character goes to any bin containing its `T*` representative's
  `λ`; a representative with `λ ≥ R` goes to the tail with mass `w(λ)`.
* Hidden columns count first-family characters by the parameter `t` of their
  rightmost `R_P` zero with `t ≥ p_h`. Second-family columns take mass
  `n₂·1[ν₂ ∈ column]`.

## 3. Near rows

**Parameters.** The row records carry `gamma`, `g1`, `t0`, `mu`, `s`, `s1`
(LD:62-67). The code asserts `t₀ > 1/3 + 1/1000`, `t₀ < 2γ`, `s ≥ s₁ ≥ 0` and
`2g₁ ≥ t₀`.

**The sieve weight.**
* It uses 2000 cells `t_k`, with `δ_k = (t_k − 1/3)/2 − 1/2000`.
* The `h_k` are exact rationals.
* The family and shifted rows use `μ = 10⁹`, `t₀ = 17/50` and `g₁ ≥ γ+1/1000`.
  This gives `h ≡ 0` by the parameter choice, but it is asserted only for the
  rc pair, dz, outside-family and hidden terms.

**Normalizers.**
* `I_up ≥ ∫e^{2st}f²/ω` is an upper Riemann sum in binary64 intervals, using
  monotonicity.
* `D_up ≥ D(0)` is exact.
* `D⁺(δ) ≥ D(δ)`.
* `d₁ = 1/6`.

**Row quantities:**
* radius `d = ⌈S(1+η)(1/(6D_up) + η)⌉`;
* diagonal `D = ⌈S(1+η)(1 − 1/(6D_up))⌉`;
* feature `V(λ,σ) = ⌊S[(F(λ−σ)/f_γ(0) − 1/6)/√(I_up·D_up) − η]⌋`, clamped at 0;
* offset diagonal `N(δ) = ⌈S(1+η)(D⁺(δ) − 1/6)/D_up⌉`. The entry is omitted if
  `D⁺(δ) − 1/6 ≤ D_up/1000`.

These are exactly the quantities of the Lean theorem `builder_threshold`.

**Family terms.**
* The rc pair uses a μ-grid with second-derivative and Lipschitz slack, and
  `c_hi`.
* The dz terms use a y-grid with the same slacks.
* The shifted row uses `C_Z = C_upper(s−a)`, from the minimum principle, a
  grid with slack and a closed-form tail.
* The old two-test row is a 4.30 premise.

## 4. Where code and PROOF.md differ

1. `J_new`: PROOF.md §3 adds `+ε`, the code does not. The `ε` is covered by E2
   in `final`.
2. Hidden columns: PROOF.md does not state `φ`. The code uses `B_{1/4}` for rc
   and `B_{1/3}` for complex, at `p_h`, with exponent at `lo_h`. The hidden tail
   (`NH = w⁻¹`) is absent from PROOF.md §7.
3. The outside `first` is only `J₂`.
4. `H = 0` in the family and shifted rows holds only through the parameter
   choice.
5. `A > 2x` is asserted only in `replace_far`. Inherited-weight leaves rely on
   `2.347 < 3.156` without an assertion.
6. `replace_far` is skipped for sources with `hidden_rows`.
7. Reserved leaves delete bins below `λ₃^{lo}`; PROOF.md §7 says only "no count
   row".
8. An rc `mu_range` row with `s ≠ s₁` falls back to the single-zero term (valid,
   weaker).
9. "Not safely positive" means `D⁺(δ) − 1/6 ≤ D_up/1000`.

## 5. Corrections from the exact reproduction

A second agent exported every leaf's metadata
(`graded_lean_export.py --numerics`). It recomputed the stored integers from
the metadata alone with mpmath (`computations/graded/leaf_numerics_check.py`;
summary in `computations/graded/lean_runs/numerics_check_3.99.json`).

**Result.**
* Every one of 530,942 integers (106,096 columns, 154 leaves from 117 roots)
  was reproduced exactly: the named roots, 50 random inside and 50 random
  outside roots, and 9 extra roots covering `den` 800/2000, identity nodes and
  rc leaves with and without `J_new`.
* The closest any `S·x` came to an integer is `4.95·10⁻⁷`, so no match depends
  on enclosure width.
* 21 of 22 planted metadata mutations were detected; the remaining one is a
  no-op.

Five gaps in the text above:
1. The tail starts at `R = max(3, r₀)` (PS:8), and the hidden grid ends at
   `max(3, p_h)` (FO:21). For every leaf checked, `R = 3`.
2. The hidden tail's far cost is `W = S`. Every hidden column uses the inherited
   weight. Hidden columns occur only in outside leaves, which always use the
   inherited weight, so each leaf uses a single far profile.
3. Second-family columns take `W` from the leaf's own profile.
4. With second-family columns, the add-back cancels the reserved term exactly,
   so `F = ⌈(1+η)V⌉ − [inside]·n⌊w(b)⌋`.
5. The `λ₃^{lo}` of the count and deletion rules is the final `third_lower`,
   after `refine_third` for rr leaves.

No leaf of the corpus charges a reserved family without columns (`J₂` in
`first`), so that path is implemented but untested by real data.
