# Referee report C — Sections 6 (far), 7 (location), 11 (case tree), 12 (exteriors), 13 (join)

Scope: `paper/sections/06-far.tex`, `07-location.tex`, `11-casetree.tex`, `12-exteriors.tex`,
`13-join.tex` (plus `16-appendix.tex` where it carries the rows of §7). The source files were being
edited while this review ran. Line numbers refer to the text as of the last read, around 03:40 UTC.
Two items I found early were fixed in the meantime, so they are **not** listed below:
- the misquotation of HB Lemma 8.4 in Input rrtables(b), which had dropped "λ₁ ≤ 0.2";
- the "B_φ decreases to φK+K²" wording in Theorem small.

References: HB = Heath-Brown 1992 (author's preprint, cited by lemma/table number), X = Xylouris
2011 dissertation (printed page = PDF page), HB90 = Heath-Brown 1990.

## Summary verdict

**I found no blocking error in the scoped sections.** Every published input I checked is quoted
with the right value, hypotheses and scope, and each is used inside that scope:
- HB Tables 2, 4, 5, 7 and 10; HB Lemmas 8.2, 8.4, 8.8, 9.4, 10.3, 11.1, 13.2 and 13.3;
- X Tables 2′, 3, 6, 7, 8 and 10; X Lemma 4.5; X (4.28), (4.29), (4.31) and (4.34); X Lemma 5.1;
- HB90 Corollary 1, rendered from the PDF, p. 406.

The new analytic content holds up:
- the 1/108 conductor refinement (Lemma lem:Lbounds, Lemma lem:explicitphi, Prop prop:conductor);
- the four-case alias analysis of the degree-5 real rows;
- the principal-index matching for the complex λ₂ rows;
- the R(Δ) bookkeeping of the λ′ rows;
- the λ₃ monotonicity rules;
- the specification semantics, source cover, node soundness, reservation split and drop rule;
- the small and tiny exceptional-zero branches;
- the order of constants.

In each case I rederived the argument, and I recomputed its numbers independently (list at the end).

What remains are justification and definition gaps that should be closed before submission (MAJOR)
and a set of precision, wording and provenance issues (MINOR). None of them changes a number, a
margin or a conclusion.

## BLOCKING

None found.

## MAJOR

**M1. The main-theorem proof uses Prop prop:detect under a hypothesis it has not established.**
- **Where.** `13-join.tex` l.67 and l.72–75 apply it; it is stated in `04-detection.tex` l.117–121.
- **Quote.** Prop prop:detect assumes "Suppose that for all sufficiently large $q$ we have
  $W(q)\le1-2\eta$". The join applies it to a single $q$ in regime (R1), (R3) or (R4).
- **Why it matters.** $W(q)\le1-2\eta$ is proved only for $q$ in those regimes, not for all large
  $q$: in (R2) $W$ is not bounded at all. So as written the hypothesis is not met and the final
  deduction is formally invalid. The proof of prop:detect is pointwise (Input criterion for
  $q\ge q_0(\eps)$), so the repair is immediate.
- **Fix.** Restate it as: "There is $q_0$ such that for every $q\ge q_0$ with $W(q)\le1-2\eta$ and
  every $a$ coprime to $q$ there is a prime $p\equiv a\ (q)$ with $q^A<p<q^L$." Cite this form in
  §13.

**M2. The certified quantity for the λ′ rows is misstated, and a prior bound is hidden.**
- **Where.**
  - `07-location.tex` l.480–484: "margins at least $1.5\cdot10^{-3}$ after the supremum of $R$ over
    all real $\Delta$ is subtracted".
  - `16-appendix.tex` Table tab:polyrows, captioned "λ₁∈[a,b] implies λ′>h".
- **Why it matters (quantity).** $R(\Delta)$ in Prop prop:polyrows (l.459) depends on
  $x=\lambda_1-a$ and $y=\lambda'-a$ through non-monotone terms $-q_i\Re F(x+ik\Delta)$ and
  $-q_i\Re F(y+ik\Delta)$. A supremum over Δ alone at fixed $(x,y)$ does not bound it.
- **What the code certifies.** The data (`computations/core/code/poly_rows.py`, `same_corr`, and
  `results/polynomial_table.json`) take the supremum over $x\in[0,b-a]$, $y\in[p_{\rm row}-a,h-a]$
  and all Δ. Here $p_{\rm row}$ (`old_lower`) is the X Table 2′ value for rows 9–82 (0.96, 0.93,
  0.91, 0.89, 0.86, 0.84, 0.83, 0.827) and $a$ for rows 83–93.
- **The hidden prior bound.** Each row is therefore "λ₁∈[a,b] and λ′≥p_row ⇒ λ′>h". It becomes
  unconditional only when combined with Table 2′. That dependence is stated nowhere.
- **The code does not guard it either.** `endgame.reduced_spec` applies the rows without checking
  `lp ≥ old_lower`. Soundness rests on the unstated invariant that every complex spec inherits
  $p\ge p_j$ from its parent. I checked that the invariant holds, and that each `old_lower` equals
  the parent's $p_j$.
- **Soundness unaffected (sampled evidence).** I sampled three rows ([.68,.6825], [.7375,.74] and
  [.80,.8025]), once with $y$ allowed down to 0 and once with $y\ge p_{\rm row}-a$.
  - In both domains the sampled $R$ is negative on Δ ∈ [0, 30]. Its supremum is therefore the limit
    0 at large Δ.
  - So the margin, $F$-terms minus $\frac M6f(0)$, does not depend on the domain: sampled about
    0.0026, 0.0030 and 0.0031, against certified 0.0018, 0.0021 and 0.0022.
- **Fix.** State the domain of the supremum, add a $p_{\rm row}$ column to Table tab:polyrows and
  cite X Table 2′ for it. Alternatively, recertify with $y\in[0,h-a]$. In either case add an
  assertion `lp ≥ old_lower` in `reduced_spec`.

**M3. The configuration sets of the "sub-cases" are never defined.**
- **Where.** `11-casetree.tex` l.217–247 (subdivision), l.252 (Prop prop:realization) and l.289–298
  (Thm thm:cover).
- **What is used.** The rc height split ($\mu_1\in[0,1]$ versus $\mu_1\ge1$) and the second-zero
  height split ($|y|\in[0,1],\dots,[5,\infty)$) produce "sub-cases". Prop realization and Thm cover
  treat these as if they had configuration sets.
- **The gap.** Def def:specification (l.41–64) has no field constraining $\mu_1$ or $y$, so
  $C(\text{sub-case})$ is undefined and "each of which is exhaustive" (l.297) is not stated as a
  lemma.
- **An ambiguity.** For type complex, λ′ is realized by a non-distinguished pair $(\chi,\rho)$ with
  $\chi\in\{\chi_1,\bar\chi_1\}$ (l.19–23). "The height difference between $\rho_1$ and $\rho'$" has
  two different values depending on whether $\rho'$ is read as a zero of $\chi_1$ or of $\bar\chi_1$
  (µ₁−µ versus µ₁+µ).
- **Fix.**
  1. Add optional constraints to Def spec, e.g. (C6) $\mu_1\in I$ and (C7)
     $\mu_1-\mu_{\rho'}\in J$, where $\rho'$ is taken as a zero of $L(s,\chi_1)$ (conjugating if
     necessary).
  2. State that the finite families of sub-intervals are exhaustive.
  3. Say that the family row of §9 is proved under exactly this convention.

## MINOR

**m1. The parent-row proof rule does not cover one table entry.**
- **Where.** `07-location.tex` l.129–131 (proof of Prop parentrows) and l.160 (complex
  $[.82,1.5]$: $p_j=.827$).
- **Why it matters.** The stated rule takes the maximum of the table rows "whose threshold $t$ is at
  least $B_j$", together with the trivial bound $\lambda_1\ge A_j$. For $B_j=1.5$ no table row
  qualifies and the trivial bound gives only 0.82.
- **Why the value is still right.** $\lambda'\ge.827$ holds on $[.82,1.5]$ by a case split:
  - λ₁ ≤ .827 is covered by X Table 2′, row (0.827, 0.827);
  - λ₁ > .827 is covered by the trivial bound λ′ ≥ λ₁.

  The code (`cover_v4/case_cover`) confirms the value.
- **Fix.** Add this case split, or state the rule as "valid on $[A_j,\min(B_j,t)]$ plus the trivial
  bound beyond $t$".

**m2. Ambiguous wording of the order cases.**
- **Where.** `07-location.tex` l.44–45: "for characters of order at least 6, 5, 4, 3 and 2
  respectively".
- **Fix.** X Lemma 4.5 is "ord ≥ 6; = 5; = 4; = 3; = 2". Write "of order ≥6, 5, 4, 3, 2
  respectively".

**m3. X (4.34) is misdescribed, and the sampled value is off.**
- **Where.** `07-location.tex` l.107–110.
- **Misdescription.** "(4.34) is less than $0.10<0.13\le\frac5{48}f(0)$". It is the supremum term
  $\sup\Re\{F(-\lambda_2+it)-F(\lambda_1-\lambda_2+it)-F(it)\}$ that is below 0.10 (X p.59). The
  expression (4.34) itself includes $-\frac5{48}f(0)$ and is ≤ 0.
- **The value.** "a sampled check of ours gives a supremum of about 0.0021". My sampling (γ = 1.04,
  93×37 parameter grid, t-step 5·10⁻⁴) gives ≈ 0.00258, at (λ₁, λ₂, t) ≈ (0.44, 1.176, 5.17).
- **Why it matters.** Rule (5) of Prop prop:third feeds the count row and the bin drop of every rr
  leaf with λ₁ ∈ [.44, .80]. The paper verifies (4.29) by interval arithmetic but (4.34) only by
  sampling.
- **Fix.** Correct the wording and the number. Enclose (4.34) rigorously in the style of
  `alias_check.py` (the margin is huge: about 0.0026 against 0.135). Alternatively, cite it purely
  as X's printed claim.

**m4. The γ column of the real-row table is rounded without saying so.**
- **Where.** `07-location.tex` Table tab:realrows (l.374 onward).
- **Detail.** The stored parameters are exact rationals, e.g. 548121/500000 = 1.096242 (printed
  1.09624) and 219043/200000 = 1.095215 (printed 1.09522). The margins agree to the printed digits
  either way: I recomputed rows 1, 2, 9, 16 and 22 of Table tab:realrows.
- **Fix.** Say "γ rounded; exact values in the data", or print the exact rationals.

**m5. Notation and proof text in Prop prop:conductor and Prop prop:realrows.**
- **Where.** `07-location.tex` l.282 and l.338–340.
- **Notation.** $\Re(\chi_2(n)n^{-i\gamma_2})^k$ reads as $(\Re z)^k$. The proof (l.290) needs
  $\Re(z^k)$.
- **Proof text of the order-4 case.** "the frequency-5 characters are nonprincipal and are charged
  1/3". The displayed coefficient $\frac{1+c_2}8+\frac{c_1+c_5}3$ also charges the frequency-1
  characters $\chi_2$ and $\chi_1\chi_2=\bar\chi_2$ at 1/3, and they could have $\varphi=\frac14$
  since ord χ₂ = 4. The coefficient is correct, being conservative; the sentence is incomplete.
- **Fix.** Write $\Re((\chi_2(n)n^{-i\gamma_2})^k)$, and say that the frequency-1 and frequency-5
  characters are charged 1/3 (conservatively).

**m6. "The same radius δ" in lem:explicitphi.**
- **Where.** `07-location.tex` l.261.
- **Why it matters.** HB's radius depends on $k=3+[3\varphi/(2\eps_0)]$. The φ_q version uses the
  φ = 1/3 choice of k. So it is "the same" only if the radius of Input X32 was already the
  φ = 1/3 one.
- **Fix.** Say "with the radius obtained for φ = 1/3 (which serves all characters)".

**m7. The "finitely many choice rules" hedge does not fit the join.**
- **Where.** `06-far.tex` l.26–32 and `13-join.tex` l.45–46.
- **The tension.** The hedge is meant to make one $q_0$ serve all choices of zeros. But $T^*$, and
  hence the $T^*$-representatives, is "chosen afterwards, for each q".
  - Under the weak reading of X Lemma 5.1 ($q_0$ depends on the choice rule), the rule would have
    to be fixed before $q_0$.
  - Under the natural reading (the proof is uniform in the choice; X §3.2.2 "wählen wir eine
    zugehörige Nullstelle"), the hedge is unnecessary.
- **Fix.** Either assert uniformity in the choice, citing that the proof of (5.22)–(5.24) never
  uses it, or fix an explicit rule in (S1), e.g. "$T^*(q)$ = least admissible point of a fixed grid
  of step $M/\LL$".

**m8. Inconsistent scope statements about representatives.**
- **06-far.tex l.159–161.** "the last term is present when $\rho_1$ is a height-one zero of
  $\chi_1$". The formula (l.157) uses $\1_{\rm inside}$, and the code subtracts only for inside
  leaves. Inside implies height one, but not conversely.
- **06-far.tex l.134–138.** Def representative is stated "for a nonprincipal character χ outside the
  first family", yet it prescribes height-one representatives for "an inside first family".
- **12-exteriors.tex l.166–168.** Theorem large applies Cor ordinarycost to every character,
  including the first family. The corollary (`05-costs.tex` l.234) is stated only for characters
  outside the first family. Its proof does not use that restriction.
- **Fix.** Align the wording in all three places.

**m9. Theorem small: $R$ must be large enough for Input hb133.**
- **Where.** `12-exteriors.tex` l.39–56 and l.103–120.
- **Why it matters.** Input hb133 requires $0<\lambda\le R$, where $R=R(\eps)$ comes from Input
  hb132. It is applied with λ = m* ≈ 2.753 and λ = m₂ = 2.829.
- **Why it is fine.** HB's proof of Lemma 13.2 works for every $R\ge R_0(\eps)$: a larger rectangle
  only adds nonnegative terms. So one may enlarge R.
- **Fix.** Say so.

**m10. HB Table 4 also has side conditions.**
- **Where.** `07-location.tex` l.30–33 mention only the root recomputation. Table 4 rows are valid
  only if (8.6) and (8.8) hold, on HB's rule: (8.6) at λ₁ = B with the λ′ of the previous row, and
  (8.8) at λ₁ = A.
- **My check.** Both hold for every row from 0.35 to 1.294.
  - (8.8) slack is at least 0.135.
  - (8.6) is tight: slack 3.8·10⁻⁶ for rows 1.05 and 1.15, 2.3·10⁻⁶ for row 1.294.
  - Row 0.3 is anyway implied by HB Table 3 (λ₁ ≤ 0.3 ⇒ λ′ ≥ 2.43).
- **Roots.** I confirm 1.4390381 against 1.439.
- **Fix.** Add one sentence stating that the side conditions were checked.

**m11. Tie-breaking in the selection of zeros.**
- **Where.** `11-casetree.tex` l.48–49: "for some admissible choice of $(\chi_1,\rho_1)$ and of the
  minimizers".
- **Why it matters.** This is sound only if every printed input holds for every tie-breaking in
  HB/X's selection of $\rho_k,\chi_k$ (§6 of HB; X (3.11)–(3.12)). It does: their proofs use only
  the maximality property. This is also what makes λ₃ well defined when two families attain λ₂.
- **Fix.** State it once in §7.1.

**m12. The per-cell bounds in the data are stronger than the text says.**
- **Where.** `11-casetree.tex` l.101–106.
- **Detail.** In `source_cover.json.gz`, 91 first-zero cells carry `source_l2` = max(r_j, lo of the
  cell), which is larger than the base cell's value. This is valid, by the same trivial bound. The
  text says only that base cells receive max(r_j, lo).
- **Fix.** Say that every cell receives max(p_j, lo) and max(r_j, lo) for its own lo.

**m13. The count rule for reserved leaves is not stated.**
- **Where.** `11-casetree.tex` l.193–195. For reserved leaves the remaining bins have count
  coefficient 0 (`triple_inputs.input_with_third`, `refine_third`).
- **Fix.** Say so explicitly.

**m14. Provenance of the (4.29) check.**
- **Where.** `07-location.tex` l.106–107 cite "supremum at most 0.00335". The corresponding
  `results/alias_condition.json` is not in the repository.
- **Reproduction.** I ran `alias_check.check()` in memory, writing nothing to disk. It gives
  supremum_upper = 0.0033430834659906; the grid part is −0.0016 and the value comes from the tail
  bound for y ≥ 30.
- **Fix.** Commit the result, or cite the script.

## Independent verification performed

The scripts are in the scratchpad `refC/`; nothing in the repository was modified.

**Far (§6).**
- Recomputed with mpmath from the printed c₁, c₂, θ, ε₀ = 10⁻⁷ and α:
  - V = 175.266403314718… (inherited) and 243.320981052205… (retuned);
  - w(0) = 10.70547515… and 13.17302351…;
  - x = 1.17368466… and 1.13033356…;
  - K_far = 16.37168 < 16.38 and 18.47118 < 18.48;
  - A − 2x ≥ 0.809.
- The α of each profile sum exactly to 1.
- Input far matches X Lemma 5.1 / (5.19) exactly: J = M, the same hypotheses on w₀, and the same
  (6.20) profile shape with ε₀ = 10⁻⁷.

**1/108 (§7).**
- HB §16 item 4 gives ψ ≤ (1/8)log q₁/log q + min(1/3, (1/4)log q₂/log q), with q₁ = rad q and
  q₂ = v³q.
- The paper's version is correct and slightly more careful: a real primitive χ* has modulus
  q* ≤ 4 rad q* (for example q* = 8m), and HB's q₁ = rad q is off by that constant factor.
- I checked the partial-summation cut with a general Q and the PV tail. The HB Lemma 2.3 exponent
  (3k−1)/(4k²) ≤ 3(k+1)/(4k²) holds. rad q ≤ q v^{−2/3} holds. The slopes 3Σ/4 − 1/12 and −1/12
  are right, and g(1/9) = 1/8 + Σ/3 − 1/108. For Σ = 1 this is 97/216.
- HB Lemma 3.1 uses (2.5) only through (3.5). The choices k, R, ε and δ can be made with φ ≤ 1/3,
  and the zero count c₀L does not depend on φ.

**Degree-5 real rows.**
- P ≥ 0 on [−1, 1]: min ≈ 9.27·10⁻⁷ at x ≈ −0.8392 (dense sampling), above the interpolation slack
  2.5·10⁻⁷ used in the code.
- The four-case alias analysis for frequencies {1, 2, 5} is exhaustive and disjoint, and each
  conductor coefficient matches its case.
- Rows [.7000,.7025], [.7025,.7050], [.7200,.7225], [.7375,.7400] and [.7525,.7550]:
  - generic margins 1.0198e−4, 5.857e−5, 4.458e−5, 3.827e−5 and 8.600e−5 (as printed);
  - order-5/10 and real margins as printed;
  - order-4 margins ≥ 0.0804 (sampled 0.0811).
- Prop realfirstsecond: 3.63e−4, 0.0827 and 0.0337.

**Complex rows.**
- I rederived the injectivity of T, the 4t coefficient ratio and the relative height w·µ, and the
  single alias family (±2, ±1) in case (ii).
- R(Δ) of Prop polyrows is rederived term by term: p₁ = c₁²/2, p₂ = c₂²/2, q₁ = c₁(1 + c₂/2),
  q₂ = c₁c₂/2 and M.
- From the JSON: 25 λ₂ rows with minimum generic margin 8.27e−4, alias 0.1637, real 0.0206 and real
  alias 0.1658; 69 λ′ rows with minimum margin 1.537e−3.

**HB tables.**
- Table 4: all 24 roots exceed the printed values (closest 1.4390381).
- Table 7: all 17 roots exceed the printed values (2.01015 and 1.00036, as the paper says).
- Table 2, row 0.10: root 4.963551. Table 5, row 0.10: root 2.845770. Both match the paper.
- Table 7 dominance by Table 6 (for χ₂⁴ = χ₀) holds from row 0.12 on. It fails only at row 0.10,
  which the paper does not use.

**Parent rows and source cover.**
- The code `cover_v5.PARENTS` reproduces all 58 rows of Table tab:parents: 33 rr, 13 rc and
  12 complex.
- `source_cover.json.gz` has 340 base cells, 478 cells, 684 gap cases and 2768 specs (rr 1083 =
  195 + 444 + 444; rc 115; complex 1570).
- Every gap partition starts at lp and ends at ∞; every reserved chain starts at l₂, is contiguous,
  ends at e ≤ 2, and carries both n₂ = 1 and n₂ = 2 plus a tail with r = e.
- Every cell's lp and l₂ are at most max(p_j, lo) and max(r_j, lo) of its parent.

**Case-tree logic.**
- Lemma familyfacts (i), (ii) and (iii) are correct. (ii) follows from minimality alone: when
  F = G₂, the reserved family is not in {F₁, G₂}, so ν(F_res) ≥ λ₃.
- The reservation split is correct.
- Every node type is exhaustive or sound.
- The far, count, hidden-count and value bookkeeping of Prop realization is consistent:
  - n·w(b) is subtracted only for inside leaves, justified by |γ₁| ≤ C_B/L ≤ 1;
  - rr is always inside;
  - rc and complex occur both inside and outside, and the hidden columns use p° = max(a, p, g⁻),
    a valid anchor.

**λ₃ rules.**
- Rule (5) on [.7025,.705]: 1.05032 unreserved and 1.08886 with cap .85 (printed 1.0502 and 1.0888).
- The same formula reproduces X Table 10: 1.1769, 1.0559 and 0.9525.
- (4.29): the repository check gives 0.003343 ≤ 0.00335. (4.34): sampled ≈ 0.00258.
- The derivation of HB (10.6) does not use λ₃ ≤ 6/7. X's reduction of (4.32)/(4.33) to (4.34) is
  valid via (3.38), which gives A_sup ≥ 0.

**Small branch.** All displayed numbers are reproduced to 10 digits:
- a_d = 3724/1875, b_d = 671/750, V_d = 184750/6993;
- m* = 2.75304422;
- A_s − a_d − 1/α = 236171/327000;
- M(0.08) = 0.1088458429, other = 0.0783116746, first = 0.0000454655, μ₁ = 0.0304887029;
- M(0.1) = 0.1050056698, other = 0.0668874692, first = 1.53·10⁻⁸, μ₂ = 0.0381181853.

The ratios are 28% and 36%. At L = 3.90 the margins are μ₁ = 0.00625 and μ₂ = 0.01667, both
positive. The monotonicity arguments, the error term ℰ and the use of Input hb111 (monotone in φ)
are correct. The two table rows at 0.10 hold for all λ₁ ≤ 0.10, and Lemma 8.8 with α = 1.09 holds on
[u₀, 0.08] (via Lemma 8.6 and HB Table 5).

**Tiny branch.** Input siegel matches HB90 Corollary 1 exactly: β₀ ≥ 1 − 1/(3 log q), a real ψ not
necessarily primitive, η = ((1−β₀)log q)⁻¹, and P(a,q) ≤ q^{3+δ} for all a coprime to q. The paper
uses it within these hypotheses (λ₁ < u₀ ≤ 0.08 < 1/3).

**Large branch.** The large-branch verification data match the text: maximum 0.9946508085154141 on
threshold interval [0.1625, 0.165], Y = 5139815868, Z = 1622818786878, 36 branches, 5436 checks, and
far budget (1+η)V at the inherited profile.

**Join.** I found no circularity:
- K₀ uses height 2 > 1 + δ₀, so M can be fixed before δ₀;
- N(C_P) does not depend on δ₀;
- T* is chosen per q after q₀.

The regimes are exhaustive, and the boundaries are covered: λ₁ = 0.1 falls in (R3), and λ₁ = 1.5
falls in (R4) (Theorem large). The only gap is M1.
