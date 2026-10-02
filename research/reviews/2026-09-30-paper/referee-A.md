# Referee report A: Sections 3, 4, 5 and 8 (with Sections 2 and 13 where relevant)

Paper: "Linnik's constant is at most 3.99" (`paper/linnik399.tex`, `paper/sections/*.tex`).
Line numbers refer to the sources as re-read at the end of the review (after 03:10 UTC).
`02-notation.tex`, `05-costs.tex` and `13-join.tex` were edited during the review. Those edits
fixed seven points I had flagged; none is listed below:
* the case λ_1 > p in Prop. 5.9;
* the wording of the J_old step;
* the definition of λ' for the complex type;
* the stage of ε_1 (now (S1));
* the cross-reference for δ_0 (now `subsec:zerocount`);
* the internal "4.33 argument" reference;
* E ≤ 2η.

Sources checked:
* **X**: Xylouris's dissertation. The printed page equals the PDF page.
* **HB**: Heath-Brown 1992, the author's preprint, checked by lemma and equation number. "copy p." means a preprint page.
* **HB90**: Heath-Brown 1990. The statement on p. 406 was checked on the rendered page.

Theorem numbers follow the compiled text:
* Input 3.2 is the comparison lemma; Inputs 3.3/3.4 are X Lemmas 3.1/3.2; Input 3.6 is X Lemma 3.10; Input 4.2 is X's criterion.
* Lemma 5.1 is the envelope lemma; Lemma 5.2 smoothing; Lemma 5.3 zero count; Lemma 5.4 anchored inequality.
* Prop. 5.6 is the localized envelope; Remark 5.7 relates it to X Lemma 3.10; Prop. 5.8 is the first family inside; Prop. 5.9 the first family outside.
* Theorem 8.3 is the graded near-density lemma; Lemma 8.4 Burgess for all characters; Lemma 8.6 the response lemma; Prop. 8.7 the threshold form; Cor. 8.8 the zero form.

Severity scale:
* **BLOCKING**: threatens the main theorem.
* **MAJOR**: the written argument has a real logical gap. The repair may be short, but it must be made.
* **MINOR**: wording, citation, notation or local precision.

---

## Summary verdict

**No blocking error found.** I re-derived every proof in Sections 4, 5 and 8 and compared every Input in Section 3 with its printed source. The analytic content is correct.

**Section 4 (prime detection).**
* **Triangle decomposition.** Each block convolution is h_{(i+j+2)κ,κ}, c_k > 0, and the left endpoints are A + kκ ≥ A = 3.156342 > 3.
* **Applicability of X (3.57).** X states (3.57) for a finite real combination with L_i > 2K_i + 3 (X p. 34). It applies with ε = ηH_0, and enlarging the square from C_0 to C_P ≥ C_0 is harmless.

**Section 5 (costs).**
* Lemma 5.1(i)–(v) holds.
* Lemma 5.2 holds (||ψ − ψ^θ||_1 ≤ 0.73θ for the stated mollification).
* The zero count holds (|1 − e^{−w}| ≥ |w|/2 for |w| ≤ 1/2; N = ⌊4c_1/K_1²⌋).
* The localized envelope holds.
* J_old holds in all cases (p < a, λ_1 ≤ p, λ_1 > p).
* J_new holds: k(t) ≥ 0, k is monotone in λ_1, and ∫k|_{λ_1=a} = H_0(e^{−Aa}h(a) − e^{−Ap}C(p,a)).
* c_out follows from two integrations by parts.
* The allowance holds: E ≤ 19ε_1 + 4ε_1 + η = 2η with ε_1 = η/23.
* Nothing needs f(0) ≥ 0 or Condition 2 where it is not verified.
  - f^θ_λ, f^(1) and the Gram test satisfy Condition 2.
  - The detector needs Condition 2 only in Lemma 8.6 and Cor. 8.8, where it is assumed.

**Section 8 (graded near-density lemma).**
* The Cauchy–Schwarz step and the first factor (upper Riemann sums with Mertens) are correct.
* **Q_1.**
  - Diagonal: by Input 3.3.
  - Distinct characters: every disc zero has λ_ρ ≥ s_1 ≥ σ_jk by SA(s_1, 2T+1); the terms drop by Condition 2; the bound is d_1 + o(1). This also holds for σ_jk < 0.
  - Same-character pairs: by Input 3.3, with the symmetrization giving e_j.
* **Q_2.**
  - The majorant holds (p ≥ q^{t_k} > D_k).
  - Graham's estimate with Stieltjes summation gives ∫ t/δ_k e^{−2δ_j t} + O(1/L).
  - Off-diagonal: Burgess with pointwise Abel summation, and Σ_{d,e≤D}[d,e]^{−2/3} ≤ 9ζ(4/3)D^{2/3}.
  - The exponent is exact: 1/9 − t_k/3 + 2δ_k/3 = −2ε'/3.
* All o(1) terms are uniform in the number of entries: they are either per-entry multiples of a_j² or multiples of (Σa_j)².
* Lemma 8.6, Prop. 8.7 and the algebra of Cor. 8.8 are correct.

**Literature checks.**
* The "any smaller radius" claim for Input 3.4 is correct. It follows from HB's proof of Lemma 3.1 (copy p. 14): the constraints 0 < R ≤ 1/k, δ < R and φ/(2k) + 6ε/(πR) + c_0δ/R² ≤ ε_0 persist when δ decreases. HB's Lemma 5.2 then discards the remaining zeros at cost ≪_δ A(f) log(2+|s|).
* The φ(χ) of Input 3.4 matches HB Lemma 2.5 (copy p. 10), stated for all non-principal χ mod q.
* Inputs 3.3–3.5, 3.7, 3.8 and 3.10 match their printed statements.

**Numerical spot checks** (my own quadrature script, `scratchpad/refA_check.py`, run with the project venv):
* Lemma 5.1(ii) and (iv) agree to quadrature accuracy.
* The J_new identity D(y) = ∫k(t) cos(yt) dt agrees at (λ_1, p) = (0.74, 1.54), y ∈ {0, 2, 10}, and min k > 0.
* The kernel constants A = 3.156342, Ψ(0) = 0.19364229…, H_0 = 0.03749733… and 3 + 2T = 3.833658 are confirmed exactly.

**What needs repair:**
1. **Order of quantifiers and constants around four parameters:**
   * the fixed disc radius δ_0 versus arbitrary (θ, ε);
   * c_out versus ε_1;
   * the separation M and the response radius versus the η'' of Cor. 8.8.

   Several statements are over-quantified as written, or (S4) fixes a constant that Cor. 8.8 does not use.
2. **The θ bookkeeping in Prop. 5.8** ("letting θ → 0").
3. **Presentation.** Every cross-reference to an Input, Lemma, Proposition or Definition prints as "Theorem" (a cleveref type bug). There are also notation overloads and citation details.

None of these affects the certificates or the value 3.99, and each is repairable without new mathematics.

---

## BLOCKING issues

None found.

---

## MAJOR issues

### A1. Cor. 8.8 applies the response lemma at η'', but (S4) fixes M (and Section 9 fixes the disc) for η'

**Where:**
* `08-near.tex` 307–309: "Put η'' = η' min(1, √(I_B D_u), D_u) and apply Theorem 8.3, Lemma 8.6 with η'' in place of η'".
* `08-near.tex` 291–294: "each entry j comes with a finite set S_j of kept zeros satisfying the hypotheses of Lemma 8.6".
* `08-near.tex` 245–246: M and δ are produced from η'.
* `13-join.tex` 21–22: "the separation M, so large that for |Y| ≥ M we have |Re F(x+iY)| ≤ η'/(2K_0+2)".
* `09-rows.tex` 97 and 110 apply the lemma on the disc of radius δ_0.

**Problem.** In Lemma 8.6 the separation M satisfies |Re F(x+iY)| ≤ (tolerance)/(2K_0+2) for |Y| ≥ M, and the radius δ is the Input 3.4 radius for ε = (tolerance)/2. Both depend on the tolerance.

Cor. 8.8 uses tolerance η'' ≤ η'. It therefore needs M(η'') and δ(η''/2). Stage (S4) fixes M only for η'.

Whenever min(1, √(I_B D_u), D_u) < 1, the separation that Lemma 9.4 (strip) delivers with the (S4) value of M does not verify the hypothesis of Lemma 8.6 at η''. This can happen: for the normalized parabolic Gram test, D(0) ≥ ∫g_1 = 5g_1/6, which is below 1 when g_1 < 1.2.

The Lean `builder_threshold` (`lean-graded/GradedNear/Builder.lean`, lines 127–128) avoids the problem: it obtains M and δ from `graded_near_threshold` applied with η''. The formal chain is therefore consistent; the paper's text is not.

It is probably harmless in the corpus, because Lemma 9.4 is only invoked in graded rows with s > l_2, where D_u contains the sieve diagonal. But the paper does not check that min(1, √(I_B D_u), D_u) = 1 for those rows.

**Fix.**
1. In Cor. 8.8 write "... satisfying the hypotheses of Lemma 8.6 with tolerance η'' (that is, with separation M(η'') and radius δ(η''))".
2. In (S4) replace η' by η''_min := η' · min over the finitely many rows of min(1, √(I_B D_u), D_u). This quantity is fixed in (S1).
3. Add to Lemma 8.6: "The conclusion holds with δ replaced by any δ' ∈ (0, δ], since Input 3.4 remains true for smaller radii." Section 9 uses the disc of radius δ_0.

### A2. A fixed disc radius δ_0 against arbitrary (θ, ε, ε_1): statements over-quantified

**Where:**
* `05-costs.tex` 108–112: "We fix once and for all a radius δ_0 ∈ (0,1/3] for which Input 3.4 holds for all the finitely many test functions and families of test functions used in this paper".
* `05-costs.tex` 157–163, Lemma 5.4: "Let θ ∈ (0,1) and ε > 0. For q ≥ q_0(θ,ε), every χ ≠ χ_0 ... Σ_{ρ in the disc of χ} Φ^θ_σ(ρ) ≤ H_0 B^θ + ε".
* `05-costs.tex` 177–178, Prop. 5.6: "For every ε_1 > 0 there is q_0".
* `05-costs.tex` 348–350, Prop. 5.9: "There is a constant c_out, depending only on the fixed choices of stages (S1)–(S3), such that for every ε_1 > 0 ...".
* `13-join.tex` 26–27.

**Problem.** Input 3.4 gives its inequality on a disc of radius δ(f, ε). That radius shrinks as ε → 0.
* In HB's proof of Lemma 3.1 one needs c_0δ/R² ≤ ε_0 with R ≤ 1/k and k ≥ 3φ/(2ε_0).
* Through X p. 36, δ also depends on the family's derivative bounds. For f^θ_σ these blow up as θ → 0.

A disc of fixed radius δ_0 therefore cannot serve every (θ, ε). Consider the zeros with δ(ε) < |1−ρ| ≤ δ_0. Each contributes Re F ≍ f(0)/λ_ρ, and no input bounds their number by less than O(L). The enlarged-disc inequality is not implied by Input 3.4 or by its proof.

Consequences:
* Lemma 5.4 as stated (all θ, all ε, disc δ_0) is not proved.
* Prop. 5.9 as stated (c_out fixed, all ε_1) is not proved. Its proof needs θ = θ(ε_1), and c_out = C_P f^θ_p(0) + |(f^θ_p)'(0)| + e^{C_P T}||(f^θ_p)''||_1 grows as θ → 0.
* The zero count (Lemma 5.3, ε = 1) is fine once δ_0 is chosen after f^(1) is fixed.

The final argument is sound. The only uses are:
* θ from (S3);
* ε = H_0ε_1/2 with ε_1 = η/23;
* ε = 1 in Lemma 5.3.

Stage (S5) chooses δ_0 after all of these.

**Fix.**
1. In §5.3, write: "Let θ be the smoothing parameter of (S3) and ε_1 = η/23. We fix δ_0 ∈ (0, 1/3] not exceeding the radius that Input 3.4 provides for f^(1) with ε = 1, for the family {f^θ_σ : σ ∈ [λ_11, C_P]} with ε = H_0ε_1/2, and for the detectors and Gram tests of the near rows with their tolerances (η''/2, and the Q_1 tolerances). This is possible because Input 3.4 remains true for every smaller radius."
2. Lemma 5.4: state it for these θ and ε. Alternatively: "for every θ, ε there is δ(θ, ε) such that for every radius δ_0 ≤ δ(θ, ε) ...".
3. Prop. 5.9: state it "for ε_1 = η/23 and the θ of (S3)", or write c_out = c_out(θ).
4. Props. 5.6 and 5.8 stay true for every ε_1: their hypotheses on the δ_0-disc imply the same hypotheses on any smaller disc. Their proofs should then apply Lemma 5.4 on the disc of radius min(δ_0, δ(θ(ε_1), H_0ε_1/2)). Or state them for ε_1 = η/23 only.

### A3. θ bookkeeping in Prop. 5.8: "letting θ → 0" is not legitimate, and the (S3) choice is not shown to suffice

**Where:**
* `05-costs.tex` 272–273: "Let θ and the errors be chosen as in the proof of Prop. 5.6".
* `05-costs.tex` 285: "+(errors)".
* `05-costs.tex` 327–330: "... up to O(θ) from replacing Ψ by Ψ^θ. Letting θ → 0 (Lemma 5.2(iii)) and choosing the errors as before gives the bound H_0(J_new/n + ε_1)".
* `13-join.tex` 16–18: θ is "chosen as in the proof of Prop. 5.6".

**Problem.** The q_0 of Lemma 5.4 depends on θ, so θ cannot be sent to 0 once q ≥ q_0 is fixed.

With θ as in Prop. 5.6 (3Nθ + H_0 sup|B^θ_φ − B_φ| ≤ ½H_0ε_1), the proof incurs errors that this budget does not contain:
* **In J_old:** 3θ for each of the α distinguished occurrences, from Φ^θ_a(ρ) ≥ X_ρ − 3θ. They are not among the ≤ N zeros counted when ρ_1 ∈ R_B \ R_P.
* **In J_new, per distinguished occurrence:** 3θ for Ψ → Ψ^θ; H_0 e^{−Aa}|h^θ(a) − h(a)| ≤ 3θ; and H_0 e^{−Ap}|C^θ(p,a) − C(p,a)| ≤ 2θ(2T + θ). These follow from Lemma 5.2(ii),(iii).

The extra total is ≤ 18θ. It is absorbed in practice:
* N ≥ 64 C_P² · 2 > 1000, so θ ≤ H_0ε_1/(6N);
* the per-character bound carries the factor e^{−Ap} ≤ e^{−0.1A} < 0.73.

The proof must say this.

**Fix.**
1. Replace lines 327–330 by an explicit estimate: "Replacing B^θ, h^θ, C^θ by B, h, C and Ψ by Ψ^θ costs at most H_0 sup|B^θ_φ − B_φ| + 18θ (Lemma 5.2(ii),(iii))."
2. In Prop. 5.6 and (S3), choose θ with 3Nθ + 18θ + H_0 sup_{σ∈[λ_11,C_P], φ∈{1/4,1/3}} |B^θ_φ − B_φ| ≤ ½H_0ε_1.

The per-character error in J_old and J_new is then ≤ H_0ε_1, with no appeal to slack.

---

## MINOR issues (in order of importance)

**m1. Every cross-reference to an Input, Lemma, Proposition or Definition prints as "Theorem".**
* **Evidence.** `linnik399.aux` records the type `[theorem]` for all such labels, for example line 190: `\newlabel{inp:X32@cref}{{[theorem][4][3]3.4}...}`.
* **Compiled text examples:**
  - "Theorem 8.3 (Graded near-density lemma). Assume Theorems 3.3, 3.4, 3.7 and 3.8." These are Inputs.
  - "Heath-Brown's Conditions 1 and 2 (Theorem 3.1)" is a Definition.
  - "as in the proof of Theorem 5.3" is Lemma 5.3.
  - "accounted for in Theorem 4.4" is Prop. 4.4.
  - "Theorem 3.7 and Theorem 8.4" are Input 3.7 and Lemma 8.4.
* **Why it matters.** In the statement of the main new result, published inputs are presented as theorems of the paper. This defeats the careful Input/Lemma distinction of Section 3.
* **Fix.** Give each environment its own alias counter. With `aliascnt`: `\newaliascnt{inp}{theorem}\newtheorem{inp}[inp]{Input}\aliascntresetthe{inp}\crefname{inp}{Input}{Inputs}`, and likewise for lemma, proposition, corollary, definition, assumption, remark and example. Alternatively use `thmtools`' `\declaretheorem[sibling=theorem]`. Then check that the aux file shows `[inp]`, `[lemma]` and so on.

**m2. Uniformity in the anchor rests on a remark in X that is not proved.**
* **Where.** `03-inputs.tex` 75–79; `05-costs.tex` 110–112 and 173–174: "The threshold q_0 is uniform in σ ∈ [λ_11, Λ] by Lemma 5.2(i) and the uniformity statement of [X, p. 36]".
* **Problem.** Cor. 5.5 uses Prop. 5.6 with anchor λ_* = λ_χ, which ranges over a q-dependent continuum. The only support is X's remark after Lemma 3.10, which he says requires "wieder einen Blick in die Beweise" and does not carry out. It is credible: HB's constants are explicit in B, x_0 and |f(0)| (A(f) = 3Bx_0 + 2|f(0)|/x_0 in (5.4); the shift constant after (5.7); the radius of Lemma 3.1 depends only on ε_0, φ and c_0). But it is load-bearing.
* **Fix (removes the dependence).** Use a finite grid {σ_i} ⊂ [λ_11, C_P] of mesh h, chosen so that |B_φ(x) − B_φ(y)| ≤ ε_1/4 for |x − y| ≤ h.
  - For λ_* ∈ [σ_i, σ_{i+1}), apply Lemma 5.4 at σ_i ≤ λ_*.
  - Every disc zero has λ_ρ ≥ λ_* ≥ σ_i. Hence Φ^θ_{σ_i}(ρ) ≥ |Ψ^θ(λ_ρ − iμ_ρ)|² and e^{−Aλ_ρ} ≤ e^{−Aλ_*}.
  - The result is e^{−Aλ_*}(B(σ_i) + ε_1/2) ≤ e^{−Aλ_*}(B(λ_*) + ε_1).
  - Only finitely many test functions f^θ_{σ_i} are used, together with the finitely many leaf anchors a and p. No uniformity statement is needed.

**m3. The first-family hypothesis needs "in R(l)".**
* **Where.** `05-costs.tex` 246–248 and 343: "every zero occurrence of the first family other than the distinguished ones has parameter at least p".
* **Problem.** Taken literally (zeros of any height), this is stronger than p ≤ λ', which after the new definition in `02-notation.tex` 52–56 concerns occurrences in R(l) only. A zero at height 100 with λ < p is not excluded by λ' ≥ p. The proofs only use disc zeros (|γ| ≤ δ_0), which lie in R(l) or have λ > (1/3) log log L.
* **Fix.** Insert "in R(l)" at lines 247 and 343. At line 252 write "equivalently, p ≤ λ'".

**m4. Lemma 8.4 (Burgess for all non-principal characters): gaps in the proof.**
* **Where.** `08-near.tex` 225–229: "Each inner sum has length at most H. Its initial point may be 0, which is handled by removing the terms up to q* and shifting by q*; this uses that ψ* sums to 0 over a period. Input 3.7 bounds each inner sum by C q*^{1/9+ε} H^{2/3}."
* **(a) Length hypothesis.** Input 3.7 requires the inner length H/e to satisfy H/e ≤ q*. This can fail when H ≤ q but q* is small. Remove complete periods of ψ* first (they sum to 0 because ψ* is non-principal). Input 3.7 then gives C q*^{1/9+ε} min(H/e, q*)^{2/3} ≤ C q^{1/9+ε} H^{2/3}.
* **(b) Start point.** When ⌊N/e⌋ = 0, shift by q* using periodicity alone; the zero-sum property is not what is used there.
* **(c) Real endpoints.** Say that N and H may be real, since the sum only sees ⌊·⌋. Theorem 8.3 applies the lemma with real M_0 and u.

**m5. Lemma 12.1 of HB as the "degenerate case" contradicts the hypothesis on the datum.**
* **Where.** `08-near.tex` 32–33: "Heath-Brown's Lemma 12.1 corresponds to the degenerate case g = f, s = s_1 = λ_1, H = 0 and all offsets 0."
* **Problem.** With g = f and H = 0, ω = f e^{λ_1 t} tends to 0 at the right end of supp f. It is therefore not bounded below on supp f, as line 23 requires. HB writes f = √f·√f and needs no lower bound.
* **Fix.** Either say "is the formal analogue of", or weaken the hypothesis to: ω > 0 where f ≠ 0, and e^{2st}f²/ω (with 0/0 := 0) is bounded and Riemann integrable. That is all the first-factor argument uses, and it includes g = f ≥ 0 literally.

**m6. X (3.57) for combinations is stated in X without proof; also a page reference.**
* **Where.** `04-detection.tex` 71–73.
* **Page.** (3.58) is on X p. 35, not p. 34.
* **Proof.** X explicitly gives no proofs in this section ("keine Beweise"; "vergleiche [23, Lemma 13.2]"). Prop. 4.4 rests on (3.57), so add the three-line justification:
  - (3.56) is linear in h.
  - In HB's proof of Lemma 13.2, the tail over the rectangles (13.1) with max(m, n) ≥ R uses |F((1−ρ)L)| ≪ e^{−(L−2K)m} n^{−2} and the density bound ≪ e^{3m}(1 + n/L)^{3/2}.
  - For h = Σ c_k h_{L_k,κ}, one has |H| ≤ Σ c_k |H_k| ≪ e^{−Am} n^{−2} with A > 3, so the same tail bound holds.
  - The zeros in the square are bounded by |Σ χ̄(a) H| ≤ Σ |H|.

**m7. Input 3.9: the cited source does not prove it.**
* **Where.** `03-inputs.tex` 148–155.
* **Problem.** HB §1 states "Principle 3" in the introduction as background attributed to Linnik, without proof or precise reference.
* **Fix.** Cite a proved statement, for example either of these:
  - Jutila 1977, Theorem 1: Σ_χ N(σ, T, χ) ≪_ε (qT)^{(2+ε)(1−σ)} for 4/5 ≤ σ ≤ 1, T ≥ 1, as quoted by HB in the proof of Lemma 6.1 and in §11. This suffices for 1 − σ = 3/L, T = 2.
  - Thorner–Zaman 2024 (explicit).

**m8. Remark 5.7: the stated H_2 violates X's condition (3.59).**
* **Where.** `05-costs.tex` 213–214: "for f_1 = f^θ_{λ_*}, M = 1 and H_2(z) = e^{Aλ_*}H(z)".
* **Problem.** With this H_2, condition (3.59) reads |Ψ(λ_*+it)|² ≤ |Ψ^θ(λ_*+it)|². That is false in general; it holds only up to 3θ.
* **Fix.** Take H_2(z) = Ψ^θ(z)², for which equality holds by Lemma 5.1(ii). Say that H is compared with (Ψ^θ)² separately, via Lemma 5.2(ii).

**m9. Cor. 8.8 compared with its formal counterpart.**
* **Where.** `08-near.tex` 318–320: "only the positivity of the D_j^+ is needed, not that of D(δ_j) − d_1 + e_j".
* **Problem.** This is true of the paper's proof. The Lean statements `builder_threshold` and `graded_near_threshold` (`lean-graded/Challenge.lean` 827–829) assume 0 < D(δ_j) − d_1 + e_j.
* **Fix.** Wherever §14 says the rows are verified through `builder_threshold`, state that the stronger positivity is what is checked. Otherwise weaken the Lean hypothesis to match Cor. 8.8.

**m10. Input 3.6 (X Lemma 3.10) has a second gap for M > 1.**
* **Where.** `03-inputs.tex` 110–115; `05-costs.tex` 217–220.
* **Problem.** Besides omitting f_{1i}(0) ≥ 0, the printed proof applies X Lemma 3.2 to each piece after restricting to the square (3.58). Lemma 3.2 bounds the sum over its disc, and the pieces' terms off the square need not be ≥ 0.
* **What is needed.** First enlarge Σ'_ρ Re F_1 to the disc sum for F_1. This is legitimate there because Re F_1 ≥ |H_2(λ + ·)| ≥ 0. Then use one common radius for all pieces.
* It is harmless for M = 1, but the description of the Input should mention it.

**m11. An inaccurate parenthetical.**
* **Where.** `05-costs.tex` 274–275: "(zeros of the disc with parameter above C_P are outside R(l) and irrelevant, ...)".
* **Problem.** A disc zero with C_P < λ_ρ ≤ (1/3) log log L lies in R(l). What is used is that such zeros have λ_ρ > C_P ≥ p, so Φ^θ_σ ≥ 0 for σ ∈ {a, p}.
* **Fix.** Reword to say exactly that.

**m12. Two slips in the proof of Cor. 8.8.**
* **Unused symbol.** `08-near.tex` 311: "writing D_n = D_u/(1+η'') so that (1+η'')I_B D_n = I_B D_u". D_n is never used; delete it.
* **Wrong clause.** `08-near.tex` 330: "(both are 0 when v'_j ≤ 0 ≤ τ)". Only (v'_j − τ)_+ vanishes. Write "(the former is 0 when v'_j ≤ 0 ≤ τ)".

**m13. The blanket claim about printed hypotheses.**
* **Where.** `03-inputs.tex` 7–8: "Every input is applied only under its printed hypotheses."
* **Problem.** Input 3.4 is applied on a smaller disc and uniformly in families. Both extensions come from HB's proofs and X's p. 36 remark, not from the printed statements.
* **Fix.** Write "... or under the extensions derived in the remarks after it".

**m14. Notation overloads that make checking hard.**
* **T.** The kernel length 0.416829, and the height bound in Theorem 8.3 (`08-near.tex` 64).
* **H.** The prime transform; the sieve weight H(t) (`08-near.tex` 19); the Burgess length (Input 3.7, Lemma 8.4); and H_2.
* **G.** G_φ = e^{−Aλ}B_φ, and the Gram transform.
* **h.** The prime weight; Ψ(λ)²/H_0; the triangles h_{L',K}; and the sieve heights h_k.
* **λ_d against λ_1.** "ν_k(p) = λ_1² = 1" (`08-near.tex` 160) reads as the first zero's parameter.
* **δ.** The disc radius; the offsets δ_j; and the levels δ_k. In Q_2, "e^{−2δ_j t_n}" (j an entry) and "D_k = q^{δ_k}" (k a cell) appear side by side (`08-near.tex` 154–175).
* **t_n against t_k.** For example, t_1 is ambiguous.
* **s.** The reference anchor, and the complex test point (`08-near.tex` 118, 126).
* **ε_1.** η/23 in §5, and a local tolerance in `08-near.tex` 104.
* **W.** The zero sum, and W(n) (`08-near.tex` 178).
* **B.** B_φ, and the bound B (`08-near.tex` 211).
* **D.** D(y) (`05-costs.tex` 312) and D(δ), D_k, D_j, D_u, D_n, D_j^+.
* **Λ.** Von Mangoldt, and Λ = C_P (`05-costs.tex` 84, 149).
* **\varphi.** Both Euler's φ(q) (Input 4.2, Prop. 4.4) and the conductor coefficient φ(χ).
* **p and a.** A prime and a residue class in §4; an anchor and a lower bound for λ_1 in §5.
* **η(δ).** In Input 3.10, against η = 10^{−6}.
* **M.** The separation; the number of triangles (Input 4.2); the number of pieces (Input 3.6); and M_0, M_1.
* **Suggestion.** Rename a few of these, for example T_ker, Γ for the Gram transform, H_sv, λ^{Sel}_d, u_k for the cell endpoints, and s_ref.

**m15. Small precision points.**
* **Lemma 5.4's proof.** `05-costs.tex` 169–170: the display omits the O(L/log L) error of Input 3.3. Apply Input 3.4 with ε/2 and absorb it.
* **Integrand convention.** `08-near.tex` 28: state that e^{2st}f²/ω := 0 where f = 0, since ω may vanish outside supp f.
* **Real characters.** `03-inputs.tex` 32: "φ(χ) = 1/4 for every real character" needs ord χ = 2 ≤ L, that is q ≥ 8.
* **Theorem 8.3's assumptions.** `08-near.tex` 62–63: the proof also uses Mertens' estimate and τ(q) ≪ q^ε. Both are classical, but list them.
