# Referee report E: consistency pass on the last round of edits

**Version reviewed.**
* Sources: `paper/linnik399.tex` and `sections/01`–`16`, last modified 04:19:39 UTC.
  * They were unchanged from 04:31 to 04:44. A snapshot is in `scratchpad/paper/snapE/`.
  * md5 prefixes: 05 `7e6389626e3d`, 07 `8ff6239f5f31`, 09 `87394d6a7855`, 11 `83d61259f4b2`.
* PDF: `linnik399.pdf`, built 04:19:57 from these sources. The log shows no undefined references and no
  multiply defined labels.
* Line numbers below refer to these files.

**Severity.**
* **BLOCKING**: threatens the theorem.
* **MAJOR**: a real gap in the written argument. The repair may be short, but it must be made.
* **MINOR**: wording, notation, or a local justification.

## Summary verdict

**No blocking error.** I re-derived each of the rewritten arguments and checked it against the rest of
the paper:
* §9: the strip lemma, `noright` at height 2l, entries (a)–(g), the two-test theorem, the paired
  proposition with (m′, D′), and `rowsvalid`;
* §11: the specification and sub-case sets C(𝔰, I), the realization's Value step, and the cover
  theorem;
* §7: the parent-row rule and the λ′-row domain;
* §4 and §13: the pointwise `prop:detect` and its use;
* §§5–6: the anchor set 𝒜, the least admissible T*, and the enlarged scope of `cor:ordinarycost`.

All of these are sound.

**One MAJOR item:** the disc radius δ₀ is fixed for the wrong tolerance.

**26 MINOR items** (item 25 below is a no-issue note). None changes a number or a certificate. They
are:
* a leftover symbol (ψ_d);
* two missing diagonal numerators;
* one false intermediate claim in entry (e);
* over- or under-stated sentences in §7 (the parent-row "largest" rule, and HB Table 4 row 0.3);
* notation clashes;
* provenance, since the new check scripts are not committed to git.

**Cross-references (d).** No wrong reference names remain.
* The aux file gives every label the correct type (`inp`, `lemma`, `proposition`, `corollary`,
  `definition`).
* In the PDF, "Theorem" appears only for Theorems 1.1, 8.3, 9.4, 10.7, 11.3, 11.6, 12.5 and 12.6.
* `\eqref{eq:X34}` prints as (7.2), `eq:pairB` as (9.1), and the (S1)–(S6) stages resolve.

## BLOCKING

None.

## MAJOR

**E-M1. δ₀ is fixed for tolerance H₀ε₁/4, but `lem:anchored` applies Input 3.4 with tolerance H₀ε₁/8.**
- **Where.**
  - `05-costs.tex:116-121`: "…the functions f^θ_σ (σ∈𝒜) with tolerance H₀ε₁/4…".
  - `05-costs.tex:172`: "Apply Input 3.4 … with tolerance H₀ε₁/8 and radius δ₀".
- **Why it matters.** Input 3.4 gives a radius δ(f, ε) that depends on ε. Knowing that the inequality
  holds on the δ₀-disc for tolerance H₀ε₁/4 does not give it for H₀ε₁/8. The proof needs the smaller
  tolerance to absorb the O(𝓛/log 𝓛) error from Input 3.3. This is exactly the quantifier chain that
  referee A (A2) asked to have fixed, and the new text leaves one link inconsistent.
- **Fix.** At line 119 write "with tolerance H₀ε₁/8". Optionally, write the same value into (S5)
  (`13-join.tex:30-33`) for the functions f^θ_σ.

## MINOR

### (b) Logic and justification in the rewritten proofs

1. **Entry (e) states a false intermediate claim.**
   - **Where.** `09-rows.tex:179-180`: "Otherwise the response bound r_j of Cor. 8.8 is negative".
   - **Problem.** When F(b−s) − C_Z < 0, the true
     r_j = m(F(λ₁−s) + Re F(λ₁−s+2iμ₁)) − f(0)/6 can still be positive. For example, F(λ₁−s) can be
     large when λ₁ = a < b.
   - **Why the conclusion survives.** Feature 0 is admissible for every entry by the last clause of
     Cor. 8.8: v′ = 0 ≤ max(v, 0), and v′ ≤ 0.
   - **Fix.** Replace the phrase with: "Otherwise the builder's bound F(b−s) − C_Z − f(0)/6 is negative
     and the entry receives feature 0. This is admissible for any value of r_j by the last clause of
     Cor. 8.8 (take v′_j = 0)."

2. **Entries (c) and (d) still lack diagonal numerators.**
   - **Where.** `09-rows.tex:140-147` and `148-166`. Entries (a), (b), (e), (f) and (g) now state
     theirs.
   - **Fix.** Add to both: "the diagonal numerator is D(0) − d₁ + (c^hi − d₁)_+".
   - For (d), the entries of χ₁ and of χ̄₁ are distinct characters, so they carry no mutual excess. Say
     so.

3. **Paired proposition: the heights claim misses the conjugate pair.**
   - **Where.** `09-rows.tex:343-346`: "at the heights γ₁−γ_k and γ′−γ_k, whose absolute values are at
     most l+1 ≤ 2l".
   - **Problem.** The term ⟨A_f, A_f̄⟩ is an average of four terms, at heights 2γ₁, γ₁+γ′ (twice) and 2γ′.
     |2γ′| can reach 2l > l+1.
   - **Why the conclusion survives.** All these heights are ≤ 2l, so `lem:noright` still applies. The
     quotient χ₁² equals χ̄₁ only for cubic χ₁, and that case is already paid by the c_G in D_f.
   - **Fix.** "…whose absolute values are at most 2l (at most l+1 against an ordinary or reserved
     entry, and at most 2l against the conjugate averaged vector)".

4. **Paired proposition: Input 3.9 is used beyond its stated scope.**
   - **Where.** `09-rows.tex:336-338`: "by Input 3.9 their number is bounded". ρ′ may have |γ′| up to l.
   - **The scope as stated.** `03-inputs.tex:164-166` says Input 3.9 is used only for zeros with
     |γ| ≤ 2.
   - **Why it is still true.** Take T = l ≤ 𝓛/10. Then (qT)^{(2+ε)·3/𝓛} ≪ 1.
   - **Fix.** Widen the scope sentence at `03-inputs.tex:164-166` to T = l, or add the half-line at
     09:337.

5. **`lem:noright` is stated for radius δ₀, but the two-test proof applies it to other discs.**
   - **Where.** The lemma is at `09-rows.tex:99-109`. The two-test proof applies it at `09:271-273` and
     `285-289`.
   - **Problem.** In that proof the discs are the Input 3.4 discs for f_{γ_Z}, g = f_{γ_G} and the
     mixtures f_ε. (S5) does not list these functions among those whose radius bounds δ₀.
   - **Why it is harmless.** The lemma's proof works verbatim for any radius δ ≤ 1, because
     2l + δ < 10l.
   - **Fix.** State `lem:noright` "for any disc radius δ ≤ 1 (in particular δ₀)".

6. **The Prop. 7.5 proof claims too much about how the entries arise.**
   - **Where.** `07-location.tex:143`: "Each entry is the largest of the following bounds".
   - **Counterexamples.** Several table entries are strictly weaker than the rules give:
     - rr, [.1,.2]: p_j = 2.293, while rule (iii), Input 7.2(b), gives 1.5·log(1/B_j) = 3.18, 2.95,
       2.75, 2.57, 2.41.
     - rr, [.85,1.5]: r_j = 0.8 < A_j (rule iv).
     - complex [.76,.78] and [.80,.82]: r_j = .74 and .78, below A_j.
   - These entries match `cover_v5.PARENTS`. They are valid, being weaker than valid bounds, and the
     table caption already says "or a weaker constant".
   - **Fix.** "Each entry is at most the largest of the following bounds".

7. **HB Table 4 side conditions: the claim "hold for every row" fails for row 0.3.**
   - **Where.** `07-location.tex:38-40`.
   - **Row 0.3, (8.8).** I recomputed from HB's printed (a, K) = (3.9, 0.89). HB (8.8) holds only for
     λ₁ ≥ 0.166 and fails at λ₁ = 0 by 0.18. So HB's Lemma 8.3 route does not give λ′ ≥ 2.293 on all of
     λ₁ ≤ 0.3.
   - **Why the parent rows are still sound.** Row (0.3, 2.293) is still true for λ₁ ≤ 0.3:
     - HB Table 3 (preprint p. 39) is stated for all 0 ≤ λ₁ ≤ b and gives λ₁ ≤ 0.30 ⇒ λ′ ≥ 2.43 − ε.
     - For λ₁ ≤ 0.2, HB Lemma 8.4 also gives λ′ ≥ 1.5·log 5 = 2.41.
   - **A caution.** Do not justify [0.2, 0.3] by HB's own (8.6) rule. At λ₁ = 0.3 with the Table 2/3
     value λ′(0.2) = 3.35, (8.6) fails by 7·10⁻⁴.
   - **Slacks.** The (8.6) slacks are 3.83·10⁻⁶ (row 1.05), 3.78·10⁻⁶ (row 1.15) and 2.34·10⁻⁶
     (row 1.294). "About 2·10⁻⁶" understates the first two.
   - **Fix.** Write "…hold for every row from 0.35 on (the smallest (8.6) slacks are 2.3·10⁻⁶ to
     3.8·10⁻⁶, at rows 1.294, 1.15 and 1.05); for λ₁ ≤ 0.3 the row (0.3, 2.293) also follows from HB
     Table 3 (λ₁ ≤ 0.30 ⇒ λ′ ≥ 2.43)". Add Table 3 to the citation of Input 7.2(a).

8. **λ′ rows: the p = a cells are attributed to the parent row.**
   - **Where.** `07-location.tex:509-514`: "p ≤ λ′ is the bound of the parent row … p = a on the cells
     beyond … since Prop. 7.5 gives λ′ ≥ p".
   - **Data check.** The values match `polynomial_table.json` `old_lower` exactly:
     - 0.96 on the 7 cells of [.68, .6975];
     - 0.93, 0.91, 0.89, 0.86, 0.84 and 0.83 on the successive intervals of width 0.02;
     - 0.827 on the 3 cells of [.82, .8275];
     - a on the 11 cells from .8275 on.
   - **Problem.** For the p = a cells the bound is the trivial λ′ ≥ λ₁ ≥ a, not Prop. 7.5.
   - **Fix.** Write "p = max(p_j, a) ≤ λ′ (Prop. 7.5 and λ′ ≥ λ₁)".

9. **Input 7.4(e) omits its side condition, and Prop. 7.16(5) does not cite the check.**
   - **Where.** Input 7.4(e) is at `07-location.tex:103-108`. The proof of Prop. 7.16 rule (5) is at
     `583-586`.
   - **Problem.**
     - Input (e) is stated unconditionally, while (d) carries its proviso.
     - The (4.34) condition appears only in the text after the Input.
     - Rule (4) cites the (4.29) verification; rule (5) does not cite the (4.34) verification.
   - **Fix.**
     - Add "provided that sup_t Re{F(−λ₂+it) − F(λ₁−λ₂+it) − F(it)} ≤ (5/48)f(0) on the box" to (e).
     - End the rule (5) proof with "the side condition (4.34) holds by our verification".
   - **Verification.** I reran `x434_check.check()` in memory (3.5 s, no files written) and reproduced
     every stored integer:
     - supremum_upper = 30941842902673 / 10¹⁶ = 0.0030942 ≤ 0.0031 (this is the tail bound);
     - permitted = 0.1351837.
   - The script's second-derivative constants, grid and tail formula match the paper's parenthesis at
     `07:121-123`.

10. **Props. 5.8 and 5.9 do not state that a, p ∈ 𝒜.**
    - **Where.** Hypotheses at `05-costs.tex:256-259` and `270-273`. The proofs apply `lem:anchored` at
      σ = a and σ = p (lines 290–291, 311–312), which requires σ ∈ 𝒜. Line 369 asserts "σ = p ∈ 𝒜"
      without a hypothesis to support it.
    - **Why it holds in use.** It holds for the anchors actually used (a, p*, p°). The data give
      p ≤ 2.293 and g⁻ ≤ 1.6, so these anchors also lie in [λ₁₁, C_P].
    - **Fix.** Add "with a, p ∈ 𝒜" to both hypotheses.

11. **The sub-case witness and the "fixed" ρ′ disagree.**
    - **Where.** §2 (`02-notation.tex:58-60`) and entry (d) (`09-rows.tex:149-150`: "fixed in §2") fix
      one ρ′. C(𝔰, I) (`11-casetree.tex:225-227`) quantifies over "some admissible choice … of ρ′".
    - **Problem.** For the second-zero split, the family row of piece I must use the ρ′ that witnesses
      |y| ∈ I, not a ρ′ fixed in advance.
    - **Fix.** Add in (d): "ρ′ is the zero for which the configuration lies in C(𝔰, I)". Or add in §2:
      "any such ρ′; in a sub-case, the one witnessing Q ∈ I".

12. **The "fixed terms" option contradicts the second-family equality.**
    - **Where.**
      - `11-casetree.tex:202-206` gives the fixed-terms option.
      - `10-lp.tex:27-28, 43` requires Σ E_c x_c = n₂S, with n₂ "the size of a reserved family".
      - The realization at `11:288-289` uses Σ z_j = n₂.
    - **Problem.** With fixed terms there are no E-columns, so the equality is infeasible as written.
    - **Code.** `graded_cert.Leaf` sets n2 = 0 when there are no columns.
    - **Corpus scan.** Every reserved leaf uses columns:
      - inside: 2195 reserved leaves;
      - outside: 1153 reserved leaves;
      - nodes: all reserved and split children.

      So there is no numerical consequence.
    - **Fix.** Either define n₂ as "the number of reserved characters carried by columns (0 for fixed
      terms)", or drop the fixed-terms alternative from the LP. It survives only as the two-test row's
      family term.

13. **`prop:rowsvalid` omits the hidden tail.**
    - **Where.** `09-rows.tex:406-407`: "the characters in the tail column are simply omitted".
    - **Fix.** Add "and in the hidden tail".

14. **Thm 12.6 does not state final = 5η.**
    - **Where.** `12-exteriors.tex:171-173`. "W ≤ 𝒱(x) − 2η as in Prop. 11.5" needs the allowance.
    - **Fix.** Add "final = 5η" to the list of data at 12:172. The data already have it:
      `large_branch_3.99.json` final = 5·10¹⁰.

### (a) Leftover or clashing symbols

15. **A leftover ψ_d.**
    - **Where.** `03-inputs.tex:135`: "The weights ψ_d in the next input". Input 3.8 now uses ξ_d.
    - **Fix.** Write "The weights ξ_d".

16. **Def. 6.4 and Thm 12.6 disagree on which representative is used.**
    - **Where.**
      - `06-far.tex:138-139`: after defining the T*-representative, "Representatives are used for the
        characters outside the first family, and also for all characters in Thm 12.6".
      - `12-exteriors.tex:168-169`: Thm 12.6 uses height-one representatives.
    - **Fix.** Write "…outside the first family; in Thm 12.6 all characters use height-one
      representatives".

17. **μ has two meanings in §9.**
    - **Where.** At `09-rows.tex:60, 65, 69`, μ is a row scaling parameter (μ = 10⁹).
    - **Problem.** In the same section μ is the normalized height: `09:144, 146, 174` ("Re F(x+2iμ)",
      "2iμ₁").
    - **Fix.** Rename the row parameter, for example μ_row or M_h.

18. **r_j and l_j have two meanings.**
    - **Where.** The reserved column is written [l_j, r_j] at `09-rows.tex:186-187` and
      `11-casetree.tex:205`.
    - **Problem.**
      - At 09:179 r_j is the response bound of Cor. 8.8.
      - At 11:95–105 r_j is the parent-row λ₂ bound.
      - l_j sits next to l and l₂.
    - **Fix.** Write the column as [σ_j⁻, σ_j⁺] or [ℓ_j, ℓ_j′].

19. **k has two meanings in §9.6.**
    - **Where.** `09-rows.tex:229` sets k = 1+η. The same proofs use k as an entry index
      (`09:285-294, 343`: "For j≠k", "⟨A_f, A_k⟩").
    - **Fix.** Rename the constant, for example k_η.

20. **The new names reuse overloaded letters.** This is not an error, and different sections are
    involved, but it partly defeats the purpose of the renaming.
    - ξ: ξ_d (Selberg, §§3, 8), ξ = v − μ (§10 Def. 10.5), ξ_i (grid points, §11).
    - ϑ: ϑ(z) (Lemma 5.3), angles (§7), ϑ_k (sieve levels, §§8–9), ϑ_ι (§10).
    - **Suggestion.** Rename the local ones in §10, for example ζ_v and ψ_ι.
    - Separately, `07-location.tex:24` says "Heath-Brown and Xylouris write λ₀".
      - HB writes λ′ (his §6, preprint p. 28, and Lemma 8.2).
      - Xylouris indexes the zero and its parameter by 0 (ρ⁰, λ⁰, p. 22).
      - Moreover, λ₀ = (1/3)log log 𝓛 in Inputs 6.1 and 12.4.

      Replace with "(Heath-Brown also writes λ′; Xylouris writes λ⁰)".

21. **Specification notation for reservations.**
    - **Where.** `11-casetree.tex:111` writes "res = ([u_j,u_{j+1}], n₂)", and `11:232` writes "the
      reservation ([r,h],1)".
    - **Problem.** Def. 11.1 defines res = (hi₂, n₂), with lo₂ = r.
    - **Fix.** Write res = (u_{j+1}, n₂) and res = (h, 1), (h, 2).

22. **"end" is undefined.**
    - **Where.** In the hidden columns at `11-casetree.tex:207-211`, and in `10-lp.tex:23` (used before
      §11).
    - **Fix.** Add "end = max(3, p°)" at 11:208.

23. **The tail definition differs between §6 and §11.**
    - **Where.** `06-far.tex:155-157` takes the tail over all characters with λ_χ ≥ R.
      `11-casetree.tex:199-201` takes it over χ ∈ O.
    - Both are valid, but make §6 say "χ ∈ O" as well.

### (c) Introduction and §15

24. **§15 does not match the §1.5 description of the limit.**
    - **Where.** `15-remarks.tex:6-7`: "the Gram barrier of a small number of characters just above the
      anchor".
    - **Problem.** "Gram barrier" is still undefined. §1.5 (`01-introduction.tex:270-273`) says the
      characters lie "just above λ₃" and describes the limit as D/(v²−d).
    - **Fix.** Write "…what remains is the limit, described in §1.5, of the Gram form on the few
      characters just above λ₃".

25. **No other inconsistency.** Abstract, §1 and §15 otherwise match the body:
    - the counts 4453 / 4788 / 4,196,879;
    - 0.9999998223…;
    - the formal-verification scope;
    - the notation ω = ge^{s₁t} + Ξ;
    - the cost function 𝒢;
    - the specification list;
    - 37 = 31 + 2 + 4 two-test rows;
    - "halving" in §15.

### (d) Cross-references

26. **Two pointers go to §10 instead of §11.5.**
    - **Where.** `05-costs.tex:388` ("the far weight w(t_χ) (Section 10)") and `05-costs.tex:391`
      ("described as follows (Section 10)").
    - **Problem.** The hidden columns and the leaf's description of the characters are in §11.5.
    - **Fix.** Use `\cref{subsec:leafmodel}` in both places.

### Provenance (§14)

27. **New check files are untracked, and one check has no recorded source.**
    - **Untracked in git.** At the time of this review, `git status` shows these as untracked:
      - `computations/core/code/x434_check.py`;
      - `computations/core/results/x434_condition.json`;
      - `computations/core/results/alias_condition.json`.

      `research/notes/paper-2026-09-30.md` says the latter "is now committed". "Data availability"
      (`14-verification.tex:152-156`) claims everything can be rerun from the repository.
    - **No script for HB Table 4.** The recomputation of HB Table 4 and Table 7 roots and of (8.6)/(8.8)
      (`07-location.tex:34-40`) has no script in the repository, and §14(1) (`14:52-54`) names only
      X (4.29) and (4.34).
    - **Fix.** Commit the three files. Either add the HB-table check (a few lines, floating point
      suffices at slack ≥ 2·10⁻⁶ on values ≈ 8·10⁻³) or say in §14 how it was done.

## Checks run (read-only)

* **x434.** `x434_check.check()` reproduces `x434_condition.json` exactly. The stored alias check gives
  0.003343 ≤ 0.00335.
* **λ′ rows.** `polynomial_table.json`: all 69 `additional` rows have `old_lower` equal to the p values
  stated at 07:510–512 (see item 8).
* **HB Table 4.** I computed (8.6) and (8.8) from the printed (t, λ′, a, K):
  - (8.6) min slack 2.34·10⁻⁶ (row 1.294), then 3.78·10⁻⁶ (1.15) and 3.83·10⁻⁶ (1.05);
  - (8.8) min slack 0.135 on rows 0.35–1.294;
  - row 0.3: (8.8) holds only for λ₁ ≥ 0.166.
* **Parent rows.** `cover_v5.PARENTS` reproduces Table 4 of the paper, including the entries that are
  weaker than rules (iii)–(iv).
* **Anchors.** `source_cover.json.gz` has max p = 2.293 and max g⁻ = 1.6, so p*, p° ≤ 2.293 < 3 ≤ C_P.
* **Reserved leaves.** Corpora scan: every reserved leaf, including split and reservation children,
  carries `second_columns`.
* **Labels.** In `linnik399.aux`, every cleveref type is correct.

## Verified correct (brief)

* **Lemma 9.2.** The proof at height 2l is correct; it uses 2l + δ₀ < 10l.
* **Lemma 9.3.** The zero lies in R(10l), hence in R(l), and is counted in K₀. The step to
  |Im ρ| ≥ T* + M/𝓛 is correct.
* **Entries (a), (b), (f), (g).** Anchors, kept sets and r are correct. The (d) multiplicity argument
  and the double-zero case (2F(λ₁−s₁) ≥ both r's, using λ₁ = λ′ ≤ g⁺) are correct.
* **Thm 9.4 (two-test).**
  - The Hilbert-space setup and the multiplicities are correct.
  - "Simple when λ₁ < s" is correct: a multiple ρ₁ gives λ₁ = λ′ ≥ p* ≥ s. For complex type the same
    holds if ρ̄₁ is also a zero of χ₁.
  - The partner count reproduces the D_o/D_f table: rr c_G/0; rc 2c_G/0; complex 2c_G/c_G. So does
    φ₁, φ₂ (n₂ = 1 ⇔ real).
* **Prop 9.6 (paired).**
  - A₁ ⊆ {ρ₁} is correct, and the use of (7.2) avoids the disc.
  - U ≥ 0 is correct.
  - The reduction to (m′ + U′, D′ + ζ*U′) is correct, with U′ = U + (m − m′).
  - The derivative (z+u)(2D′ − ζ*z + ζ*u)/(D′ + ζ*u)² is correct.
  - The corner-plus-interpolation bound for (9.1) is correct: separable, with h²/8 · ∫t²f e^{(s−a)₊t}
    and ∫t²f.
* **Prop 9.7.** The feature-0 columns argument is correct.
* **§4 and §13.** Prop 4.4 pointwise and its use in §13 (R1, R3, R4) are correct.
* **§5.**
  - The construction of 𝒜, and Prop 5.5 with its grid point σ ≤ λ*, are correct.
  - eq. (5.1) covers J_old: 3(N+2)θ.
  - It covers J_new: 3Nθ + 18θ.
* **§6.** Cor 5.7 for any character and Lemma 6.3 (least T*) are correct.
* **§11.**
  - (C1)–(C5) are correct, and C(𝔰) = ∪_I C(𝔰, I).
  - The Value step is correct: p° is admissible, and e^{−Aλ} and e^{−Aλ}/w are decreasing.
  - The count and drop rules are correct.
* **§10.** The renamed duals Y_F, Y_C, Y_N, Y_E^± agree between Def 10.6, the proof of Thm 10.7 and
  Thm 12.6.
* **§12.** Enlarging R in Input 12.2 is correct (−Σ′ only decreases), and Input 12.3 holds for any
  fixed R ≥ λ. The ϖ_i and 𝓜(u) derivations and the table arithmetic (ϖ₁, ϖ₂) are correct.
