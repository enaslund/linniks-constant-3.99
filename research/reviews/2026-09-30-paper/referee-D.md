# Referee report D: consistency, numbers, citations, readability

Paper: *Linnik's constant is at most 3.99* (`paper/linnik399.tex`, `sections/01`–`16`, `references.bib`).

Line numbers refer to the sources as of 2026-09-30, about 03:15 UTC. The files were being edited
while I worked. Two intro items I had noted were already fixed in the current text: the weight is
now written `ω = g e^{s1 t} + H` rather than `g_1 …`, and `d_1` and `e_j` are now glossed. Each item
below quotes the text so it can be found if the lines move.

Records I compared against:
* the verification, candidate and `lean_runs/*.json` files;
* `corpora/README.md`, `SHA256SUMS`, and the corpus files themselves (hashed and scanned);
* `config_v4.py` and `far_enclosures.py`;
* `existing_components_verified.json`;
* `numerics_check_3.99.json`;
* `polynomial_table.json`;
* `STATE.md`, `PROOF.md` (§6.6), the independent-checks note and the source-table audit;
* `sieve-majorant-near.md` (§§2g, 6e, 6h, 8);
* `lean-graded/README.md`;
* the deep-dive reports, `references-log.md`, and the literature texts in `scratchpad/lit/`.

## Summary

Almost every number in the abstract, introduction, §14 and §15 matches the records. This covers
the hashes, byte counts, roots, leaves, boxes, maxima, cases, forgeries, mutation count, row and
entry counts, timings, kernel and far-profile constants, exterior margins and the history table
(see "Checked and confirmed" at the end). The main problems are listed below.

1. **Abstract: wrong value.** It says "largest certified value 0.99999983". The recorded value is
   0.9999998223…, and the introduction and §14 print 0.99999982234….
2. **Introduction: number from a different program.** It says "the large-λ₁ program has value
   about 0.52 at L=3.95". That value belongs to an uncertified variant with added graded rows. The
   certified program has value 0.99465 at 3.99.
3. **§15: Xylouris misquoted.** "Doubling the constant in his (5.19)" should be "halving" (he
   means a bound twice as good).
4. **§9: two-test row counts.** The text says 32 single, 2 mixture and 4 paired rows, "one root
   uses both". The corpus has exactly 37 two-test rows, one per root. That matches the "37" used
   in §1, §14 and the Lean `rowcheck`. PROOF.md §6.6 gives 31 single, 4 paired and 2 mixture.
5. **§7 and Appendix A: coverage claim.** The 69 λ′ rows do not cover [0.68,0.855]; the cell
   [0.6975,0.70] is missing from both the table and the data. The note "(or 0.00125)" matches no
   row.
6. **Internal inconsistencies.**
   * §5 fixes ε₁=η/23 "in stage (S5)"; §13 uses it in (S3).
   * §13 points to the wrong subsection for δ₀.
   * The introduction uses δ₀ for the margin 2η, while δ₀ is a disc radius elsewhere.
   * §2 defines λ′ so that λ′=λ₁ always for type complex. §11 has the correct definition.
   * §5 refers to "the 4.33 argument of the present project"; everywhere else the earlier
     computation is at 4.30.
7. **Overstatements about formal verification.**
   * The abstract says "relative to the published inputs". The Lean leaf theorem also assumes
     the leaf's zero-level hypotheses (from the unformalized case tree), a derived envelope
     hypothesis, and the count-type integers.
   * "The data of every leaf": the numeric checker covers only G, W, F and first.
   * The Comparator and nanoda check covers only the 18 statements of the near lemma and the
     certificate checker.
   * "Each near row is a concrete instance" is false for the two-test rows.
8. **Reproducibility claim.** §14 says the independent checks "can each be rerun from" the
   repository. The independent certificate checker and the 38-leaf audit exist only in a session
   scratchpad; they are not in git.
9. **Citations to fix.**
   * Montgomery–Vaughan 1973 is cited under "sieve weights"; it is the Brun–Titchmarsh source.
   * Friedlander–Iwaniec 2023 is not "sieve methods alone": they use the classical zero-free
     region.
   * The small-modulus exponent attributed to Iwaniec 1974 is unverified (references-log, item 17).
   * Motohashi's "Lemma 3" is a large-sieve inequality; the multi-point statement is his Lemma 4.
   * Zhao is an unrefereed preprint, so "gives" should be "claims".
10. **Bibliography rendering in amsplain.**
    * arXiv identifiers are dropped, so 8 preprints have no locator.
    * MR numbers print as "MR MR188172".
    * A few notes render badly: "2012., pp.", "(Chinese), In Chinese.", capitalized "An …".
11. **No code.** There is no embedded code and no construct that runs code at compile time.

---

## 1. ERRORS (numbers, facts, attributions)

**E1. Abstract (`linnik399.tex:81`): "largest certified value $0.99999983<1$".**
* Records: `verification_3.99.json` has `maximum_numerator` 9999998223456687, which is
  0.9999998223…. The introduction (l.247) prints 0.99999982234… and §14 (l.57) prints
  0.9999998223….
* 0.99999983 is only an upper bound for the value.
* Fix: "largest certified value $0.9999998223\ldots<1$".

**E2. Intro l.276: "the large-$\lambda_1$ program has value about $0.52$ at $L=3.95$".**
* The certified program of Thm 12.6 uses one near row with s=s₁=3/2. Its value is 0.9946508 at
  L=3.99 (`existing_components_verified.json`).
* The figures .478 (3.99), .518 (3.95) and .572 (3.90) come from a different, floating-point
  program that adds graded rows at 1.9 and 2.3 (`sieve-majorant-near.md` §6e; STATE: ".52 at 3.95
  … with graded rows").
* As written, the reader compares 0.52 with 0.9947 and sees the value fall as L falls.
* Fix: "…and a variant of the large-λ₁ program with graded rows at 1.9 and 2.3 has floating value
  about 0.52 at L=3.95 (the certified one-row program has value 0.9947 at 3.99)."

**E3. §15 l.9–11: "doubling the constant in his (5.19) would lower his exponent to about 4.6".**
* Xylouris, p. 87: "eine Ungleichung mit doppelt so guter Konstante, nämlich cM²/(2c₁c₂²)
  anstelle von cM²/(c₁c₂²) in (5.19) … L = 4.6". This means the constant is halved, i.e. the
  bound is twice as strong.
* Fix: "halving the constant in his (5.19) (a far-density bound twice as strong)".

**E4. §9 l.335–336: "with a single test on $32$ of them, with a mixture on $2$, and in the paired
form on $4$ (one root uses both a single and a paired row)".**
* I scanned `inside.jsonl.gz`. It has exactly 37 rows of kind `old`, one per root.
  * The roots are 10, 11, 15–18, 20–36, 1198–1201, 1212–1215, 1218, 1219, 2603, 2608, 2613
    and 2633.
  * Root 2633 has one leaf with one `old` row.
  * In 1218 and 1219 the row sits in the lowest ninth of the reserved pair's 9-way split
    (`…/0/children1/children0`).
* This agrees with "the $37$ two-test rows" (intro l.342), "the $37$ inherited rows" (§14 l.110)
  and `rowcheck_inside` (13,565 − 13,528 = 37).
* If one root used two such rows there would be 38.
* PROOF.md §6.6 gives 31 single (rr 10, 11, 15–18, 20–36; complex 1198–1201, 1212–1215),
  4 paired (2603, 2608, 2613, 2633) and 2 mixture (1218, 1219).
* The "2633 single and pair" in deepdive-near comes from the 4.30 records, not from the 3.99 rows.
* Fix: check the regenerated rows; most likely the text should read "single on 31, mixture on 2,
  paired on 4".

**E5. §7 l.475–482 and Appendix A, Table 6.**
* The text says "There are $69$ rows of \cref{prop:polyrows}, on cells covering $[0.68,0.855]$".
* `polynomial_table.json` has 69 `additional` rows with cells [0.68,0.6975] ∪ [0.70,0.855].
  The cell [0.6975,0.70] is absent; covering the whole interval would need 70 cells of width
  0.0025. Appendix Table 6 likewise jumps from [.695,.6975] to [.7,.7025].
* This is not a proof gap, since the rows are optional updates and exclusions. The sentence is
  still false.
* Also, "each on a cell of width $0.0025$ (or $0.00125$)" (l.475): all 94 listed rows (25 + 69)
  have width 0.0025.
* Fix: "on 69 of the 70 cells of width 0.0025 in [0.68,0.855] (all except [0.6975,0.7])". Drop
  "(or 0.00125)", or say which rows it refers to.

**E6. Stage of ε₁ (`05-costs.tex:404`).**
* §5 says "We choose $\eps_1=\eta/23$ in stage (S5)".
* §13 (S3) (l.15–17) chooses θ "as in the proof of Prop 5.5 for $\eps_1=\eta/23$". So ε₁ must
  exist before (S3). Stage (S5) is for the tolerances of the published results.
* Fix: list ε₁=η/23 among the fixed data of (S1), or write "(S3)" in §5.

**E7. `13-join.tex:26`: "the radius $\delta_0$ of \cref{subsec:envelope}".**
* δ₀ is defined in §5.3, "A uniform zero count" (l.107–114), which has no label. §5.1 is "The
  envelope functions".
* Fix: label §5.3 and cite it.

**E8. §2 l.52–54: definition of λ′.**
* The text reads: "a further zero occurrence of $\chi_1$ or $\bchi_1$ in $R(l)$, other than
  $\rho_1$ (and other than $\overline{\rho_1}$ when $\chi_1$ is real and $\rho_1$ is not)".
* For type complex, ρ̄₁ as a zero of χ̄₁ has parameter λ₁ and is not excluded. As written,
  λ′=λ₁ always for that type.
* The definitions in §11 (l.19–23, "distinguished occurrences") and §7 (ρ′ taken among the zeros
  of χ₁) are correct.
* Fix: "other than the distinguished occurrences: ρ₁ as a zero of χ₁, and ρ̄₁ as a zero of χ₁
  (type rc) or of χ̄₁ (type complex)".

**E9. Intro l.142: "is at most $1-\delta_0$ for a fixed $\delta_0>0$".**
* Prop 4.4 needs W ≤ 1−2η, with ε=ηH₀ tied to η=10⁻⁶.
* δ₀ is the disc radius in §5.3, §9 and §13.
* Fix: "at most $1-2\eta$, where $\eta=10^{-6}$".

**E10. `05-costs.tex:265`: "This is the first-family bound of the $4.33$ argument of the present
project."**
* This refers to an internal file (`research/arguments/4.33.md`). Everywhere else the earlier
  computation is at L=4.30.
* Fix: delete the sentence, or write "It was used in the earlier computation at L=4.30 (§1)."

**E11. `12-exteriors.tex:105`: "as $\mathcal B_\phi$ decreases to $\phi K+K^2$ as $\lambda\to0$".**
* B_φ is decreasing in λ, so as λ→0 it increases to its supremum φK+K². Numerically,
  B_{1/4}(0.01)=0.07856 < B₁=0.0786854.
* Fix: "as $\mathcal B_\phi$ is decreasing in $\lambda$, with limit $\phi K+K^2$ as $\lambda\to0$".

**E12. `06-far.tex:137`: "The reserved second family (\cref{sec:location})".**
* The reserved family is defined in Def 11.1 (C4), not in §7.
* Fix: `\cref{def:specification}`.

**E13. §15 l.14–18: HB §16 items and citations.**
* The text reads: "…Brun–Titchmarsh bounds [Titchmarsh1930, Iwaniec1982, Maynard2013], and
  improved sieve weights in the density argument [MontgomeryVaughan1973large,
  FriedlanderIwaniec2023selberg]".
* Montgomery–Vaughan, "The large sieve" (1973), is the source of π(x;q,a) ≤ 2x/(φ(q)log(x/q)).
  That is exactly the form (16.1) used in HB's item 3, so it belongs with the Brun–Titchmarsh
  citations.
* HB item 7 (a continuous weight w in the §11 argument) is what Xylouris's Lemma 5.1 implements,
  and that lemma is used here (Input 6.1). Only item 6 (replacing b_n by b′_n) is unused.
* Fix: move MV1973 to the Brun–Titchmarsh list, and write "the modified sieve coefficients of his
  item 6".

**E14. Intro l.44: Iwaniec1974zeros cited for "much smaller exponents are known".**
* `references-log.md`, discrepancy 17: zbMATH describes only a zero-free region, and the Linnik
  exponent for Iwaniec 1974 was not verified.
* Fix: verify an exponent, or cite the paper as "zero-free regions for such moduli".

**E15. Intro l.40–41: "by sieve methods alone \cite{FriedlanderIwaniec2023sifting}".**
* Friedlander–Iwaniec (arXiv v1, p. 3) say "we do appeal to the classical zero-free region". What
  they dispense with is log-free density and repulsion.
* Fix: "by sieve methods, without log-free zero-density estimates or the Deuring–Heilbronn
  phenomenon".

**E16. Intro l.20–21: ThornerZaman2024refinements cited for "explicit unconditional estimates".**
* Confidence: medium; the log does not record the content.
* The Math. Z. paper proves a uniform, effective prime number theorem for progressions, with
  Linnik's bound as a corollary. It is not numerically explicit. Bennett–Martin–O'Bryant–
  Rechnitzer is the explicit one.
* Fix: "explicit [BMOR] and uniform [TZ] unconditional estimates".

**E17. Intro l.211–213: "Lemma~3 of Motohashi \cite{Motohashi1975density}, both of which use a
single anchor".**
* Motohashi's Lemma 3 is a Selberg-weighted large-sieve inequality over distinct characters. It
  has no evaluation point at all.
* The point-evaluation statement is his Lemma 4. There the points s_{j,k} may have different real
  parts, but the bound depends only on min σ_{j,k}.
* Fix: "Lemmas 3–4 of Motohashi, whose bounds depend only on the smallest real part", or similar.

**E18. Intro l.262: "the printed bounds place the second family close ($\lambda_2\ge0.73$–$0.79$
only)".**
* The printed bounds alone give λ₂ ≥ 0.702–0.79 on [0.64,0.80] (Table 4: .79, .74, .704, .702,
  .72, .74, .74, .78).
* The range 0.73–0.79 already includes the new rows of Prop 7.12 and the bound λ₂ ≥ λ₁.
* Fix: "the available lower bounds (printed, and those of §7) place …".

**E19. §14 (4), l.70–71: "for a random sample of $100$ roots every stored integer of the leaf
programs was recomputed".**
* `numerics_check_3.99.json` covers 117 roots (100 random plus 17 named), 154 leaves and 530,942
  integers.
* The fields are the per-column G, W, C, NH and E, and F, first and final. The near-row integers
  (d, D, v) are not included; they are the row checker's job.
* Four of the random roots have no leaf.
* Fix: "for 117 roots (100 chosen at random), all 530,942 column and budget integers of their 154
  leaves (objective, far, count, hidden-count and second-family coefficients, F, first and final)
  were recomputed from the metadata in 50-digit arithmetic and agree exactly".

**E20. §14 (4), l.66–69: "every constant of the leaf program ($19{,}616$ objective and far
coefficients, … all $120$ near rows)".**
* The note records 19,616 objective (G_i) and 19,616 far (W_i) checks.
* Count coefficients and "final" were not audited.
* The 120 rows are the family, shifted and graded rows; the two-test row constants "were not
  audited here".
* Fix: "19,616 objective and 19,616 far coefficients, the tail, hidden and second-family columns,
  F, first, and all 120 family, shifted and graded near rows".

**E21. §14 l.107–108: "The certificate checker and the numeric checker have Mathlib-free copies
that are proved equal to the verified ones".**
* Only the certificate checker has a copy proved equal to it (`Cert.checkLeaf_ofCore`).
* The numeric checker `LeafCheckCore.checkNum` and the row checker `RowCheckCore` are
  Mathlib-free themselves and are proved sound directly (`checkNum_sound`, `rowCheck_sound`).
* Fix the sentence to say this.

## 2. OVERSTATEMENTS

**O1. Abstract (`linnik399.tex:84–86`).**
* Text: "…the passage from a certified case to a prime are formally verified in the Lean proof
  assistant, relative to the published inputs."
* The Lean leaf theorem (`checked_leaf_rows_gives_prime`) also assumes:
  * the leaf's zero-level hypotheses, which come from the unformalized case tree and zero
    location;
  * a derived, unprinted hypothesis (`OrdinaryEnvelope`, i.e. Prop 5.5);
  * the count-type integers, as they stand.
* Also, "certified case" should be "certified leaf".
* Suggested text: "…are formally verified in Lean, assuming the published inputs, the localized
  envelope and the zero-level hypotheses of each leaf; the case analysis, zero location and
  exterior regimes are checked by computer but not formally."

**O2. §14 (c), l.94–97.** The same omission. Add "and the localized envelope (Prop 5.5), which
enters as a hypothesis".

**O3. "The data of every leaf".**
* Where it appears:
  * intro l.341–342: "the data of every leaf";
  * §14 l.108–109: "every leaf's data";
  * §14 l.71–72: "The formally verified numeric checker … covers all leaves".
* `MetaValid` constrains only G and W per column, F and first. The count, hidden-count and
  second-family coefficients, n_g, n₂ and final enter the Lean hypotheses as they stand
  (`lean-graded/README`, "What is not formalized"). They were recomputed only on the 117-root
  sample.
* Fix: "the objective, far and first-family data of every leaf". Also add to the "not formally
  verified" list: "the count-type integers of the leaf programs, recomputed in 50-digit arithmetic
  for 117 roots".

**O4. §14 l.81–83: "The statements of the main formal theorems have been checked against their
proofs with the Comparator tool … and the independent kernel nanoda."**
* The Comparator Challenge holds 18 statements: the near lemma and the certificate checker.
* `lean-graded/README`, Limits: "The leaf-level and near-row statements are not part of the
  Palomar Challenge". The run was local, without the sandbox.
* Fix: "The 18 statements of the near lemma and the certificate checker were checked with the
  Comparator tool, which replays their proofs in both the Lean kernel and the independent kernel
  nanoda. The leaf-level and near-row theorems were checked by the Lean kernel (and
  `leanchecker`)."

**O5. §14 (f), l.102: "each near row is a concrete instance of \cref{thm:graded}".**
* This is false for the 37 two-test rows; §9.6 says "It is not an instance of Theorem 8.3".
* Fix: "each graded, family and shifted near row".

**O6. §14, Data availability, l.136–137: "The replay, the independent checks and the formal
verification can each be rerun from it."**
* The independent-checks note says: "Their code is in the session scratchpad (`indep_check/`)".
  That covers the independent certificate checker (`icheck_core.py`, `full_run.py`) and the
  38-leaf mpmath audit. `git ls-files` shows neither.
* Fix: commit them, or narrow the sentence to the replay, the mutation test, the numerics check
  and the Lean checks.
* Also for reproducibility: pin a commit or tag (or a Zenodo DOI), and state the Lean toolchain
  and Mathlib version (`v4.35.0-rc3`). The replay report records no code hash (deepdive-casetree
  H3).

**O7. Abstract l.84 ("checked by two independent programs") and §14 (2), l.58–60.**
* The second checker rebuilds each leaf's integer data from the same regenerated input and
  `graded_leaves` rows as the replay (note §1, and "Limits: Leaf inputs"). Its independence
  concerns the certificate check only.
* Fix: add in §14 (2): "It takes the leaf data from the same generator; the leaf data are checked
  separately in (4) and §14.3."

**O8. §14 (3), l.64–65: the mutation test.**
* It ran on the 19 leaves of three inside roots (1671, 1320, 1416).
* The perturbations were 0.1% of six input kinds, +10⁻⁴ on the first-family charge, and removal
  of the 5η allowance.
* On non-tight leaves, rejection comes from the exact comparison with the stored maximum, not from
  a bound exceeding 1.
* Fix: "On the 19 leaves of three of the tightest inside roots, all 133 unfavourable
  perturbations … were rejected."

**O9. Intro l.105–107: "…all of which are effectively computable in principle".**
* The §13 Remark says: "We therefore expect $q_0$ and $C$ to be effectively computable, but we have
  not checked this input by input".
* Fix: "which we expect to be effectively computable (see the remark at the end of §13)".

**O10. §14 l.114: "The following are \emph{not} formally verified, and are proved in this paper by
hand:".**
* The published inputs are not proved in this paper.
* The exterior regimes and the location rows rely on interval computations.
* The assembly of §13 (order of choices and regimes) is missing from the list, as are the
  count-type integers (O3).
* Fix: split into "(i) the published inputs, quoted from the literature …" and "(ii) the
  following, proved here by hand or by interval computation: …", and add the assembly of §13.

**O11. §15 l.27–29: Zhao "gives the exponent $5$".** This is an unrefereed preprint
(arXiv:2511.05631). Fix: "claims the exponent 5 in a recent preprint". "Independent" is also
unclear; say "A different recent approach".

**O12. Intro l.295–296: Xylouris "would give about $4.96$".** He writes "vermuten wir, dass wir …
L = 4.96 beweisen könnten". Fix: "conjectures that his method … could give about 4.96".

**O13. Intro l.263–268: "On a typical hard leaf …".**
* Leaf 1230/0 is one of the three hardest, not typical.
* The cost split (0.433 / 0.18 / 0.28) is a floating-point decomposition whose only record is
  STATE.md. It appears before the sentence that labels the floating measurements.
* The three parts total 0.893; the rest of the leaf's value is not accounted for.
* Fix: "On one of the hardest leaves … in floating point, …; the remaining characters account for
  the rest."

**O14. Abstract l.79–80: "Every leaf is certified by exact integer dual certificates over a
bisection of the space of thresholds".**
* Some relaxation cases, and whole second-zero pieces, are closed by exclusions.
* The splits are at arbitrary integer ticks, not at midpoints.
* Fix: "…by exact integer dual certificates (or exclusions) over a subdivision of the threshold
  box". The same applies to intro l.222, "A certificate bisects this box".

**O15. Repository status versus the paper (process note).**
* `research/STATE.md` still says "no exponent below Xylouris's published 5 is established here as
  a theorem" and "No human expert has refereed the argument". `candidate_3.99.json` says "Not a
  theorem; not formalized".
* AGENTS.md asks that claims stay tied to their scope.
* Either update STATE.md, if the frontier has changed, or say in §1.8 or §14 that the new hand
  proofs and the inherited location rows have so far been checked only by AI-assisted reviews.

## 3. CONSISTENCY

**C1. Names for the 233 nodes.**
* They are called:
  * "leaves of one kind and $233$ of another" (§11 l.156–158);
  * "five roots of the second kind of leaf" (§11 l.237);
  * "the auxiliary nodes of the earlier tree" (§14 l.38–39, 44);
  * "identities nodes" in the repository.
* Intro l.242–243 says "We reuse its internal nodes unchanged … and replace every leaf". But the
  233 were terminal nodes closed by a different argument, and they are replaced too.
* Fix: define the term once in §11, e.g. "auxiliary nodes: terminal nodes of the earlier tree
  that were closed by another argument; here each is replaced by a leaf program". Use it
  everywhere. In §1, write "replace each of its terminal nodes (2,913 + 1,642 LP leaves and 233
  auxiliary nodes)".

**C2. "roots" means two things in §11.**
* Step (2), l.101, says "giving $340$ roots", and step (3) says "The roots are tiled by $478$
  first-zero cells".
* The case tree itself has 4453 roots (l.89–91, §14).
* Fix: call the 340 objects "base cells".

**C3. "case" means two things.**
* A configuration class: intro l.214 "(a \emph{case})", abstract "root cases", §11 "gap cases",
  "sub-case".
* A relaxation case vector ι: Def 10.6 and §14 l.60, "$29{,}397{,}336$ cases".
* Fix: "relaxation cases" in §10 and §14.

**C4. "first" means two things.**
* (5.1), l.392–393: "first … is the sum of the hidden-column values … for an outside leaf".
* §11 l.212–214: first is "$0$ for an outside leaf"; the hidden columns carry those values in G_c.
* Fix: in (5.1) write `first` only for inside leaves, and add "(for an outside leaf these values
  are carried by the hidden columns of §11.5)".

**C5. The error bound (05-costs l.405).**
* The text says "then $E\le3\eta$".
* With ε₁=η/23, E2 + E4 ≤ (19 + 4)ε₁ = η and E3 ≤ η, so E ≤ 2η. The bound 3η is valid, but the
  spare η is unexplained; with 2η one gets W ≤ V − 3η.
* Fix: "then $E\le2\eta<3\eta$", or say what the extra η is kept for.

**C6. Notation reused for different things.** Most important first; I suggest renaming at least
the first six.
* λ_d (Selberg weights) versus the first-zero parameter λ₁: `08-near.tex:159`,
  "$\nu_k(p)=\lambda_1^2=1$". Use ψ_d, as in Input 3.7, or ϑ_d.
* δ_j (entry offsets) and δ_k (sieve parameters) occur in the same formulas (§8 l.26–30,
  173–175, 205), e.g. $e^{-2\delta_jt_k}(t_{k+1}^2-t_k^2)/(2\delta_k)$.
* T: the kernel width 0.416829 (§1, §4); the height bound in Thm 8.3 ("Let $0\le T\le\LL/3$",
  l.64); also T in Input 3.9, T_S and T*.
* H: the transform of h (§1 l.136, §4); the sieve step function H(t) (§1 l.203, §8); the interval
  length in Input 3.6; H(u) in §12.
* G: the cost G=G_{1/3} (§5; "objective $G(x_i)$" in §11) versus the transform G of the Gram test
  g (§8–9, e.g. "$\Re G(-s_1+iy)$").
* M: the separation constant; the dual M in Def 10.6; the number of triangles (Input 4.2); the
  number of pieces (Input 3.6); M in Prop 7.13; M(u) in §12.
* R_B: the buffer (§2) versus $R_B=\int f^2e^{st}/g$ in the two-test row (§9.6 l.213).
* C_c: the count coefficient of column c (§10) versus C_c(d) of Lemma 9.1(v).
* σ: a specification (§9.3, §11) versus an anchor σ (Lemmas 9.2–9.3, same subsection).
* τ: thresholds (§10) versus the type τ ∈ {rr, rc, complex} (Def 11.1).
* κ: T/16 (§4); κ and κ₂ in §9.6; κ_k in §9.2; κ_* in Prop 9.6.
* V: the far constant, the dual V, and Graham's level V.
* F: the far budget, the transforms, and the families F ≠ F₁.
* h: the prime weight, h(λ), the heights h_k, the height class h, the bound h for λ₂, and h in
  Lemma 10.3.

**C7. `06-far.tex:152–153`: "$R=\max(3,r_0)$ … $r_0$ is the leaf's lower bound".** §11 writes
R=max(3,r). Use r in both places.

**C8. Thm 11.3 (l.117): "$0.1\le\lambda_1\le1.5$".** Everywhere else the middle range is
0.1≤λ₁<1.5. This is harmless, but unify.

**C9. Intro l.239–241: "The tree has three kinds of internal node. … \emph{Leaves} carry a
certificate."** Leaves are not internal nodes. Fix: "two kinds of internal node (splits; location
and exclusion nodes), and leaves, which carry certificates".

**C10. Intro l.231–237, the list of specification data.**
* It says "lower bounds for the parameters $\lambda_2,\lambda_3$".
* Def 11.1 stores l₂ (for λ₂) and r (for the height-one parameters of the other families). The
  λ₃ bound is computed (Prop 7.16), not stored. The height class is missing from the list.
* Fix the list to match Def 11.1.

**C11. Lemma 7.15 (`lem:updates`, §7 l.~504–516).**
* It uses C(σ), l₂, r, lo₂, hi₂, g^±, p and ν(F), all defined only in Def 11.1, with no pointer.
* It is never cited; §11 ("Location update") restates it.
* Fix: move it to §11, or add "(Definition 11.1)".

**C12. The disc radius is described three ways.**
* §3 l.80–82: "so $\delta\le1/6$ … We may and do assume $\delta<1/2$".
* §5.3: "$\delta_0\in(0,\frac13]$".
* §13: "every admissible radius".
* Fix: state the constraint once and refer to it.

**C13. Organization (intro l.346–362).** It omits §15 and Appendix A.

**C14. "(4.29)" is ambiguous.** It appears at `14-verification.tex:53` and `07-location.tex:552`.
The paper's own equations in §4 are numbered (4.1)–(4.3), so a reader may look there. Write
"[X, (4.29)]" every time.

**C15. Repository jargon in §6.**
* l.87: "the one recorded in its source".
* The names "inherited" and "retuned" profile.
* Fix: e.g. "the profile of the earlier computation" and "a re-optimized profile"; "each leaf uses
  the profile with which it was built".

**C16. §10 l.27: "counts $n_g$ and $n_2$".** n_g is never defined; §11 (d) says "The hidden count
is at most $n$". State n_g = n.

**C17. Abstract "root cases" versus §11 "root specifications" / "roots".** Pick one term.

**C18. The Graham citation (intro l.211–212).** It reads "which go back to Graham
\cite{Graham1978asymptotic}". HB §11 attributes the sieve-weighted density estimate to Graham's
Linnik work (his refs [9] and [11]); the 1978 paper is the sieve asymptotic used as Input 3.7.
Cite Graham1981linnik (and the thesis) here.

## 4. READABILITY

**R1. "Gram barrier" is undefined** (intro l.263; §15 l.6). Suggested rewrite of intro
l.261–263:

> "…which forces the near rows to be anchored low. After a second family is reserved and the
> third-family bound is applied, a few characters remain just above λ₃, and a single
> Cauchy–Schwarz row cannot rule out fewer than about F(−s)²/r² characters of response r (the
> Bessel limit of the Gram form). This limit binds."

**R2. "shift of the near rows" (intro l.262)** is defined only in §11. Replace it as in R1.

**R3. "a count rule" (intro l.219)** is undefined. Gloss it: "(at most two characters outside the
first family lie below λ₃)".

**R4. Intro l.51–53.** The text reads: "Chen, Jutila, Graham and Wang lowered them in a long
series of papers, among them the introduction of sieve weights …". Rewrite as: "…in a long series
of papers, which includes Graham's introduction of Selberg sieve weights into zero-density
estimates".

**R5. §2 l.33–34.**
* "heights of zeros in $R(l)$ are physical heights $|\gamma|\le l$" should read "zeros in $R(l)$
  have physical height $|\gamma|\le l$".
* The "height-one region" is given in physical, not normalized, coordinates, so "described in the
  normalized coordinates" does not apply to it.

**R6. §5 l.265, "of the present project"; §9.6 "inherited".** These are repository terms. Say
"from the earlier computation at L=4.30".

**R7. §14's structure.** Items (1)–(4) mix certificate checks with leaf-data checks. A
two-column summary ("what is checked" / "by what") would make O3 and O7 visible at a glance.

**R8. MSC.** Consider adding 68V15 (theorem proving and formal verification) and 90C05 (linear
programming) as secondary classes.

**R9. Code check.** I found:
* no embedded code;
* no `\write18`, `\directlua`, `minted`, `pythontex`, `\immediate\write` or shell escape;
* no code file names.

The only file names are the three data files in §14 (`inside.jsonl.gz` and the other two), which
is fine. The repository URL is mentioned only in "Data availability".

### Bibliography as rendered by amsplain

**B1. arXiv identifiers are dropped.** amsplain ignores `eprint`, `archivePrefix`, `url` and
`doi`.
* These entries render as "Title, 2025." with no locator:
  * ChenGuptaLi2025large;
  * Helfgott2015ternary;
  * Kerr2019moments;
  * MatomakiMerikoskiTeravainen2024primes;
  * Meng2010note;
  * Pintz2018new;
  * Zhao2025exceptional.
* Xylouris2009linnik lacks arXiv:0906.2749.
* mpmath2023library has only a `url`, so it renders with no locator either.
* Fix: add `note = {arXiv:2507.08296}` and so on (or use `howpublished`), and
  `howpublished = {\url{https://mpmath.org/}}`.

**B2. "MR MR188172".** The `mrnumber` fields include the prefix "MR", and amsplain's `\MR` adds
another.
* Affected entries: Chen 1965, 1977, 1979; Chen–Liu III, IV; Graham thesis; Jutila 1970, 1972;
  Linnik I, II; Pan 1957; Rodosskiĭ; Selberg 1947; Tatuzawa; Tenenbaum; Turán 1961, 1971; Wang
  1986; Weil.
* Fix: `mrnumber = {188172}`.

**B3. Dirichlet1889beweis.** It renders "Reimer, Berlin, 1889, Reissued by Cambridge University
Press, 2012., pp. 313–342." Remove the final "." in the note (or drop the note).

**B4. Pan1958least.** It renders "(1958), 3–36 (Chinese), In Chinese. Issue no. 1 of 1958." Use
`number = {1}` and drop the note.

**B5. Carneiro et al. 2025.** It renders "Math. Comp. (2025), Published electronically 2025-12-02;
volume and pages not yet assigned." Rewrite as "Math. Comp., to appear (published electronically 2
December 2025), doi:10.1090/mcom/4154".

**B6. Notes capitalized after a comma.**
* Bailey2020nanoda: ", An external type checker for Lean 4."
* LeanFRO2025comparator: ", A trustworthy judge for Lean proofs."
* Xylouris2011nullstellen: ", Also Bonner Mathematische Schriften 404."
* Turan1984new: ", A Wiley-Interscience Publication."
* Fix: lowercase or drop these notes. For Xylouris, use `series`/`number` for Bonner Math.
  Schriften 404.

**B7. Stray address fields.** "(Cham)", "(Berlin)" and "(Providence, RI)" appear in odd places in
deMouraUllrich2021lean, SolovyevHales2011efficient and Turan1971recent. Turan1971recent also
prints "Proc. Sympos. Pure Math." twice. Clean up `booktitle` and `address`.

**B8. Weil1952formules.** It renders "\textbf{1952} (1952), no. Tome Supplémentaire, 252–265".
Rewrite as "Tome supplémentaire (1952), 252–265".

**B9. Inconsistent author names.** These break alphabetical order and `\bysame`.
* Friedlander–Iwaniec appears as "J. B. Friedlander and H. Iwaniec", "John Friedlander and Henryk
  Iwaniec" and "John B. Friedlander and Henryk Iwaniec". As a result the 2023 Acta paper sorts
  before the 2010 book.
* Other pairs: "S. Graham" / "Sidney West Graham"; "H. Iwaniec" / "Henryk Iwaniec"; "Y. Motohashi"
  / "Yoichi Motohashi"; "J. Pintz" / "Janos" / "János"; "P. Turán" / "Paul Turán"; "Dave Platt" /
  "David J. Platt"; "H. L. Montgomery and R. C. Vaughan" / "Hugh L. … Robert C. …".
* Fix: normalize the names.

**B10. Minor.**
* Sion1958general is in `references.bib` but not cited (harmless).
* BibTeX warns about missing pages for Carneiro et al., Jutila1970new and Jutila1972density; the
  last two print "8 pp."/"13 pp.", which is acceptable.
* The verification-URL notes mentioned in `references-log.md` have been removed.

---

## 5. Checked and confirmed (no action needed)

**Data files.** The SHA-256 hashes and byte sizes of all three corpora (`inside` 298,536,973,
`nodes` 159,624,716, `outside` 8,626,435) match `SHA256SUMS`, and I recomputed them from the files
on disk.

**Counts and maxima.**
* Roots: 4453 = 2768 + 1685.
* Leaves: 4788 = 2913 + 233 + 1642.
* Boxes: 3,067,092 + 1,042,363 + 87,424 = 4,196,879 ("about 4.2 million").
* Maxima: inside 9999998223456687 (node root 2432); outside 9999942478462508.
* Replay time: 6159 s ≈ 1.7 h.
* Certificate trees: 5591 = 3949 + 1642.

**Independent checker.**
* Cases: 29,397,336 = 19,123,142 + 9,953,103 + 321,091.
* Exact maxima at most 9·10⁻¹⁶ below the stored ones.
* 17 of 18 forgeries rejected; the accepted one is also rejected by `graded_cert`.

**Other checks.** Mutation test: 133 trials. Constants audit: 38 leaves, 120 rows.

**Lean.**
* Rows: 16,842 = 3,314 + 13,528, with 11,135,323 = 2,021,521 + 9,113,802 entries; 37 rows
  unchecked.
* Kernel-checked: 6 certificates, 122 boxes.
* Compiled checks: 17,342 s ≈ 4.8 h ("about 5 hours").
* Size: 23,946 lines, which includes 3,612 generated sample lines and the 989-line Challenge;
  about 19,300 lines are handwritten. There are 826–844 theorem and lemma declarations. Only the
  three standard axioms are used.

**Kernel and far profiles.**
* Kernel: the 16 values β_i match `config_v4.py`; T=0.416829; A=3.156342; 3+2T=3.833658;
  Ψ(0)=0.1936422928; H₀=0.0374973376.
* Far profiles: c₁, c₂, θ and ε₀=10⁻⁷ match, and so do all 20 α_i (the inherited α₁₀ is
  1−Σ = 0.1201979632).
* V = 175.2664033… and 243.3209810…; x = 1.1736847 and 1.1303336; w(0) = 10.70548 and 13.17302.
* K_far = 16.372 and 18.471, so K_far < 16.38 and < 18.48 hold, and "< 19" is justified.

**Exteriors.**
* Small branch: K=0.1821, c₁=0.057, c₂=0.1554, a_d=3724/1875, b_d=671/750, V_d=184750/6993,
  m*=2.7530442, and the margin 236171/327000.
* The P₁ and P₂ table matches exactly: M, other, first and μ_i.
* Margins are 28% and 36%.
* Large branch: 0.9946508085154141; 36 intervals; 5436 column inequalities;
  Y=5139815868, Z=1622818786878; interval [0.1625,0.165].

**History and literature.**
* The history table (values, years, authors) agrees with `references-log.md` (zbMATH reviews,
  Xylouris 2011 Table 1). The 1970/1971 order and the Graham/Chen note are fine.
* The Heath-Brown quote from §16 item 9 is verbatim.
* HB Lemma 12.1 loses to Lemma 11.1 as soon as λ ≥ 1.1 (Table 13).
* Xylouris 2018, p. 82: 4.96 and Maple. Xylouris 2011, p. 87: the remarks cited in §15 (apart from
  E3).
* HB 1990, Corollary 1 (q^{3+δ}, effective) and Corollary 2 (q^{2+δ}, ineffective).
* The HB Lemma 5.2 misprint (Λ(n) missing).
* The HB remark that cube-free moduli improve everything, and Lemma 2.1 for any k.
* Chang (12/5), Meng (4.5), FI (75,744,000) and MMT (350) agree with "much larger/smaller
  exponents".

**Case tree.** 340/478/684/2768; 1083/115/1570; 195/444/444; the node table (1/408/593, 225/75,
11/0, 352/70, 197); 343 and 70 empty roots. All agree with the independent census in
deepdive-casetree. The graded anchors 1.5, 1.6, 1.9, 2.1 and 2.3 are within s_max=3.

**Floating-point measurements.**
* 382 leaves: median 0.917, 99th percentile 0.979, maximum 1.026.
* 0.992 at 3.97 and 1.020 at 3.95 (leaf 1244/0, with columns).
* The small branch stays positive to about 3.90.
* Leaf 1230's spec: complex, [0.6625,0.665], n₂=2, [0.81,0.88].

**Location rows.**
* The 25 λ₂ rows are contiguous on [0.66,0.7225], with conclusions 0.763 → 0.725, margins
  ≥ 8.2·10⁻⁴ and alias margins ≥ 0.163.
* The 22 degree-5 rows cover [0.700,0.755].
* The λ′ margins are ≥ 1.5·10⁻³.

**Cross-references.** All `\cref`/`\ref` targets resolve, with no undefined references or
citations. Apart from the exceptions in E7, E12 and C11 they point to the intended object.

**Constants across sections.** These agree between §§2, 4, 6, 9 and 13:
* η = η′ = 10⁻⁶ and S = 10¹⁶;
* λ₁₁ = 0.05 and s_max = 3;
* K₀ counts zeros with |γ| ≤ 2;
* C_P ≥ max(C₀(ηH₀), 3) and C_B > max(C_P+M, 1.5);
* T* ∈ [1/2, 1];
* final = 5η and u₀ = min(1/η(1/2), 0.08).

The exceptions are E6 (the stage of ε₁), E9 (δ₀) and C5 (3η).
