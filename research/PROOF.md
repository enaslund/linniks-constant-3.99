# The graded-near proof

2026-09-27; revised 2026-09-29. This document gives the whole argument in its
simplified form. It replaces most of the near-density machinery of the 4.30
candidate with one lemma, the **graded near lemma** (§6). The 4.30
candidate's own two-test near row is kept only as a fallback row, on inside
leaves where the graded rows alone do not certify (§6.6). Everything else is
either a published input or a repository deduction that the 4.30 candidate
already used.

> **2026-09-30: the argument is now written up as a paper,
> [`paper/linnik399.tex`](../paper/linnik399.tex).** Writing it closed several
> gaps in this document's reasoning, none of which changes a certificate. They
> are listed in [notes/paper-2026-09-30.md](notes/paper-2026-09-30.md). Among
> them are a proof of the 1/108 conductor saving, the order of constants, the
> paired row for rounded data, and the prior bound behind the λ′ rows. Where
> this document and the paper differ, the paper is the corrected statement.

**The new ingredient.** The graded near lemma is a *weighted* near-density
inequality. The zero of each character enters one Selberg-sieve-weighted Gram
form, each with its own anchor, so crowds of zeros at different distances from
`σ=1` are charged at their own rates. Heath-Brown identified exactly such an
inequality as desirable and did not find one. In the list of possible
improvements closing his paper he writes (H §16, item 9):

> It would be nice to have a weighted version of Lemma 12.1, in the way that
> (11.4) is a weighted version of (11.5). Unfortunately, no neat way of
> achieving this seems available.

A literature search in September 2026 found no earlier inequality of this
kind
(notes/literature-2026-09-28 §2). It covered
Heath-Brown, Graham, Jutila, Motohashi, Bombieri, Gallagher, Maynard,
Thorner–Zaman and Soundararajan–Thorner. The closest precedents are the
sieve-weighted Gram forms of Heath-Brown's §11 (after Graham) and Motohashi's
1975 Lemma 3, both with a mollified detector.

This lemma is where the gain over the published exponent 5 and over the 4.30
route comes from. It is also the part of the argument that no one outside
this project has checked.

**Status (2026-09-29).**
* **The finite part at `L=3.99` is complete and verified.** Every case of the
  4.30 source tree has an exact certificate at 3.99:
  * 2,768 inside roots, with 3,146 leaves including all 233 identities nodes;
  * 1,685 outside roots, with 1,642 leaves;
  * about 4.2 million threshold boxes, with maximum `.99999982<1`;
  * both exterior regimes.

  A full replay regenerates every leaf from the 4.30 trees and passes
  (`computations/graded/verification_3.99.json`). An independent checker
  written from §7 alone verifies every certificate. The assembled record is
  `computations/graded/candidate_3.99.json`.
* **The step from these certificates to the theorem uses the analytic
  premises of §11.** These are of three kinds:
  * printed theorems, checked against the pages;
  * deductions inherited from the 4.30 route;
  * the new deductions of this proof, which have had two to four independent
    reviews each.

  All reviews so far were done by AI agents. No human expert has refereed
  the argument. These parts are formalized in Lean
  ([lean-graded](../README.md)):
  * the graded near lemma with its zero form (§§6.2–6.5), from four printed
    inputs;
  * the soundness of the certificate checker (§7), whose native copy is
    proved equal to it;
  * the leaf level (§§2–4, 7):
    * prime extraction from (3.57);
    * the far budget from X Lemma 5.1;
    * the enclosures of the column data;
    * the theorem that a checked leaf gives primes under its zero-level
      hypotheses.

  The rest is not formalized: the case tree, zero location, the count-type
  and near-row integers, and §9. So `L=3.99` follows **if the §11 premises
  hold**. It is not yet an established theorem.
* Evidence and review records are in STATE and
  LOG.

The target statement is the usual one. There are an exponent `L` and a constant
`C` such that every reduced residue class `a mod q` contains a prime
`p ≤ C q^L`, here with `L=3.99`. Every component below is stated for a
general `L` at which its certificate exists.

## 0. Architecture

| Component | Content | Section |
| --- | --- | --- |
| Prime detection | 16-step kernel, Xylouris's (3.57) positivity criterion | §2 |
| Zero costs | Per-character all-zero envelope; first and reserved second family bounds | §3 |
| Far density | Xylouris Lemma 5.1 with a weight profile; one representative per character | §4 |
| Zero location | Source cover of first-zero cells, λ′/λ₂/λ₃ bounds, exclusions | §5 |
| **Graded near lemma** | The main near-density inequality; every near row except the inherited fallback row is an instance | §6 |
| Inherited two-test row | The 4.30 candidate's near row, used only where the graded rows fail | §6.6 |
| Leaf LPs and certificates | Bins, rows, threshold boxes, exact integer duals | §7 |
| Case tree, exteriors, join | Finite cover of all zero configurations; uniform `q₀` | §§8–10 |

The 4.30 candidate used several near-density models, each with its own
analytic premises:
* the two-test near row with detector mixtures and paired tests;
* the collective envelope;
* the outside first-block relaxation;
* the separated hidden-family blocks with their identity branches.

The last three are removed here. The two-test near row is kept as a fallback
row (§6.6). The 3.99 cover showed that some unreserved cells need it (35
roots so far, of types `rr` and complex), and so does the hardest reserved
pair of roots 1218–1219. Every other near
constraint is an instance of §6. Section 12 lists what was removed and why
the remaining structure does not need it.

## 1. Notation

`q` is the modulus and `ℓ=log q`. A zero `ρ` of `L(s,χ)` is written
`ρ=1-λ/ℓ+iμ/ℓ`, so `λ` is its normalized distance from `Re s=1` and `μ` its
normalized height. Zeros are counted with multiplicity. `χ₀` is the principal
character, and all characters below are mod `q`.

Several regions of zeros occur.
* **Global.** Xylouris's enlarged rectangle
  `R(x)={1-loglogℓ/(3ℓ)≤σ≤1, |t|≤x}` (X (3.7)) with `x=l`. Here `l=l(q)` is
  an integer with `1≤l≤ℓ/10`, and X Lemma 3.3 says that no zero lies in
  `R(10l)\R(l)`. Heights in `R(l)` are **physical** heights `|t|≤l`.
* **Physical height one.** `|Im ρ|≤1`. This is the region of the far lemma.
* **Prime window** `R_P={λ≤C_P,|μ|≤C_P}`. Only zeros here enter the prime
  objective.
* **Buffer** `R_B={λ≤C_B,|μ|≤C_B}`, with `C_B>C_P+M`.

`C_P`, `M` and `C_B` are fixed constants, chosen in the order of §10.

**Families.** A family is a character together with its conjugate. The global
family parameters `λ₁≤λ₂≤λ₃` are the successive minima of `λ` over zeros in
`R(l)`, where each family is removed whole before the next minimum is taken
(X §3.1.2). `χ₁` is the first character, and `ρ₁` its zero with `λ=λ₁`. `λ′` is
the least parameter of another zero occurrence of `χ₁` or `\barχ₁`. It equals
`λ₁` when `ρ₁` is multiple. For a real `χ₁` with nonreal `ρ₁` it excludes
`\barρ₁`.

Put `n=2` if `χ₁` is nonreal and `n=1` otherwise. The **type** is
* `rr` if `χ₁` and `ρ₁` are both real;
* `rc` if `χ₁` is real and `ρ₁` is nonreal;
* `complex` if `χ₁` is nonreal.

Every inequality below holds for `q≥q₀`, where `q₀` depends on finitely many
fixed choices. `η=10⁻⁶` denotes the repository's fixed tolerance.

## 2. Prime detection

**Kernel.** Take `T=.416829`, the step width `κ=T/16` and the sixteen step
heights `β₀,…,β₁₅` of `computations/core/code/config_v4.py`. Put
`ψ=∑βᵢ1_{[iκ,(i+1)κ)}` and `Ψ(z)=∫ψ(t)e^{-zt}dt`. Put `A=L-2T`, so `A=3.156342`
at `L=3.99`. The prime weight is `h(t)=(ψ*ψ)(t-A)`, supported in `[A,L]`. Its
transform is

\[
 H(z)=e^{-Az}\Psi(z)^2,\qquad H_0=\Psi(0)^2 .
\]

`h` is exactly a positive combination of 256 of Xylouris's triangles (3.51).
Every left endpoint is at least `A`.

**Criterion** [X (3.57)–(3.58), pp. 34–35; cf. H Lemma 13.2]. Suppose every
component left endpoint exceeds 3, that is `A>3` (`L>3.8337`). Fix `ε>0`. Then
for `q≥q₀(ε)`,

\[
 \sum_{p\equiv a\,(q)}\frac{\log p}{p}\,h\!\Bigl(\frac{\log p}{\ell}\Bigr)
 \ \ge\ \frac{\ell}{\varphi(q)}\Bigl[H_0-\sum_{\chi\ne\chi_0}\sum_{\rho\in R_P}|H((1-\rho)\ell)|-\varepsilon\Bigr].
\]

Put `W=H₀⁻¹∑∑|H|`. If `W≤1-δ₀` for some fixed `δ₀>0`, and `ε<δ₀H₀`, then there
is a prime `p≡a (q)` with `q^A<p<q^L`.

* **Occurrence form.** The criterion charges each zero occurrence separately
  (`W_occ`), not each character's grouped sum. All the costs in §3 bound
  individual occurrences, so they bound `W_occ`.
* **Mixture.** X p. 34 states (3.56) and (3.57) for any finite real
  combination `Σα_i h_{L_i,K_i}` of triangles (3.51) with every
  `L_i>2K_i+3`. Here `1_{[iκ,(i+1)κ)}*1_{[jκ,(j+1)κ)}` is the triangle with
  `K=κ` on `[(i+j)κ,(i+j+2)κ]`. So the 256 products collapse to
  `h=Σ_{k=0}^{30}c_kh_{A+(k+2)κ,κ}`, whose left endpoints `A+kκ` are all `≥A>3`.
  The criterion therefore applies as printed, with the norm taken after
  summing the triangle transforms at each zero. Xylouris's own kernel (6.2)
  uses (3.57) in the same way
  ([interface closure](notes/interface-closure-2026-09-29.md) §1).
* **Error allowance.** Every leaf value includes `final=5η`. It is split as
  follows ([interface closure](notes/interface-closure-2026-09-29.md) §6):

  | Term | Content | Bound |
  | --- | --- | --- |
  | E1 | the criterion's `ε`, with `ε=ηH₀` | `η` |
  | E2 | envelope errors, `ε₁=ηH₀/19` per character, summed through `Σ_χe^{-Aλ_χ}≤(1+η)V/w(0)<19` (§4, since `e^{-Aλ}/w(λ)` decreases) | `η` |
  | E3 | at most four outside distinguished terms, each `≤c_out/C_B²` | `η`, by the choice of `C_B` (§10) |
  | E4 | the auxiliary smoothing of §10 | `η` |

  The total is at most `4η<5η`. Prime powers are inside (3.57), the far
  lemma's `ε` is inside `(1+η)V`, the near-lemma errors are inside `η′`, and
  enclosure errors are rounded outward.

## 3. Zero costs

Each nonprincipal character contributes the occurrence sum of its zeros in
`R_P`. Three bounds are used, all inherited from the 4.30 candidate.

**Ordinary envelope** [X Lemma 3.10, (3.60), pp. 35–36, applied as in X
§6.1–6.2; two-test foundation §5]. Put

\[
 f_\lambda(t)=2\int_0^{T-t}\psi(u)\psi(u+t)e^{-\lambda(2u+t)}du,\qquad
 B_\phi(\lambda)=H_0^{-1}\bigl[F_\lambda(-\lambda)+\tfrac\phi2 f_\lambda(0)\bigr],
\]

and `G(λ)=e^{-Aλ}B_{1/3}(λ)`. Let `χ` have no zero with parameter below `λ` in
the disc `|1-ρ|≤δ` at height 0. Then its zeros in `R_P` cost at most
`G(λ)+εe^{-Aλ}`, uniformly in `λ≥λ_min>0`. This is the error form that E2 (§2)
sums. For `λ≤C_P` it is Lemma 3.10 with `εe^{-AC_P}` in place of `ε`. For
`λ>C_P` and large `q`, `R_P` holds no zero of `χ`: a zero there has
`|1-ρ|≤√2C_P/𝓛≤δ` and parameter `≤C_P<λ`. `B` is decreasing.

The anchor is the parameter of the character's **representative**. For an
ordinary character this is the rightmost zero with `|γ|≤T*` (§4). Every zero in
the height-0 disc has `|γ|<T*`, so the localized form of Lemma 3.10 applies.
This needs a disc radius `δ<1/2≤T*`. The radius of X Lemma 3.2 (H Lemma 5.2)
comes from H Lemma 3.1, whose proof (H p. 14) takes `δ=min(1/(2k),ε₀/(3c₀k²))`
with `k≥3`, so `δ≤1/6`. The same proof works for every smaller `δ`, and H
remarks after Lemma 5.2 (p. 24) that `δ=1/log 𝓛` may be taken.

The step kernel violates Xylouris's Condition 1. The argument therefore
smooths `ψ` in `L¹` after fixing the per-character zero count. Summed over
unboundedly many characters, the errors are controlled through the far
resource because `A>2x` (§4).

**First family, inside** [4.33 §2; refines X (6.23)–(6.24)]. Let `λ₁∈[a,b]`,
and let every other first-family occurrence have `λ≥p`. Put `α=2` for type
`rc` and `α=1` otherwise. Put `B_t=B_{1/4}` for a real `χ₁` and `B_{1/3}`
otherwise; the `B_{1/4}` case is derived from a printed proof [PD]. Put
`h(a)=Ψ(a)²/H₀` and

\[
 C(p,a)=\frac{2}{H_0}\int_0^T\psi(u)e^{-2pu}\int_u^T\psi(v)e^{-a(v-u)}dv\,du .
\]

Two bounds hold, and the leaf takes their minimum.
* **Old bound:** `J_old=n[e^{-Ap}(B_t(a)-αh(a))₊+αe^{-Aa}h(a)]`.
* **Shifted bound** (when `p≥b`):
  `J_new=n{αe^{-Aa}h(a)+e^{-Ap}[B_t(p)-αC(p,a)]}+ε`.

The shifted bound keeps the distinguished zero and its correction together.
It uses X Lemma 3.2 at `1-p/ℓ` and X Lemma 3.5, and needs no clipping at zero.

**Reserved second family** [published_single_inputs; 4.33 §3]. A leaf may
reserve `n₂∈{1,2}` characters whose height-one representatives have
`ν₂∈[lo₂,hi₂]`. Each costs at most `G_{φ₂}(ν₂)`, where `φ₂=1/4` exactly when
`n₂=1`.
* The 4.30 model charges the family at the ends: `J₂=n₂G_{φ₂}(lo₂)` in the
  objective, and its far cost and near features at `hi₂`.
* The graded-near leaves instead give the family its own LP columns (§7),
  sub-bins of `[lo₂,hi₂]` on the grid `1/400`. This is a relaxation of the
  corresponding split, since the LP may spread the mass `n₂` over several
  columns. The actual configuration, with mass `n₂` on `ν₂`'s column, is
  feasible.

**Outside first zero.** When `ρ₁∉R_B`, the first family's global zero is not in
`R_P` and costs nothing. Its zeros in `R_P` become hidden columns (§7). Each
first-family character has at most one such column, its rightmost `R_P` zero
with `t≥p`. That column costs `e^{-At}B(p)`. This model (`outside_buffer`,
near-blocks §5) covers every `|μ₁|>C_B`,
including physical heights `C_B/ℓ<|γ₁|≤1`.

The leaf objective is

\[
 \mathrm{first}+\mathrm{final}+\sum_i G(\mathrm{lo}_i)\,x_i+\sum_h G_h y_h,
\]

where `x_i` counts ordinary characters in bin `i` and `y_h` counts hidden
columns. `first` is `min(J_old,J_new)+J₂`, or its outside analogue.

## 4. Far density

**Lemma** [X Lemma 5.1, (5.19), p. 66; H Lemma 11.1 is the case of one sieve
piece]. Fix `c₁,c₂>0`, a number of sieve pieces (X's `M`, here 10), weights
`α_i≥0` with `∑α_i=1`, and a profile `w₀`
that is continuous, piecewise `C¹` and bounded away from zero. Put
`u=1/3+2c₁` and `x=2/3+3c₁+c₂`, and

\[
 w(\lambda)^{-1}=\int_u^x w_0(t)^2e^{2\lambda t}dt .
\]

Choose at most one zero per character with `|Im ρ|≤1`. Then
`∑_χ w(λ_χ)≤(1+η)V`, where `V` is the explicit constant of (5.19).

* Any one zero per character may be chosen. Ordinary characters use their
  `|γ|≤T*` representative. The reserved second family and an inside first
  family use their height-one representatives.
* A nonreal character and its conjugate count separately. The principal
  character is excluded.

**Weights.** Two profiles are used, both of shape X (6.20):
* the inherited one: `c₁=.09035`, `c₂=.235968`, `θ=1.28683`, `V≈175.266`;
* the retuned one of `far_enclosures.CANDIDATE`: `V≈243.321`.

Each leaf uses the weight recorded in its 4.30 source. Each is a finite
parameter choice inside the same lemma.

**Budget.** `F=⌈(1+η)V⌉-1_{inside}·n·w(b)-n₂w(hi₂)`. A leaf with `F<0` is
excluded. The graded-near leaves move the last term into the second-family
columns (§7).

**Tail.** Bins cover `[r₀,R]` with `R=max(3,r₀)`. The tail `[R,∞)` is one
column with far cost 1 and objective `G(R)/w(R)`. This is valid because
`e^{-Aλ}/w(λ)` decreases when `A>2x`. That holds at `L=3.99`: `2x≤2.348`,
while `A=3.156`.

**Strip representatives** [sieve-majorant-near §2]. Fix `s_max`, the count
`K₀` of zeros (all characters, with multiplicity) with parameter `≤s_max` and
height `≤2`, and then `M`. `K₀` is `O(1)` by a log-free density estimate. It is
counted to height 2, not `1+δ`: Lemma 3.2's disc radius `δ<1` depends on a
tolerance chosen after `M`, and `M` depends on `K₀` (§10). By pigeonhole, choose `T*∈[1/2,1]` so that no such
zero lies within normalized distance `M` of `|γ|=T*`. Representatives only move
right when the strip shrinks. The count rule and the ordinary lower bound
therefore remain valid.

## 5. Zero location

These inputs are independent of `L`. They are the 4.30 candidate's own
inputs, together with one refinement.

Printed table values are used as exact bounds for `q≥q₀`. Each value is
proved by a strict contradiction with a computed margin, so it holds once the
source's `ε` is below that margin. For example:
* H p. 38: the printed Table 2 values lie "a little below" the computed roots
  `λ₀b`, and `λ₀≥λ₀b-ε`;
* X p. 55 (Tables 9 and 10; proof pp. 55–59): every grid value is "etwas
  Negatives", giving for example `λ₃>1.176`.

A source-table audit (2026-09-29,
[source-table audit](notes/source-table-audit-2026-09-29.md)) checked every
zero-location input of the 3.99 case tree against the printed page: its value,
its scope and this convention.
* **H Tables 4 and 7** state no rounding convention. Their exactness rests on
  recomputing H's roots from his printed parameters. The tightest rows are:
  * Table 4, row 1.05: root 1.43904 against the printed 1.439;
  * Table 7, row .20: root 2.01015 against 2.01;
  * Table 7, row .55: root 1.00036 against 1.00.
* **Inputs used in the form `c-ε`** are reduced explicitly:
  * `.001` for H Tables 2 and 5 (§9);
  * `.857<6/7` for H Lemma 10.3;
  * `α=1.09<12/11` for H Lemmas 8.4 and 8.8.

**Types and first-zero cells.**
* X Lemma 4.5/Table 11 gives `λ₁>.44` for a nonreal `χ₁` or `ρ₁`, and
  `λ₁>.628` for type `rc` (H Lemma 9.5 alone gives only .348–.518). So
  `λ₁≤.44` forces type `rr`.
* The middle range `.1≤λ₁<1.5` is covered by 340 roots and 478 first-zero
  cells, giving 2768 specifications. Each specification records a type, a
  cell `[a,b]`, a `λ′` lower bound or gap interval, the global
  `source_l2≤λ₂`, the height-one bound `ordinary_lower`, and either a reserved
  second family or none.
* Sources for the cover:
  * H Tables 4 and 7, H Table 10 (row .70 gives .704, applied through
    Lemma 9.4), and H Lemmas 8.4, 8.8 and 9.4;
  * X Tables 2′, 3, 6 and 7;
  * X's selection rules (3.11)–(3.12);
  * `computations/core/code/cover_v5.py` and `refinement_cover.py`.

**Global λ₂ rows** [repository].
* A degree-2 row, and 25 complex rows re-evaluated on each actual cell.
* Degree-5 real rows with Heath-Brown's weighted `1/108` conductor saving;
  for example `λ₂>.7793` on `[.700,.7025]`.
* A row is used only when the whole cell lies inside it. It raises `λ₂` and the
  shift, and excludes any reserved interval lying below it.

**λ₃** [`triple_inputs.third_bound`].
* H Lemma 10.3 gives `λ₃≥.857`.
* X Table 8 applies to complex first zeros with `λ₁≤.62`.
* X Table 10 applies to type `rr`.
* X (4.28) with `γ=5/4` is re-evaluated on complex cells. Its alias condition
  (4.29) is regenerated rigorously.
* **Refinement** [sieve-majorant-near §2d]. X (4.31) with `γ=1.04` is applied
  pointwise on X's verified box, `λ₁∈[.44,.80]` and `λ₂≤1.176`, on each `rr`
  cell. The global `λ₂` is capped by a reserved second family's upper end.
  For example, `λ₃>1.0884` on `[.7025,.705]`, where Table 10 gives `.952`.

**Count rule** [4.33 §3]. Without a reserved second family, at most two
ordinary characters have representatives below `λ₃`: one global family. With a
reserved family, ordinary bins wholly below `λ₃` are dropped.

**Exclusions** (independent of `L`).
* Real positivity: `(1+χ₁)(1+Re χ₂n^{-iγ₂})≥0`, 197 nodes.
* Polynomial rows that remove a whole reserved or gap interval: 352 inside
  and 70 outside nodes.
* Real conductor rows: 75 nodes.
* Leaves with a negative far budget.

**Inside and outside.** A real zero has `μ=0`, so type `rr` is always inside
`R_B`. For types `rc` and `complex`, each specification is covered twice:
* **Inside** (`ρ₁∈R_B`): `|γ₁|≤C_B/ℓ`, so `ρ₁` is its character's height-one
  and `T*` representative.
* **Outside** (`|μ₁|>C_B`): the 1685 outside roots, each in the
  `outside_buffer` model of §3.

## 6. The graded near lemma

### 6.1 Data

The following are fixed before `q→∞`.
* **Detector.** An admissible `f≥0` supported in `[0,2γ]` with transform
  `F(z)=∫f(t)e^{-zt}dt`. Admissible means `Re F(z)≥0` for `Re z≥0`; the
  parabolic autocorrelation `f_γ` is used.
* **Short Gram test.** An admissible `g₁`, with transform `G₁`.
* **Anchors.** A safe anchor `s₁` and a reference anchor `s≥s₁`. The **safe
  anchor hypothesis** is that every zero of every nonprincipal character mod
  `q` in `R(l)` has parameter `≥s₁`. In a leaf, `s₁=⌊λ₁^{lo}⌋_{1/50}≤λ₁`.
* **Sieve weight.** `H=∑_k h_k1_{[t_k,t_{k+1})}` with `h_k≥0` and
  `t₀>1/3+2ε′`. Put `ω(t)=g₁(t)e^{s₁t}+H(t)`, and assume `ω>0` on `supp f`.

Put

\[
 I_B(s)=\int\frac{e^{2st}f(t)^2}{\omega(t)}dt,\qquad
 D(\delta)=\int g_1(t)e^{(s_1-2\delta)t}dt+\sum_kh_ke^{-2\delta t_k}\frac{t_{k+1}^2-t_k^2}{2\delta_k},
\]

with `δ_k=(t_k-1/3)/2-ε′` and `d₁=g₁(0)/6`.

**Entries.** An entry is a triple `(χ_j,γ_j,s_j)`: a nonprincipal character, a
physical height `|γ_j|≤l`, and a response anchor `s_j≤s`. Its offset is
`δ_j=s-s_j≥0`, taken from a finite set. Two distinct entries `j≠k` must be of
one of three kinds:
1. **distinct characters**, `χ_j≠χ_k`;
2. **separated heights**, `χ_j=χ_k` with `|γ_j-γ_k|ℓ≥M`;
3. **a controlled pair**, `χ_j=χ_k` with `δ_j=δ_k=0`, whose normalized
   height difference `|(γ_j-γ_k)ℓ|` lies in a stated range. Two cases occur:
   * the conjugate pair of a real character, `γ_k=-γ_j`, with difference
     `2μ₁`;
   * the first family's two zeros (§6.5).

Kinds 2 and 3 are allowed only when `H=0`. The **response** of an entry is the
prime sum

\[
 R_j=-\ell^{-1}\sum_n\Lambda(n)\,\Re\bigl(\chi_j(n)n^{-(1-s_j/\ell+i\gamma_j)}\bigr)f(t_n),
 \qquad t_n=\frac{\log n}{\ell}.
\]

### 6.2 Statement

**Theorem (graded near lemma).** Fix `η′>0`. For each controlled pair let
`c^{hi}` be an upper bound for `Re G₁(-s₁+iy)` over its range of normalized
height differences `y`. Put `e_j=(c^{hi}-d₁)_+` for the two members of a pair, and
`e_j=0` otherwise. Then for `q≥q₀` and every `a_j≥0`,

\[
 \Bigl(\sum_ja_jR_j\Bigr)_+^2\le(1+\eta')I_B(s)\Bigl[\sum_j\bigl(D(\delta_j)-d_1+e_j\bigr)a_j^2+(d_1+\eta')\Bigl(\sum_ja_j\Bigr)^2\Bigr].
\]

The number of entries may grow with `q`. Only the finitely many anchors,
offsets and tests must be fixed.

**Lemma (responses)** [X Lemma 3.2, H Lemma 5.2]. Let `(χ,γ,σ)` be an entry
with `σ` in a fixed finite set. Let `S` be a set of zeros of `χ` in the local
disc about `1+iγ`. It must contain every disc zero `ρ` with `λ_ρ<σ` and
`|μ_ρ-γℓ|<M`. Assume also that at most `K₀` disc zeros have `λ_ρ<σ`.
* For entries of height at most 1, the disc lies below height `1+δ<2`, and
  `K₀` is the count of §4.
* Entries of larger height are used only with `σ≤λ₁`, where no zero has
  `λ_ρ<σ`. These are the outside global zero and the first family's second
  zero `ρ′`. `λ′` is defined over `R(l)`, so `ρ′` may lie as high as `l`.

Then

\[
 R\ \ge\ \sum_{\rho\in S}\Re F\bigl((\lambda_\rho-\sigma)+i(\mu_\rho-\gamma\ell)\bigr)-\tfrac16f(0)-\eta'.
\]

*Proof.* The local explicit formula bounds `-R` above by
`(φ/2)f(0)-∑_ρ Re F((1-σ/ℓ+iγ-ρ)ℓ)+o(1)`, summed over the disc. A zero with
`λ_ρ≥σ` not in `S` has a term with nonnegative real part, by admissibility, so
it can be dropped. Disc zeros with `λ_ρ<σ` that are not in `S` are at
normalized distance `≥M`. There are at most `K₀` of them, and `M` is chosen so
that `|F(x+iY)|≤η′/(2K₀)` for `|Y|≥M` and `x` in the fixed range. ∎

### 6.3 Proof of the theorem

For `(n,q)=1` put

\[
 Y_n=\sum_ja_je^{-\delta_jt_n}\chi_j(n)n^{-i\gamma_j},
\]

so that `∑_ja_jR_j=-Re ℓ^{-1}∑_n(Λ(n)/n)e^{st_n}f(t_n)Y_n`. This holds
because `n^{-(1-s_j/ℓ+iγ_j)}=n^{-1}e^{s_jt_n}n^{-iγ_j}` and
`e^{s_jt_n}=e^{st_n}e^{-δ_jt_n}`. By Cauchy–Schwarz with the weight `ω`,

\[
 \Bigl(\sum_ja_jR_j\Bigr)_+^2\le
 \Bigl(\ell^{-1}\sum_n\frac{\Lambda(n)}n\frac{e^{2st_n}f(t_n)^2}{\omega(t_n)}\Bigr)
 \Bigl(\ell^{-1}\sum_{(n,q)=1}\frac{\Lambda(n)}n\,\omega(t_n)|Y_n|^2\Bigr).
\]

**First factor.** By the prime number theorem the first factor is `I_B(s)+o(1)`.
Its integrand is bounded, piecewise continuous and compactly supported.

**Second factor.** Split it as `Q₁+Q₂` according to `ω=g₁e^{s₁t}+H`. Expanding
`|Y_n|²` gives, with `ψ_{jk}=χ_j\barχ_k`,

\[
 Q_1=\sum_{j,k}a_ja_k\,\Re\,\ell^{-1}\sum_{(n,q)=1}\Lambda(n)\psi_{jk}(n)\,
      n^{-(1-\sigma_{jk}/\ell)-i(\gamma_j-\gamma_k)}g_1(t_n),\qquad
 \sigma_{jk}=s_1-\delta_j-\delta_k\le s_1 .
\]

The entries are bounded as follows.
* **Diagonal.** `ψ=χ₀` at height 0. By X Lemma 3.1 the entry is
  `∫g₁e^{(s₁-2δ_j)t}+o(1)`.
* **Distinct characters.** `ψ_{jk}` is nonprincipal. X Lemma 3.2 bounds the real
  part by `(φ/2)g₁(0)-∑Re G₁(·)+o(1)`. By the safe anchor hypothesis, every
  zero of `ψ_{jk}` in the disc has parameter `≥s₁≥σ_{jk}`. Its term therefore
  has nonnegative real part and is dropped, leaving `≤d₁+o(1)`.
  * For `σ_{jk}<0` the test point lies to the right of 1. X Lemma 3.2 still
    applies, with every zero dropped.
  * All test and Gram points have physical height `≤2l≤9l`, which lies
    inside X Lemma 3.4's region `R(9l)`. By X Lemma 3.3 every disc zero lies
    in `R(l)`, or far to the left. Also `2l≤ℓ`, so X Lemma 3.1 is uniform in
    the height.
* **Separated heights.** `ψ=χ₀` at height `τ=γ_j-γ_k` with `|τ|ℓ≥M`. By X
  Lemma 3.1 the entry is `G₁(-σ+iτℓ)+o(1)`. For `M` large its modulus is at
  most `η′/4≤d₁`.
* **Controlled pair.** `ψ=χ_j\barχ_j=χ₀` at the height difference `y/ℓ`.
  The entry is `G₁(-s₁+iy)+o(1)`, uniformly for heights up to `ℓ` (X
  Lemma 3.1; H Lemma 5.3). Its real part is at most `c^{hi}+o(1)`. For the
  conjugate pair of a real character, `χ₁²=χ₀` and `y=2μ₁`.

For `a≥0`, the off-diagonal part is therefore at most
`d₁[(∑a_j)²-∑a_j²]+∑_{pairs}2a_+a_-(c^{hi}-d₁)_+`. Since `2a_+a_-≤a_+²+a_-²`,
the pair excess becomes the diagonal terms `e_j`.

**The sieve part `Q₂`** (only when `H≠0`, so only distinct characters occur).
Treat each cell `k` separately. Let `D_k=q^{δ_k}`, put
`λ_d=μ(d)log(D_k/d)/log D_k` for `d≤D_k`, and put `ν_k(n)=(∑_{d|n}λ_d)²≥0`.
* **Majorant.** For primes `p≥q^{t_k}>D_k`, `ν_k(p)=1`, so
  `Λ(p)=(log p)ν_k(p)`. Composite non-prime-powers have `Λ=0`, and higher
  prime powers contribute `O(q^{-t_k/2}ℓ)(∑a_j)²`.
* **Diagonal.** For `j=k`, drop coprimality. Graham's estimate
  `∑_{n≤x}ν_k(n)=x/log D_k+O(x/log²D_k)` (H (11.13), `U=1`) and partial summation
  bound the cell by `h_ke^{-2δ_jt_k}(t_{k+1}²-t_k²)/(2δ_k)+O(1/ℓ)`.
* **Off-diagonal.** For `j≠k`, `ψ_{jk}` is nonprincipal. Open `ν_k` as
  `∑_{d,e≤D_k}λ_dλ_eψ([d,e])∑_mψ(m)W(m[d,e])`. Each inner sum runs over
  `m≥M₀=q^{t_k}/[d,e]≥q^{t_k-2δ_k}=q^{1/3+2ε′}`, since `2δ_k=t_k-1/3-2ε′`.
  * Use Abel summation with the **pointwise** Burgess bound
    `|∑_{M₀≤m≤u}ψ(m)|≪u^{2/3}q^{1/9+ε}` (X Lemma 5.2; H Lemma 2.1 with `k=3`).
    Also `|∂_uW(u[d,e])|≪ℓ^{O(1)}(1+|τ|)u^{-2}[d,e]^{-1}`, where `τ` is the
    height difference, `|τ|≤2l≤ℓ`. Together these give
    `≪ℓ^{O(1)}(1+|τ|)[d,e]^{-1}q^{1/9+ε}M₀^{-1/3}`.
  * The crude form `sup|S|·(‖W‖_∞+Var W)` would lose `q^{2(t_{k+1}-t_k)/3}`,
    which exceeds the saving once the cell is wider than about `ε′`.
  * **Imprimitive `ψ`.** If `ψ` is induced by `ψ*` mod `q*`, Möbius inversion
    over the primes of `q` not dividing `q*` costs `τ(q)≪q^ε`. If `q*<M₀`,
    complete periods vanish.
  * **Sum over `d,e≤D_k`.** Since `∑_{d,e≤D}[d,e]^{-2/3}≪D^{2/3}`, the total is
    `≪ℓ^{O(1)}q^{1/9-t_k/3+2δ_k/3+ε}=ℓ^{O(1)}q^{ε-2ε′/3}`. This is
    `q^{-c(ε′)}` for `ε<2ε′/3`, uniformly in characters and heights.

Every error is either uniform per entry, and absorbed into the responses, or
a uniform `o(1)` multiple of `∑a_j²≤(∑a_j)²`. ∎

### 6.4 Threshold form

Let `r_j=∑_{ρ∈S_j}m_ρ Re F((λ_ρ-s_j)+i(μ_ρ-γ_jℓ))-f(0)/6` be the main term of
the response lemma's bound, so that `R_j≥r_j-η′`. Put
`N=\sqrt{(1+η′)I_B(s)D(0)}` and define

\[
 v_j=\frac{r_j-\eta'}{N},\qquad D_j=\frac{D(\delta_j)-d_1+e_j}{D(0)},\qquad d=\frac{d_1+\eta'}{D(0)}.
\]

The theorem gives `(∑a_jv_j)_+²≤∑D_ja_j²+d(∑a_j)²` for all `a≥0`. By the
threshold identity (two-test foundation §3; Lean `Near.common_threshold_iff`)
this is equivalent to

\[
 \exists\tau\in[0,\sqrt d]:\quad \sum_j\frac{(v_j-\tau)_+^2}{D_j}\le1-\frac{\tau^2}{d}. \tag{T}
\]

Entries with `v_j≤0` may be omitted. `D(δ)` decreases in `δ`, so a leaf may round
`δ` down to the grid `1/200`. An entry whose `D_j` is not safely positive is
omitted.

**The normalization of the leaf builders.** `sieve_inputs.py` uses an upper bound
`I_u≥I_B(s)` and `D_u≥D(0)`, and computes:
* features `r_j/\sqrt{I_uD_u}-η′`;
* diagonals `(1+η′)D_j^+/D_u`, with `D_j^+≥D(δ_j)-d₁+e_j`;
* the radius `(1+η′)(d₁/D_u+η′)`.

These satisfy (T) whenever (T) holds as above. Apply the theorem with the
smaller allowance `η″=η′min(1,\sqrt{I_BD_u},D_u)` in place of `η′`, and with
`D_u/(1+η″)` in place of `D(0)`. The quadratic form inequality is homogeneous,
so any positive normalizer works. Each builder quantity is then on the safe side:
* its feature is at most `(r_j-η″)/\sqrt{I_BD_u}` (or `≤0`);
* its diagonal is at least `(1+η″)(D(δ_j)-d₁+e_j)/D_u`;
* its radius is at least `(1+η″)(d₁+η″)/D_u`.

No condition on `I_u` or `D_u` is needed, since the theorem holds for every
`η″>0`. This is the Lean theorem `GradedNear.builder_threshold`
([lean-graded](../README.md)).

**Formalized.** The following are proved in Lean, conditional on X Lemmas
3.1–3.2, Burgess and Graham:
* the theorem of §6.2;
* the response lemma;
* (T) for kept zeros (`graded_near_threshold`) and in the builders'
  normalization;
* the entry bounds of §6.5;
* the passage from (T) to the rows of the leaf LP (`Cert.near_row_of_bins`).

### 6.5 The rows used

Each row fixes `(f,g₁,H,s₁,s)` and its entries. Every character of the
configuration may enter the same row at most once, except for the pairs and
separated heights allowed above.

| Row | Anchor `s` | Sieve | Entries |
| --- | --- | --- | --- |
| **Family** (inside) | `s=s₁` | `H=0` | First family (anchor `s₁`); for `rc`, the conjugate pair; reserved second family; ordinary characters |
| **Shifted** (inside) | repository shift `min(1.9,λ′_lo,source_l2)` | `H=0` in the parameters used; `H≥0` would be allowed, since every entry is a distinct character | First family above its anchor; second family; ordinary |
| **Graded** | menu, e.g. 1.5, 1.9, 2.3 | `H≥0` | First family (inside), second family, ordinary, each at `min(own lower bound, s)` |
| **Family** (outside) | `s=s₁` | `H=0` | Global first zero; local first-family zeros (hidden columns); second family; ordinary |

The responses used in each case follow from the response lemma, with `S` as
stated.
* **Ordinary character in bin `[lo,hi]`.** It uses its `T*` representative
  `ρ_j` and anchor `s_j=min(lo,s)`.
  * A zero of `χ_j` with `λ<s_j≤λ_j` lies outside `|γ|≤T*`, so by the choice
    of `T*` it is at distance `≥M`. Hence `S={ρ_j}`.
  * Since `F` decreases on the real line, `r_j≥F(hi-s_j)-f(0)/6`. The
    diagonal is `D(s-s_j)`.
* **Inside first family.** The anchor `σ=min(a,s)≤λ₁` means no zero lies to
  the right. `S={ρ₁}` gives `r≥F(b-σ)-f(0)/6`.
* **Type `rc` pair** (family row). The entries are `(χ₁,±γ₁,s₁)`, with
  `S={ρ₁,\barρ₁}`. Both zeros lie to the left, so
  `r≥F(λ₁-s₁)+Re F(λ₁-s₁+2iμ₁)-f(0)/6`.
  * The height is split as `μ₁∈[0,1]` and `μ₁≥1`.
  * `Re F` and `c(μ)` are enclosed on a `μ` grid, with second-derivative
    slack and a closed-form tail for `μ≥10`, where `Re F≥0` is used.
* **First family's second zero** (family row; complex type with a finite gap
  `λ′∈[p,p^{hi}]`). Each first-family character `χ` has, besides `ρ₁`, a zero
  `ρ′` with parameter `λ′`. This is the minimizer defining `λ′`, or its
  conjugate for `\barχ`. Let `y` be the normalized height difference
  between `ρ′` and `ρ₁`. The row carries two entries for `χ₁`, and the
  conjugate entries `(\barχ₁,-γ₁,s₁)`, `(\barχ₁,-γ′,s₁)` for `\barχ₁`:
  * `(χ₁,γ₁,s₁)`, with `S={ρ₁,ρ′}`, giving
    `r≥F(b-s₁)+Re F(λ′-s₁+iy)-f(0)/6`;
  * `(χ₁,γ′,s₁)`, with `S={ρ′,ρ₁}`, giving
    `r≥F(p^{hi}-s₁)+Re F(λ₁-s₁-iy)-f(0)/6`.

  Cross-character pairs have the nonprincipal quotient `χ₁²`, so they keep
  `d₁`. A multiple zero (`y=0`) gives two identical vectors. The bound is then
  exactly the double-zero statement.

  Both zeros lie to the left of both test points, so every term has
  nonnegative real part. The two entries form a controlled pair, and their
  Gram excess `(c^{hi}-d₁)_+` is added to both diagonals.
  * The leaf is split by `y∈[0,1]`, `[1,3/2]`, `[3/2,2]`, `[2,3]`, `[3,5]`
    and `[5,∞)`.
  * On each piece, `Re F` and `c(y)` are enclosed on a grid with
    second-derivative slack and Lipschitz slack in `λ₁` and `λ′`. For
    `y≥10` the closed-form tail is used, where `Re F≥0`.
  * When `ρ′` lies outside the local disc of `ρ₁`, its term is simply
    absent, and the bound `Re F≥0` covers that case.
  * This is the one place where a piece may be **excluded** outright rather
    than bounded. On leaf 1285/0 the pieces with `y≤2` are infeasible: the
    four first-family entries alone give `min_τ` of the left side of (T)
    equal to 1.60, 1.45 and 1.27, all above 1. The certificate records such a
    piece through the exact exclusion rule of §7. For `y∈[2,3]` the four
    entries alone are feasible, and that piece is bounded by the whole LP.
* **Shifted first family.** Here `a≤s≤min(λ′,λ₂)`, and every other zero of the
  first family has `λ≥λ′≥s`.
  * Take `S={ρ₁}`, plus `\barρ₁` for type `rc`. Then
    `r≥F(b-s)-C_Z-f(0)/6`, where
    `C_Z=sup_{Re z≥a-s}(-Re F(z))` applies only for type `rc` with `s>a`.
  * With multiplicity `m`, the kept terms are `m(F(λ₁-s)+Re F(·))`, since
    conjugate zeros of a real character have equal multiplicity. This is at
    least `F(b-s)-C_Z` whenever that number is `≥0`. When it is `<0`, the
    entry's feature is `≤0` and the entry contributes nothing
    (`keptBound_pair_neg`).
  * `F(λ₁-s)≥F(b-s)` holds also for negative arguments.
  * The Gram part stays at `s₁`, so no quotient correction arises.
* **Reserved second family.** It uses its height-one representative
  `ν₂≤hi₂` and anchor
  `σ₂=min(max(a,min(source_l2,lo₂)),s)`.
  * Its characters are not first-family characters. Every one of their zeros
    in `R(l)` therefore has `λ≥λ₂≥source_l2`, and also `λ≥λ₁≥a`.
  * No zero lies to the right, so `S` is the representative, and
    `r≥F(hi₂-σ₂)-f(0)/6`.
  * No strip argument is needed. That argument would not keep `ν₂≤hi₂`.
* **Outside first family** (family row only).
  * The global zero `ρ₁`, with `|μ₁|>C_B` and physical height at most `l`,
    gives `r≥F(b-s₁)-f(0)/6`.
  * A hidden column is a first-family character's rightmost `R_P` zero `ρ_h`,
    with `t∈[lo_h,hi_h]` and at most one per character. It gives
    `r≥F(hi_h-s₁)-f(0)/6`.
  * A hidden entry and the global entry of the same character have separated
    heights, since `|μ₁-μ_h|≥C_B-C_P≥M`. All other pairs are distinct
    characters.
* **Large branch** (`λ₁≥1.5`, §9). This is the family row with `s=s₁=1.5`,
  `H=0` and no family entries.

The Gram test, detector and sieve weight of each row are rational parameters
chosen by a floating proposer (`family_row.py`, `propose_params.py`). Every
value used is then re-enclosed with outward interval arithmetic
(`sieve_inputs.py`).

### 6.6 The inherited two-test row

The regular model's input (`make_endgame`, §8) carries the 4.30 candidate's
own near row. That row is the two-test near row, with the leaf's variant:
* the single test (two-test foundation §3);
* a detector mixture (near refinements §3);
* a paired first-family test (near refinements §4, inequalities (5)–(8)).

It is a premise of the 4.30 candidate, not an instance of §6. In threshold
form it reads

\[
 \exists\tau\in[0,\sqrt d]:\quad \sum_i x_i\frac{(V_i-\tau)_+^2}{D}
 \le 1-\frac{\tau^2}{d}-n\frac{(v_f-\tau)_+^2}{D_f}-n_2\frac{(v_2-\tau)_+^2}{D}.
\]

Here `d`, `D`, `D_f`, the first family's feature `v_f`, the bin features `V_i`
and a reserved second family's feature `v₂` are the input's own enclosures at
`L`. The row enters a leaf LP like any other row, with its own threshold.
* **Representatives.** In the 4.30 candidate the row's ordinary entries were
  height-one representatives. The graded LP's columns are `T*`
  representatives (§6.5). The row still holds for them:
  * every zero of a non-first character has `λ≥λ₂≥source_l2≥s`, where `s` is
    the row's anchor;
  * so the two-test inequality with any single selected zero of height at
    most `T*≤1` gives a feature at least `V_i` for its bin;
  * `T*` representatives are at least the height-one representatives, hence
    at least `ordinary_lower`, so the bins cover them.
* A reserved second family keeps its fixed term. `v₂` is enclosed at the
  range's upper end, and the feature decreases in `λ`, so `v₂` bounds the
  feature over the whole reserved range. It does so also when the family is
  charged by columns (§7), which then carry no feature in this row.
* Negative features are replaced by 0. This is exact, since `τ≥0`.
* The row's premises do not involve anything the simplified model drops. The
  budget windows and first-dimension handling of the old certifier were
  tightenings only.
* The driver uses the row only when the graded rows alone fail on an inside
  leaf (`graded_driver.OLD_STAGES`); it is never used outside.
* At 3.99 it is needed on 37 unreserved roots of both types, in all three
  variants ([sieve-majorant-near §6h](arguments/sieve-majorant-near.md)):
  * `rr` cells with `λ₁∈[.20,.46]` (roots 10–36; single test);
  * complex cells with `λ₁∈[.44,.48]` and `[.58,.62]` (roots 1198–1201 and
    1212–1215; single test);
  * complex cells with `λ₁∈[.80,.82]` (roots 2603, 2608, 2613, 2633; paired
    first family);
  * roots 1218 and 1219 (mixture): on the lowest ninth of the reserved
    pair's 9-way split.
* Review 9 (sieve-majorant-near §8) found the embedding valid. It checked
  the exact equivalence with the repository formula and the rounding, the
  clamping, the columns, and the verifier's rejection of forged records.

## 7. Leaf LPs and exact certificates

**Leaf.** A leaf has the following data.
* **Ordinary columns.** Parameter bins `[lo_i,hi_i]` with grid `1/den` on
  `[r₀,R]`, plus the tail. Their unknowns are `x_i≥0`.
* **Hidden columns** (outside leaves). Unknowns `y_h≥0`.
* **Second-family columns**, when a second family is reserved. Sub-bins
  `[l_j,r_j]` of `[lo₂,hi₂]` with grid `1/400`, unknowns `z_j≥0`, and the
  constraint `∑z_j=n₂`.
  * Each column has far cost `w(r_j)` and objective `G_{φ₂}(l_j)`.
  * In each row its anchor is `min(max(a,min(source_l2,l_j)),s)` and its
    feature is taken at `r_j`. This is the fixed term's rule of §6.5 with
    `lo₂` replaced by `l_j`.
  * The family's `n₂` characters share one parameter `ν₂`. The configuration
    therefore puts mass `n₂` on the column containing `ν₂`, which is a
    feasible point.
  * The objective `first` then omits `J₂`, and the far budget omits `n₂w(hi₂)`.
* **Constraints:**
  * far: `∑w(hi_i)x_i+∑w_hy_h+∑w(r_j)z_j≤F`;
  * count: `∑_{hi_i≤λ₃^{lo}}x_i≤2` (none when a second family is reserved);
  * hidden count: `∑y_h≤n`;
  * second family: `∑z_j=n₂`;
  * one constraint (T) per near row `k`, with its own unknown threshold
    `τ_k`. Here `v`, `D` and the family terms are those of §6.5.
* **Value.** The objective of §3. Every cost is monotone, so each column uses
  the right endpoint for resources and features and the left endpoint for the
  objective.

The configuration is feasible for the leaf's relaxation, so `W` is at most the
LP maximum. The leaf is **certified at `L`** if that maximum is below 1 for
every possible thresholds `(τ_1,…,τ_K)`.

**Certificate.** A certificate is a bisection tree over the threshold box
`∏[0,\sqrt{d_k}]`, with ticks `10⁻⁶`. With `d_k` stored as an integer scaled
by `S=10¹⁶`, the box's end in ticks is
`end_k=⌈√(⌊d_k·10¹²/S⌋+1)⌉`. The end is not stored in the record, so a
verifier must reproduce it. It satisfies `end_k²·S≥d_k·10¹²`, so the box
contains `[0,√d_k]`. At each tree leaf, each dimension uses one of two
relaxations.
* **First order.** Costs at the upper threshold, budget at the lower.
* **Second order.** `Φ_k(τ)=∑c(v-τ)_+²+τ²/d` is convex and `C¹`. If `m` is the
  midpoint and `h` the half-width, then `Φ_k(τ*)≤1` forces
  `Φ_k(m)∓hΦ′_k(m)≤1` for one sign. Term by term these are linear:
  * `(v-m)_+²±2h(v-m)_+=((v-m)_+±h)²-h²`;
  * `m²∓2hm=(m∓h)²-h²`.

Each resulting case records one of two things.
* **An exclusion.** This is a constraint whose costs are **all nonnegative**
  and whose budget is negative. In tangent case 1 costs can be negative, and
  then a negative budget proves nothing (review of sieve-majorant-near §8).
* **Integer duals** `Y,V,U,P,M,Z_1..Z_K≥0`. They must satisfy
  `Yw_i+V cnt_i+∑Z_k cost_{ik}≥G_i` exactly on every column. A second-family
  column also carries `(P-M)`, the free dual of its equality.
  * Weak duality then bounds the case value by
    `⌈(YF+2SV+n_gSU+(P-M)n₂S+∑Z_kB_k)/DS⌉+first+final`. Here all data are
    scaled by `S=10¹⁶`, `n_g` is the hidden count and `n₂` the reserved
    count.
  * Signed costs are allowed, because only the multipliers must be
    nonnegative.

Scales: inputs `10¹⁶`, thresholds `10⁶`, duals `10¹²`. All enclosures are
outward in the safe direction:
* costs and far weights are rounded down;
* objectives and budgets are rounded up.

Code: `computations/graded/graded_cert.py` (`verify_tree`).

## 8. The case tree and its leaves

**Middle range, inside.** Each of the 2768 specifications is the root of the
verified 4.30 source tree `computations/frontier/collective_full_4.30`. Two
kinds of node are kept unchanged.
* **Splits:** first-zero, second-family and `λ′`-gap bisections. The children
  exhaust the parent.
* **Location and exclusion nodes:**
  * real conductor rows (restrict or exclude);
  * complex location rows;
  * polynomial second-family and gap exclusions;
  * real positivity.

  None depends on `L`.

Every LP leaf of that tree is replaced by the **regular inside model** of its
case at `L`. This covers core, far, collective and repair leaves, and every
`inside_repair` identities node. The regular model consists of:
* the repository's `make_endgame` input;
* the leaf's recorded far weight;
* the refined `λ₃`;
* no collective envelope;
* the rows of §6.5.

The hidden-family identity branches are not used. The regular model is
valid for every case, because the identities were only an alternative
certificate.

**Middle range, outside.** Each of the 1685 outside roots keeps its 4.30 tree
(`near` outside regime). Each `buffered_first` leaf is replaced by the
**regular outside model** at `L`. That model is the repository's
`first_out_input` in the leaf's subcase, with the count row and the outside
rows of §6.5. The outside first-block near relaxation is not used.

**Further subdivision.** A leaf may be certified through children that
exhaust it. The second-family columns of §7 make most such splits
unnecessary.
* **Second-family splits.** The repository's `split_specs(·,'second',mid)`,
  with 3 or 5 children.
* **Reservation split** of an unreserved case at `h` with `r<h≤2`, where `r`
  is the case's `ordinary_lower`. The children are:
  * a lowest local non-first family (any minimizer of the representative
    parameter `ν`) is reserved in `[r,h)` as one real character;
  * such a family is reserved in `[r,h)` as a nonreal pair;
  * no non-first height-one representative lies below `h`
    (`ordinary_lower=h`).

  Why the children exhaust the parent:
  * Conjugate characters have the same representative parameter, because
    every region used is symmetric in the height.
  * So either `ν<h`, where a minimizing family is real or a nonreal pair, or
    every non-first representative is at least `h`. Ties may place a
    configuration in two children, which is harmless.

  Each child is a case of the kind the source cover already uses. The
  third-family rule (4.33 §3) needs exactly the minimality of the reserved
  family.
  * A reserved child also gets the `λ₃` bound with cap `h`. This is valid
    because `λ₂≤ν<h`.
  * The driver uses `h=min(λ₃^{lo},2)`, taken from the parent. The
    verifier checks only `r<h≤2`. Nothing uses the identification of the
    reserved family with the global second family: the third-family rule
    needs only its minimality.
  * Review 7 (sieve-majorant-near §8) found the split valid, and review 11
    confirmed it.
  * It is used on four inside roots (1218, 1219, 2461, 2486) and on five
    identities-node roots (1479, 1490, 1501, 1512, 1523).
* **Height split for type `rc`.** `μ₁∈[0,1]` and `μ₁≥1`, in the family row.

**Replay.** `computations/graded/graded_verify.py` traverses the 4.30 source
trees with the repository's own verifiers. Every location row, exclusion and
split is re-checked on the way. Each LP leaf or identities node is intercepted,
its regular model is regenerated at `L` from the tree's own specification, and
the stored certificate is checked with exact integers.

## 9. Exterior regimes

**No zero in `R(l)`.** The zero sum is empty. `W` is then at most the error
allowance, and the criterion gives the prime.

**Small first zero, `0<λ₁≤.1`** [4.33 §6; `small_exception_tables.py`]. This
is certified at 3.99 in two pieces.
* Source exclusions leave only a real simple exceptional zero `u=λ₁`.
* **The shared setup.**
  * The kernel is a single triangle: `K=.1821` and `A=3.6258`.
  * Other characters are charged through H (13.3) and X (5.18) with
    `c₁=.057` and `c₂=.1554`.
  * On a piece `[a,b]` the main deficit `(H(0)-H(u))/u` decreases in `u`, so
    it is taken at `b`. The zero terms carry a factor `1/u`, so they are taken
    at `a`.
* **Piece `u₀≤u≤.08`.**
  * H Lemmas 8.4 and 8.8 give every other zero `λ≥1.09·log(1/u)`.
  * Monotonicity in `u` reduces the check to `u=.08`.
  * The margin is `.0305`, which is 28% of the main deficit.
* **Piece `.08≤u≤.1`.** Heath-Brown's own tables at `λ₁≤.10` are used. Each
  row holds for all `λ₁` up to its value, for `q≥q(ε)` (H p. 38).
  * **Table 5** (p. 46, from Lemma 8.5 with the `k=2` function of Lemmas 7.1
    and 7.5): every zero in `R` of every other character has `λ≥2.83-ε`.
  * **Table 2** (p. 39, from Lemma 6.3): every other zero of `L(s,χ₁)` has
    `λ≥4.96-ε`.
  * With `ε=.001`, the margin is `.0381`, which is 36% of the main deficit.
* **Why the tables matter.** The earlier single check at `u=.1` used
  `1.09·log(1/u)`, whose value there is 2.51 (margin `.000804u`, 0.77%), and
  this branch was then what blocked any exponent below 3.99. In floating
  point the two pieces stay positive down to about `L=3.90`, so the middle
  range is now the binding part.
* **Below a fixed `u₀`.** H's §8 bounds are not proved for extremely small
  `λ₁`, so this range needs a separate theorem: Heath-Brown, *Siegel zeros
  and the least prime in an arithmetic progression*, Quart. J. Math. Oxford
  (2) 41 (1990) 405–418, Corollary 1 (p. 406), read directly.
  * Its hypotheses: `ψ` is a real character mod `q`, not necessarily
    primitive, with `L(β₀,ψ)=0` and `β₀≥1-1/(3 log q)`. Put
    `η=((1-β₀)log q)^{-1}=1/λ₁`.
  * Its conclusion: for any `δ>0` there is an effectively computable `η(δ)`
    such that `η≥η(δ)` implies `P(a,q)≤q^{3+δ}` for every `a` coprime to `q`.
  * We use `δ=1/2` and `u₀=1/η(1/2)`.
  * Corollary 2 of the same paper gives `q^{2+δ}`, but with an ineffective
    `η(δ)`.
  * Xylouris's dissertation, Lemma 6.2(d) (pp. 87–92), is an independent
    ineffective alternative with `q^{3.5+ε}`.

**Large first zero, `λ₁≥1.5`** [4.33 §7; `computations/graded/graded_large.py`]. This
is certified at 3.99.
* The near constraint is the single-anchor row: §6.5 with `s=s₁=1.5`, `H=0`
  and no distinguished family.
* The far weight is the inherited one.
* The row is normalized as in §6.5, with the builders' upper Riemann sum for
  `I_B` (`t₀=1`). With the 16-step kernel, `W≤.9966814` on 36 threshold
  intervals.
* The certificate is checked by `graded_cert` and by the verified Lean
  checkers:
  * `certrun`, and the kernel (`GradedNear/Cert/Samples/Large.lean`);
  * `leafcheck` (numerics) and `rowcheck` (the near row).
* The earlier certificate (`verify_published_single.py`, `W≤.9946508`)
  normalized the row with a tighter enclosure of `I_B`. The row checker does
  not accept that normalization.

Both are replayed by `computations/frontier/verify_existing_components.py`
(`existing_components_verified.json`).

## 10. Join and uniformity

Every configuration falls into at least one of four cases:
* no zero in `R(l)`;
* `λ₁≤.1`;
* `.1≤λ₁<1.5`, inside or outside `R_B`, with a specification and a tree leaf
  containing it;
* `λ₁≥1.5`.

Each case has a certificate at an exponent `≤L`. A prime below `q^{L'}` with
`L'≤L` is below `q^L`.

The choices are made in the following order
([interface closure](notes/interface-closure-2026-09-29.md) §5).
1. `L`, the kernel, far weights, tests, anchors, grids, trees and
   certificates; `η=η′=10⁻⁶`; `u₀=1/η_{HB}(1/2)`.
2. `C_P≥max(C₀(ηH₀),3)`, with `C₀` from X (3.57).
3. The auxiliary smoothings.
4. `K₀` (§4, zeros to height 2); then `M` with `|F(x+iY)|≤η′/(2K₀)` and
   `|G₁(-σ+iY)|≤η′/4` for `|Y|≥M`; then `C_B>max(C_P+M,1.5)` with
   `4c_out/(H₀C_B²)≤η`.
5. The tolerances of the source lemmas: X Lemmas 3.1, 3.2, 3.10 and 5.1,
   Graham and Burgess, the prime number theorem, the tables' `ε`, and the
   small branch.
6. Finally `q₀`, as the maximum of finitely many thresholds, including
   `ℓ>4M(K₀+1)` for the `T*` pigeonhole.

There are finitely many leaves and fixed tests. Errors summed over unboundedly
many characters are controlled through the far resource, since
`e^{-Aλ}/w(λ)` decreases (`A>2x`). Moduli below `q₀` are absorbed into `C`. All
inputs are effective; `q₀` and `C` are not computed.

## 11. Premises

Tags:
* **[P]** printed in the source;
* **[PD]** derived from a printed proof;
* **[R]** repository deduction used by the 4.30 candidate;
* **[N]** new in this proof.

| Premise | Tag | Review status |
| --- | --- | --- |
| Prime criterion X (3.57) for the step mixture, occurrence form | P | Finite combinations printed at X p. 34 (checked 2026-09-29, §2). Each §3 cost bounds one occurrence (interface closure §2, one review). **Lean**: stated as printed (`XylourisCriterion357`); prime extraction for the step kernel, whose admissibility and `H(0)=H₀` are proved (`Kernel.exists_prime`) |
| Ordinary envelope, X Lemma 3.10, localized at the `T*` representative | P/PD | Localized form reviewed with the sieve note. **Lean**: a derived hypothesis (`OrdinaryEnvelope`, with `δ<1/2` and error `εe^{-Aλ}`), not proved |
| `B_{1/4}` for real characters | PD | Inherited |
| Old and shifted first-family bounds (4.33 §2) | R | Inherited |
| Far density X Lemma 5.1, both weights, any one zero per character | P | **Lean**: stated as printed (`XylourisLemma51`). Both weights satisfy its printed conditions, and the far budget with the reserved families follows (`far_bound_corpus`, `far_from_lemma`). The choice of one zero per character is left to the case logic |
| Zero tables (H §§8–10, X ch. 4), selection rules, λ₂ rows, λ₃ rules, exclusions | P/R | Inherited; alias checks regenerated. Every printed value used was audited against the page for value, scope and `ε` convention, and all 818 source-cover records were rechecked (2026-09-29, [source-table audit](notes/source-table-audit-2026-09-29.md)). The repository rows (degree-5 `1/108`, polynomial rows, `λ₂>.762`) remain [R] |
| Refined `rr` third-family bound, X (4.31) pointwise | PD | (4.31), and (4.34) `≤0` on `λ₁∈[.44,.80]`, `λ₂∈[.44,1.176]` with `γ=1.04`, are printed (X pp. 58–59, checked 2026-09-29). The per-cell use is X's own monotone evaluation, done with rigorous enclosures (`third_refine.py`, `γ=26/25`) |
| Graded near lemma §6.2–6.3: sieve majorant, decoupled and graded anchors, distinct-character Gram entries | N | Reviewed (sieve-majorant-near §8, reviews 1–2). Review 10 (2026-09-29) re-derived it in full from H and X and checked the code; its text repairs are made. **Formalized in Lean** (2026-09-29, `lean-graded/`, `GradedNear.graded_near_lemma`), from X Lemmas 3.1–3.2, Burgess and Graham as stated hypotheses; standard axioms only. The response lemma, (T) for kept zeros (§6.4) and in the builders' normalization (`response_lemma`, `graded_near_threshold`, `builder_threshold`) are formalized as well |
| Family row with first and second families (anchor `≤λ₁^{lo}`) | N | Reviewed (§8, review 2) |
| Type `rc` conjugate pair (X Lemma 3.1 at height `2γ₁`) | N | Reviewed (§8, review 2) |
| Count row in the outside model | N | Reviewed (§8, review 3) |
| Outside first family in the family row (global zero) | N | Reviewed (§8, review 3) |
| Outside hidden columns in the family row (separated heights) | N | Two reviews (sieve-majorant-near §8, reviews 5 and 11). Zero pair excess for separated same-character pairs is proved in Lean (`pairExcess_eq_zero`) |
| Shifted row (first family above its anchor, `C_Z` for type `rc`) | N | Two reviews (reviews 5 and 11; `C_upper` checked against brute force twice). The entry bound, with multiplicities, is proved in Lean (`keptBound_pair_neg`) |
| Second-family anchor up to the global λ₂ bound (`sec_anchor='l2'`) | N | Two reviews (reviews 5 and 11) |
| Identities nodes replaced by the regular model | N | Two reviews (review 5, structural; review 11, with a byte-identity check of 15 node models) |
| Reserved second family as LP columns (§7) | N | Two reviews (reviews 5 and 11) |
| Exact checker and replay (`graded_cert`, `graded_driver`, `graded_verify`) | N | Code audit (§8, review 6); one verifier hole fixed. An independent checker written from this section alone verified every certificate of the 3.99 corpus (4,652 roots, 4,196,879 boxes; 2026-09-29), and rejected 17 of 18 forged certificates. The accepted forgery has no effect on the bound, and `graded_cert` rejects it. The mutation test rejected all 133 input and dual perturbations ([independent checks](notes/independent-checks-2026-09-29.md)). **Formalized**: the Lean transliteration `Cert.checkLeaf` is proved sound (`Cert.checkLeaf_sound`). Run in Lean, it accepts every outside certificate (87,424 boxes) with values equal to `graded_cert`'s, and six certificates are verified by kernel evaluation. The proof required nonnegative family counts, which `graded_cert.Leaf` asserts |
| Reservation split of unreserved cases (§8) | N | Two reviews (sieve-majorant-near §8, reviews 7 and 11) |
| First family's second zero in the family row (§6.5, controlled pair) | N | Two reviews (sieve-majorant-near §8, reviews 8 and 11). The entry bounds, including the double zero and the conjugate entries, are proved in Lean (`keptBound_pair`, `keptBound_double`, `zeroTerm_conj`) |
| Two-test near row of the regular model, as a fallback row (§6.6): single test, detector mixture, paired first family | R | Inherited from the 4.30 candidate (two-test foundation §3; near refinements §§3–4). Its embedding as a threshold row has had two reviews (sieve-majorant-near §8, reviews 9 and 11; exact agreement with `build_progress.near` on 300 random boxes). |
| Exterior branches: small (H Lemmas 8.4 and 8.8, Tables 2 and 5 near `λ₁=.1`, H (13.3), X (5.18)) and large | P/R | Certified at 3.99. The small branch uses H's table rows since 2026-09-28 (margins 28% and 36%). |
| Tiny exceptional zero `λ₁≤u₀`: Heath-Brown 1990, Corollary 1 (p. 406), effective `P(a,q)≤q^{3+δ}` | P | Read directly (literature/, 2026-09-28); its hypotheses match the use in §9. Alternative: Xylouris dissertation Lemma 6.2(d), ineffective `q^{3.5+ε}` |
| Join, buffer order, uniform `q₀`, split of the `5η` allowance | R | Order and split written out (§§2, 10); one review (interface closure §§5–6) |

Each of the 4.30 candidate's open interface items now has a written argument
([interface closure](notes/interface-closure-2026-09-29.md); one review, with
the printed statements it cites checked):
* **The empty rectangle** is Xylouris's own case (X p. 36, p. 81).
* **The occurrence route** is the one used. The grouped route is not needed.
* **Actual-zero row realization** is the construction in the note's §4. What
  remains is a line-by-line check that the row generators produce the rows of
  §§6.5–7.
* **The buffer quantifier order** is §10.

The representative used in the Lean outside application concerns only the
formalization. See STATE and FORMALIZATION.

## 12. What the simplification removes

| Removed | Why it is not needed |
| --- | --- |
| Collective envelope (1,517 terminals at 4.30) | The graded rows bound the same crowds directly. On the tested leaves at 3.99 the regular model with graded rows certifies without it. |
| Two-test near row, detector mixtures, paired tests, **on most leaves** | Replaced by the family and shifted rows, which are instances of §6. They need no conductor corrections `C_G,C_Z,E` at `s₁`, apart from `C_Z` in the shifted `rc` row. The replacement is not complete: the row is kept as a fallback (§6.6), because 37 unreserved roots need it at 3.99. These are low-`λ₁` `rr` cells, complex cells at `λ₁≈.44–.48`, `.58–.62` and `.80–.82`, and the reserved pair of 1218–1219. |
| Outside first-block relaxation (`Q=K·I+β11ᵀ`, frozen global residual) | Replaced by the outside family row. The global zero and the local zeros are entries of one Gram form. |
| Hidden-family identities (`distinct`, `same_reserved`, `unhidden`) and separated blocks | These were a repair device for 233 nodes. The regular model of each node's case is valid, and graded rows certify it. |
| Old near-row budget windows and first-dimension special cases | Every near row has the same form (T). |

The removed items carried their own premises:
* X p. 36's intermediate inequality and the collective cohort bounds;
* the frozen block identity and signed features;
* global/local hidden-family bookkeeping.

These premises are no longer needed.

## 13. Reproduction

* **Leaf inputs.** Regenerated from the repository's source trees
  (`computations/graded/graded_leaves.py`).
* **Certificates.** Built by `computations/graded/graded_batch.py` from inputs
  captured while replaying the 4.30 trees. The captured inputs are not
  trusted: the replay regenerates every leaf.
* **Replay.** `python3 computations/graded/graded_verify.py --L 3.99 --inside
  <corpus> --nodes <corpus> --outside <corpus>`. The corpora are
  `computations/graded/corpora/3.99/{inside,nodes,outside}.jsonl.gz`. The two
  large ones are committed in parts under 100 MB.
  `computations/graded/corpora/assemble.sh` rebuilds them and checks their
  SHA-256 ([corpora README](../computations/graded/corpora/README.md)).
* **Exteriors.** `python3 computations/frontier/verify_existing_components.py`.
* **Auxiliary inputs.** `python3 computations/near/code/verify_auxiliary_inputs.py`
  regenerates the polynomial rows, the alias condition X (4.29), the source
  cover and the real first/second exclusion. The replay does not re-run them.
* **Negative test.** `python3 computations/graded/graded_mutation_test.py
  <roots>` perturbs regenerated inputs and certificate duals by 0.1% against
  the proof and checks that the replay rejects each one (README of
  `computations/graded`).

Derivations and failed experiments behind §6 are in
[sieve-majorant-near](arguments/sieve-majorant-near.md). The inherited
components are derived in 4.33,
two-test foundation and
near blocks.
