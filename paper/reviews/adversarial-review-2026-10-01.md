# Adversarial review of the 3.99 manuscript

This report is copied from the research repository (commit 32b512b). Its audit code, raw results and reproduction commands are in this repository at the same paths (`computations/`), and the commands run from this repository's root.

Review of commit `22c11027d946951ef5ec67be80f85250f73a0dad`, begun
2026-10-01 and completed 2026-10-02, in response to a request to find errors in the entire paper and
identify any failure to prove the claimed exponent. The review covers the
80-page manuscript: the main source, Sections 1–15, and both appendices in
`sections/16-appendix.tex`. The flattened upload source was regenerated into
a temporary file and agrees exactly with `paper/dist/linnik399.tex`.

**Assessment:** one definite local mathematical error was found, in Example
8.9(i). It does not invalidate the threshold proposition or its use in the
leaf programs. No counterexample to a main proof step or missing case in the
deduction of 3.99 has been identified by this review. This is an audit result,
not an independent proof of the global theorem.

The manuscript and its existing certificates were not edited. New source
checks are in
[`adversarial_source_checks.py`](../../computations/audit/adversarial_source_checks.py).
Fresh numerical evidence is retained in
[`adversarial_20261001/`](../../computations/audit/adversarial_20261001/);
the [aggregate report](../../computations/audit/adversarial_20261001/summary.json)
records the counts, maxima and file hashes.

## Confirmed error: a missing sign assumption in Example 8.9(i)

Location: [`08-near.tex`, lines 362–369](../../paper/sections/08-near.tex#L362),
printed page 41, immediately following Proposition 8.8.

The example assumes that there are $N$ identical features $v$, identical
diagonals $D>0$, and $v^2>d>0$, and concludes

\[
N\le\frac{D}{v^2-d}.
\]

The preceding proposition explicitly allows real, possibly negative features.
Its hypothesis is

\[
\left(\sum_j a_jv_j\right)_+^2
\le\sum_jD_ja_j^2+d\left(\sum_j a_j\right)^2
\qquad(a_j\ge0).
\]

Setting all $a_j=1$ gives $(Nv)_+^2\le ND+dN^2$, whereas the example
writes $(Nv)^2\le ND+dN^2$. Removing the positive part requires $v\ge0$.

An exact counterexample is

\[
N=2,\qquad v=-1,\qquad D=1,\qquad d=\tfrac14.
\]

For every $a_1,a_2\ge0$, the left side of the quadratic hypothesis is zero,
so the hypothesis holds. Also $v^2>d$. But the claimed conclusion is

\[
2\le \frac1{1-1/4}=\frac43,
\]

which is false. The threshold proposition itself remains valid: $\tau=0$
makes its left side zero and its right side one.

**Repair:** require a positive feature $v>0$, or replace the hypothesis
$v^2>d$ by $(v_+)^2>d$. Section 15 already says “positive feature” in
the corresponding observation. Corollary 8.10 permits nonpositive features
to be replaced by zero; the leaf builders do this. The proof of Proposition
8.8 retains the positive part and does not rely on the erroneous example.
Consequently this counterexample does not demonstrate a failure of the
claimed Linnik bound.

## Section-by-section audit

| Part | Main issues examined | Result |
| --- | --- | --- |
| §1, statement and introduction | Uniformity in the residue class; eventual bound versus all moduli; claims about the computational/formal scope | No obstruction identified. The theorem asserts existence of constants, without an explicit numerical threshold. |
| §2, notation | Physical versus normalized height; successive selection after removing entire conjugate families; the additional occurrence; multiple zeros and ties; inside/outside windows | The conventions support the subsequent counts. A real character and a nonreal conjugate pair are counted differently, as required. |
| §3, published inputs | Conditions 1 and 2; conductor coefficients; shrinking explicit-formula discs; permissible heights; one-zero selection in density estimates; exceptional real zeros | Compared the relevant statements and supporting arguments with the local primary-source PDFs. No material scope mismatch found. |
| §4, detection | The 16-step kernel, 31 triangular pieces, support above exponent 3, individual zero occurrences, prime rather than prime-power detection | $A=3.156342>3$; Xylouris's printed (3.57) allows the finite triangular combination used. The positive weighted prime sum gives the stated eventual prime. |
| §5, costs | Autocorrelation majorization; smoothing; finite anchors; disc enlargement; distinguished-zero subtraction; negative correction in the new first-family bound; hidden first-family costs | No invalid inequality found. In particular, the new first-family estimate bounds the distinguished term together with its correction through a nonnegative cosine kernel. |
| §6, far density | One zero per character; the two profiles; tail monotonicity; selecting $T^*(q)$; total error over an increasing number of characters | The representatives have physical height at most 1. The selected strip and $A>2x$ justify the uses of density and tail bounds. |
| §7, zero location | Printed table ranges and endpoint margins; real/nonreal types; conductor saving; all principal aliases of the degree-five polynomial; injectivity of the complex matching map; additional-zero multiplicity; third-family side conditions | Fresh table, polynomial and side-condition checks pass. No invalid application was found in the reviewed reduction. New exact/interval checks also confirm the signs behind HB Tables 4 and 7. |
| §8, graded lemma | Uniform Gram bounds; same-character pair excess; sieve majorization; imprimitive Burgess; Abel summation; response errors; threshold optimization; rounding normalization | The local error is in Example 8.9(i). The main quadratic lemma, threshold proof, and zero-form passage survived the checks described below. |
| §9, concrete near rows | Safe versus response anchors; global family bounds versus local representatives; repeated characters in sieve rows; conjugate/second-zero pairs; discarded negative terms; two-test, mixture and paired fallback rows | No hypothesis violation identified. All 37 fallback rows pass the separate comparison run, including every certificate interval. |
| §10, certificates | Complete threshold-box cover; both tangent alternatives; negative tangent costs; floors/ceilings; nonnegative duals; signed equality multiplier; exclusion rule | The mathematical weak-duality argument was checked. Full replay and the independent exact checker agree on all 4,196,879 boxes. |
| §11, case tree | Parent coverage; λ′ and reservation subdivisions; the reserved family need not be global family 2; count bound below family 3; ordinary/hidden/reserved columns; tail masses; realization | No omitted configuration or double charge identified. The replay regenerates leaf data while traversing and checking the source tree. |
| §12, exteriors | Empty rectangle; tiny exceptional zero; fixed positive cutoff for small-zero estimates; monotonicity on the two small pieces; large first-zero leaf | The small-piece intervals and the large-leaf checks pass. The tiny branch agrees with HB 1990 Corollary 1 for a possibly imprimitive real character. |
| §13, assembly | Dependence of constants; uniform $q_0$; unbounded character count; prime-detection margin; finite exceptional moduli | No circular choice or uncovered regime identified. |
| §14, verification | What exact certificates, interval arithmetic and Lean actually establish; shared leaf generation; separate fallback-row checks; access to the data | The paper explicitly distinguishes conditional/formal components from conventional analytic arguments. A passed leaf checker alone is insufficient for the global theorem. |
| §15 and appendices | Limitations of the relaxation; printed location rows; fixed numerical constants | No further mathematical error identified. Section 15 correctly includes the sign assumption missing in Example 8.9. |

## Attempts to break the analytic reduction

### Individual zeros versus selected representatives

An obvious possible failure is to substitute a bound for one selected zero
for the explicit formula's sum over all zero occurrences. Section 5 does not
make this substitution: the autocorrelation envelope bounds the sum of
absolute contributions of a character, including multiplicities, and the
selected representative only determines a valid anchor/cost. The far-density
budget charges one selected zero per character. These are separate steps.

For a character with a zero in the prime window, its representative exists
and has parameter at most $C_P$. The disc centered at 1 used for its cost
has height below $1/2\le T^*$; therefore a smaller-parameter zero in that
disc would contradict the definition of the representative. This closes the
most direct attempted objection to the localized envelope.

### Changing anchors and losing zeros

The ordinary near-row anchor can exceed the global lower bound for the
second family. That would be unsafe without control of omitted zeros. The
paper chooses a strip boundary $T^*$ separated from every zero with
parameter at most 3. A zero to the right of an ordinary response anchor is
either ruled out by minimality inside the strip or separated from its
representative by at least $M$ in normalized height. Its possibly negative
transform is then included in the response error.

The reserved-family entries use a different, globally justified anchor,
involving `source_l2`. Treating the reserved height-one minimum as a global
zero-free bound would be an error; the current formulas do not do so.

For an outside first family, the global zero can have physical height of
order $\log q$. The graded lemma allows $\Gamma\le\mathcal L/3$, rather
than requiring fixed physical heights. The zero-free annulus gives
$\mathrm{SA}(s_1,2l+1)$, and the actual entry heights are at most $l\le\mathcal L/10$. Thus this growing-height use is within the stated scope.

### The new first-family charge

It is not legitimate to replace an isolated oscillating correction by its
value at height zero without a sign argument. The proof of $J_{\rm new}$
supplies one: for $\lambda_1\le p$, the combined kernel contains

\[
e^{-\lambda_1t}
\left(e^{-\lambda_1(A+2u)}-e^{-p(A+2u)}\right)\ge0.
\]

Consequently the cosine transform is bounded above by its value at zero,
and this value decreases with $\lambda_1$. The argument remains valid when
$B_{\phi_1}(p)-\alpha C(p,a)$ is negative. A negative correction alone
does not refute the charge.

### Sieve off-diagonal terms

Opening the sieve square creates $[d,e]$, whose power must be accounted
for correctly. The paper's use of Burgess at every partial-summation
endpoint gives

\[
\mathcal L^2q^{1/9+\varepsilon-t_k/3}[d,e]^{-2/3}.
\]

Summation over $d,e\le q^{\vartheta_k}$ costs
$O(q^{2\vartheta_k/3})$, not $O(q^{2\vartheta_k})$. After the
$1/\mathcal L$ normalization the exponent is
$\varepsilon-2\varepsilon'/3<0$. Sieve rows require distinct characters,
so no principal quotient is passed through this off-diagonal Burgess step.
Rows containing repeated characters have zero sieve weight and pay their
pair excess instead.

### Location bounds and aliases

The degree-five real-first row separates orders 2, 4, 5 and 10 from the
generic conductor calculation. Its saving $1/108$ follows by maximizing

\[
\frac18-\frac\theta{12}
+\Sigma\min\left(\frac13,\frac14+\frac{3\theta}4\right)
\]

at $\theta=1/9$, using $\Sigma\ge1/9$. The complex-first matching argument
was checked for possible collisions and for accidental use of an already
charged axis coefficient. A collision forces equality of the two conjugate
families, which its hypotheses exclude. A finite-group diagnostic also
checked 50,032 character pairs; that diagnostic supplements the algebraic
argument and is not its proof.

For third-family refinements, the side conditions of Xylouris (4.29) and
(4.34) were regenerated on the parameter boxes actually used. The latter
check covers the slightly larger interval ending at 1.18, which contains
the source's 1.176 endpoint.

### Two-test fallback rows

The 37 fallback rows are not covered by the graded near-row formalization,
so they were reviewed separately. The checks included principal quotient
degrees, first-family diagonals, the norm of the mixed detector, and the
monotonicity required to eliminate the paired first-family parameter.

For the paired row, retaining the additional zero at potentially large
height relies on Xylouris's working explicit formula (Lemma 3.4), not on
silently enlarging a local disc. The current text explicitly uses that
formula. All four paired rows have a nonreal first character. The fresh
comparison found the stated monotonicity margins positive.

### Exceptional zeros and constants

The argument does not take a fixed-tolerance error estimate all the way to
$\lambda_1=0$. The tiny range is handled separately by HB 1990, Corollary 1
(printed page 406, also inspected as an image because PDF text extraction
drops its displayed formula). The remaining small interval has a fixed
positive lower endpoint $u_{\rm exc}$; its errors are chosen after that
endpoint. Its envelope anchors are fixed, even though its repulsion bound
$1.09\log(1/u)$ varies.

The finite anchor set, smoothing and per-character zero count do not depend
on the later disc radius in a circular way. The separation count $K_0$
uses physical height 2, which already covers every later admissible disc
around an ordinary representative. Summed envelope errors are bounded by
the far-density estimate, not by multiplying a fixed error by $\varphi(q)$.

## Fresh computation results

The replay is run with assertions enabled, regenerating leaf programs from
the source tree. It feeds those leaf programs and the stored certificates
to the already committed independent checker. This is a new execution of
that checker, not a claim that its implementation was written during this
review or that its shared leaf generator is independent.

Both full replays completed successfully, with zero rejected certificates
and zero disagreements between the checkers: 4,453 roots, 5,591 certificate
trees, 4,196,879 boxes, and 29,397,336 relaxation cases (29,387,906 dual cases
and 9,430 exclusions). The maximum is
$9999998223456687/10^{16}=0.9999998223456687$, at inside tree
2432_1. The inside run took 1,792 seconds and the outside run 377 seconds,
overlapping in time. The compressed per-tree stats are retained alongside
the reports.

| Check | Fresh result |
| --- | --- |
| Inside corpus, including supplementary nodes | PASS: 2,768 roots, 3,949 certificate trees, 4,109,455 boxes; maximum $9999998223456687/10^{16}$. |
| Outside corpus | PASS: 1,685 roots, 1,642 certificate trees, 87,424 boxes; maximum $9999942478462508/10^{16}$. |
| Printed source tables | PASS: 315 uses, with 303 exact matches and 12 safe-direction differences; no out-of-scope use found by the audit. |
| Complex polynomial rows | PASS: all 94 regenerated, comprising 25 second-family and 69 additional-zero rows. |
| Alias conditions | PASS: interval checks of X (4.29) and X (4.34). |
| Independent polynomial diagnostics | PASS: 50,032 finite-group pairs, including 7,504 with principal aliases; direct quadrature on 14 selected rows at 65 digits. Sampling is diagnostic, not exhaustive interval proof. |
| Two-test comparison | PASS: all 37 rows (31 single, 2 mixture, 4 paired); 1,079 distinct certificate intervals and 11,211 additional sampled/edge boxes; 13,373,472 column comparisons; all 707 deliberate invalid perturbations detected. |
| HB Tables 4 and 7 | Floating recomputation agrees with the paper. In addition, the new script checks 24 Table 4 contradiction signs exactly, its 23 subsequent-row side-condition pairs exactly, and all 17 Table 7 contradiction signs with 60-digit intervals. The Table 4 first row still uses the published Table 3 fallback, as the paper says. |
| Small exceptional range | PASS: independent 60-digit interval margins $0.030488702860959985\ldots$ and $0.038118185336160880\ldots$, both above 0.0304. |
| Large first-zero range | PASS: regenerated graded leaf; 36 boxes; maximum $9966813270344512/10^{16}$; native Lean certificate, numeric and row checkers accept it. |

The supplemental HB floating-point program completed its calculations and
wrote its JSON report, then raised a `ValueError` while printing the output
path because the review redirected it outside the repository. The completed
JSON was inspected; this path-formatting failure does not concern the
mathematics. The new exact/interval sign checker has a normal `--out` option
and completed successfully.

## Limits of this conclusion

No fatal gap was found. It would be incorrect to convert that statement
into either “3.99 is disproved” or “this review proves 3.99.” The analytic
reduction, source statements and case realization are mathematical premises
of the finite checks. This review examined their conventional arguments,
but did not independently reprove all of Heath-Brown, Xylouris, Burgess,
Graham and Jutila, or rebuild the entire Lean development and all numerical
Lean checks from source. The manuscript itself describes the formalization
boundary; the absence of a global Lean theorem is not a counterexample to
its conventional proof.

Likewise, the small worst-case numerical margin is not itself evidence of
an error. Acceptance uses exact integer inequalities after conservative
enclosures. The important remaining possibility is an analytic or semantic
mistake missed in the reduction to those integers, not ordinary floating
roundoff in the final dual comparison. No such mistake was established in
this review.

The data-availability statement still calls for a public versioned archive
before submission. The certificates are available to this repository review;
external availability is a reproducibility issue, separate from whether the
mathematical argument is valid.

*[Added 2026-10-02: the certificates, programs, reports and Lean sources are now public in this repository; see [computations/README.md](../../computations/README.md). The paper's §14 cites it.]*

## Reproduction

Run from the repository root, using its existing virtual environment. The
full replay takes substantial time. The output directory below is separate
from the historical reports. For repeated runs, use a fresh directory or
remove the old stats files, since the checker appends to them.

~~~sh
REVIEW399_DIR=/tmp/linnik399-adversarial
mkdir -p "$REVIEW399_DIR"
bash computations/graded/corpora/assemble.sh 3.99

.venv/bin/python computations/graded/graded_lean_export.py \
  --kind inside --roots all --L 3.99 --jsonl --workers 10 \
  --checker "python3 $PWD/computations/audit/independent_cert_check.py --stats $REVIEW399_DIR/inside-stats.jsonl" \
  --out "$REVIEW399_DIR/inside-replay.json"

.venv/bin/python computations/graded/graded_lean_export.py \
  --kind outside --roots all --L 3.99 --jsonl --workers 4 \
  --checker "python3 $PWD/computations/audit/independent_cert_check.py --stats $REVIEW399_DIR/outside-stats.jsonl" \
  --out "$REVIEW399_DIR/outside-replay.json"

.venv/bin/python computations/audit/printed_tables_check.py \
  --out "$REVIEW399_DIR/printed-tables.json"
.venv/bin/python computations/graded/two_test_compare.py \
  --workers 2 --boxes 300 --seed 20261001 \
  --out "$REVIEW399_DIR/two-test.json"
.venv/bin/python computations/audit/adversarial_source_checks.py \
  --out "$REVIEW399_DIR/source-signs.json"
~~~

The supplementary calls imported the following functions, writing their
results to the temporary directory instead of replacing historical reports:

* The complex-location check used
  <code>poly_rows.verify_polynomial_table()</code>,
  <code>alias_check.check()</code> and <code>x434_check.check()</code>, with
  <code>computations/core/code</code> on the Python import path.
* The independent diagnostic used
  <code>independent_polynomial_checks.aliases()</code> and
  <code>independent_polynomial_checks.refs()</code>.
* The small-branch check used
  <code>independent_small_tables_check.main()</code> after redirecting its
  module-level <code>OUT</code> to the temporary directory.
* The large-branch check used <code>graded_large.main()</code> with
  <code>--lean</code>, redirecting both <code>OUT</code> and
  <code>LEAN_OUT</code>. This reused the existing compiled Lean checkers; it
  did not rebuild them.
* The supplemental floating source-table recomputation used
  <code>hb_tables_recompute.main()</code> at its default 30-digit precision
  and 45-digit convergence recheck, with <code>OUT</code> redirected. Its
  final path-printing exception is described above.
