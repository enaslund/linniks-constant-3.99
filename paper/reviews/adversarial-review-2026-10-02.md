# Second adversarial review of the 3.99 manuscript

This report is copied from the [research repository at commit 32b512b](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/research/notes/adversarial-review-2026-10-02.md). Audit code, raw results, and reproduction commands refer to that repository, which requires access where private.

Date: 2026-10-02. This follows the
[first review](adversarial-review-2026-10-01.md) and the subsequent one-line
positivity correction to Example 8.9(i). The request was to look harder for
an error invalidating the claimed global exponent, not merely to repeat
certificate acceptance.

**Result:** no new counterexample, invalid analytic implication, or omitted
root case was established. This does not establish the global theorem.
In particular, the computations below are not substitutes for the analytic
reduction from Dirichlet zeros to the leaf hypotheses. No further manuscript
change was made in this review.

## Scope and approach

The full manuscript was re-read, including the appendix and verification
claims. The detailed section-by-section checklist in the first report still
applies. The emphasis in this pass was on the conventional arguments outside
the formalized boundary: source hypotheses, the envelope and representatives,
the sieve estimate, conductor and alias corrections, fallback rows, case
realization, exterior regimes, and the order of constants. Relevant arguments
were checked in the repository copies of
[Heath-Brown 1992](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf)
and [Xylouris's dissertation](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/literature/xylouris-2011-dissertation.pdf).

The previous full replay was not repeated. Its 4,196,879 accepted boxes are
previous evidence, not a new result of this pass. Two new checks target
different possible failures:

* an independent numerical calculation of the fallback rows' analytic
  constants, from integrals and a separate transform formula;
* an exact check of the root cover against parent rows extracted directly
  from the paper, importing none of the existing case builders.

## Source hypotheses and analytic attacks

### Sieve diagonal and off-diagonal

The Graham input would be suspect if it required a longer interval than the
sieve cells supply. Heath-Brown (11.13), with his parameter $U=1$, explicitly
gives the needed estimate for $N\ge V$, with $V=z$ here. The lower endpoints
of the cells exceed $z$. This attempted objection fails.

The off-diagonal estimate was checked again at the partial-summation level.
Opening the sieve produces $[d,e]^{-2/3}$, and summing that factor costs
$O(z^{2/3})$. With
$2\vartheta=t_k-1/3-2\varepsilon'$, the normalized error is bounded by
$O(\mathcal L q^{\varepsilon-2\varepsilon'/3})$, which tends to zero for
the stated choice of $\varepsilon$. Growing physical heights of order
$\mathcal L$ cost logarithmic factors only. The requirement that characters
be distinct when sieve weights are present is essential and is imposed in
the row construction.

For the Gram estimate, only an upper bound for the real part of each
off-diagonal entry is needed: its coefficients are nonnegative. An absolute
value bound for the Gram entries is not needed. The safe anchor and the
zero-free annulus apply to the quotient character, including when the
quotient's height is a difference of two entry heights.

### Retaining distant zeros

The paired fallback row cannot retain a second zero at arbitrary height by
silently inserting it into a local-disc formula. It invokes Xylouris's
working formula, Lemma 3.4, instead. His printed statement uses 10 zeros,
but the paragraph following it explicitly permits any fixed number. The
paper's fixed-$N$ use is therefore supported by the source. The height
arguments remain in $R(9l)$, and the retained second zero has parameter at
least the response anchor. No invalid extension was found here.

### Third-family tables and their side conditions

A potentially serious scope issue is the real-first third-family estimate
derived from Xylouris (4.31). The source's derivation needs control of the
additional first-family zero relative to the second family. On the box used
by the manuscript, $\lambda_2\le1.176<1.294\le\lambda'$, so that condition
is met. The complex-first estimate (4.28) does not introduce an extra
assumption $\lambda'\ge\lambda_3$. The source arguments and the required
supremum side conditions were checked separately from the displayed tables.

Likewise, the apparent restrictions $\lambda_2\le\lambda'$ and
$\chi_2^4\ne\chi_0$ in the derivation of Heath-Brown's Table 7 are removed
in the surrounding source argument. They are not unhandled branches of the
paper's parent table.

### Representatives, multiplicity, and family identity

Three different choices of zero must not be confused: a global minimum in
$R(l)$, a height-one representative, and a representative in the smaller
$T^*$ strip. Their roles were checked against the row entries and leaf
constraints.

* The zero-cost disc around 1 lies below $T^*$. Its zeros cannot have smaller
  parameter than the ordinary representative.
* A disc centered at that representative can extend beyond $T^*$. The
  chosen strip boundary separates all omitted zeros to the right of its
  anchor by at least $M$ in normalized height; the fixed-modulus log-free
  count bounds their total error. Heath-Brown's proof of Lemma 6.1 quotes
  Jutila's estimate in precisely the all-characters, fixed-modulus form
  needed for this count.
* The reserved family need not be the global second family. If it is a
  different family, its height-one parameter is at least $\lambda_3$;
  minimality then forces even the global second family's height-one
  parameter to be at least that large. Thus the drop of ordinary bins
  below $\lambda_3$ remains justified. The cap is only
  $\lambda_2\le\nu_*\le\mathrm{hi}_2$.
* Coincident first and additional zeros are handled with multiplicity.
  The pair of identical entries also pays the same-character Gram excess;
  it is not treated as two orthogonal characters.

No missing factor of two or illicit interchange of these representatives
was identified. The finite cover check below does not prove these analytic
facts; they were checked in the written argument.

### First-family cost and paired-row elimination

The negative correction in $J_{\mathrm{new}}$ was re-examined. Its combined
cosine kernel contains

\[
 e^{-\lambda_1t}
 \bigl(e^{-\lambda_1(A+2u)}-e^{-p(A+2u)}\bigr),
\]

which is nonnegative and decreases with $\lambda_1$ when
$\lambda_1\le p$. This justifies the simultaneous height-zero and
left-endpoint bound. Bounding the correction alone would not justify it.

For the paired fallback row, the elimination of its unknown response
correction uses
$2D'\ge\zeta_*\max(m',0)$. Differentiating
$(m'-\tau+u)^2/(D'+\zeta_*u)$ on the relevant positive-part range gives
exactly this condition. The ordinary graph has degree at most two, and the
first-family graph at most one for a nonreal first character, including
order three. Averaging the two vectors does not multiply those degrees.

### Exterior regimes and uniformity

The very small exceptional-zero range remains delegated to Heath-Brown
1990, not to a fixed error estimate divided by a parameter tending to zero.
The rest of the small range has the fixed positive lower endpoint
$u_{\mathrm{exc}}$. The large range uses a fixed safe anchor $1.5$ even
when the actual first parameter grows. The empty rectangle and finite
exceptional moduli are also covered in the assembly.

The count used to choose $M$ is taken up to physical height 2 before the
eventual local-disc radius is selected. The envelope smoothing and buffer
are chosen in the stated order. No circular choice of constants or loss of
uniformity from the number of characters was identified.

## New numerical attack on all 37 fallback rows

The first review's exact row comparison had a shared dependency: both sides
used the same analytic enclosure routines. It checked the translation into
the leaf row, but could not detect a common error in those constants. Also,
these 37 rows are outside the Lean near-row checker.

The new script,
[`fallback_integral_attack.py`](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/computations/audit/fallback_integral_attack.py),
uses the old routines only as targets. Its reference values use 70-digit
quadrature of the defining norms and an integration-by-parts recurrence for
the polynomial Laplace-transform moments. The transform recurrence was
cross-checked against direct complex quadrature at 36 points; the largest
scaled discrepancy was below $4.7\cdot10^{-68}$.

For all 31 single rows, two mixture rows and four paired rows it checks:

* the integral norm against the claimed enclosure;
* the correlation and ordinary/first-family diagonals;
* ordinary features throughout each rational grid from the shift to 3,
  plus special endpoints, and first-family features;
* numerically searched negative-transform maxima;
* for each paired row, its correlation expression over endpoint/midpoint
  choices of both zero parameters, a height grid, local maximization, and
  additional tail probes.

**Result:** all 37 rows passed; 13,438 ordinary feature values were checked.
The smallest ordinary-feature slack was approximately
$2.4028\cdot10^{-8}$, on root 1218. The four paired rows have $s=a$, so
their negative-transform corrections vanish by Condition 2. None of the
searched values exceeded its claimed bound.

The [raw report](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/computations/audit/adversarial_20261002/fallback-integrals.json)
records each row. This is a numerical falsification exercise, **not an
independent interval proof of a supremum over a continuum**. In particular,
nonnegative supremum estimates reported as zero include the limiting value
zero; they are not claims that a maximum was attained in the search.

## New exact check of the root cover

[`paper_root_cover_check.py`](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/computations/audit/paper_root_cover_check.py)
extracts the 58 parent implications from the LaTeX table and reads the
compressed source-cover data. It imports no existing cover validator,
builder, or analytic-constant routine. Exact rational checks verify:

* complete parent and subcell interval coverage for each of the three types;
* that each stored lower bound follows from its printed parent row and the
  trivial lower bound from the first-zero cell;
* coverage of the entire additional-zero range, including the infinite tail;
* complete reservation chains for **both** possible family sizes, followed
  by the unreserved tail;
* sequential specification identifiers and the inside/outside root census.

The [report](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/computations/audit/adversarial_20261002/root-cover.json)
passes with 340 base cells, 478 first-zero cells, 684 gap cases, and 2,768
specifications, yielding 2,768 inside and 1,685 outside roots. It found no
uncovered endpoint, missing reservation size, or stronger-than-parent bound.

This check accepts the printed parent implications as mathematical premises.
It does not independently check the subsequent refinement trees; those were
traversed by the prior full replay and reviewed in the manuscript.

## Remaining limits

The genuine remaining verification boundaries are those listed in section
14 of the manuscript: the conventional analytic deductions, source scopes,
the complete zero-configuration realization, the fallback rows, count-type
integers, exterior realization, and assembly are not all parts of a single
formal global theorem. The new checks reduce two particular shared-code
risks but do not erase that boundary.

Absence of a formal global theorem is not itself an error in a conventional
proof. Conversely, accepted certificates do not establish that their
hypotheses hold for every actual modulus. I cannot identify a defensible
point at which this manuscript fails to prove 3.99 on the evidence found in
this review. It would be inaccurate to report either a refutation or a
complete independent validation.

## Reproduction

Run from the repository root:

```sh
.venv/bin/python computations/audit/fallback_integral_attack.py \
  --out computations/audit/adversarial_20261002/fallback-integrals.json
.venv/bin/python computations/audit/paper_root_cover_check.py \
  --out computations/audit/adversarial_20261002/root-cover.json
```

The fallback check reads the 37 rows from the retained first-review report,
and records that file's SHA-256. The root check records hashes of both its
inputs. Additional source and script hashes are in
[`provenance.json`](https://github.com/enaslund/linniks-constant/blob/32b512bfac76806bbeb99134d5ec4fdf5ec9452b/computations/audit/adversarial_20261002/provenance.json).
