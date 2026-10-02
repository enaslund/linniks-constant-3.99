# Rebuilt checks: Heath-Brown's tables, printed transcriptions, the two-test row (2026-10-01)

**Why.** Three checks that the paper cites were made on 2026-09-29 by scripts left in session
scratchpads, which have since been deleted:
* the recomputation of Heath-Brown's Tables 4 and 7 and their side conditions (paper §7.1), and
  of the rows .10 of his Tables 2 and 5 (§12);
* the comparison of every printed number with the source pages (census and status tables);
* the exact comparison of the two-test row with the 4.30 implementation (§14).

See the [source-table audit](source-table-audit-2026-09-29.md) and reviews 9 and 11 in
[sieve-majorant-near](../arguments/sieve-majorant-near.md). At the author's request each was
rewritten by a fresh agent and committed, as was the certificate checker the day before
([independent checker](independent-checker-2026-09-30.md)). All three pass, and all are rerun
here with identical results.

## Heath-Brown's tables (`computations/audit/hb_tables_recompute.py`, about 60 s)

**Method.** The script implements HB's formulas from the local copy of his paper:
* Lemma 7.1's test function, with `θ` from Lemma 7.5;
* Table 4 from (8.7) of Lemma 8.3, with the side conditions (8.6) and (8.8) as HB prescribes them;
* Table 7 from (8.11) of Lemma 8.7, with `k = 0.98 − 0.15B` and `θ = 1`;
* row .10 of Table 2 from Lemma 6.3, and of Table 5 from Lemma 8.5.

It uses mpmath at 30 digits, with the key roots confirmed at 45. A separate double-precision
quadrature confirmed them to about 1e-13.

**Results.**
* **Roots.** All 24 roots of Table 4 and 17 of Table 7 exceed the printed values. Each printed
  value is the root rounded down: this is HB's unstated convention.
* **Closest cases.**
  * Table 4, row 1.05: 1.439038 against 1.439.
  * Table 7: row .20, 2.010146 against 2.01; row .55, 1.000358 against 1.00.
* **Side conditions.**
  * (8.6) is the tightest. Its slacks are 3.83e-6, 3.78e-6 and 2.34e-6 at rows 1.05, 1.15 and
    1.294.
  * (8.8) has slack at least 0.135.
  * For the row (0.3, 2.293) they need not hold; Table 3's row .30 (root 2.436310 ≥ 2.43)
    covers it.
* **Rows .10.** Table 2 gives 4.963551 and Table 5 gives 2.845770.
* **Paper.** All three of the paper's claims reproduce digit for digit. The paper's phrase "the
  closest cases" now names the closest case in each table: across both tables, two rows of Table
  4 are closer than row .20 of Table 7.
* **Used values.** Every value that the code and `tab:parents` use is at most the recomputed
  root of its row.
* **Misprints in rows not used.** In Table 2, rows .07 and .16 have their printed `λ` digits
  transposed (0.895 for 0.985, 0.952 for 0.925).

## Printed numbers against the pages (`computations/audit/printed_tables_check.py`, under 1 s)

**Method.**
* It parses the 16 tables used (HB and Xylouris) from `pdftotext -layout` of the source pages.
* It checks the parsed rows against stored transcriptions.
* It matches 32 printed lemma statements, with their constants and ranges.
* It compares every number the proof uses, in the code and in the paper, with its printed value
  and scope: type, order of `χ₁` and range of `λ₁`.

**Results.**
* **Uses.** Of 315 uses, 303 are equal and 12 are weaker in the safe direction: the explicit
  `ε`, 0.857 < 6/7, `α = 1.09`, and one side condition checked on a larger box.
* **Cover.** All 818 source-cover records and all 58 parent rows are supported. `tab:parents`
  equals the code.
* **Mutation test.** All 18 deliberate corruptions are caught.

**Findings.**
* HB says (p. 48 of the local copy) that the estimates of his §8 are not proved for extremely
  small `λ₁`. The paper stated this only for Lemma 8.8. It now states it for all of
  `inp:rrtables` and for §12's rows, every use being on a range bounded away from 0.
* **Misprints in the sources, none used:**
  * H Lemma 8.3 has "ρ₁ is complex" for ρ′ (as X p. 23 notes);
  * H Table 8 row .66 reads 0.783 for 0.738 (X p. 43);
  * H Table 7 row .10 fails when `χ₂⁴ = χ₀`. It is not used.
* **Not checked.** HB 1990, Corollary 1: the local copy is a scan without displayed formulas.

## The two-test row (`computations/graded/two_test_compare.py`, 2.4 min on 16 cores)

**Method.**
* It scans the corpora and replays the 37 roots whose leaves use the row:
  * 31 with a single test, 2 with a mixture, 4 paired;
  * all inside, each leaf with one `old` row;
  * every replayed leaf equals its corpus record.
* It compares the row as `graded_cert` uses it with the 4.30 implementation of the same
  inequality: its builder `build_progress.near` and its checker `verify_progress.scenario`.
* The comparison is exact, using rewrites of the committed sources with exact division.
* It runs on every interval the 37 certificates use (1,079 intervals from 23,341 boxes) and on
  11,211 seeded random intervals, with first order and both tangent cases on each: 36,870
  box-case pairs.
* For the tangent cases the reference is the tangent rule applied to the exact 4.30 inequality,
  since the 4.30 code had only the first order.

**Results.**
* **Equality.** The graded costs and budgets equal the 4.30 ones times `S/D`, as exact rationals.
* **Rounding.** It is always safe, with gaps under 3e-16.
* **Data.** The row's integers (`d`, `D`, `D_f`, `v_f`, `v₂`, the 13,321 bin features) regenerate
  identically from the 4.30 interval routines.
* **Negative test.** All 707 one-unit perturbations are detected.
* **Paired form.** Margins 0.186–0.296, `B ≥ 0`.

**Scope.** The partner is the 4.30 pipeline's own code: a separate code path, but its constants
come from the same interval routines. The paper now says this, in place of "an independent
implementation on sample boxes", and adds the comparison as item (5) of §14.
