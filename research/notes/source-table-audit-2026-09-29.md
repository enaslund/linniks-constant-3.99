# Source-table audit of the 3.99 case tree

Date: 2026-09-29. This audit checks every printed zero-location number that
the 3.99 case tree uses ([PROOF.md](../PROOF.md) §§5 and 9) against the
printed source. For each number it checks three things:
* its value;
* its scope: the type of `χ₁`/`ρ₁`, the order of `χ₁`, the `λ₁` range, and
  side conditions;
* whether it holds exactly for `q≥q₀`, or only as `c-ε`.

The audit was done by one independent agent. Its scripts were kept in the session
scratchpad (`table_audit/`) and were not preserved. On 2026-10-01 they were replaced by
committed programs that reproduce every result below; see
[rebuilt checks](rebuilt-checks-2026-10-01.md):
* `computations/audit/hb_tables_recompute.py`, which recomputes H's tables and side conditions;
* `computations/audit/printed_tables_check.py`, which compares every used number with the
  printed pages.

The lost scripts were:
* `h_table4.py`, `h_table7.py`, `h_table10.py`, `h_table25.py`;
* `x_tables_gl.py`, `x_table2p3.py`, `x_table67.py`, `x_table8.py`,
  `x_table11.py`;
* `parents_check.py`, `cells_check.py`.

How the numbers were checked:
* transcriptions against `pdftotext` of the printed pages, by script;
* all 818 records of `source_cover.json.gz` (340 roots, 478 cells): every
  `lp` and `source_l2` is supported by a printed row plus the orderings
  `λ′,λ₂≥λ₁`;
* H's table roots recomputed from his printed parameters;
* X's rows reproduced from his printed sup bounds `C`.

H = Heath-Brown 1992 (retained copy); X = Xylouris, dissertation.

**Result.** Nothing could invalidate the 3.99 case tree.
* Every number matches the printed source, or is weaker in the safe
  direction.
* Every input is used inside its printed scope.
* Each holds exactly for `q≥q₀`, or `ε` is subtracted explicitly.

## Inputs

"Exact" means the printed value lies strictly on the safe side of the
`ε=0` threshold, so it holds once `ε` is below the margin.

| Input | Code | Printed source | Scope | Convention |
| --- | --- | --- | --- | --- |
| H Table 4 (`λ′`, type rr), 24 rows | `cover_v5.py` `H_PRIME`; `case_cover.py` (2.195, 1.832, 1.63) | H p. 44; meaning of a row, p. 43 | rr only, used when the cell's top is `≤t`. A real `ρ₀` is covered by H Lemma 8.2 (2.427 > 2.293) | Exact. The recomputed (8.7) roots exceed the printed values by 4e-5 to 9e-4. (8.6) and (8.8) hold |
| H Lemma 8.4, 1.294 | `case_cover.py` | H p. 43 | rr | Exact (root 1.29465) |
| H Table 7 (`λ₂`, rr), rows .12–.745 | `cover_v5.py` `H_SECOND`; `case_cover.py` (2.01, 1.42, .92) | H p. 48; Lemma 8.7, p. 47 | rr, valid for all `λ₁≤B` (increasing left side). `χ₂⁴=χ₀` is covered by Table 6, and `λ₂≤λ₀` is redundant. The .10 row, which X p. 24 excepts, is correctly omitted | Exact. The roots exceed the printed values by 1.5e-4 to 8.6e-3 |
| H Lemma 8.8, .745 | `case_cover.py` | H p. 48 | rr | Exact (root .74552) |
| X Table 3 (`λ′`, type rc), 12 rows .66–1.099 | `cover_v4.py`; `case_cover.py` | X p. 45 | Order of `χ₁` in {2,3,4}, with `χ₁` or `ρ₁` nonreal; rc is order 2 | Exact: strict contradiction (X pp. 43–44); all rows reproduced |
| X Table 3, row .86 → 1.35 | `poly_rows.py` | X p. 45 | Nonreal `χ₁` of order 3 or 4 | Exact |
| X Table 6 (`λ₂`, rc): .93, .82 | `case_cover.py` | X p. 53 (Fall 7, order 2) | Yes | Exact (reproduced) |
| X Table 2′ (`λ′`, nonreal `χ₁`), 12 values 1.36…0.827 | `case_cover.py`; `cover_v4.py` | X p. 62 | "`χ₁` or `ρ₁` complex", used only for nonreal `χ₁` | Exact (all 20 rows reproduced) |
| X Table 7 (`λ₂`, nonreal `χ₁`): 1.04, .85, .79, .74 | `case_cover.py` | X p. 53 | All cases | Exact. The Table 5 and Table 4 rows behind it were reproduced |
| H Table 10, row .70 → .704; H Lemma 9.4, .702 | `case_cover.py` | H p. 57; Lemma 9.4, p. 56 | Yes | Exact. H shows failure at the printed value plus `δ`; the left side was recomputed `<0` for rows .66–.702 |
| X Lemma 4.5 / Table 11: `λ₁>.44` (nonreal `χ₁`), `>.628` (rc) | cover starts, `cover_v5.py` | X pp. 60–61 | The minimum over orders `≥3` is .440; order 2 gives .628 | Exact (strict). Roots .4460, .4934, .4781, .4988, .6295 reproduced |
| H Lemma 10.3, `λ₃≥6/7-ε` | `triple_inputs.py`, .857 | H p. 67 | All cases | `c-ε` handled: `.857<6/7` |
| X Table 8 (`λ₃`), 6 rows | `triple_inputs.py` | X p. 55, "alle Fälle" column | Applied to every type except rr. It never fires for rc, whose cells start at .628 > .62. A row means "`λ₁≤bb`" | Exact (strict; Fall 1 column reproduced) |
| X Table 10 (`λ₃`, rr) | `triple_inputs.py` | X p. 55; proof pp. 58–59 | rr, cell inside the printed interval | Exact. Thresholds 1.1768 (capped at 1.176), 1.0558, .9524 reproduced |
| X (4.28), `γ=5/4`, constant 7/6; alias condition (4.29) | `triple_inputs.py`; `alias_check.py` | X pp. 56–57 | Nonreal `χ₁`, `λ₁∈[.44,.85]`. The cap `λ₂≤h` is valid, since the reserved family's zero lies in `R(l)` | Margin `10⁻⁵f(0)` |
| X (4.31), `γ=26/25`, constant 9/8 | `third_refine.py` | X pp. 58–59 | rr, `λ₁∈[.44,.80]`, `λ₂∈[.44,1.176]` | Margin `10⁻⁵f(0)` |
| H Table 5, row .10: 2.83 | `small_exception_tables.py` | H p. 46 | rr, all `λ₁≤.10`; `λ₂≤λ₀` redundant | `c-ε` handled (−.001); also exact (root 2.8458) |
| H Table 2, row .10: 4.96 | `small_exception_tables.py` | H p. 39 | Yes | `c-ε` handled; also exact (root 4.9636) |
| `α=1.09` (H Lemma 8.4, `2-ε`; Lemma 8.8, `12/11-ε`) | `small_exception_tables.py`; `small_exception.py` | H pp. 43, 48 | `λ₁≤.2`, not for tiny `λ₁` (the `u₀` branch) | `c-ε` handled: `1.09<12/11` |
| Heath-Brown 1990, Corollary 1 | PROOF.md §9 | QJM 41, p. 406 | `β₀≥1-1/(3 log q)`, `ψ` real and not necessarily primitive, effective `η(δ)`, `P(a,q)≤q^{3+δ}` | Effective |

## Findings

1. **Thin but positive margins.** H states no rounding convention for Tables
   4 and 7, so their exactness rests on the recomputation. The tightest rows:
   * Table 4, row 1.05: root 1.43904 against the printed 1.439;
   * Table 7, row .20: 2.01015 against 2.01;
   * Table 7, row .55: 1.00036 against 1.00.

   All are strictly on the safe side. PROOF.md §5 now cites them.
2. **Reading of X Table 3.** X's Lemma 3.9 parameters (`k₁=2k`,
   `k₃=2(k²+3/4)`, X p. 44) mean that `C₁` bounds the whole term `2·sup`.
   With that reading every row reproduces. Under the other reading, rows .62,
   .66, 1.02 and 1.099 would fail. The printed parameters make the reading
   unambiguous.
3. **PROOF.md §5 text, now fixed.**
   * The .44/.628 bounds come from X Lemma 4.5 alone.
   * H Table 10 is now named among the cover sources.
   * `α=1.09` is now listed among the `c-ε` inputs.
   * X Tables 9 and 10 are printed on p. 55; pp. 55–59 is their proof.
4. **Source errata, not used by the code.** Avoid these in future work.
   * **X Table 9, last row** (`λ₁∈[.74,.78]`, `λ₂≤.78 ⇒ λ₃>.996`) does not
     reproduce. X's own monotone scheme gives about .966, so this is
     probably a misprint. The other 12 rows reproduce.
   * **H Table 8, row .66:** .783 should read .738 (noted by X p. 43).
   * **H Lemma 8.3** says "providing that `ρ₁` is complex"; it should read
     `ρ₀` (X p. 23 confirms).

## Not audited here

**Printed but not re-derived.**
* X's sup bounds (the `C` values of Tables 2′, 3 and 4–7, and of (4.34)) are
  taken as printed. The (4.29) alias condition is regenerated by the code.
* X Table 8's Fall 2–4 column (rows .52 and .54 → 1.320 and 1.243) is
  accepted under X's strict convention but was not reproduced.

**Density constants:** H (13.3) and X (5.18) (`c₁=.057`, `c₂=.1554`,
`K=.1821`, `A`), used by the small branch.

**Repository deductions, not printed numbers.** These are premises of type
[R] in PROOF.md §11:
* the degree-5 real rows' `1/108` conductor saving
  ([real conductor rows](../arguments/real-conductor-rows.md));
* the rr row `λ₂>.762` (`new_positivity.py`);
* the polynomial rows;
* the conductor coefficients `φ=1/3` and `1/4`.
