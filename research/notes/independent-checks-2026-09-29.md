# Independent checks of the 3.99 certificates

Date: 2026-09-29. This note records three checks of the finite part of
[PROOF.md](../PROOF.md) (§§7–8) that do not share checking code with
`computations/graded/graded_cert.py`:
* an independent certificate checker;
* an independent audit of the leaf constants;
* a mutation test of the repository's own replay.

The first two were written by one independent agent. Their code was kept in that
session's scratchpad (`indep_check/`) and was not preserved: the scratchpad has since been
deleted, and no session transcript on the machine contains it (checked 2026-09-30). The
certificate checker has been rewritten and committed; see the
[independent checker](independent-checker-2026-09-30.md). The Lean numeric and row checkers now
check, for every leaf, the quantities of the constant audit (§2 below), except the two-test rows. The mutation test is
`computations/graded/graded_mutation_test.py`.

## 1. An independent certificate checker

**Independence.** `icheck_core.py` was written from PROOF.md §7 alone. It
imports none of `graded_cert`'s checking functions. It rebuilds each leaf's
integer data from the regenerated input and the rows of `graded_leaves.leaf`:
* the objective, far, count and hidden-count data (G, W, cnt, NH), the
  second-family columns, F, first and final;
* each row's d, D, v, Dv, vh, Dvh, vs, Dvs and fam.

That data is cross-checked against `graded_cert.Leaf`.

**What it checks, in exact arithmetic.**
* **Relaxations.** In the first-order relaxation, the costs are `(v-b)₊²/D`
  and the budget is `1-a²/d-Σn(v_f-b)₊²/D_f`. In the tangent cases, the
  costs are `((v-m)₊±h)²-h²` with `((m∓h)²-h²)/d`, and the family terms go on
  the budget side.
* **Exclusions.** A case is excluded only if some row has all costs `≥0` and
  a budget `<0`.
* **Dual feasibility.** On every column (ordinary, hidden, second-family),
  including the free dual `P-M` of the second-family equality.
* **Weak-duality bound.** Computed three ways:
  * exact rational (the rigorous value);
  * PROOF.md's rounding;
  * the builder's rounding, to test exact reproduction.
* **Trees.**
  * The root box end is `⌈√(⌊d·10¹²/S⌋+1)⌉` (now stated in PROOF.md §7).
  * Every split is valid.
  * Coverage is checked three ways: by an integer volume sum, by containment,
    and by locating 2,000 random and box-face points.
* **Records.**
  * Reserve records have three children with the right paths.
  * Second-family splits tile the interval.
  * mu and dz parts have the canonical ranges, and only on the family row.

**Full corpus (2026-09-29).** After the sample below, the checker was run over
the entire corpus, in seven shards (`full_run.py`). **Every root passes:**

| Corpus | Roots | Trees | Boxes | Cases | Exclusions | Exact maximum |
| --- | --- | --- | --- | --- | --- | --- |
| Inside | 2,768 | 3,600 | 3,067,092 | 19,123,142 | 8,336 | .9999998132810006 |
| Nodes | 199 | 349 | 1,042,363 | 9,953,103 | 375 | .9999998223456686 |
| Outside | 1,685 | 1,642 | 87,424 | 321,091 | 719 | .9999942478462506 |

* No failures, no stored-value mismatches, and no dual that needed more than
  the builder's floors.
* The exact maxima are at most 9·10⁻¹⁶ below the stored ones.
* The box totals equal those of the replay (4,196,879).

So every certificate of the 3.99 cover has now been checked by two
implementations that share no checking code.

**Sample.** 62 requested roots and 50 random ones all pass.
* **The requested roots:**
  * 31 inside roots: all the hardest; every dz, mu, reserve and
    second-family split kind; the fallback-row roots 10, 35, 1212 and 2603;
  * 10 node roots: 1251, 1523, 1501, 2397, 2369, 2410, 1808, 1479, 212 and
    1785;
  * 21 outside roots.
* **The requested sample in total:** 136 leaf records, 238 trees, 609,968
  boxes, 5,366,785 cases and 425 exclusions.
* **Random sample:** 25 more inside and 25 more outside roots, with 63 trees
  and 36,067 boxes.

| Comparison with the stored records | Result |
| --- | --- |
| Box counts, every tree and root | Equal |
| Stored maxima, every tree and every split, reserve, mu or dz parent | Reproduced exactly |
| Stored per-box values | 0 mismatches |
| Duals that need more than the builder's floors | 0 |
| Exclusions that satisfy the strict rule | All 425 |
| Exact maxima vs stored | 0–5·10⁻¹⁶ lower, so the stored maxima are conservative |

The worst exact maxima:
* inside root 1416: .9999998132810006;
* node root 2369: .9999991793651958;
* outside root 1990: .9999942478462506.

**Forgeries.** 18 forged certificates were tried; 17 were rejected:
* `Y=0`;
* `Y×0.999`;
* the largest `Z` set to 0;
* a negative dual;
* a float dual;
* a dropped case;
* flipped orders;
* a split point on a box boundary;
* swapped children;
* a dual case relabelled "excluded";
* `first+1`;
* `G₀+10⁻⁷`;
* `M` raised on a leaf with second-family columns;
* `P` set to 0 there;
* halved `Z` on the fallback-row leaf 35;
* halved `Z` on the rc leaf 1146;
* a missing mu part;
* a widened mu range.

The one accepted forgery sets a nonzero `M` on a leaf without second-family
columns. That equality row is empty, so the forgery has no effect on the
bound, and `graded_cert` rejects it by assertion.

The strict exclusion rule is exercised as well. Six leaves contain 22
feasible tangent case-1 cases, with a negative budget and a negative cost.
Claimed exclusions of these were rejected both by this checker and by
`graded_cert.excludable`.

## 2. An independent audit of the leaf constants

The audit uses mpmath at 25–40 digits, from the formulas of PROOF.md
§§2–4 and 6.4–6.5 and X (3.60), (5.19) and (6.20). No repository code enters
the mathematics.

**Kernel and far weights.**
* `H₀=.0374973375696671475` and `A=3.156342`.
* `B_φ` agrees with double quadrature of its definition to `3·10⁻²¹`
  relative.
* The enclosures of `G` (`φ=1/3` and `1/4`), `h`, `C(p,a)`, `w` and `1/w`
  bracket the true values.
* `V` is 175.26640331471829 for the inherited weight and 243.32098105220588
  for the retuned one.
* `2x` is 2.347 (inherited) and 2.261 (retuned), both below `A`.

**38 leaves.** Six are outside, four are nodes and 28 are inside. They
include rc mu parts, dz parts, reserve children, second-family columns and
eleven leaves on the retuned far weight. All 120 of their family, shifted and
graded rows were audited.

| Quantity | Checks | Slack, units of 10⁻¹⁶ |
| --- | --- | --- |
| `G_i` (upper bounds) | 19,616 | 0.00002–0.999 |
| `W_i` (lower bounds) | 19,616 | 0.0001–0.9997 |
| Tail column | 38 | 0.23–0.37 |
| Hidden columns | 2,027 | 0–1 |
| Second-family columns | 698 | 0–1 |
| `F` | 38 | 0.23–2.04 (at most three roundings) |
| `first` | 38 | 0–0.93 |

**Near rows.**
* `D_up` equals `D(0)` to `10⁻¹⁶` relative.
* `I_up` exceeds `I_B` by 0.16–0.28%. This is safe; it comes from the
  cell-wise enclosure.
* `d`, `D` and `D_j` are valid.
* Every feature `v_j` is within one unit of its true bound.
* The rc-pair and dz terms are valid with larger safe-side slack: `1.8·10⁻³`
  and `1.5·10⁻²` absolute, from their Lipschitz and grid margins.
* `C_Z` (root 1088) is on the safe side.

**No value is on the wrong side.** The looseness in `I_up` and the dz term is
margin that could be recovered below 3.99.

## 3. Mutation test of the replay

`graded_mutation_test.py` replays stored certificates with every regenerated
input perturbed by 0.1% in the unfavourable direction. Each mutation below is
applied on its own:
* the far budget;
* the objective;
* the first-family charge, by `+10⁻⁴`;
* the near-row radius `d`;
* the features `v`;
* one dual `Y`.

It also removes the `5η` allowance.

It ran on inside roots 1671, 1320 and 1416: 19 leaves, including the three
tightest of the corpus (up to .9999998).
* Every unmutated leaf passed.
* All 133 mutations were rejected.
* On tight leaves an unfavourable input pushes a box value above 1 (for
  example 1.00027 for the far budget on 1671/1), or breaks a column
  inequality.
* On every leaf, the replay's exact equality with the stored maximum rejects
  any change of the value, favourable or not.

## Limits

* **Leaf inputs.** The checker takes leaf inputs and row features from the
  repository's builders. Only the 38 audited leaves test that data
  independently.
* **Fine grids.** The rc-pair, dz and `C_Z` audits use fine grids: high
  precision, but not rigorous.
* **The fallback row.** The constants of the inherited two-test row were not
  audited here. Review 11 checked that row against `build_progress.near` in
  exact rationals; that check is now redone and committed
  (`computations/graded/two_test_compare.py`,
  [rebuilt checks](rebuilt-checks-2026-10-01.md)).
* **Analytic premises.** They were not examined here. They are the subject of
  reviews 10 and 11, the
  [interface closure](interface-closure-2026-09-29.md) and the
  [source-table audit](source-table-audit-2026-09-29.md).
* **Coverage.** The full-corpus run covers every certificate, but leaf inputs
  still come from the repository's builders (first limit above).
