# Deep dive: the finite case tree for $.1\le\lambda_1<1.5$ and the join

Component of the paper "Linnik's constant satisfies $L\le 3.99$".
Scope: PROOF.md §§5 (how it feeds the tree), 7 (leaf data only), 8 (case tree and leaves),
10 (join). The analytic content of the zero-location rules, of the near rows (§6) and of the
certificate checker (§7) is covered by other agents; here each such rule is stated as a
*premise* and it is checked that the code applies it within its stated scope.

Repository state examined: `master` at `3e63657` (clean). Everything below that is marked
**[checked]** was re-verified by me with code in this session (scripts listed in §9).

---

## 0. Summary

* The case tree is a finite set of **specifications** (2,768 from the source cover, each used
  with height *inside*, and the 1,685 non-`rr` ones also with height *outside*), each the root
  of a stored 4.30 **refinement tree** whose internal nodes are splits, location updates and
  exclusions, and whose terminals are LP leaves (2,913 inside, 1,642 outside) or
  `identities` nodes (233, inside).
* Every internal node is re-validated by the replay, and every terminal is re-modelled at
  $L=3.99$ from the specification that the replay itself derives. The stored trees are
  therefore untrusted data, except for the analytic premises behind the location rows.
* I found **no blocking hole** in the combinatorics of the cover, the splits, the
  reservation split, the height and second-zero splits, the replay's interception or the join.
  The semantics that make the reserved partition and the $\lambda_3$ rule exhaustive
  (minimality of the reserved family) are correct but are **not written down in PROOF.md**;
  the paper must state them (§2.1, Lemmas 2.3–2.5 below).
* The concerns are listed in §9: one premise-scope question (height uniformity of the
  location inputs in the outside regime), provenance of the replay report, and a set of
  documentation mismatches (9-way splits, reversed `orders` legend, "roots 10–36", counts).

---

## 1. Configurations and the quantities the tree classifies

Fix a large modulus $q$, $\ell=\log q$, and the height $l=l(q)$ of X Lemma 3.3
($1\le l\le\ell/10$, no zero in $R(10l)\setminus R(l)$), with
$R(x)=\{1-\log\log\ell/(3\ell)\le\sigma\le1,\ |t|\le x\}$.

**Configuration.** $\mathcal Z$ is the multiset of pairs $(\chi,\rho)$ with $\chi\ne\chi_0$ a
character mod $q$, $L(\rho,\chi)=0$, $\rho\in R(l)$, counted with multiplicity. Write
$\rho=1-\lambda_\rho/\ell+i\mu_\rho/\ell$. A **family** is an orbit $\{\chi,\bar\chi\}$ (one
character if $\chi$ is real). Minima over empty sets are $+\infty$.

* $\lambda_1=\min\lambda_\rho$; $(\chi_1,\rho_1)$ a minimizer (any choice); $F_1=\{\chi_1,\bar\chi_1\}$,
  $n=|F_1|$.
* **Type**: `rr` ($\chi_1$, $\rho_1$ real), `rc` ($\chi_1$ real, $\rho_1$ nonreal; we may and do choose
  $\mu_1>0$, since $\bar\rho_1$ is a zero of $\chi_1$ with the same $\lambda$), `complex`
  ($\chi_1$ nonreal).
* **Distinguished occurrences** $D$: $\{(\chi_1,\rho_1)\}$ for `rr`; $\{(\chi_1,\rho_1),(\chi_1,\bar\rho_1)\}$
  for `rc`; $\{(\chi_1,\rho_1),(\bar\chi_1,\bar\rho_1)\}$ for `complex` (one copy each).
  $\lambda'=\min\{\lambda_\rho:(\chi,\rho)\in\mathcal Z\setminus D,\ \chi\in F_1\}$
  (so $\lambda'=\lambda_1$ if $\rho_1$ is multiple; by conjugation it suffices to look at $\chi_1$).
* $\lambda_2=\min\{\lambda_\rho:\chi\notin F_1\}$, $G_2$ a minimizing family;
  $\lambda_3=\min\{\lambda_\rho:\chi\notin F_1\cup G_2\}$.
* **Height-one representative** of $\chi$: $\nu(\chi)=\min\{\lambda_\rho:(\chi,\rho)\in\mathcal Z,\ |\operatorname{Im}\rho|\le1\}$.
  **$T^*$-representative**: $\nu_{T^*}(\chi)$, the same with $|\operatorname{Im}\rho|\le T^*$,
  $T^*\in[\tfrac12,1]$ the pigeonholed strip height of PROOF §4. Hence
  $\nu_{T^*}(\chi)\ge\nu(\chi)\ge\lambda_2$ for $\chi\notin F_1$ (the representative lies in $R(l)$).
* **Conjugate symmetry.** $L(\rho,\chi)=0\iff L(\bar\rho,\bar\chi)=0$, and the regions
  $|\operatorname{Im}\rho|\le1$, $|\operatorname{Im}\rho|\le T^*$ are symmetric, so
  $\nu(\chi)=\nu(\bar\chi)$ and $\nu_{T^*}(\chi)=\nu_{T^*}(\bar\chi)$: $\nu$ is a function of the
  family. Put $\nu_*=\min\{\nu(F):F\ne F_1\}$.
* **Height class** (PROOF §5): *inside* if $\rho_1\in R_B=\{\lambda\le C_B,|\mu|\le C_B\}$, i.e.
  (since $\lambda_1<1.5<C_B$) $|\mu_1|\le C_B$; *outside* if $|\mu_1|>C_B$. Type `rr` has
  $\mu_1=0$ and is always inside.

---

## 2. Specifications and the source cover

### 2.1 Definition and semantics

A **specification** is a tuple
$$\sigma=(\tau,[a,b],p,g,l_2,r,\mathrm{res},h)$$
with $\tau\in\{\mathrm{rr},\mathrm{rc},\mathrm{complex}\}$, a cell $a<b$, $p$ (`case.lp`),
an optional gap $g=[g^-,g^+]$ with $p\le g^-<g^+\le\infty$ (`gap`, complex only),
$l_2$ (`case.source_l2`), $r$ (`ordinary_lower`) with $l_2\le r\le3$, a reservation
$\mathrm{res}\in\{\text{none}\}\cup\{(\mathrm{hi}_2,n_2):r<\mathrm{hi}_2\le2,\ n_2\in\{1,2\}\}$
(`second`, whose `lo` always equals $r$), and $h\in\{\text{inside},\text{outside}\}$.
Its **configuration set** $C(\sigma)$ consists of the configurations (for some admissible choice
of $(\chi_1,\rho_1)$ and of minimizers) with

1. type $\tau$ and $\lambda_1\in[a,b]$;
2. $\lambda'\ge p$, and $\lambda'\in[g^-,g^+]$ if $g$ is present ($\lambda'=\infty$ allowed when $g^+=\infty$);
3. $\lambda_2\ge l_2$;
4. if $\mathrm{res}=$ none: $\nu(F)\ge r$ for every family $F\ne F_1$;
   if $\mathrm{res}=(\mathrm{hi}_2,n_2)$: $\nu_*\in[r,\mathrm{hi}_2]$ and a family $F_{\rm res}$ attaining
   $\nu_*$ has exactly $n_2$ characters ($n_2=1$: real; $n_2=2$: nonreal pair). Then
   automatically $\nu(F)\ge r$ for all $F\ne F_1$;
5. $h=$ inside $\iff|\mu_1|\le C_B$.

**This semantics is not written in PROOF.md** (it is implicit in 4.33 §3, PROOF §8 and the
code). The paper must state it, because the exhaustiveness proofs of §2.3 and §3 and the
$\lambda_3$ rule (Lemma 2.4) use exactly item 4 ("reserved = a $\nu$-minimizing non-first
family", "ordinary_lower bounds every non-first height-one representative").

### 2.2 How the 2,768 specifications are generated

*Parent rows.* `core/code/case_cover.py` (17 base rows) → `cover_v4.py` (refines `rc` by X Table 3
and `complex` by X Table 2′) → `cover_v5.py` (refines `rr` by H Table 4 [`H_PRIME`, $\lambda'$]
and H Table 7 [`H_SECOND`, $\lambda_2$]). Result: 58 parent rows $P_j=(\tau,A_j,B_j,p_j,r_j)$, each a
table fact

> (T2) every configuration of type $\tau$ with $\lambda_1\in[A_j,B_j]$ has $\lambda'\ge p_j$ and $\lambda_2\ge r_j$.

(For a table row "$\lambda_1\le t\Rightarrow\lambda'\ge v$" a parent $[A,B]$ uses the rows with $t\ge B$.)
The `rr` parents tile $[.1,1.5]$ (33 rows), `rc` tile $[.628,1.5]$ (13), `complex` tile $[.44,1.5]$ (12).

*Roots.* `cover_v5.roots()` cuts each parent into cells of width $.01$: **340 roots**. A cell
$[lo,hi]\subset[A_j,B_j]$ gets `lp` $=\max(p_j,lo)$ and `source_l2` $=\max(r_j,lo)$ (the max with
$lo$ is trivially valid, since $\lambda',\lambda_2\ge\lambda_1$).

*Cells, gap cases, records* (file `core/results/source_cover.json.gz`, produced by the 4.33
search; only its structure is trusted, and it is validated). Each root is tiled by
**478 first-zero cells** in total (each again of the form `cell(parent,lo,hi)`); each cell has
`gap_mode` `none` (one gap case, no gap) or `partition` (complex only; gaps
$[p,g_1],[g_1,g_2],\dots,[g_k,\infty]$); **684 gap cases** in total. Each gap case is
*unreserved* (one record, $r=l_2$, no reservation) or *reserved* with a `tail_start`
$e\ge l_2$: records $(\text{res}=([x_j,x_{j+1}],1)),(\text{res}=([x_j,x_{j+1}],2))$ for a chain
$l_2=x_0<x_1<\dots<x_m=e$ with $x_{j+1}\le2$ and $r=x_j$, then a tail record (no reservation,
$r=e$). **2,768 records** = specifications, numbered in order (`spec_id`). Composition
**[checked]**: `rr` 1,083 (195 unreserved + 444 real-reserved + 444 pair-reserved),
`rc` 115 (all unreserved, no gap), `complex` 1,570 (934 reserved with gap, 262 unreserved with
gap, 262 reserved without gap, 112 unreserved without gap). Ids: `rr` 0–1082, `rc` 1083–1197,
`complex` 1198–2767. The 1,685 non-`rr` ids are the outside roots.

*Validation* (`refinement_cover.validate_source_cover` + `verify_v5.check_leaf/check_density`;
re-run by every replay worker through `endgame.specs()`): roots equal `cover_v5.roots()`;
cells are `cell(parent,·,·)`, contiguous inside each root, and per type tile the start value to
$1.5$; gaps chain from `lp` to $\infty$; unreserved records have $r=l_2$; reserved chains are
contiguous from $l_2$ to `tail_start` in $(1,2)$-pairs with equal intervals, then the tail;
$l_2\le r\le3$, $r=\mathrm{lo}_2<\mathrm{hi}_2\le2$, $n_2\in\{1,2\}$, every record's `gap` equals its
gap case's. **[checked]** I re-implemented these structural checks independently on the raw
JSON: 340 roots, 478 cells (rr 195 on $[.1,1.5]$, rc 115 on $[.628,1.5]$, complex 168 on
$[.44,1.5]$), 684 gap cases, 2,768 specifications, no violation.

### 2.3 Exhaustiveness of the source cover

**Theorem 2.1.** Assume (T1) X Lemma 4.5/Table 11 (nonreal $\chi_1$ or $\rho_1\Rightarrow\lambda_1>.44$;
type `rc` $\Rightarrow\lambda_1>.628$) and (T2) for the 58 parent rows. Then every configuration
with $.1\le\lambda_1\le1.5$ lies in $C(\sigma)$ for at least one of the 2,768 specifications
$\sigma$ (with its $h$ set by $|\mu_1|$; type `rr` only inside).

*Proof.* Let $\tau$ be the type. By (T1), $\lambda_1\ge.1$ if $\tau=$ rr, $\lambda_1>.628$ if rc,
$\lambda_1>.44$ if complex, so $\lambda_1$ lies in a cell $[lo,hi]$ of type $\tau$ (the cells tile the
closed range; a boundary value lies in two cells). By (T2) for the cell's parent,
$\lambda'\ge\texttt{lp}$ and $\lambda_2\ge l_2$. If the cell is partitioned, the gaps cover
$[\texttt{lp},\infty]$, so some gap contains $\lambda'$. In that gap case: if unreserved, every
family $F\ne F_1$ has $\nu(F)\ge\lambda_2\ge l_2=r$. If reserved with chain $x_0<\dots<x_m=e$:
$\nu_*\ge l_2=x_0$; if $\nu_*<e$, choose $j$ with $\nu_*\in[x_j,x_{j+1}]$ and a minimizing family,
which is real ($n_2=1$) or a nonreal pair ($n_2=2$): the configuration is in that record; if
$\nu_*\ge e$ (including $\nu_*=\infty$) it is in the tail record. $\square$

Remarks. (i) The cover comments say "left closed, right open"; the model treats cells as closed.
This is harmless: a boundary value lies in the next cell, whose (left-closed) bounds hold.
(ii) The only analytic input is (T1)+(T2) (58 rows, audited in
`notes/source-table-audit-2026-09-29.md`); all other structure is case distinction.

### 2.4 Three lemmas used by every model

**Lemma 2.3 (count rule).** For every configuration at most two characters $\chi\notin F_1$
have $\nu_{T^*}(\chi)<\lambda_3$. *Proof.* Such a $\chi$ has a zero in $R(l)$ with
$\lambda<\lambda_3$, so $\chi\in G_2$, and $|G_2|\le2$. $\square$

**Lemma 2.4 ($\lambda_3$ drop by minimality).** Let $F_{\rm res}$ be any $\nu$-minimizing family
$\ne F_1$. Then $\nu(F)\ge\lambda_3$ (hence $\nu_{T^*}(F)\ge\lambda_3$) for every family
$F\notin\{F_1,F_{\rm res}\}$. *Proof.* If $F\ne G_2$, all zeros of $F$ in $R(l)$ have
$\lambda\ge\lambda_3$. If $F=G_2\ne F_{\rm res}$, then $F_{\rm res}\notin\{F_1,G_2\}$ gives
$\nu(F_{\rm res})\ge\lambda_3$ and $\nu(G_2)\ge\nu(F_{\rm res})$. $\square$
(This is 4.33 §3's "transfer"; it needs no identification $F_{\rm res}=G_2$.)

**Lemma 2.5 ($\lambda_2$ cap).** In a reserved specification $\lambda_2\le\nu_*\le\mathrm{hi}_2$
(the representative is a zero in $R(l)$ of a non-first family). Hence any $\lambda_3$ bound
proved under the hypothesis "$\lambda_2\le h$" may be used with $h=\mathrm{hi}_2$.

In the LP, bins are assigned half-open ($[x_i,x_{i+1})$, a representative on a boundary goes
right); with features and far costs taken at right ends and objectives at left ends this is a
valid assignment, and a counted bin ($x_{i+1}\le\lambda_3^{lo}$) then only holds characters with
$\nu_{T^*}<\lambda_3$.

---

## 3. The refinement trees and their node types

### 3.1 Storage

* Inside: `computations/frontier/collective_full_4.30/roots.jsonl.gz`, one line per spec id
  (0–2767), field `inside`; loaded by `collective_cover.load_root` (asserts `id`, `target='4.30'`).
* Outside: `computations/near/results/outside_regime_4.30.jsonl.gz`, one record per non-`rr` id,
  field `outside_buffer`; loaded by `certificate_io.load_outside('4.30')`, and
  `validate_outside_records` asserts the ids are exactly the non-`rr` spec ids in order.

Node grammar (inside, as traversed by `collective_cover.verify_tree` →
`far_full.verify_tree_new` → `verify_progress.verify_tree`, with repair subtrees
`collective_cover.verify_inner` → `inside_repair.verify_leaf`):
`split{split∈{first,second,gap},mid,children[2]}`, `real_location{row,child|excluded}`,
`complex_location{row,child|excluded}`, `second_exclusion{proof}`, `positivity{g,…}`,
LP terminals `record` / `core` / `far` / `collective`, wrappers `repair`, `collective_repair`,
and `identities{branches,maximum}`. Outside (`outside_regime.verify_tree`): `split`,
`second_exclusion`, `positivity` (never occurs), `buffered_first` terminals.

### 3.2 Node semantics and why each is sound

Let $\sigma$ be the node's specification (computed by the verifier from the root, never read from
storage). In every case the claim is: **every configuration of $C(\sigma)$ lies in $C$ of some child**
(or $C(\sigma)=\emptyset$ for an exclusion).

* **`split(first, m)`** (`endgame.split_new`): asserts $a<m<b$; children $[a,m]$ and $[m,b]$,
  all other fields (incl. `lp`, $l_2$) kept. Exhaustive since $\lambda_1\le m$ or $\lambda_1\ge m$;
  kept bounds stay valid on sub-cells. (A kept $l_2$ may be below the child's $a$, e.g. node
  1501/1 has $l_2=.7225<a=.72375$; still valid, merely weak.)
* **`split(second, m)`** (`refinement_cover.split_specs`): needs a reservation; asserts
  $r<m<\mathrm{hi}_2$; children $(r,[r,m])$ and $(m,[m,\mathrm{hi}_2])$ (upper child gets
  $r:=m$). Exhaustive: $\nu_*\le m$ or $\nu_*\ge m$; in the upper case every non-first $\nu\ge\nu_*\ge m$
  (**uses minimality**).
* **`split(gap, m)`**: complex only; $g=[g^-,g^+]$ (or $[\texttt{lp},\infty]$ if absent); asserts
  $g^-<m<g^+$; children $[g^-,m]$, $[m,g^+]$. Exhaustive.
* **`real_location`** (rr only; `inside_repair.real_update`, row regenerated by
  `polynomial5_rows.regenerate_row5` and compared for equality): the row covers $[a,b]$ and
  proves $\lambda_2>h$ (degree-5 conductor rows with the $1/108$ saving, premise [R]). If
  $\mathrm{hi}_2\le h$ the reserved record is empty (excluded); else $l_2,r\leftarrow\max(\cdot,h)$,
  $\mathrm{lo}_2\leftarrow r$. Sound: every non-first $\nu\ge\lambda_2>h$.
* **`complex_location`** (complex; `inside_complex_rows.complex_update`, row regenerated by
  `complex_second_row`): same update with a proved global $\lambda_2>h$.
* **`second_exclusion`** (`endgame.reduced_spec` returns `None`, and its proof list equals the
  stored one): (a) rr with $.7\le a\le b\le.7025$: $\lambda_2>.762$ (`new_positivity.lambda2_row`,
  margins re-asserted) excludes $\mathrm{hi}_2\le.762$; (b) complex, table rows of
  `poly_rows.applicable_polynomials(a,b)`: type `second` ($\lambda_2>h$) excludes
  $\mathrm{hi}_2\le h$; type `additional` ($\lambda'>$ `new_lower`) excludes a gap with
  $g^+\le$ `new_lower`.
* **`positivity(g)`** (`extension_enclosures.positivity_proof`; rr with a real reserved
  character, $n_2=1$): re-computes
  $\big(F(b-a)+F(\mathrm{hi}_2-a)-F(-a)-\tfrac38f(0)\big)/f(0)>2\cdot10^{-5}$ for the test of
  parameter $g$ at shift $a$; the explicit formula applied to the nonnegative weight
  $(1+\chi_1)(1+\operatorname{Re}\chi_2n^{-i\gamma_2})$ then gives a contradiction for every
  configuration of the spec, which is therefore empty. Premise [R].
* **Implicit location update at every leaf**: `make_endgame` first applies `reduced_spec`
  (raising $l_2,r,\mathrm{lo}_2$ or `lp`, $g^-$ by the same rows). Idempotent, and only adds valid
  implications, so the leaf's model is for a superset of $C(\sigma)$.

None of these depends on $L$ (they are zero-location statements). **[checked]** node census of
the 4.30 trees (independent walk):

| Node | Inside | Outside |
| --- | ---: | ---: |
| `split first` / `second` / `gap` (top level) | 1 / 378 / 584 | 0 / 27 / 0 |
| `split second` / `gap` inside repair trees | 30 / 9 | – |
| `real_location` restrict / exclude (all degree-5, saving 1/108) | 225 / 75 | – |
| `complex_location` restrict / exclude | 11 / 0 | – |
| `second_exclusion` (351 complex polynomial + 1 real `.762`) | 352 | 70 (all complex polynomial) |
| `positivity` | 197 | 0 |
| LP terminals: `core` 939, `far` 457, `collective` 1,517 | **2,913** | **1,642** `buffered_first` |
| `identities` nodes (in 199 roots) | **233** | – |

343 inside roots and 70 outside roots contain no terminal (entirely excluded).

---

## 4. The leaf models at the target exponent

The graded replay replaces **every** terminal by a *regular model* built from the terminal's
specification $\sigma$ (after `reduced_spec`), at $L$.

### 4.1 Regular inside model (`graded_leaves.inside_input`)

$\texttt{make\_endgame}(\sigma,L,\mathrm{par},\mathrm{den})$ (`endgame.py`), then the leaf's recorded far
weight (`replace_far` iff the 4.30 input carried `far_parameters`: all 457 `far` and 1,517
`collective` leaves use the retuned weight; the 939 `core` leaves and all 233 identities nodes
use the inherited one), then `third_refine.refine_third`. The collective envelope is never
applied. Components:

* **Shift** $s=\min(1.9,\,p^\*,\,l_2)$ with $p^\*=g^-$ if a gap, else `lp`
  (`published_single_inputs.make_single`, `shift_rule='source-global-lambda2'`): a *global*
  bound, valid for every configuration of $C(\sigma)$ (it does not use $r$).
* **Ordinary bins**: $[r,R]$, $R=\max(3,r)$, grid $1/\mathrm{den}$ with
  $\mathrm{den}\in\{200,400,500,800,2000\}$ taken from the 4.30 leaf; far cost $w(\text{right})$
  rounded down, objective $G(\text{left})=e^{-A\,\text{left}}B_{1/3}(\text{left})$ rounded up;
  tail $[R,\infty)$: far cost 1, objective $G(R)/w(R)$.
* **Third-family rule** (`triple_inputs.input_with_third`):
  $\lambda_3^{lo}=$ `third_bound`$(a,b,\tau,\mathrm{hi}_2)$ (H Lemma 10.3 `.857`; X Table 8 for
  non-rr with $b\le.62$; X Table 10 for rr; X (4.28) with cap $\min(t,\mathrm{hi}_2)$ for complex
  $[.44,.85]$), then for rr on $[.44,.80]$ `rr_third` (X (4.31), $\gamma=26/25$, cap $\mathrm{hi}_2$).
  Reserved: bins with right end $\le\lambda_3^{lo}$ are dropped (Lemma 2.4). Unreserved: those
  bins get count cost 1 and $\sum\le2$ (Lemma 2.3). Caps use Lemma 2.5.
* **First family**: $\min(J_{\rm old},J_{\rm new})$ (`enclosures.first`, `triple_inputs.shifted_first`;
  $J_{\rm new}$ only if $p^\*\ge b$), far deduction $n\,w(b)$ ($\rho_1$ and, for complex,
  $\bar\rho_1$ are the height-one representatives since $|\gamma_1|\le C_B/\ell$).
* **Reserved family**: fixed term $J_2=n_2G_{\phi_2}(r)$ ($\phi_2=\tfrac14$ iff $n_2=1$), far
  $n_2w(\mathrm{hi}_2)$; or, with `second_columns: 400`, columns on $[r,\mathrm{hi}_2]$ with grid
  $1/400$, far $w(r_j)$, objective $G_{\phi_2}(l_j)$, $\sum z_j=n_2$ (`graded_leaves.second_columns`
  removes exactly $J_2$ and adds back exactly $n_2w(\mathrm{hi}_2)$ for the leaf's own far weight).
* **Near rows** (PROOF §6.5; parameters stored, rebuilt by `graded_leaves.build_row`):
  `family` (anchor $s_1=\lfloor a\rfloor_{1/50}$), `shifted` (anchor $s$; allowed only if
  $a\le s\le\min(p^\*,l_2)$, asserted), `graded` (anchors used in the corpus: 1.5, 1.6, 1.9, 2.1,
  2.3), and the inherited `old` two-test row (fallback, 37 inside roots). All family anchors in
  the corpus lie in $[.1,1.48]$, shifted anchors in $[.7225,1.9]$ **[checked]**.
* The near-row parameters `par` (method, $\gamma_G,\gamma_Z$, mix, $\zeta$) of the 4.30 leaf only
  affect the `old` row's data ($d,D,D_f,v_{\rm first}$, bin features); the graded rows do not use them.

### 4.2 Regular outside model (`graded_leaves.outside_input` → `leaf_driver.regen_out` → `first_outside_blocks.first_out_input(σ,L,'outside_buffer',par,den)`)

* `make_endgame` with $h=$ outside: far budget $\lceil(1+\eta)V\rceil-n_2w(\mathrm{hi}_2)$ (no first-family
  deduction; inherited far weight), same bins, same third rule and count costs.
* `first` $:=J_2$ only (the outside first-family bound is removed).
* **Hidden columns**: $p=\max(a,\texttt{lp},g^-)$; bins of $[p,\max(3,p)]$ on grid $1/\mathrm{den}$ plus a
  tail; objective $e^{-A\,\text{left}}B_{\phi_1}(p)$ ($\phi_1=\tfrac14$ for rc), far $w(\text{right})$,
  hidden-count cost 1 per finite bin and $1/w(\text{end})$ (rounded down) for the tail;
  constraint $\sum y_h\le n$. Semantics: each first-family character's rightmost $R_P$ zero
  (all first-family $R_P$ zeros have $\lambda\ge\lambda'\ge p$ because $D\cap R_P=\emptyset$ when
  $|\mu_1|>C_B$).
* Count row as inside (`Leaf.cnt` from `count_cost`); hidden columns have count 0.
* Rows: `family` in mode `outside_first` ($s=s_1$, $H=0$ asserted; global zero as an entry;
  hidden columns with features, asserted $\ge s_1$) and `graded` rows carrying only the reserved
  family. `shifted`, `old`, `mu_split`, `dz_split` are rejected outside by assertions.

### 4.3 Validity for every case, including identities nodes

**Proposition 4.1.** For every specification $\sigma$ occurring at a terminal (LP leaf *or*
`identities` node), the regular model of $\sigma$ is a relaxation of $C(\sigma)$: every
configuration in $C(\sigma)$ yields a feasible point, given the analytic premises of §§3–6 of
PROOF.md.

*Why this holds (case-tree part).* The model reads from $\sigma$ only: the cell (first-family
bound, far deduction $w(b)$, anchors $\le a$), $p^\*$ (shift, $J_{\rm new}$, hidden columns),
$l_2$ (shift; second-family anchor $\max(a,\min(l_2,l_j))$), $r$ (bin start, justified by item 4
of §2.1), the reservation (Lemmas 2.4–2.5), and $\lambda_3^{lo}$ (from the cell and cap). Every
one of these is a property of *all* of $C(\sigma)$. The 4.30 `identities` node partitioned
$C(\sigma)$ further by the hidden global second family ($\lambda_2\in[\max(l_2,a),r)$ attained at
height $>1$, identity `distinct`/`same_reserved`, or `unhidden`) and added a bonus near
constraint in each branch. Because the regular model never uses "$\lambda_2\ge r$" (its shift uses
$l_2$, not $r$; see the comment "The local second-family lower bound is NOT a global zero-free
bound" in `make_single`), it is valid on the union of the branches, i.e. on $C(\sigma)$. A hidden
family's $T^*$-representatives still satisfy $\nu_{T^*}\ge\nu\ge r$ (its low zero is at height
$>1$), and its high zero is at normalized distance $\ge M$ from every $T^*$-entry by the
pigeonhole choice of $T^*$, so the strip argument of PROOF §6.5 applies unchanged. Hence the
statement "the identities were only an alternative certificate" is **correct**. $\square$

Details of the replacement: the node's model is regenerated from
`inside_repair.make_endgame(σ,'4.33',par0,200)` where `par0` is the repair's near parameters, or
`SINGLE_PAR` if they were of `pair` type (this only affects the `old` row, which no node
certificate uses: 0 old rows in `nodes.jsonl.gz` **[checked]**); far weight inherited.

---

## 5. Further subdivision inside graded records

A graded leaf record may subdivide its case. Grammar (`graded_driver.verify_leaf`/`_verify_record`):
`excluded_by_location` | `reserve{h,children[3]}` | `split{mids,children}` | plain record
(`rows`, `tree`, `maximum`), with optional `second_columns: 400`, or a `mu_split` (2 parts) or
`dz_split` (6 parts) whose parts are plain records.

### 5.1 Second-family split (`split`)
Children $i=0..k$ along paths $[(\text{second},m_{i-1},1),(\text{second},m_i,0)]$ (`split_paths`).
Verifier: $m_1<\dots<m_{k}$ strictly, $r<m_1$, $m_k<\mathrm{hi}_2$ of the regenerated parent, each
child's stored `path` equals the computed one, children are not `split`/`reserve`, each child
regenerated. Exhaustive by §3.2 (`split(second)` applied repeatedly). Driver: equal parts,
$k\in\{3,5,9\}$ children. Corpus **[checked]**: inside 6 records (3-way ×4, 9-way ×2 in the
reserved-pair children of 1218, 1219); nodes 21 records (3-way ×17, 5-way ×3, 9-way ×1, root 2397).

### 5.2 Reservation split (`reserve`)
For an unreserved $\sigma$ (ordinary lower bound $r$) and $h$ with $r<h\le2$
(`graded_leaves.reserve_specs`): children
(0) $\mathrm{res}=([r,h],1)$; (1) $\mathrm{res}=([r,h],2)$; (2) no reservation, $r:=h$.

**Lemma 5.1.** $C(\sigma)\subseteq C(\sigma_0)\cup C(\sigma_1)\cup C(\sigma_2)$ for every $h\in(r,2]$.
*Proof.* $\nu$ is a family function (conjugate symmetry, §1). If $\nu_*<h$, a minimizing family
$F\ne F_1$ exists; it is real or a nonreal pair, so the configuration is in child 0 or 1
($\nu_*\in[r,h)$; all non-first $\nu\ge\nu_*\ge r$). Otherwise every non-first $\nu\ge h$: child 2.
Ties between minimizing families put a configuration in both reserved children, which is
harmless. $\square$

In the reserved children the model uses (a) Lemma 2.4 (only minimality; *not* that the reserved
family is $G_2$ — although with $h\le\lambda_3^{lo}$ it necessarily is), (b) the cap $\lambda_2\le h$
(Lemma 2.5) in `third_bound`/`rr_third`, (c) second-family anchors $\le\max(a,\min(l_2,\cdot))$,
valid because all zeros of a non-first family satisfy $\lambda\ge\max(\lambda_1,\lambda_2)$. Driver:
$h=\min(\lambda_3^{lo}(\text{parent}),2)$, only at depth 0; verifier: only $r<h\le2$, $h$ in normal form,
three children with exact paths, recursive verification (a child may itself be a `split`).
Corpus **[checked]**: inside roots 1218 (h=.8959), 1219 (.8934), 2461 (.8713), 2486 (.8707);
node roots 1479, 1490, 1501 (twice: .882, .8817), 1512, 1523 — as PROOF §8 states. For root 2486 I
regenerated the three children: children 0/1 get $\lambda_3^{lo}=.8708$ with cap $.8707$ and drop the
bins below it; child 2 has $r=.8707$.

### 5.3 Height split for type rc (`mu_split`)
Parts `mu_range` $=[0,1]$ and $[1,\infty)$ (`leaf_driver.RC_MU_SPLIT`), for $\mu_1>0$ chosen as in §1
(inside: $\mu_1\le C_B$). Verifier: exactly these two ranges in this order, only for inside rc,
the range carried by the family row (row 0) and no other row carrying a different range
(review 6's fix). A plain rc record without `mu_split` is also accepted: its family row then
uses the single-zero term, which is valid for all $\mu_1$ (the conjugate zero's term is
$\ge0$ and dropped). All 115 rc roots use `mu_split` **[checked]**.

### 5.4 Second-zero height split (`dz_split`)
For inside complex leaves with a finite gap ($\lambda'\in[g^-,g^+]$, $g^+<\infty$): $y=|$normalized height
difference of $\rho'$ and $\rho_1|\in[0,1],[1,\tfrac32],[\tfrac32,2],[2,3],[3,5],[5,\infty)$
(`DZ_SPLIT`). $\operatorname{Re}F(x+iy)$ and $\operatorname{Re}G_1(-s_1+iy)$ are even in $y$, so
$|y|$ suffices. Verifier: exactly these pieces, only when `dz_applicable`, range only on the family
row. Pieces may be certified by exclusion (§7 rule). Corpus: 108 inside records, 10 node records.

### 5.5 Second-family columns
Not a split: a relaxation of the $1/400$ split (the configuration puts mass $n_2$ on $\nu_*$'s
column). The verifier pins the grid to 400 and re-applies `second_columns`. Used on 2,227 inside
leaf records, 285 node records, 1,153 outside records.

### 5.6 Verifier versus driver

| Item | Driver chooses | Verifier checks |
| --- | --- | --- |
| rows | staged sets (F, S, 1.5/1.6/1.9/2.1/2.3, greedy menu, then `OLD_STAGES`) | rebuilds each row from kind + stored rational parameters; builder assertions ($s\ge s_1=\lfloor a\rfloor_{1/50}$; shifted $a\le s=$ shift $\le\min(p^\*,l_2)$; pair/second-zero terms need $H=0$; outside family $s=s_1$, $H=0$) |
| second split | $k\in\{3,5,9\}$ equal parts | any strictly increasing interior mids; exact paths |
| reservation | $h=\min(\lambda_3^{lo},2)$, depth 0 | $r<h\le2$ only |
| rc / dz splits | fixed lists | exact equality with the fixed lists |
| columns | on when reserved | grid $=400$ |
| certificate | proposer (floating LPs) | exact integer check of every box/case (`graded_cert.verify_tree`), stored maxima must equal recomputed ones, every value $<S$ |

---

## 6. The replay: what is recomputed and what is trusted

`computations/graded/graded_verify.py` (assertions required):

1. Loads `endgame.specs()` (re-validates the source cover; asserts 2,768 specs). Outside: loads
   the 1,685 records and asserts their ids are the non-`rr` ids in order.
2. For each inside root $i$: `collective_cover.verify_tree(with_height(specs()[i],'inside'), tree)`.
   Hooks installed in each worker: `verify_progress.scenario`, `inside_repair.verify_core`,
   `collective_model.scenario` (capture each LP terminal's **regenerated** input, after running the
   original 4.30 check), `inside_repair.verify_leaf` (intercepts nodes whose keys are exactly
   `{identities,maximum}` and captures `make_endgame(σ,'4.33',par0,200)`; everything else falls
   through), `inside_repair.verify_branch` raises (no identities branch may be reached).
   **[checked]** in a live worker: `far_full.scenario`, `inside_repair.verify_core`,
   `collective_model.scenario` are the hook and `collective_cover.verify_leaf` is the node hook,
   so no LP-leaf verifier escapes interception.
3. Outside: `outside_regime.verify_job` with `first_verify` hooked.
4. The captured list for a root is matched **by position** with the stored graded records
   (`len` equal, `index==j`); each record is verified by `graded_driver.verify_leaf(src,L,rec)`,
   which regenerates the model at $L$ from `spec_of(src)` along the record's path. The inside
   total must include exactly 233 intercepted identities nodes.

| Object | Recomputed by the replay | Taken from storage |
| --- | --- | --- |
| root specification | from `source_cover.json.gz` + `cover_v5` tables, validated | the partition endpoints (validated structurally) |
| each node's specification | from the root through `split_new`/updates | node kinds, split axes and mids |
| split | exhaustiveness asserts ($a<m<b$ etc.) | — |
| real/complex location rows | row certificate regenerated and compared for equality | row parameters |
| `second_exclusion` | `reduced_spec` recomputed, proof compared | **polynomial table rows** (`polynomial_table.json`) are used as stored; regenerated only by `verify_auxiliary_inputs.py` |
| `positivity` | margin recomputed | $g$ |
| 4.30 LP terminal input | regenerated from the spec, hash-compared (then discarded) | near parameters, `lambda_den`, far parameters |
| graded leaf model at $L$ | regenerated from `spec_of(src)` (+ path) | row kinds and rational parameters, split points, $h$, paths, flags |
| certificate | every box and case checked in exact integers | tree, orders, duals |
| $\lambda_3$ (4.28) alias condition (4.29) | not re-run | checked separately (`alias_check`, `auxiliary_regeneration.json`) |

So, beyond the analytic premises, the replay trusts only: the table facts hard-coded in
`case_cover/cover_v4/cover_v5/triple_inputs`, the polynomial table JSON and the alias check
(both checked by `verify_auxiliary_inputs.py`), and the code itself.

**My partial replays [checked]:** inside roots 0, 10, 1083 and outside root 1198
(passed, 15 s); inside root 2486 (reservation split + 3-way split) with node root 1523
(reservation split) (passed, 74 s).

---

## 7. The join (PROOF §10)

Let $W$ be the normalized zero sum of the criterion (PROOF §2). The four regimes:

1. **No zero in $R(l)$.** $R_P\subset R(l)$ for large $q$ ($C_P\le\log\log\ell/3$, $C_P/\ell\le l$) and the
   principal $L$-function has no zero there, so $W=0$.
2. **$0<\lambda_1\le.1$.** By (T1), type rr; $\rho_1=\beta_0$ real. Sub-cases:
   $\lambda_1\le u_0$ (Heath-Brown 1990, Cor. 1: $P(a,q)\le q^{3.5}$; hypotheses
   $\beta_0\ge1-1/(3\log q)$, i.e. $\lambda_1\le\tfrac13$, and $\eta=1/\lambda_1\ge\eta(\tfrac12)$);
   $u_0\le\lambda_1\le.08$ and $.08\le\lambda_1\le.1$ (certified pieces of `small_exception_tables`).
3. **$.1\le\lambda_1<1.5$.** Theorem 2.1 gives a specification; §3 gives a terminal of its tree
   (inside if $|\mu_1|\le C_B$, else outside; rr always inside); §4–§5 give a certified model.
4. **$\lambda_1\ge1.5$.** Large branch (every zero has $\lambda\ge1.5$; single-anchor row).

*Coverage and boundaries.* If a zero exists, $\lambda_1\in(0,\log\log\ell/3]$, and
$(0,.1]\cup[.1,1.5)\cup[1.5,\infty)$ covers it; $\lambda_1=.1$ is in regimes 2 and 3 (the rr cells
start at the closed value .1); $\lambda_1=1.5$ is in regime 4 (and in the closed last cells). The
middle range for rc with $\lambda_1\le.628$ and complex with $\lambda_1\le.44$ is empty by (T1).
The interval $(u_0,.1]$ is covered by the two certified pieces; if $1/\eta(\tfrac12)$ exceeded .08
the first piece is empty and the HB 1990 range overlaps (take $u_0=\min(1/\eta(\tfrac12),.08)$).

*Order of constants* (interface closure §5). S0: $L$, kernel, far weights, tests, anchors, grids,
trees, certificates, $\eta=\eta'=10^{-6}$, $u_0$. S1: $C_P\ge\max(C_0(\eta H_0),3)$. S2: $K_0$
(zeros of all characters with $\lambda\le s_{\max}$, $|\gamma|\le2$), then $M$. S3:
$C_B>\max(C_P+M,1.5)$ with $4c_{\rm out}/(H_0C_B^2)\le\eta$. S4: source tolerances. S5: $q_0$
(incl. $\ell>4M(K_0+1)$). The certificates do not depend on $C_B$; the inside/outside split
does, and is fixed before $q_0$. From the corpus, the largest response anchor is $2.3$, so
$s_{\max}=2.3$ suffices (PROOF gives no value). There are finitely many terminals (4,788),
rows and tests, hence one $q_0$; $\delta_0=1-\max(\text{leaf values})>0$ with the maximal value
$.99999982$ and every value including the $5\eta$ allowance.

---

## 8. Numbers (all **[checked]** against the corpora and the trees)

| Quantity | Value | Where stated | Status |
| --- | --- | --- | --- |
| source roots / cells / gap cases / specs | 340 / 478 / 684 / 2,768 | PROOF §5, 4.30 verification | ✓ |
| inside roots; LP leaves; identities nodes (roots) | 2,768; 2,913; 233 (199) | STATE, corpora README | ✓ (my tree walk; per-root match with corpus) |
| inside leaf records incl. nodes | 3,146 | verification JSON, PROOF | ✓ |
| inside boxes; nodes boxes | 3,067,092; 1,042,363 | STATE, README | ✓ |
| inside max; nodes max | .99999981 (root 1416); .99999982 (root 2432) | STATE | ✓ (9999998132810008, 9999998223456687) |
| outside roots, leaves, boxes, max | 1,685; 1,642; 87,424; .99999425 (root 1990) | STATE, JSON | ✓ |
| total | 4,453 roots, 4,788 leaves, 4,196,879 boxes | STATE, README | ✓ |
| independent checker "roots" | 4,652 = 2,768 + 199 + 1,685 | STATE | ✓ |
| Lean leafcheck inside "leaves" | 3,949 plain certificate trees = 3,600 inside + 349 nodes | STATE, `lean_runs` | ✓ |
| rows | inside 12,238 + nodes 1,327 = 13,565 (37 `old`); outside 3,314 | STATE (rowcheck) | ✓ |
| fallback `old` row | 37 roots: rr 10, 11, 15–18, 20–36 (single); complex 1198–1201, 1212–1215 (single); 2603, 2608, 2613, 2633 (pair); 1218, 1219 (mixture) | PROOF §6.6 | ✓ variants; range wording off (H6) |
| reservation split | inside 1218, 1219, 2461, 2486; nodes 1479, 1490, 1501, 1512, 1523 | PROOF §8 | ✓ |
| exclusions | positivity 197; polynomial 352 in / 70 out; real conductor 75 | PROOF §5 | ✓ (see H7) |

---

## 9. HOLES AND CONCERNS

Severity: **blocking** = the proof is wrong as stated; **major** = a premise/definition the
paper must supply or confirm; **minor** = documentation, provenance or robustness.

**H1 (major, exposition — not a mathematical error). The semantics of a specification is never
stated.** PROOF §5 lists the fields but not what "reserved" and `ordinary_lower` *mean*. The
exhaustiveness of the reserved partition (Thm 2.1), of `split(second)` (upper child needs
$r:=m$), of the reservation split, and the $\lambda_3$ drop rule all rely on: the reserved family is a
$\nu$-minimizing non-first family (by *height-one* representative) and $r$ bounds $\nu$ of every
non-first family. *Fix:* put §2.1 and Lemmas 2.3–2.5 into the paper, and state the closed-cell /
half-open-bin conventions.

**H2 (major, premise scope — likely benign, unconfirmed). Height uniformity of the location
inputs in the outside regime.** The 1,685 outside trees reuse, for $|\mu_1|>C_B$ (physical height
up to $l$), every inside location input: the parent-row facts (T1)–(T2), the $\lambda_3$ rules in
`third_bound` (H 10.3, X Table 8, X (4.28)) that drive the count row and the bin drop, and the
complex polynomial rows in `reduced_spec` (70 outside exclusions). The source-table audit checks
value, type/order and $\lambda_1$ range, but says nothing about the height of $\rho_1$. The X/H
parameters are defined over $R(l)$ and test points at $k\gamma_1$ ($k\le4$) stay in $R(9l)$, and the
repository polynomial rows carry all-height alias bounds, so this is probably fine, but it is a
premise the paper uses without a written check. *Fix:* add a "height of $\rho_1$" column to the
audit and a sentence in PROOF §5 that every location input is uniform for $\rho_1\in R(l)$.

**H3 (minor, provenance). The replay report is not bound to its inputs.**
`verification_3.99.json` records only counts, maxima and time; `candidate_3.99.json` binds the three
corpora hashes and the report hash, but no hash of the code, of the 4.30 trees
(`collective_full_4.30/roots.jsonl.gz`, `outside_regime_4.30.jsonl.gz`), of `source_cover.json.gz` or
of `polynomial_table.json`. The graded code, the corpora and both reports arrive together in one
commit (`54d3df9`), so git history cannot show which code version produced the report either. Soundness is unaffected (the replay re-validates
every structure), but "the replay passes" should name what it replayed. *Fix:* record the commit
and SHA-256 commitments as `collective_cover.verification_commitments` does.

**H4 (minor). "Every location row, exclusion and split is re-checked" is slightly overstated.** The
replay recomputes `reduced_spec` against `polynomial_table.json` as stored and does not re-run the
alias check (4.29); these are checked only by `verify_auxiliary_inputs.py` (PROOF §13 says so). *Fix:*
call `verify_polynomial_table()` and `alias_check()` at replay start, or qualify the sentence in §8.

**H5 (minor, doc). "3 or 5 children" (PROOF §8) is wrong:** there are 9-way splits in three records
(1218, 1219, node root 2397); PROOF §6.6 itself mentions the 9-way split. The §8 list of
"further subdivision" also omits the `dz_split` (§6.5) and `excluded_by_location` children.

**H6 (minor, doc).** PROOF §6.6 "rr cells … (roots 10–36)" — only 23 of those 27 roots use the
fallback (not 12, 13, 14, 19); STATE says the fallback "repaired 22 low-λ₁ rr roots" while 23 rr
roots carry it (22 failures plus root 36). Total 37 is right.

**H7 (minor, doc).** PROOF §5's exclusion counts omit the 225 restricting degree-5 real rows and
the 11 restricting complex location rows; "Polynomial rows … 352 inside" includes one real
`.762` exclusion (`new_real_first_second_zero_row`, itself a polynomial row). State all node counts
(table in §3.2).

**H8 (minor, doc).** `computations/graded/corpora/README.md` says "`orders`: first (1) or second (2)
order per row" — reversed: in `graded_cert.cases` order 1 is the tangent (second-order) pair and
order 2 the first-order relaxation (`graded/README.md` is correct). The same README calls `split`
"second-zero splits at the listed `λ₂` points"; they are second-*family* splits of
$[r,\mathrm{hi}_2]$ (points of $\nu_*$), not $\lambda_2$, and unrelated to the "second zero" of `dz_split`.
`graded/README.md` lists duals "(Y,V,U,Z₁…Z_K)" and omits $P,M$.

**H9 (minor, terminology).** "leaves" means 3,146 LP-leaf records in `verification_3.99.json` but
3,949 certificate trees in `lean_runs/leafcheck_full_inside_3.99.json` and `rowcheck_*` (key
`leaves`). Rename one of them.

**H10 (minor, reproducibility).** Graded rows are regenerated from stored parameters, but
`SieveNearTest` derives the sieve heights $h_k$ with numpy floats (`np.exp`, `np.sqrt`) before
rationalizing (`limit_denominator(10**12)`). Any $h_k\ge0$ is admissible and later enclosures are
outward, so soundness is unaffected; but a different libm could change $h_k$ and make a stored
certificate fail to replay on another platform. *Fix:* store the $h_k$ (or a digest of each row's
integer data) in the record.

**H11 (minor, statement).** $s_{\max}$ (PROOF §4, §10) is never given a value; from the corpus
$s_{\max}=2.3$ suffices (graded anchors 1.5–2.3, shifted and old-row shifts $\le1.9$, family
anchors $\le1.48$). $u_0$ should be defined as $\min(1/\eta_{HB}(\tfrac12),.08)$ (with $\lambda_1\le\tfrac13$
implicit in HB's hypothesis).

**H12 (minor, robustness; no effect).** (a) `check_records` returns early for roots without
captured terminals and does not check that the stored record is empty. (b) `node_bases` would
collapse consecutive identical node specifications into one certificate; no collapse occurs
(233 captured = 233 certified), and a collapse would be sound anyway. (c) The replay does not
check the 4.30 corpus digest or `all_pass`; unresolved nodes raise (`far_full.verify_tree_new`,
`inside_repair.verify_leaf`), so nothing can be skipped silently. (d) The replay also re-checks
every 4.30 certificate at 4.30 (time only).

**H13 (minor, inherited premise).** Steps that use $l_2$ (shift, second-family anchor, fallback
row, identities replacement) inherit the 4.30 premise that `source_l2` bounds the *global*
$\lambda_2$ at every node. Structurally it is only ever raised by global $\lambda_2$ rows
(`real_update`, `complex_update`, `reduced_spec`) and kept under `first` splits — **[checked]** in
the code — so the premise reduces to (T2) and the location rows.

No blocking issue was found.

---

## 10. References

Repository (paths relative to `/home/naslund_eric/src/enaslund/linniks-constant/master`):

* `research/PROOF.md` §§2, 4, 5, 6.5–6.6, 7, 8, 10, 13; `research/STATE.md`;
  `research/arguments/4.33.md` §3 (third-family transfer); `research/arguments/hidden-families.md`
  §§3–5 (hidden global family, identities); `research/arguments/near-blocks.md` §5 (two buffered
  windows); `research/arguments/sieve-majorant-near.md` §§2d–2h, 6f–6h, 8 (reviews 5–7, 9–11);
  `research/notes/interface-closure-2026-09-29.md` §§3–7; `research/notes/source-semantics.md` §§2–5;
  `research/notes/source-level-reduction.md`; `research/notes/source-table-audit-2026-09-29.md`;
  `research/notes/independent-checks-2026-09-29.md`.
* Source cover: `computations/core/code/case_cover.py`, `cover_v4.py`, `cover_v5.py`,
  `refinement_cover.py` (`validate_source_cover` l.146, `with_height` l.173, `split_specs` l.176),
  `verify_v5.py` (`check_density` l.13, `check_leaf` l.48), `computations/core/results/source_cover.json.gz`.
* Models: `computations/core/code/endgame.py` (`reduced_spec` l.15, `make_endgame` l.42, `split_new` l.51),
  `published_single_inputs.py` (`make_single`, shift l.20), `triple_inputs.py` (`third_bound` l.12,
  `input_with_third` l.43, `shifted_first` l.91), `enclosures.py` (`first` l.45),
  `extension_enclosures.py` (`positivity_proof` l.135), `computations/frontier/far_enclosures.py`
  (`replace_far` l.51), `computations/sieve_near/third_refine.py`, `leaf_driver.py` (`spec_of` l.26,
  `safe_anchor` l.53, `graded_row` l.109, `regen_out` l.446, `RC_MU_SPLIT` l.742),
  `sieve_inputs.py` (`pair_bounds`, `second_zero_bounds` assert $H=0$),
  `computations/near/code/first_outside_blocks.py` (`first_out_input` l.6).
* Trees and their verifiers: `computations/frontier/collective_full_4.30/roots.jsonl.gz`,
  `collective_cover.py` (`verify_inner` l.39, `verify_tree` l.74), `far_full.py` (`verify_tree_new` l.174),
  `computations/core/code/verify_progress.py` (`verify_tree` l.54), `computations/frontier/inside_repair.py`
  (`real_update` l.82, `verify_leaf` l.188), `inside_complex_rows.py` (`complex_update` l.64),
  `polynomial5_rows.py`, `computations/near/results/outside_regime_4.30.jsonl.gz`,
  `computations/near/code/outside_regime.py` (`verify_tree` l.40), `certificate_io.py`
  (`validate_outside_records`).
* Graded layer: `computations/graded/graded_verify.py`, `graded_driver.py` (`certify_case` l.268,
  `verify_leaf` l.367), `graded_leaves.py` (`reserve_specs` l.61, `inside_input` l.92,
  `second_columns` l.121, `old_row` l.170), `graded_cert.py` (`Leaf` l.69, `check_case` l.197,
  `verify_tree` l.240), `README.md`, `corpora/README.md`, `verification_3.99.json`,
  `candidate_3.99.json`, `lean_runs/*.json`, `computations/near/results/auxiliary_regeneration.json`.
* My check scripts (scratchpad): `walk430.py`, `walkout.py` (node census), `scan_corpus.py`
  (record census, per-root leaf match), `scan_params.py` (row anchors), `oldvariants.py`
  (fallback variants), plus inline scripts for the source-cover re-check, hook binding, and the
  partial replays.

Literature: Xylouris, dissertation (BMS 404), Lemmas 3.1–3.4, 3.10, 4.4–4.5, 5.1, Tables 2′, 3, 6–11,
(4.28)–(4.34); Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in an
arithmetic progression*, Proc. LMS (3) 64 (1992), Lemmas 6.1, 8.2–8.8, 9.4, 10.3, Tables 2, 4, 5, 7,
10; Heath-Brown, *Siegel zeros and the least prime in an arithmetic progression*, Quart. J. Math.
Oxford (2) 41 (1990), Corollary 1.
