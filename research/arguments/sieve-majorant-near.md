# A sieve-majorant near-density inequality

2026-09-27. New analytic deduction, first rigorous component certificates and
floating measurements.
* This note derives the graded near lemma. [PROOF.md](../PROOF.md) §6 states
  it in final form and uses it as the only near-density inequality of the
  current proof.
* This note does not establish a new complete exponent. §6 records its
  numerical evidence, §7 lists what a complete cover needs, and
  STATE records the covers.
* An adversarial review (§8) found no fatal problem. Its two repairs are built
  into §§2–3 below.
* §§2e–2g describe the steps added for the simplified proof. Each has had one
  review (review 5, §8).

## 1. The idea

The two-test near inequality (foundation §3) detects
each ordinary zero with a Λ-weighted prime sum. It controls the Gram matrix of
the detector vectors through Lemma 3.1, so every off-diagonal entry is at most
the conductor term `(φ/2)g(0)` of the quotient character. This has two costs:

* A crowd of `N` characters pays `N²(φ/2)g(0)`, so the response must exceed
  `sqrt(R_B(φ/2)g(0))` before the inequality says anything.
* The response anchor `s` must lie below every global lower bound for zeros of
  quotient characters, `s ≤ min(λ', λ₂^{global}, 1.9)`. In the binding 4.30
  cases this is only `0.73–0.76`.

Two independent changes remove these costs.

1. **Decoupling.** Split the Cauchy–Schwarz weight, `n^{-s}=n^{-s₁/2}·n^{-(s-s₁/2)}`.
   The Gram form then sits at the safe anchor `s₁`, while the response anchor
   `s` may sit at the crowd (up to its own rightmost zero). This alone halves
   the crowd bound at `λ=1.75` (§4).
2. **Sieve majorant.** For primes `n>q^{t₀}` with `t₀>φ`, majorize Λ by a
   Selberg weight inside the Gram quadratic form:

   \[
    \Lambda(n)\le (\log n)\Bigl(\sum_{d\mid n,\ d\le D}\lambda_d\Bigr)^2 ,
    \qquad D^2\le n\,q^{-\phi-\varepsilon}.
   \]

   Every off-diagonal term becomes a smooth character sum of length at least
   `q^{φ+ε}`. Burgess makes it `o(1)`, with no zeros of the quotient character
   involved. The price is a diagonal inflation `κ(t)=log n/log D → 2t/(t−φ)` at
   `n=q^t`, which is at least the parity factor 2. This removes the `N²` term
   for long primes and extends the useful range to `λ≥1.9`.

H §11 and X Lemma 5.1 use the same sieve-weighted Gram, paired with the
mollified 1-detector. Here it is paired with the Λ-detector of H §12.

## 2. Statement

Put `ℓ=log q`, `t_n=log n/ℓ`, and `φ=1/3` (any valid uniform character-sum
exponent for quotient characters may be used). Fix the following before
`q→∞`:

* an admissible detector `f ≥ 0` on `[0,2γ]`, e.g. the parabolic
  autocorrelation `f_γ` of the foundation note, with transform `F`;
* a response anchor `s>0` and a *safe* anchor `s₁ ≤ s`. The safe anchor obeys
  the existing global shift rule. With `s₁ ≤ λ₁^{lo}` (every zero of every
  character has parameter at least `s₁`), no exceptional correction arises;
* an admissible short Gram test `g₁`;
* a sieve weight `H ≥ 0` that is a finite sum of step cells
  `h_k 1_{[t_k,t_{k+1})}` with `t_0>φ+2ε'`;
* such that `ω(t):=g₁(t)e^{s₁t}+H(t)>0` on the support of `f`.

**Representatives.** Fix `M` large and `s_max`, and let `K₀` bound the number
of zeros with parameter `≤s_max` and height `≤1+δ` (the local discs reach above
height 1). Such a bound is `O(1)` by
log-free density. By pigeonhole choose a strip height `T*∈[1/2,1]` (depending
on `q`) such that no such zero lies within normalized distance `M` of
`|γ|=T*`. Select for each character its rightmost zero with `|γ|≤T*`. X
Lemma 5.1 allows any one zero per character in `|t|≤1`, so the far inequality
is unchanged. Representatives can only move right, so the count row and the
ordinary lower bound remain valid. X Lemma 3.10 is used in its localized form:
its proof only uses the disc `|1−ρ|≤δ` at height 0.

Let `χ₁,…,χ_N` be distinct nonprincipal characters outside the distinguished
first family, with representatives `ρ_j=1−λ_j/ℓ+iγ_j` and `λ_j ≥ s`. Every
other zero of `χ_j` in the local disc about `1+iγ_j` with parameter below `s`
lies outside the strip. It is therefore at normalized distance greater than
`M` from `ρ_j`, and all such zeros together cost at most
`K₀ sup_{|Im z|≥M}|F(z)| < η/2`.

Define

\[
 r_j=F(\lambda_j-s)-\tfrac{\phi(\chi_j)}2 f(0),\qquad
 I_B=\int \frac{e^{2st}f(t)^2}{\omega(t)}\,dt ,
\]
\[
 D_1=\int g_1(t)e^{s_1t}\,dt,\qquad
 D_2=\sum_k h_k\,\frac{t_{k+1}^2-t_k^2}{2\delta_k},\quad
 \delta_k=\frac{t_k-\phi}2-\varepsilon',\qquad
 d_1=\tfrac{\phi}2\,g_1(0).
\]

`D₂` is the exact finite-partition value. As the cells shrink it tends to
`∫κH` with `κ(t)=2t/(t−φ)`.

**Theorem (sieve-majorant near inequality).** For every fixed `η>0` and
`q ≥ q₀(η, tests)`, and for all `a_j ≥ 0`,

\[
 \Bigl(\sum_j a_j (r_j-\eta)\Bigr)_+^2
 \le (1+\eta) I_B\Bigl[\sum_j (D_1+D_2+c_j-d_1)a_j^2
                        + (d_1+\eta)\Bigl(\sum_j a_j\Bigr)^2\Bigr].
\]

Here `c_j ≥ 0` is the foundation note's exceptional-quotient correction of the
`g₁` Gram at `s₁`; it is `0` when `s₁ ≤ λ₁^{lo}`. Dividing by `I_B(D₁+D₂)`
gives the form (TT) of the foundation note, so the exact scalar threshold
identity (T) applies.

Characters with `λ_j<s` are omitted (coefficient zero). Different anchors `s`
give different valid inequalities for the same configuration. Taking `H=0`
recovers the decoupled two-test inequality, and `H=0, s=s₁` recovers the
original one.

### 2a. The family row (anchor at most `λ₁^{lo}`)

In an inside leaf the first zero `ρ₁` lies in the height-one strip, with
`λ₁∈[a,b]`. Take `s₁≤s≤a`. Then every zero of every character in the source
rectangle has parameter at least `λ₁≥s`. So the local explicit formula at
`1−s/ℓ+iγ_j` has no zero to the right of the test point for any character. All
zeros other than the retained one have nonnegative real part and are dropped.

Hence the theorem holds with the following characters included together with
the ordinary ones:

* the `n` first-family characters (`n=2` for a nonreal pair), each with
  representative `ρ₁` and response at least `F(b−s)−(φ/2)f(0)`;
* a reserved second family of `n₂` characters with `λ∈[lo₂,hi₂]`, each with
  response at least `F(hi₂−s)−(φ/2)f(0)`.

The representative-strip argument is not needed, because no zero has parameter
below `s`. The Gram part is unchanged. Every quotient character has all zeros at
parameter at least `λ₁^{lo}≥s₁`, so Lemma 3.1 applies with `c_j=0`. The sieve
part does not involve zeros. In threshold form the fixed families contribute
`n(v_f−τ)_+²/D` and `n₂(v₂−τ)_+²/D` to the left side. They are subtracted
from the budget exactly as in the repository's old near row.

This is the repository's two-test row with three changes: the anchor is at most
`λ₁^{lo}`, so the corrections `C_G, C_Z, E` vanish; the Gram test is
decoupled; and the parameters `(γ,g₁)` are chosen for the low family rather
than the crowd. At the binding leaves it bounds the low family much more
tightly than the old row. With the first and second families present:

| Leaf | low family at `λ₃` | old near row allows | family row allows |
| --- | --- | ---: | ---: |
| 193 (rr, `λ₁≈.70`, reserved pair `≤.852`) | `λ₃=.952` | 9.29 | 5.49 |
| 2557 (complex, `λ₁≈.78`, 2 below `λ₃`) | `λ₃=.868` | 6.57 | 2.99 |

(floating; `family_row.py`, sieve part `H=0` since it does not help such small
crowds).

### 2b. Graded rows: a response anchor per character

A row with anchor `s` omits every character with `λ_j<s`. The adversary
therefore places its crowd just below each anchor, where only the next lower
anchor sees it, and at distance up to the anchor spacing. This is the main loss
of the menu of §6b. The Cauchy–Schwarz step allows a separate response anchor
for each character.

Fix a reference anchor `s` and, for each character, an anchor `s_j≤min(λ_j,s)`.
Put `δ_j=s−s_j≥0`. Since `e^{s_jt}=e^{st}e^{−δ_jt}`,

\[
 \sum_ja_jR_j=-\Re\,\ell^{-1}\sum_n\frac{\Lambda(n)}n e^{st_n}f(t_n)Y_n,\qquad
 Y_n=\sum_ja_je^{-\delta_jt_n}\chi_j(n)n^{-i\gamma_j}.
\]

Apply Cauchy–Schwarz with the same weight `ω`. The first factor is `I_B` at the
reference anchor. The Gram entries become

\[
 \ell^{-1}\sum_n\frac{\Lambda(n)}n\,\omega(t_n)e^{-(\delta_j+\delta_k)t_n}
 \chi_j\bar\chi_k(n)n^{-i(\gamma_j-\gamma_k)} .
\]

* **`g₁` part.** (In this note "Lemma 3.1" is the conductor bound for a
  nonprincipal character, X Lemma 3.2 / HB Lemma 5.2 in the sources' own
  numbering. X Lemma 3.1 is the principal-character asymptotic.) This is the
  conductor bound for `χ_j\barχ_k` with the admissible test
  `g₁` at shift `σ_{jk}=s₁−δ_j−δ_k≤s₁`. Every zero of every quotient character
  has parameter at least `λ₁^{lo}≥s₁≥σ_{jk}`, so the off-diagonal entries are at
  most `(φ/2)g₁(0)+o(1)` as before. For `σ_{jk}<0` the test point has real part
  above 1; X Lemma 3.2 allows this (`|σ−1|≤(\log ℓ)^{1/2}/ℓ` on both sides) and
  every zero drops. The finitely many `σ_{jk}` make the bound uniform. The
  diagonal is `∫g₁(t)e^{(s₁−2δ_j)t}dt` (X Lemma 3.1).
* **Sieve part.** The weight `H(t)e^{−(δ_j+δ_k)t}` is nonnegative and of
  bounded variation on each cell. The majorant and Burgess argument of §3 give
  `o(1)` off the diagonal. The diagonal is at most
  `Σ_k h_k e^{−2δ_jt_k}(t_{k+1}²−t_k²)/(2δ_k)`.

The theorem therefore holds with `r_j=F(λ_j−s_j)−(φ/2)f(0)` and per-character
diagonal `D_j=D(δ_j)−d₁` in place of `D₁+D₂−d₁`, where

\[
 D(\delta)=\int g_1(t)e^{(s_1-2\delta)t}dt+\sum_kh_ke^{-2\delta t_k}\frac{t_{k+1}^2-t_k^2}{2\delta_k}.
\]

The response step is unchanged for each character at its own anchor
`s_j≤λ_j`. It uses the representative-strip argument of §2, or no argument at
all when `s_j≤λ₁^{lo}`. The exact threshold form (T) of the foundation note
allows unequal diagonals.

In a leaf, an ordinary bin `[lo,hi]` below `s` uses `s_j=lo`. Its feature is
`(F(hi−lo)−1/6)/\sqrt{I_BD(0)}` and its diagonal is `D(\lfloor s−lo\rfloor_{1/200})−d₁`,
normalized by `D(0)`. `D` decreases in `δ`, so rounding `δ` down is safe. Bins
above `s` are as before. The first family uses `s_j=\min(λ₁^{lo},s)`, and a
reserved second family also uses `\min(λ₁^{lo},s)`. Then every zero lies to the
left of its test point, so the family's height-one representative, whose
parameter is at most `hi₂`, can be retained without the strip argument. (An
anchor `\min(lo₂,s)>λ₁^{lo}` would need the strip representative, whose
parameter need not stay below `hi₂`. Review, §8.) A bin whose `D(δ)−d₁` is not safely
positive is omitted. The family row of §2a is the graded row with `s=s₁`.

By Cauchy–Schwarz, `I_B(s)D(δ)≥F(−(s−δ))²`. This is the same lower bound as for
a row anchored at `s−δ`. The loss relative to a dedicated anchor is second
order in `δ`. For a crowd just below an anchor, the menu loss was first order in
the spacing.

### 2c. A real first character with a nonreal zero (rc)

Let `χ₁` be real with first zero `ρ₁=1−λ₁/ℓ+iγ₁`, `γ₁≠0`, and put `μ₁=γ₁ℓ`.
Then `\barρ₁` is also a zero of `χ₁`. Nothing in §2 requires the vectors to
belong to distinct characters, so the family row (`s=s₁`, `H=0`) may carry both
vectors `z_±(n)=χ₁(n)n^{∓iγ₁}`.

* **Responses.** At the test point `1−s/ℓ±iγ₁`, all zeros of `χ₁` have
  parameter at least `λ₁≥s`. Retaining both `ρ₁` and `\barρ₁` gives
  `R_±≥F(λ₁−s)+\Re F(λ₁−s+2iμ₁)−(φ/2)f(0)−η`.
* **Pair entry.** `χ₁²=χ₀`, so `⟨z_+,z_−⟩=ℓ^{−1}\sum_{(n,q)=1}Λ(n)n^{−(1−s₁/ℓ)−2iγ₁}g₁(t_n)`.
  This is the principal-character sum at height `2γ₁`. By X Lemma 3.1
  (HB Lemma 5.3), uniformly for `|2γ₁|≤ℓ`, it equals the pole term
  `G₁(−s₁+2iμ₁)` up to `O(1/\log ℓ)`. Hence `\Re⟨z_+,z_−⟩=c(μ₁)+o(1)` with
  `c(μ)=\Re G₁(−s₁+2iμ)`. The sieve part is identically zero in this row (it is
  asserted).
* **Other entries.** `χ₁\barχ_k` is nonprincipal for every ordinary `χ_k`, so
  Lemma 3.1 bounds these entries by `d₁` as before.

In the Gram bound the pair entry exceeds `d₁` by at most `(c−d₁)_+`. Since
`2a_+a_−≤a_+²+a_−²`, the pair enters the threshold form as two characters with
feature `(F(b−s)+R_{lo}−1/6)/\sqrt{I_BD}` and diagonal
`D+(c_{hi}−d₁)_+`. Here `R_{lo}` and `c_{hi}` bound `\Re F(λ₁−s+2iμ)` from below
and `c(μ)` from above over the height range.

The height is split into `μ₁∈[0,1]` and `μ₁≥1`. Both bounds come from point
evaluations on a grid in `μ`, with second-derivative slack
`|∂_μ²|≤4∫t²(\cdot)`, and a Lipschitz bound in `λ₁`. For `μ≥10` the closed
form of the transform gives the tail. `R_{lo}=0` is used there, which is valid
by admissibility. For `μ₁≥1` the pair is two nearly orthogonal characters
(`c_{hi}≈d₁`). For `μ₁≤1` the conjugate zero doubles the response instead.
Either way the rc first family has about twice the weight of the single-vector
treatment. On leaf 1083 at `L=4.00` the floating maximum drops from 1.05 to
0.82 (`μ₁≤1`) and 0.97 (`μ₁≥1`). Both parts certify.

### 2d. Location inputs used with the new rows

* **Refined rr third-family bound** (`third_refine.py`). X, Lemma 4.4, real
  character with real zero: inequality (4.31) with `γ=1.04`, valid for
  `λ₁∈[.44,.80]`, `λ₂≤1.176`. X applies it on three `λ₁` intervals, giving
  Table 10. Applied on the leaf's own `[a,b]`, with the global `λ₂` capped by a
  reserved local second family (as in the repository's complex rule X_4_28),
  the same computation gives e.g. `λ₃>1.0884` instead of `.952` for
  `λ₁∈[.7025,.705]`. The code reproduces Table 10 on X's own intervals
  (1.1760 at the cap 1.176, 1.0558, 0.9524). The repository's third-family rule is then
  re-applied with the new value.
* **Second-family splits** (`leaf_driver.split_certify`). A hard leaf is
  replaced by the children of the repository's `split_specs(·,'second',mid)`,
  which exhaust the parent. Each child is regenerated by the repository
  builders. This removes the mismatch between the second-family cost (at `lo₂`)
  and its near response (at `hi₂`), and it lowers the complex `λ₃` rule's cap.

### 2e. Outside-buffer and hidden-family models

The repository certifies two further LP families with the old near row
through its own relaxations:

* outside-buffer leaves (`first_outside_blocks.first_near`);
* the inside hidden-family branches of `inside_repair` identities nodes
  (`separated_blocks.near_block`).

The following changes are made for these families.

* **Count row.** Both inputs carry the repository's third-family count
  (`count_cost`, budget 2), but its verifiers did not use it. The rule is
  global: at most two ordinary characters below the global λ₃, and the
  ordinary columns exclude the first family, whose local zeros are the hidden
  columns. It is added as one more LP row. Representatives only move right,
  so a character in a counted row belongs to a family with parameter below λ₃.
* **Outside graded rows.** A reserved height-one second family joins every row
  with anchor `≤λ₁^{lo}`, as in §2a.
  * The outside first family (global zero at normalized height `|μ₁|>C_B`)
    joins the **family row only** (`s=s₁`, sieve part asserted zero; mode
    `outside_first`). The third review (§8) confirmed this.
  * All test and Gram points lie within X Lemma 3.4's `R(9l)`: `χ₁` at height
    `≤l`, quotients against height-one vectors at `≤l+1`, and `χ₁` against
    `\barχ₁` at `≤2l`.
  * By X Lemma 3.3 no zero lies in `R(10l)\R(l)`. So every disc zero is in
    `R(l)`, with parameter at least `λ₁`, or far to the left.
  * Graded rows with a sieve part carry only the second family.
* **Outside hidden columns in the family row** (mode `hidden='outside'`, used
  by the simplified proof; found valid in review 5, §8).
  * The hidden columns are, for each first-family character, its rightmost
    zero in the prime window `R_P`; there is at most one per character.
    Earlier they had feature 0. In the family row they now get the feature
    `(F(hi_h-s₁)-1/6)/\sqrt{I_BD}`.
  * A hidden entry and the global entry of the same character have normalized
    heights at least `C_B-C_P≥M` apart. Their Gram entry is the principal sum
    at that height difference, `G₁(-s₁+i(μ₁-μ_h))+o(1)` (X Lemma 3.1). Its
    modulus is at most `η≤d₁` once `M` is large.
  * All other pairs are distinct characters. The row is therefore an instance
    of the lemma with separated-height entries (PROOF.md §6.1, kind 2).
  * On root 1492 at 3.99 this row lowers the floating maximum from about .97
    to .88 with no old outside block row.
* **Hidden-family branch rows.** The first zero is inside, so the first family
  and the reserved second family join the rows as in §2a. The hidden columns
  are the hidden family's local height-one centers, one per character. The
  family's global zero is the old row's shadow term only.
  * In `distinct` branches the family row gives the hidden columns features
    `(F(hi−s₁)−1/6)/\sqrt{I_BD}` (mode `graded_block_famh`, sieve part zero).
    They are distinct characters from all others at heights at most 2, so the
    argument of §2a applies. The fourth review (§8) confirmed this.
  * In `same_reserved` the hidden columns can be the reserved family's own
    fixed-term zero. Two identical vectors have Gram entry `D`, so the hidden
    columns keep feature 0 there. They also have feature 0 in rows with a
    sieve part. In the `unhidden` branch there are no hidden rows, and
  the refined rr third bound (below) is applied as for ordinary inside leaves.
  The other branches reuse the ordinary grid for their hidden rows, so they keep
  the repository's bound.
* **Splits.** A hard leaf is replaced by the repository's
  `split_specs(·,'second',mid)` children. Inside leaves are regenerated by
  `make_endgame`, outside leaves by `first_out_input`. The children exhaust the
  parent.

### 2f. Shifted row and the second family's anchor (simplified proof)

These two steps let the simplified proof drop the old two-test near row. Both
were found valid in review 5 (§8).

* **Shifted row** (mode `families='shifted'`).
  * **Anchors.** The reference anchor is the repository's validated shift
    `s=min(1.9,λ′_lo,source_l2)`. The row is used only when `s≥λ₁^{lo}`
    (`graded_driver.has_shifted`; the row builder asserts `s≥a`). This is a
    condition, not a fact: on node 1501/1, `s=.7225<λ₁^{lo}=.72375`, and the
    row is not used there. The Gram part stays at `s₁≤λ₁^{lo}` with `H=0`.
  * **First-family response.** The first family enters at anchor `s`,
    although its zero may lie to the right of the test point. Every other
    first-family occurrence has `λ≥λ′≥s`. The retained zero gives
    `F(λ₁-s)≥F(b-s)`, since `F` decreases on the whole real line.
  * **Type `rc`.** For a real `χ₁` with nonreal `ρ₁`, the conjugate zero
    `\barρ₁` lies at the same parameter and height difference `2μ₁`. Its
    term is bounded below by `-C_Z`, with `C_Z=sup_{Re z≥a-s}(-Re F(z))`.
    `C_Z` is enclosed by the repository's `C_upper`.
  * **Ordinary characters and the second family** use anchors
    `min(own lower bound,s)`. Here `s≤source_l2≤λ₂` means that no zero of any
    character outside the first family lies to the right of a test point.
  * **Role.** This row carries the first family's large response at the shift,
    which is what the old two-test row contributed. Unlike the old row it
    needs no `C_G` or `E` corrections, because its Gram form sits at `s₁`.
* **Second-family anchor up to the global `λ₂` bound** (`sec_anchor='l2'`).
  * The reserved second family takes anchor
    `σ₂=min(max(a,min(source_l2,lo₂)),s)` instead of `min(a,s)`.
  * Its characters are not first-family characters. Every one of their zeros
    in `R(l)` therefore has `λ≥λ₂≥source_l2`, and also `λ≥λ₁≥a`. No zero lies
    to the right, and the height-one representative `ν₂≤hi₂` is retained
    without the strip argument.
  * This relies on `source_l2` being a lower bound for the **global** `λ₂` in
    every retained node.

### 2h. The first family's second zero in the family row

Complex leaves with a finite gap `λ′∈[p,p^{hi}]` failed at 3.99 when the gap
was lowest (roots 1285, 1296, 1307, 1378). There the envelope charges the
first family's other zero `ρ′`, but the near rows ignore it.

The conjugate-pair argument of §2c carries over. Each first-family character
`χ` has two entries in the family row:
* `(χ,γ₁)`, whose response is `F(λ₁-s₁)+Re F(λ′-s₁+iy)`;
* `(χ,γ′)`, whose response is `F(λ′-s₁)+Re F(λ₁-s₁-iy)`.

Here `y` is the normalized height difference. The Gram entry of the two is
the principal sum at height `y`, bounded by `c^{hi}` over each range of `y`.
The leaf is split by `y∈[0,1]`, `[1,3/2]`, `[3/2,2]`, `[2,3]`, `[3,5]`,
`[5,∞)` (PROOF.md §6.5).

Floating prototype on leaf 1285/0 (`λ₁∈[.68,.6825]`, gap `[.975,1.06)`,
reserved pair `[.768,.784)`) at 3.99, with rows F, S, 1.5, 1.9, 2.3:

| `y` piece | floating maximum |
| --- | ---: |
| none (baseline) | .99242 |
| `[0,1]`, `[1,3/2]`, `[3/2,2]`, `[2,3]` | infeasible |
| `[3,5]` | .908 |
| `[5,∞)` | .934 |

The prototype computed the correlation excess with a slightly wrong
normalization. The pieces with `c^{hi}≤d₁`, namely `[3,5]` and `[5,∞)`, are
unaffected.

Exact certificates at 3.99 through the driver's split, each re-verified:

| Leaf | Certified maximum | Boxes | Certification time |
| --- | ---: | ---: | ---: |
| 1378/0 (unreserved, gap `[.958,1.03)`) | .99991 | 5,437 | 324 s |
| 1307/0 (gap `[.971,1.06)`, reserved pair `[.768,.784)`) | .999985 | 2,966 | 513 s |
| 1285/0 (gap `[.975,1.06)`, reserved pair `[.768,.784)`) | .999985 | 2,784 | 749 s |

Neither needed the reservation split or second-family splits.

### 2g. The reserved second family as LP columns

The 4.30 leaf model charges a reserved second family at the two ends of its
interval `[lo₂,hi₂]`:
* its objective `n₂G(lo₂)` at the low end;
* its far cost `n₂w(hi₂)` and its near features at the high end.

The adversary pays the worst of both, which is what second-family splits
repaired. The graded-near leaves instead give the family LP columns: sub-bins
`[l_j,r_j]` of `[lo₂,hi₂]` (grid `1/400`), with masses `z_j≥0` and `∑z_j=n₂`.
* Column `j` has objective `G(l_j)` and far cost `w(r_j)`.
* In each row its anchor is `min(max(a,min(source_l2,l_j)),s)` and its feature
  is taken at `r_j`.
* The family's characters share one height-one parameter `ν₂`, so the actual
  configuration is a feasible point. The equality has a free dual in the
  certificate ([PROOF.md](../PROOF.md) §7).

This is equivalent to splitting `[lo₂,hi₂]` into 400ths, at the cost of one LP
instead of a certificate per piece. Floating maxima at `L=3.99`, with the
family, shifted and graded 1.5, 1.9 and 2.3 rows:

| Leaf | fixed family | columns |
| --- | ---: | ---: |
| 1230/0 (complex, `[.6625,.665]`, `ν₂∈[.81,.88]`) | 1.01079 | .97692 |
| 1225/0 (`ν₂∈[.88,.95]`) | .99407 | .96479 |
| 1244/0 (`ν₂∈[.81,.88]`) | 1.01218 | .97822 |

At lower exponents, with the same rows:

| Leaf | `L` | fixed family | columns |
| --- | --- | ---: | ---: |
| 1244/0 | 3.97 | 1.03924 | .99206 |
| 1244/0 | 3.95 | 1.06725 | 1.01954 |
| 1230/0 | 3.95 | 1.06578 | 1.01806 |

With columns, even the hardest known leaf is just below 1 at 3.97 and above
it at 3.95. More rows or splits would lower these values somewhat.

## 3. Proof

**Response.** This is the existing near argument (X (5.35)–(5.38), foundation
§3). Apply the local-disc explicit formula (X Lemmas 3.1–3.2) to `χ_j` at
`s_j=1−s/ℓ+iγ_j` with the admissible test `f`. Zeros of `χ_j` in the disc with
parameter at least `s` have terms with nonnegative real part. The others cost
less than `η/2` by the choice of representatives. Retaining only `ρ_j`, whose
term is `F(λ_j−s)`, gives

\[
 -K_f(s_j,\chi_j):=-\ell^{-1}\sum_n\Lambda(n)\,\Re\bigl(\chi_j(n)n^{-s_j}\bigr)f(t_n)
 \ \ge\ r_j-\eta/2-o(1).
\]

**Cauchy–Schwarz with a split weight.** Put `X_n=Σ_j a_jχ_j(n)n^{-iγ_j}`.
Since `n^{-s_j}=n^{-1}e^{st_n}n^{-iγ_j}`,

\[
 \sum_j a_j(r_j-\eta/2-o(1))\le \Bigl|\ell^{-1}\sum_n\frac{\Lambda(n)}n e^{st_n}f(t_n)X_n\Bigr|
 \le \Bigl(\ell^{-1}\sum_n\frac{\Lambda(n)}n\frac{e^{2st_n}f(t_n)^2}{\omega(t_n)}\Bigr)^{1/2}
     \Bigl(\ell^{-1}\sum_n\frac{\Lambda(n)}n\,\omega(t_n)|X_n|^2\Bigr)^{1/2}.
\]

The first factor is `I_B+o(1)` by the prime number theorem. This uses only the
principal character, and the integrand is bounded, piecewise continuous and
compactly supported. The second factor does not involve `s`. Split it as
`Q₁+Q₂` according to `ω=g₁e^{s₁t}+H`.

**The short Gram `Q₁`.** Expanding `|X_n|²`,

\[
 Q_1=\sum_{j,k}a_ja_k\,\ell^{-1}\sum_n\Lambda(n)n^{-(1-s_1/\ell)}g_1(t_n)
      \chi_j\bar\chi_k(n)n^{-i(\gamma_j-\gamma_k)} .
\]

This is exactly the foundation note's Gram form for `(g₁,s₁)`. Its diagonal is
`D₁+o(1)` (principal pole). Each off-diagonal entry is at most
`(φ/2)g₁(0)+o(1)` plus the exceptional correction: apply Lemma 3.1 to the
quotient character and drop its local zeros, which is valid by admissibility
of `g₁` and the rule on `s₁`. Lemma 3.1 bounds these entries even though `H`
also weights some of the same `n`. So
`Q₁ ≤ Σ_j(D₁+c_j−d₁)a_j²+d₁(Σ_j a_j)²+o(1)(Σa_j)²`.

**The long Gram `Q₂` (new).** Treat each cell `k` separately. Let
`D_k=q^{δ_k}`, let `λ_d=μ(d)log(D_k/d)/log D_k` for `d≤D_k`, and put
`ν_k(n)=(Σ_{d|n}λ_d)²≥0`.

For primes `p≥q^{t_k}>D_k` we have `ν_k(p)=λ₁²=1`, so `Λ(p)=(log p)ν_k(p)`.
Composite non-prime-powers have `Λ=0`. Prime powers `p^k` (`k≥2`) with
`n≥q^{t_k}` contribute at most `(Σ_j a_j)² O(q^{-t_k/2}ℓ)`. For `(n,q)>1` we
have `X_n=0`. Hence

\[
 Q_2\le\sum_k h_k\sum_{j,k'}a_ja_{k'}\,T^{(k)}_{jk'}+o(1)\Bigl(\sum_ja_j\Bigr)^2,\qquad
 T^{(k)}_{jk'}=\ell^{-1}\sum_{q^{t_k}\le n<q^{t_{k+1}}}\frac{\log n}{n}\,\nu_k(n)\,\psi_{jk'}(n)n^{-i\tau_{jk'}},
\]

with `ψ_{jk'}=χ_j\barχ_{k'}` and `|τ_{jk'}|≤2`.

*Diagonal.* When `j=k'`, drop the coprimality condition, which can only
increase the sum. We have `Σ_{n≤x}ν_k(n)=x/log D_k+O(x/log²D_k)` for
`x≥D_k`: this is Graham's estimate, H (11.13) with `U=1`. Alternatively,
expand `Σ_{n≤x}ν=xΣλ_dλ_e/[d,e]+O(D_k²)` with
`Σλ_dλ_e/[d,e]=1/log D_k+O(log^{-2}D_k)`. Partial summation gives

\[
 T^{(k)}_{jj}\le \frac{t_{k+1}^2-t_k^2}{2\delta_k}+O(1/\ell).
\]

*Off-diagonal.* When `j≠k'`, `ψ` is nonprincipal. Write
`T^{(k)}_{jk'}=Σ_{d,e≤D_k}λ_dλ_eψ([d,e])Σ_mψ(m)W(m[d,e])`, where
`W(y)=ℓ^{-1}(\log y)y^{-1-iτ}1_{[q^{t_k},q^{t_{k+1}})}(y)`.

The inner sum is taken over an interval of length at least
`q^{t_k-2δ_k}=q^{φ+2ε'}`. Use partial summation against Burgess partial sums,
as in X's proof of (5.22) (X Lemma 5.2; H Lemma 2.1 with `k=3`). Imprimitive
`ψ` costs only `q^ε` (H §2). The result is

\[
 \Bigl|\sum_m\psi(m)W(m[d,e])\Bigr|\ll \ell^{O(1)}\,[d,e]^{-1}\,
      \Bigl(\frac{q^{\phi}[d,e]}{q^{t_k}}\Bigr)^{\eta_0}q^{\varepsilon},
\]

for some fixed `η₀>0` once the Burgess `ε` is small relative to `ε'`. The
indicator cell costs nothing because only bounded variation is used. Summing
over `d,e≤D_k` with `Σ[d,e]^{-1+η₀}≪D_k^{2η₀}ℓ³` gives
`T^{(k)}_{jk'}≪q^{-c(ε')}`, uniformly in the characters and heights.

Every error is either uniform per character, and absorbed by `r_j−η`, or a
uniform `o(1)` times `Σa_j²≤(Σa_j)²` or `(Σa_j)²`. No bound on the number of
characters is needed. ∎

## 4. Strength in the binding cases

For a crowd of `N` characters at one parameter `λ`, the old inequality gives
`N ≤ R_BR_G/(r²−R_B(φ/2)g(0))`. It becomes void once `r²≤R_B(φ/2)g(0)`. At the
safe shifts of the binding cases this happens near `λ≈1.7`. This is why the
4.00 diagnostics place a crowd of about 350 characters at `λ≈1.75`, priced
only by the far resource.

The table below gives floating crowd bounds (`s₁=1.0`, `s=λ`). The last column
uses parameters optimized per anchor: `γ≈.93–.99`, `g₁=f`, `t₀≈.34–.44`.

| λ | far resource | old, `s=s₁` | decoupled old (`H=0`) | sieve near |
| ---: | ---: | ---: | ---: | ---: |
| 1.50 | 233 | 58.6 | 49.0 | 64 |
| 1.75 | 372 | 622 | 332 | 116 |
| 2.00 | 598 | void | void | 204 |
| 2.25 | ≈968 | void | void | 357 |
| 2.50 | 1576 | void | void | 632 |

A rigorous input at `s₁=.76`, `s=1.75` (§6) gives 121.0 at `λ=1.75`. The
reviewer's coarse joint optimization reached about 48, 97 and 178 at
`λ=1.5, 1.75, 2.0`. Every value here is a bound for a crowd at one `λ`; the LP
decides where the adversary actually places mass.

## 5. Relation to existing work

* H §11 and X Lemma 5.1 use the sieve-weighted Gram with the 1-detector.
  H §12 and the two-test argument use the Λ-detector with Lemma 3.1
  off-diagonals. H §16(9) remarks that a weighted Lemma 12.1 seemed
  unavailable. The combination here is not in H, X or the repository's
  earlier notes. It is assembled from classical parts: the Graham–Selberg
  sieve Gram, the Brun–Titchmarsh-type large sieve for primes, and Burgess.
  Novelty against Motohashi's sieve/large-sieve density work and more recent
  explicit log-free density papers has not been checked.
* The pole part of the all-zero envelope is also a Λ-weighted character sum.
  The same majorant makes the collective envelope decay like `N^{-1/2}` per
  character, but only for the portion of `f_p` with `t>φ`. For the 4.30 kernel
  (`T=.416829`), about 98% of the pole mass at `λ=1.75` lies below `t=1/3`, so
  this helps only wider kernels.

## 6. Numerical evidence

The code is in [computations/sieve_near/](../../computations/sieve_near/):

* `sieve_inputs.py`: outward `I_B`, `D`, `d` and row features for the
  water-filling step weight `h_k=(e^{sm}f(m)/\sqrt{μκ_k}-g₁(m)e^{s₁m})_+` of §2.
  Mesh bounds use the monotonicity of `f`, `g₁` and the exponentials.
* `propose_params.py`: floating choice of `(γ,g₁,t₀,μ)` per safe anchor and
  anchor. It is a proposal only; every value is re-enclosed.
* `certificate2.py`, `certificate3.py`: multi-threshold certificates (§6a),
  checked with exact integers.
* `certificate_out.py`: the same for the outside-buffer regime of
  `computations/near`, whose old near row, hidden first-family columns and
  hidden count are the repository's own `first_near` relaxation.
* `leaf_driver.py`, `batch.py`, `verify_all.py`: regenerate repository leaves
  at a target exponent, choose anchors, certify, and replay.

### 6a. Second-order threshold certificates

Each near inequality has the scalar form `∃τ: Φ(τ) ≤ c`, where
`Φ(τ)=Σ_j c_j(v_j−τ)_+²+κτ²` is convex and `C¹`. The repository's
certificates cover the threshold range by intervals `[a,b]`. On each interval
they use costs at `b` and the budget at `a`. The two first-order errors add,
although `Φ'(τ*)=0` at the adversary's own threshold.

Instead, let `m=(a+b)/2` and `h=(b−a)/2`. Convexity gives
`Φ(τ*) ≥ Φ(m)+Φ'(m)(τ*−m)`, so either `Φ(m)−hΦ'(m) ≤ c` or
`Φ(m)+hΦ'(m) ≤ c`. Term by term these are exact linear constraints:

* `(v−m)_+²±2h(v−m)_+=((v−m)_+±h)²−h²`, and
* `m²∓2hm=(m∓h)²−h²`.

A box therefore needs one dual per case, and its error is second order in the
width. With several near inequalities, each dimension contributes two cases.
`certificate3.py` uses the one-case first-order relaxation where it already
suffices, and the two tangent cases only on dimensions whose constraint is
active. The old near dimension is also trimmed to the window where its concave
budget is nonnegative. On leaf 567 at 4.30 with no sieve rows, the
repository-style first-order cover needs 262 intervals; the second-order cover
needs 18 boxes.

### 6b. Results

> **Superseded.** The plain-row results below were built before the exclusion
> fix of §8. Their trees are not proofs, although their maxima probably stand.
> The claims rest on the regenerated graded-row covers of §6c.

*Complete integer certificates on the hardest 4.30 leaves.* Each leaf is
regenerated by the repository's builders at the target `L`. The old near,
far, count and objective rows are unchanged. The sieve rows use the safe
anchor `s₁=⌊λ₁^{lo}⌋_{1/50}`.

| Leaf | `L` | anchors | maximum | boxes |
| --- | --- | --- | ---: | ---: |
| 567 inside (rr, `λ₁≈.75`) | 4.20 | 1.6 | .99761 | 54 |
| 567 inside | 4.15 | 1.5, 1.8, 2.1 | .99965 | 518 |
| 1760 inside (complex, `λ₁≈.73`) | 4.20 | 1.6, 1.65 | .99943 | 92 |
| 1294 inside, all 9 leaves | 4.20 | 1–4 each | ≤.99999 | 23–256 |
| 1492 outside (binding outside root at 4.30) | 4.20 | 1.7 | .99942 | 142 |
| 193 inside (rr, `λ₁≈.70`, 821 bins) | 4.20 | 1.5, 1.7, 1.9 | .99990 | 391 |
| 281 inside | 4.17 | 1.3, 1.6, 1.9 | .99957 | 387 |
| 766 inside | 4.17 | 1.5, 1.7 | .99975 | 89 |
| 747 inside | 4.17 | 1.5, 1.7 | .99899 | 89 |
| 113 inside | 4.17 | 0.9, 1.3, 1.6 | .99743 | 241 |

Anchors are chosen greedily from the menu `0.9, 1.1, …, 2.5`. At each step
the anchor added is the one that most lowers the floating LP maximum. An
earlier rule placed each anchor just below the costliest occupied bin; it
produced clustered anchors and failed on root 193, which the menu rule
certifies. A certificate at an exponent `L'` shows that every zero configuration in that
leaf's case yields a prime below `q^{L'}`. Every configuration lies in some
leaf, and there are finitely many leaves, so their `q₀` can be taken
uniformly. The global exponent is therefore the maximum over leaves of the
exponent at which each leaf is certified. No monotonicity in `L` is needed.

The full inside and outside covers at 4.20 are recorded separately in
STATE once complete.

*How the adversary responds.* At 4.15 the worst populations of leaf 567 sit
just below each anchor (for example 1.495, 1.795 and 2.2 with anchors 1.5,
1.8 and 2.1). Characters there are covered only by the next lower anchor.
Below 4.20 the cost is mainly the number of anchors.

*Floating LP on captured 4.30 leaves.* The LP inputs were captured from the
verified 4.30 corpus and regenerated at lower `L`. Values below are with
several sieve anchors (bins coarsened to 0.01, so slightly pessimistic):

| Leaf | `L=4.30` old → new | 4.20 | 4.15 | 4.10 |
| --- | --- | ---: | ---: | ---: |
| 567 (rr, `λ₁≈.75`) | .9994 → .773 | .864 | .929 | .999 |
| 1760 (complex, `λ₁≈.73`) | .9994 → .821 | .900 | .966 | 1.037 |
| 2557 (complex, `λ₁≈.78`) | .9991 → .894 | .970 | 1.031 | 1.099 |
| 1294/1 (complex, `λ₁≈.68`) | .9959 → .755 | .859 | .922 | .991 |
| 2602 | .9994 → — | .920 | .979 | 1.047 |

Leaf 2557 is weakest: its worst population puts about six characters at
`λ≈.868`, just above the third-family bound, where anchors `≥1.2` do not
apply. Low anchors just above `s₁` are needed there.

The floating script `augment.py` used the leaf's shift as `s₁`, which for
leaf 567 is `.7599>λ₁^{lo}`, without the correction `c_j`. The effect is small.
The rigorous driver takes `s₁≤λ₁^{lo}`, so `c_j=0` there.

### 6c. Graded-row covers and findings

*Pipeline.* Every LP leaf of the verified 4.30 corpora is regenerated at the
target exponent by the repository builders:

* the inside scenarios (`verify_progress.scenario`, `inside_repair.verify_core`,
  collective scenarios: 2913 leaves);
* the inside hidden-family branch leaves of `inside_repair` identities nodes
  (`separated_blocks.verify_block`: 918 leaves);
* the outside-buffer leaves (`first_verify`: 1685 roots).

Each leaf is certified with graded rows by a staged driver. That driver tries
the family row plus a row at 1.9, then rows at 1.5, 1.9 and 2.3, then greedy
additions. rc leaves are split by `μ₁`, and hard leaves by the second family.
The remaining nodes of the 4.30 trees are location, positivity or
second-family exclusions, which do not depend on `L`. The exterior ranges
`λ₁≤.1` and `λ₁≥1.5` have repository certificates at 3.99
(`computations/frontier/existing_components_verified.json`). Results are in
STATE.

*Measured limits (floating, before case splits).* On a stratified sample of
382 inside leaves at `L=4.00`, with the family row and graded rows at 1.5, 1.9
and 2.3, the median was .917, the 99th percentile .979 and the maximum 1.026.
The worst leaves by kind:

* rc (1083, 1099): the λ₂-bound family at .93. The conjugate pair (§2c)
  brings 1083 from 1.05 to .97.
* complex with a reserved second family (1244, 1219). Second-family splits
  bring 1244 from .998 to .964 at 4.00. It stays above 1 at 3.95, so the middle
  range bottoms out near 3.97–3.98.
* rr with a reserved pair (193, 208, 225). The refined λ₃ gives 193 .927 at
  4.00.

*Failed or superseded experiments* (kept for reuse):

1. Merging several anchors into one row is weaker than separate rows.
2. Menu anchors (plain rows, up to six) saturate near `L≈4.13`. The
   adversary parks crowds just below each anchor.
3. Plain rows with low anchors just above `s₁` do not help the low family. Its
   limit is the Gram (Bessel) barrier `N≳F(−s)²/r²`. What helps is putting the
   first and second families into the row (§2a).
4. The sieve part `H` does not help crowds of fewer than about ten characters.
   The diagonal inflation `κ≥2` dominates.
5. A narrower kernel (`T=.36`) is worse than `T=.416829` on the binding
   leaves.
6. A (4.28)-type refinement of λ₃ is useless for rc leaves whose global λ₂
   bound already exceeds it (1083: λ₂≥.93 against about .90).
7. A graded row anchored at λ₃ instead of `s₁` does not beat the family row
   on the low family (193: 5.82 against 5.49 allowed).
8. Adding only the reserved second family to outside rows barely helps
   (1534: 1.023 → 1.021 at 3.99). Its low family at λ₃ needs the first family
   (§2e) or a second-family split. Each alone brings it to about .95–.97.
9. Certificate engineering:
   * An active-set solver for the small dual LPs, warm-started across boxes, was
     slower than HiGHS on the full LP (20 s against 12 s CPU on an inside
     leaf).
   * Lowering the split heuristic's dual floor from .5 to .05 exhausted 40000
     boxes where .5 needed 6915.
   * Trimming sieve dimensions to the window where their fixed family budget
     is nonnegative removes only 1–6% of the range.
   * HiGHS primal simplex saves 13–30% CPU.
   * Mixed first/second order in the outside and block certificates lowers CPU
     but can use more boxes.

*Two errors found and fixed during this work.*

1. **Uncaptured leaves.** The replay originally intercepted only scenario-type
   leaves. The 918 hidden-family branch leaves go through
   `separated_blocks.verify_block` and were missing. `verify_all.py` now
   intercepts `inside_repair.verify_branch` as well.
2. **Exclusion bug in the certificate checkers.** See §8.

### 6d. The simplified structure: ablations

These measurements led to the simplified proof ([PROOF.md](../PROOF.md)). All
values are floating LP maxima at `L=3.99` unless marked exact.

*Which 4.30 ingredients matter* (fixed rows: family row plus graded rows at
1.5, 1.9 and 2.3):

| Leaf | full | without collective | without old near row | without both |
| --- | ---: | ---: | ---: | ---: |
| 193/0 | .9413 | .9444 | .9419 | .9481 |
| 2557/0 | .9532 | .9532 | .9513 | .9513 |
| 567/0 | .8969 | .8969 | .9021 | .9021 |
| 1760/0 | .9142 | .9142 | .9170 | .9170 |
| 1400/3 | .9528 | .9448 | .9582 | .9550 |
| 1218/0 | .9914 | .9914 | 1.0198 | 1.0198 |
| 1244/0 | 1.0091 | .9997 | 1.0259 | 1.0258 |

The collective envelope never matters by more than about .01. On 1244 it even
lowers the maximum when removed, because the proposer then chooses different
rows. The old near row matters on 1218 and 1244, through its first-family
feature at the shift.

*The shifted row* (§2f) replaces the old row's first-family feature. This is
the simplified model: regular leaf, family, shifted and graded rows.

| Leaf | 4.30-style | simplified |
| --- | ---: | ---: |
| 193/0 | .9413 | .9390 |
| 567/0 | .8969 | .8949 |
| 2557/0 | .9532 | .9436 |
| 1400/3 | .9528 | .9392 |
| 1760/0 | .9142 | .9028 |
| 1218/0 | .9914 | .9992 |
| 1244/0 | 1.0091 | 1.0053 |

The simplified model is the lower of the two on every leaf here except 1218.
The two leaves above or near 1 are the known hard complex cells, which need
second-family splits in either model. The rc leaf 1083 falls from 1.0395 to
.7983 and .9631 on its two height ranges (§2c).

*Identities nodes by the regular model.* The regular model of the node's own
case, with graded rows, gives the following floating maxima:
* roots 212, 214 and 227 (rr): .9548, .9551, .9528;
* roots 2110 and 1973 (complex): .9771, .9736;
* the twelve second-family pieces of root 1840: .9703–.9837.

The hidden-family branches are therefore unnecessary on these nodes.

*Outside roots.* Without the old first-block row, and with graded rows
carrying only the second family, the maxima are .757–.980 on seven sampled
roots (1204, 1417, 1492, 1534, 1558, 1600, 1774). Adding the outside family
row with the global first zero and hidden local zeros (§2e) brings 1492 from
.9713 to about .878.

*End-to-end exact certificates* of the simplified pipeline
(`computations/graded`), each re-verified by `graded_driver.verify_leaf`:

| Leaf | kind | maximum | boxes |
| --- | --- | ---: | ---: |
| 567/0 | inside | .999828 | 1,384 |
| 1492/0 | outside | .998050 | 38 |
| 212 | identities node, regular model | .999866 | 4,205 |

### 6e. Exterior branches below 3.99 (floating)

Both exterior regimes are certified at 3.99 by earlier repository arguments
(4.33 §§6–7).

* **Large first zero, `λ₁≥1.5`.** The certified argument uses one two-test
  row at `s=1.5` and gives `W≤.9947` at 3.99. That argument has no
  distinguished family, so the graded near lemma applies directly: safe anchor
  `1.5`, graded rows at 1.9 and 2.3 with sieve parts, and the same far row and
  objective. Floating maxima (`computations/graded/exterior_probe.py large`):

  | `L` | 3.99 | 3.95 | 3.90 |
  | --- | ---: | ---: | ---: |
  | graded rows | .478 | .518 | .572 |

  The large branch therefore does not limit the exponent near 4.
* **Small exceptional zero, `.1≥λ₁≥u₀`.** The certified argument
  (`small_exception_399.py`) uses:
  * one triangle kernel;
  * repulsion `λ≥1.09log(1/λ₁)` for every other zero;
  * X (5.18) density for the other characters.

  Its relative margin at the binding point `λ₁=.1` is `.0066` at 3.99. A
  floating scan (`exterior_probe.py small`) over the kernel width `K` and the
  density parameters `(c₁,c₂)` finds no positive margin below 3.99: the best
  is `-.049` at 3.97 and `-.108` at 3.95. **This branch is what fixes the
  exterior exponent at 3.99.** Lowering it needs a different argument.

  *A proposal, not yet carried out.* Treat the branch like a leaf.
  * **Cells and constraints.** Split `λ₁=u` into cells. On a cell, every
    other zero has `λ≥m(u_{hi})` by H Lemmas 8.4 and 8.8. Bound the other
    characters with the LP of §7: far row, and graded rows whose safe anchor
    is `s₁≤u_{lo}`. At that anchor the exceptional character's zero, which is
    the only zero of the quotient `χ_jχ̄_k=χ₁`, lies to the left of every Gram
    test point, so no correction arises.
  * **Target.** The LP value must stay below the main-term deficit
    `(H(0)-H(u_{lo}))/H(0)`, less the first character's other zeros.
  * **Why the old bound is loose.** At `u=.1`, (5.18) permits about 1,400
    characters near `λ≈2.5`, which costs about as much as the whole deficit.
    The large-branch probe above suggests the graded rows bound such a
    population far more tightly.
  * **Consequence.** The middle range would then decide the exponent, at
    about 3.97 in floating point (§2g).

### 6f. Certificate cost in the hard region, and fewer rows

The first attempt at the 3.99 cover finished no hard inside root in 30
minutes. Profiling leaf 1230/0 (complex, `λ₁∈[.6625,.665]`, second family as
columns) showed where the time went.

* **LPs are cheap; there are too many.** One HiGHS solve takes about 7 ms
  with 865 columns. With five near rows, each threshold box needed about 20:
  one first-order case, 16 tangent cases on four active dimensions, and a
  centre check.
  * The old builder exhausted its 12,000-box budget after 89,000 LPs (15
    minutes), with a box still at 1.009.
  * The builder was then changed to fail at the first failing case, to check
    the box centre first, and to skip tangent cases that cannot succeed. It
    still exhausted the budget with five rows (780 s).
* **Fewer rows.** The dimension of the threshold box is what matters. On the
  same leaf, the strong floating maxima of several row sets were (F = family
  row, S = shifted row):

  | Rows | floating maximum |
  | --- | ---: |
  | F, S, 1.5, 1.9, 2.3 | .97658 |
  | S, 1.5, 1.9, 2.3 | .97790 |
  | F, S, 1.6, 2.1 | .98231 |
  | F, 1.5, 1.9, 2.3 | .98891 |
  | F, S, 1.5, 2.0 | .99021 |
  | F, S, 1.7, 2.2 | .99096 |
  | F, S, 1.5, 1.9 | .99938 |
  | F, S, 1.7 | 1.0507 |

  The four rows S, 1.5, 1.9, 2.3 certify this leaf exactly: maximum .99980,
  3,864 boxes, 50,626 LPs, 606 s at about 75% of one core. Five rows do not
  certify it within 12,000 boxes.
* **The proposer's search underestimates.** Its coordinate search gave 1.0367
  with three rows and 1.0416 after adding a fourth, although an extra row can
  only lower the true maximum. The driver now uses a stronger search (more
  starts and sweeps) for the multi-row stages.
* **Driver.** `graded_driver.ROW_STAGES` tries F, S, 1.9 first, then the
  four-row sets above, then the five-row set, then greedy additions.
* **Basis reuse.** Each case LP has only about 10 rows, so its optimal basis
  is small. The builder re-solves the previous basis for the new box, a 10×10
  system, and calls HiGHS only when that basis is not dual feasible below the
  target. Rounding and the exact check are unchanged, so this affects speed
  only.
  * On leaf 1230 it saved only 6% of the LPs (47,502 against 50,626), with
    the same 3,864 boxes.
  * Its certified maximum was .999995, against .99980 without reuse. The
    reused duals are feasible but not optimal, and are accepted as soon as
    they fall below the target.
  * The cost of a hard leaf is therefore the number of boxes and cases, not
    the individual LP.
* **Column generation.** Each case LP is solved on a working set of columns;
  all columns are priced, and the full LP is the fallback. On leaf 1230 it
  gave the identical certificate (3,864 boxes, the same maximum) in 265
  CPU-seconds with about 115 columns per solve. The full LP (865 columns)
  took 535 CPU-seconds: a factor of two.
* **Exact check.** With column generation, the exact column check
  (`check_case`) became about 57% of the build time: roughly 7 ms per case,
  with one Python generator per column. It was rewritten to accumulate each
  row's contribution over all columns in exact Python integers, with the same
  arithmetic and the same assertions.
  * Stored certificates re-verify with identical maxima and box counts.
  * The code review's corruption, exclusion and second-column tests still
    reject every forged record.
* **First root of the full cover.** Root 1223 failed the staged driver in the
  earlier full method. It is now certified at 3.99 by S, 1.5, 1.9 and 2.3:
  * floating maximum .977, certified .99989;
  * 3,604 boxes and 30,585 cases, about 19 minutes at 44% of one core.

  Its tree splits all four dimensions about equally, to depth 15–21. Most
  leaf boxes use tangent cases in three or four dimensions.

### 6g. Unreserved leaves and the reservation split

The first failures of the 3.99 cover were roots 1218, 1219 and 1378. All three
are **unreserved** specifications: no local second family is reserved, and
the count row allows at most two ordinary characters below `λ₃`. Take root
1378: complex, `λ₁∈[.70,.7025]`, shift .7394, `λ₃≥.8866`.
* Every row set stays above 1 in floating point; the best is 1.0025, with
  five rows.
* Second-family columns and splits do not apply.

The **reservation split** at `h=λ₃` (PROOF.md §8) gives these floating
maxima:

| Child of 1378 | floating maximum |
| --- | ---: |
| one real character reserved in `[.7394,.8866)` | .95898 |
| nonreal pair reserved in `[.7394,.8866)` | .99822 |
| no non-first family below .8866 | .96746 |

The pair child is tight. Its own second-family splits lower it further.

### 6h. The unreserved tail of the 3.99 cover: the old near row is still needed

The 3.99 cover queued the 674 unreserved roots last. By 13:30 UTC on
2026-09-28, 2,316 roots had certified, and 24 failed with "repairs exhausted".

**Roots 10–35 (22 failures).** These are `rr` cells with `λ₁∈[.20,.43]`.
Their ordinary families start at the source `λ₂` bound, 1.77 for
`λ₁≤.25` and 1.18 at `λ₁≈.42`, so there is nothing below `λ₃` to reserve.
* The graded rows alone stay above 1. For example, the best stages were:
  * root 10: 1.0023;
  * root 11: .9854 (just above the stage margin);
  * root 33: 1.0579.
* The earlier full method had certified all three at 3.99 with only two
  graded rows (.9994, .9902, .99993). The difference is not the collective
  envelope, since none of these leaves carried one. It is the regular model's
  own **two-test near row** (`d`, `D`, `Df`, `v_first` and the bin features
  `rows[i][4]` of the `make_endgame` input). The earlier certifier imposed that
  row; the simplified certifier dropped it (PROOF.md §12).
* Floating maxima with the old row added:

  | Root | family + 1.9 | old + family + 1.9 | old + S, 1.5, 1.9, 2.3 |
  | --- | ---: | ---: | ---: |
  | 10 | 1.01683 | .95339 | .89568 |
  | 11 | .99985 | .93815 | .88171 |
  | 33 | 1.35922 | .92303 | .84502 |

* With the old row as a fallback stage, both roots certify exactly and
  re-verify:
  * root 10: .9998091, 257 boxes, 19 s;
  * root 33: .9999320, 274 boxes, 27 s.

The claim of §6d and PROOF.md §12 that the family and shifted rows replace the
two-test row is therefore **false for these `rr` cells at 3.99**.

**Roots 1218 and 1219.** These are complex cells with `λ₁∈[.64,.66]`, source
`λ₂=.79`, `λ′≥1.08` and no gap bound.
* The reservation split at `h=λ₃^{lo}` (.8959 and .8934) works for the real
  child. The nonreal-pair child fails.
  * Its best four-row set is .98845 on the lowest ninth of `[.79,h)`.
  * A 30-start search gives .98894. With five rows the search gives .9887,
    so the true maximum is about .989.
  * The exact build stopped at 20,000 boxes with open boxes at 1.04–1.05.
* Anatomy of the worst point (rows S, 1.5, 1.9, 2.3):

  | Contribution | Cost |
  | --- | ---: |
  | first family | .226 |
  | reserved pair at .79 | .228 |
  | 2.2 characters at `λ≈.995` | .116 |
  | 80 characters at `λ≈1.735` | .288 |
  | tail | .130 |

  The shifted row at .79 carries the largest dual (1.28).
* Remedies measured in floating point on that piece:
  * a finer bin grid: .98878 at `lambda_den=200`, .98468 at 400, .98272 at
    800;
  * the best of 455 four-row sets: S, 1.5, 1.7, 2.3 at .98589;
  * the old near row added to S, 1.5, 1.9, 2.3: **.96891**.

**Repair.** `graded_driver` now tries `OLD_STAGES` when the graded stages fail
on an inside leaf. These stages are the graded stages with the old row
appended last, so height and second-zero splits keep the family row first.
* The row is `graded_leaves.old_row`: the repository constraint divided by
  `D`, with the first family as a fixed term with diagonal `Df`.
* A reserved second family keeps its fixed term at `v2`, which bounds the
  feature over the whole reserved range, also when it is charged by columns.
* Negative features are set to 0. This is exact, because features enter only
  through `(v-τ)_+` with `τ≥0`.
* Certificates found without the old row are unchanged.

The cover was restarted with this driver at 13:43 UTC.
* All 22 `rr` roots re-certified within four minutes: maxima .9924–.99997,
  72–306 boxes, under 30 s each.
* By 14:15, 35 roots in all had used the fallback, all of them unreserved:
  * `rr`, `λ₁∈[.20,.46]`: roots 10, 11, 15–18 and 20–36;
  * complex, `λ₁∈[.44,.48]` with source `λ₂` 1.04: roots 1198–1201;
  * complex, `λ₁∈[.58,.62]` with source `λ₂` .85: roots 1212–1215;
  * complex, `λ₁∈[.80,.82]` with a finite gap: roots 2603, 2608, 2613 and
    2633.

  The earlier run had not finished the last thirteen. The fallback is tried
  only after the graded stages fail, so without it they would have failed
  too.
* **Root 1218** certifies with the fallback: .9999979, 62,688 boxes,
  72 minutes under load, re-verified by `verify_leaf` in 117 s. Its record is
  a reservation split at .8959:
  * the real child certifies with graded rows;
  * the pair child fails as a whole, and its 3- and 5-way second-family
    splits fail at their lowest piece;
  * the 9-way split certifies, with the lowest piece `[.79,.8018)` on the
    fallback stages;
  * the child with no family below .8959 certifies.
* **Identities node 1501/1: a driver bug.** It is a complex cell with
  `λ₁∈[.72375,.725]`, source `λ₂=.7225` and `λ′≥1.03`.
  * The repository shift is `min(1.9,λ′,source λ₂)=.7225`. That is above
    the safe anchor .72 but below `λ₁^{lo}`, so the shifted row (PROOF.md
    §6.5, `a≤s`) does not apply.
  * The driver tested only `s>s₁`, and the row builder's assertion stopped
    the node.
  * `graded_driver.has_shifted` now also requires `s≥λ₁^{lo}`.
  * Without the shifted row, the node's best stage is .98857 (family, 1.5,
    1.9, 2.3). The old row does not help it (1.005–1.008).
  * No inside root had such a cell, since all certified.
  * Recomputed with the fix, root 1501 certifies. Both of its nodes go
    through the reservation split, with a 3-way second-family split of the
    pair child:
    * node 0: .9999891, 10,747 boxes;
    * node 1: .9999969, 4,301 boxes;
    * 42 minutes in all.

## 7. Remaining obligations

1. The source-interface list must record these uses:
   * the representative choice of §2: the strip height `T*`, the localized
     use of X Lemma 3.10, and height-one representatives for the reserved
     second family (§2b);
   * the pointwise use of X (4.31) on X's verified box (§2d).
2. The new inequalities are analytic premises. §§1–3 and §§2a–2d each have
   one independent adversarial review (§8). They have not been formalized.
3. The complete covers at a given `L` must be replayed against the
   repository's own 4.30 source trees.
   * For the simplified proof the replay is
     `computations/graded/graded_verify.py`. It covers inside scenario leaves,
     identities nodes (as regular models) and outside leaves.
   * The earlier full-method replay (`computations/sieve_near/verify_all.py`)
     also covers hidden-family branch leaves.
4. The steps of §§2e–2g and the replacement of identities nodes by the
   regular model have had one review each (review 5, §8).
5. The two-test row is used as a fallback (§6h, PROOF.md §6.6). Its
   embedding as a threshold row (`graded_leaves.old_row`) has had one review
   (review 9, §8), which found it valid.

## 8. Review record

**Review 11** (2026-09-29, independent referee, "R2") re-checked the ten
auxiliary steps of the simplified proof, both the mathematics and the code:
1. the shifted row;
2. `sec_anchor='l2'`;
3. second-family columns;
4. the reservation split;
5. the first family's second zero;
6. identities nodes as regular models;
7. the outside model;
8. the refined `rr` `λ₃` and the rc pair;
9. the fallback two-test row;
10. split structures and forced repairs.

All ten are valid. It found no problem that could affect a certificate. Its
scripts were kept in the session scratchpad (`review_R2/`) and were not preserved. The
fallback-row comparison below was redone on 2026-10-01 by the committed
`computations/graded/two_test_compare.py`. It covers every certificate interval of the 37 roots
([rebuilt checks](../notes/rebuilt-checks-2026-10-01.md)).
* **Independent checks.**
  * A census of the three corpora.
  * Partial replays of inside roots 10, 212, 1197, 1285, 1501, 2461, 2486 and
    2603, and outside roots 1083 and 1492.
  * The replay hooks intercept every LP-leaf verifier, so no 4.30
    certificate can survive silently.
  * The fallback row matches `build_progress.near` in exact rationals on 300
    random boxes (roots 10, 2603 and 1218's lowest piece), in every case
    type.
  * Dense mpmath checks of the dz enclosures (1285/0) and of `C_Z` (rc roots
    1083 and 1084).
  * For 15 nodes, `make_endgame(spec_of(captured base))` is byte-identical to
    the node's own `make_endgame`.
* **Text repairs, now made.**
  * §2f: `s≥λ₁^{lo}` is a condition of use, not a fact (node 1501/1).
  * PROOF.md §3: second-family columns relax the `1/400` split. They are not
    "equivalent to splitting arbitrarily finely".
  * PROOF.md §8: the reservation split needs only minimality. The claim
    "necessarily the global second family" is not checked by the verifier
    and not used. Its usage is four inside roots and five node roots.
  * PROOF.md §6.5: pieces `y≤2` of the dz split are excluded outright, the
    only exclusion of this kind.
  * PROOF.md §7: the weak-duality formula now shows the scaling by `S`.
* **Shared premise.** Steps 1, 2, 6 and 9 inherit the 4.30 premise that
  `source_l2` bounds the global `λ₂`.

**Review 10** (2026-09-29, independent referee, "R1") re-derived the whole
graded near lemma (PROOF.md §6) from H (Lemmas 2.1, 2.5, 5.2, 5.3, (11.13),
§12) and X (Lemmas 3.1–3.4, 5.1–5.2). It found no error that invalidates the
lemma or changes a certificate. Its scripts (`chk_F.py`, `chk_sieve.py`,
`chk_T.py`, `chk_dz.py`) are in the session scratchpad (`review_R1/`).
* **Valid as written.**
  * The Gram/positivity argument and its signs. `ω≥0`, so the second factor
    may be summed over all `n`.
  * The response lemma for every entry kind, including the shifted row's
    `F(λ₁-s)≥F(b-s)` and `-C_Z`.
  * Where each entry kind is placed, with the code's asserts.
  * The threshold form (T). A separation argument gives the equivalence, and
    300 randomized cases matched.
  * Uniformity in characters, heights and the number of entries.
* **Code fidelity.**
  * `sieve_inputs.py`, `diag_up`, the normalization, `RigorousTest.F`
    (30-digit agreement with quadrature), the `C_Z`, `pair_bounds` and
    `second_zero_bounds` slacks, and `graded_row`'s anchors all implement the
    lemma, rounded outward.
  * Quadrature on five cached parameter sets gives `I_up≥I_B`, `D_up≥D(0)`,
    and `diag_up` bounds `D(δ)`.
* **Text repairs, now made in PROOF.md.**
  * §6.3 needs Abel summation with the pointwise Burgess bound. The crude
    `sup|S|·Var` form loses `q^{2(t_{k+1}-t_k)/3}`, which is fatal for cells
    wider than about `ε′` (the code's cells are about `8·10⁻⁴`, and
    `ε′=5·10⁻⁴`).
  * The inner sums start at `m≥M₀≥q^{1/3+2ε′}`; it is not the interval
    length that is at least that.
  * Heights up to `l` cost a factor `(1+|τ|)≤ℓ`.
  * §10: `η′` is fixed with the certificates, and `K₀` counts zeros to height
    2.
  * §3: the disc radius must be `<1/2`. It is `≤1/6` in H's proof of Lemma
    3.1 (checked, H p. 14), and H p. 24 allows `δ=1/log 𝓛`.
* **Documentation.**
  * Review 8's reason for the infeasible pieces `y≤3` (`∑v²/D′≈1.87>1`) holds
    only at `τ=0`. On a 1285-like cell the four family terms alone are
    feasible for `y∈[2,3]` at `τ≈.156`. Exclusions there come from the whole
    LP, through the exact `excludable` rule. No certificate relied on the
    wording.
  * PROOF.md §6.4 subtracts `η′` twice, a harmless extra margin.

**Review 9** (2026-09-28, independent reviewer) found the fallback two-test
row (§6h; PROOF.md §6.6) valid on all five points. No certificate is
affected, and only text repairs were required. The reviewer's scripts are in
the session scratchpad (`review9/`), which was not preserved. Its exact-equivalence check is
redone by `computations/graded/two_test_compare.py` (2026-10-01).
* **Exact equivalence.**
  * `old_row` with `graded_cert._row_case` imposes exactly the repository
    constraint divided by `D`, in the first-order and both tangent cases. The
    same formula appears in `verify_progress.scenario`, `verify_v4`,
    `build_progress`, `certificate.py` and `certificate3`.
  * On 10 input variants × 65 boxes × 3 cases, integer costs never exceeded
    the exact value (gap under 2.1·10⁻¹⁶), and budgets never fell below it
    (under 2.7·10⁻¹⁶).
  * 4,881 tight random configurations all satisfied the integer rows.
  * Dropping the old certifier's budget window only enlarges the threshold
    box.
* **Clamping.** It is exact in all three cases, and identical on 1,209
  synthetic negative-feature box cases. In practice only the tail feature is
  negative.
* **Columns.**
  * `v₂` is enclosed at `hi₂`, and the feature decreases in `λ`.
  * The columns carry zero cost in this row, so the row is literally the
    repository inequality.
* **Validity in the simplified model.** The row's premises are:
  * the shift;
  * the first-family corrections;
  * upper-end features;
  * (7) for the paired variant.

  None depends on the collective envelope, the identities branches, the old
  window, `replace_far`, `refine_third`, or the reservation and second-family
  splits.
  * *Repair applied:* PROOF.md §6.6 now states why `T*` representatives are
    covered.
  * *Repair applied:* the mixture and paired variants' premises are now
    cited: near refinements §3, and §4 (5)–(8).
  * The fallback uses all three variants: single test (roots 10–36,
    1198–1215), mixture (1218–1219) and paired (2603–2633).
* **Driver and verifier.**
  * The row is rebuilt from the regenerated input. Corrupting the captured
    `v_first`, `d`, `D` and features leaves the verified maximum unchanged.
  * Twelve forged records are rejected at the intended checks. These are
    rows with parameters, height or second-zero ranges, placed first in a
    split part, used outside, dropped, or with an altered maximum.
  * Genuine records re-verify, including 1218 (.9999978664, 62,688 boxes).
* **Text repairs applied:**
  * PROOF.md §§6.6, 11 and 12;
  * the docstrings of `graded_leaves.py` and `graded_cert.py`.

**Review 8** (2026-09-28, independent reviewer) found the first family's
second-zero entries (§2h, PROOF.md §6.5) valid.
* **The zero exists.**
  * By X §3.1.2 (printed pp. 21–22), `ρ′` is a zero of `L(s,χ₁)`, and `\barρ′`
    is a zero of `\barχ₁` with the same `λ′` and `|y|`.
  * A finite gap branch has an actual witness (source-semantics note).
* **Entries.**
  * The four entries use the nonprincipal quotient `χ₁²` across characters.
  * Each character appears as exactly one controlled pair.
  * `y=0` gives the exact double-zero bound.
* **Responses.** X Lemma 3.4 permits keeping both zeros for any test point in
  `R(9l)`. The `γ′` test point lies there because `|γ′|≤l`.
* **Enclosures.**
  * The curvature (no factor 4 in `y`), the Lipschitz slack and the units
    match `pair_term`.
  * The closed-form `G₁` tail holds for any `u`, so also for `u=10`. Direct
    evaluation for `y∈[10,5000]` never exceeded .018 of it.
  * On a leaf-1285-like cell, every piece's bounds lie outside dense
    numerical maxima and minima.
* **Verifier.** It accepts exactly the six canonical pieces, and only on
  inside complex finite-gap leaves. `dz_range` must sit on the family row of a
  part, and nesting with height splits or columns is excluded.
* **Infeasible pieces.** The pieces `y≤3` were reported infeasible because
  four entries give `∑v²/D′≈1.87>1`. That holds only at `τ=0`; see review 10.
  The exact checker excludes a piece only through the whole LP.
* **Fixes applied.**
  * PROOF.md now writes the conjugate entries at `-γ₁,-γ′`.
  * It names `ρ′` among the high entries.
  * It states the pair range for `|(γ_j-γ_k)ℓ|`.
  * `graded_pack` strips logs inside `dz_split` parts.

**Review 7** (2026-09-28, independent reviewer) found the reservation split
(§6g, PROOF.md §8) valid.
* **Why the children exhaust the parent.**
  * Conjugate characters share their representative parameter, since every
    region used is symmetric in the height.
  * Ties are harmless.
  * `ν=h` falls in the unreserved child.
* **The rules in each child.**
  * The third rule holds because the reserved family is a minimizer. With
    `h≤λ₃^{lo}` it is the global second family.
  * The capped `λ₃` bounds (X (4.28), and (4.31) via `refine_third`) are
    valid because `λ₂≤ν<h`.
  * The location reductions of `reduced_spec` hold in every child.
* **Code.** The reviewer ran 18 honest and forged records against the real
  verifier. Every forgery was rejected, including:
  * a non-normalized `h`;
  * missing, reordered or mismatched children;
  * `h≤r` or `h>2`;
  * a split of a reserved parent;
  * nested splits in the wrong child;
  * a false exclusion;
  * an understated maximum.
* **Fixes applied.**
  * `apply_path` now asserts the child index.
  * PROOF.md now states the threshold `min(λ₃^{lo},2)` and the minimality
    that the third rule uses.
* **Measured (floating) on cell `[.70,.7025]`.** The capped `λ₃` bound is
  .8867 with cap .8866, and 1.0562 with cap .74. So a reserved child gains
  most from its own second-family splits near `r`.

**Review 6** (2026-09-28, independent code audit) examined the graded-near
checker (`computations/graded/graded_cert.py`, `graded_driver.py`,
`graded_verify.py`), including the second-family columns and memoization.
* **Sound:** the exact checker (`verify_tree`, `check_box`, `check_case`,
  `excludable`, `row_case`). Its adversarial tests covered:
  * rounding against exact rationals, over 2,520 box/case combinations;
  * the tangent-case implication, 31,206 exact boundary checks;
  * 25 corrupted trees and duals;
  * a feasible negative-cost case that the old exclusion rule would have
    accepted;
  * exact-LP probes;
  * the far add-back for both far weights.
* **Hole, fixed.** `verify_record` validated a row's `mu_range` (the rc
  pair's height range) only on the first row of a height split. A forged
  plain record limited to `μ₁≥1` was accepted as covering every height. The
  verifier now requires:
  * every row of a plain record to have no range;
  * each height-split part to carry exactly its own range, and only in its
    family row;
  * height splits to occur only on inside rc leaves.

  Honest certificates were unaffected, because the builder never wrote such
  records.
* **Hardening, applied.**
  * The replay makes any escaping identities branch fail loudly.
  * It checks that the outside records are complete and in order.
  * It asserts that there are 2768 specifications.
  * Leaf data must be Python integers, with positive diagonals.
  * The second-column grid is pinned to `1/400`.

**Review 5** (2026-09-28, independent reviewer) covered the steps added for the
simplified proof. It found all five valid:
* the shifted row (§2f);
* the second-family anchor at the global `λ₂` bound (§2f);
* outside hidden columns in the family row (§2e);
* identities nodes replaced by the regular model;
* second-family LP columns (§2g).

The reviewer's checks and findings:
* **Checks.**
  * `λ′` is defined over all of `R(l)`, so it bounds every other occurrence of
    `χ₁` and `\barχ₁`.
  * `source_l2` is raised only by global `λ₂>h` rows in the retained nodes.
  * `C_upper` was compared against a brute-force supremum of `-Re F` on
    `Re z=-d` for several `γ` and `d`.
  * The 4.30 tree has 233 identities nodes and 1517 collective terminals.
  * The column far add-back and the removal of `J₂` are exact for both far
    weights.
* **Text repairs to PROOF.md, now applied.**
  * `R(l)` uses physical heights `|t|≤l`, not `l/ℓ`.
  * `K₀` is scoped to entries of height at most 1.
  * Conjugate pairs need `δ=0`.
  * The stale `height_one` subcase was removed.
  * The shifted row may carry `H≥0`.
* **Replay fragility, now fixed.** `collective_cover` imports `verify_leaf` by
  name, so the replay patches that binding too. A full replay also asserts
  that exactly 233 identities nodes are intercepted.

An independent adversarial review (2026-09-27) checked:

* the pointwise majorization, the diagonal via Graham, and the partition into
  cells;
* the split-anchor Cauchy–Schwarz;
* the response hypothesis and the omission of characters;
* dependence on the number of characters.

It also reproduced the crowd bounds. It found two gaps, both repaired above:

1. `λ_j≥s` alone does not give the local-disc hypothesis once
   `s>λ₂^{global}`. Repaired by the strip choice `T*`.
2. The Mellin decay argument was insufficient and did not cover step weights.
   Replaced by partial summation against Burgess partial sums.

It also asked that `D₂` be stated as the finite-partition value and that the
gain from decoupling be credited separately. Both are done above.

A fourth review (same reviewer) found the hidden-column features valid in
`distinct` branches. It corrected their description: they are local centers,
not global zeros. It agreed with excluding `same_reserved`, found the
certificate changes sound, and found the optional dimension-0 tangent cases
(`SIEVE_DIM0_TANGENT`, unused) sound.

A third review (2026-09-27, same reviewer) found §2e valid. The count row in
the outside and hidden-family models holds because λ₃ is defined by families
(HB §6). In the distinct and same_reserved branches the hidden family is the
global second family by construction, and omitting hidden columns from the
count is a relaxation. It also found valid the families in branch rows for all
three identities, the refined third bound on unhidden branches, and outside
rows carrying only the second family. It re-verified new outside and block
records exactly. No exclusion rested on a tangent case-1 dimension, and the
count dual was used in 2,115 cases of one record.

A second independent adversarial review (2026-09-27) covered §§2a–2d and the
code implementing them (`graded_row`, `pair_bounds`, `third_refine`,
`family_row`, and the budget and cost rounding in `certificate.py` and
`certificate3.py`).

* **§§2a–2d: sound.** Its findings on each section:
  * First-family inclusion at `s≤λ₁^{lo}` (X Lemma 3.3/3.4; no correction
    terms).
  * Graded Cauchy–Schwarz and diagonals. The off-diagonal bound holds for
    `σ_{jk}<0` by X Lemma 3.2.
  * The rc pair entry via X Lemma 3.1, uniform in `μ₁`. The reviewer
    re-derived the grid, derivative and tail bounds numerically.
  * The refined rr bound. (4.31) holds pointwise on X's verified box, and the
    `h` cap and third rule are legitimate. The reviewer re-derived the 9/8
    constant, and a floating check gives `sup(4.34)≈.0026<5f(0)/48`.
* **Repaired.** The reserved second family in graded rows needed anchor
  `≤λ₁^{lo}`, because its interval is defined through height-one
  representatives. `K₀` must count zeros to height `1+δ`. The citations
  (Lemma 3.1 versus 3.2) were corrected, and the stale Table 10 figures were
  fixed.
* **Soundness bug in the certificate checkers (fixed).** `check_box` accepted
  `'excluded'` for any negative case budget. In tangent case 1 the costs
  `((v−m)_+−h)²−h²` can be negative, so a negative budget proves nothing. The
  reviewer gave an explicit feasible counterexample. The family terms made this
  frequent. Exclusion is now allowed only for a constraint whose costs are all
  nonnegative (`excludable`). `check_case` accepts negative budgets, since weak
  duality needs only nonnegative multipliers. The builders obtain certificates
  for infeasible cases from a bounded dual LP. The reviewer re-solved affected
  cases in floating point and found maxima .70–.91, so the previously reported
  maxima probably stand. The earlier trees, including those behind §6b and the
  4.20/4.17 runs, are nevertheless not proofs. Every certificate used for a
  claim is regenerated with the fixed code.
