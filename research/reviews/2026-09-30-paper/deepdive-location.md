# Far density and zero location (PROOF.md §§4–5): statements, proofs, verification

Deep-dive component of the paper on $L\le 3.99$. Scope: PROOF.md §4 (far density,
far budget, tail column, strip representatives $T^*$, $K_0$) and §5 (zero location:
types, source cover, table inputs, $\lambda_2$/$\lambda'$ rows, $\lambda_3$ rules,
count rule, exclusions, inside/outside split).

**Sources and pagination.**
* **X** = T. Xylouris, dissertation (Bonn 2011 = Bonner Math. Schriften 404). Printed
  page numbers coincide with PDF page numbers.
* **H** = D. R. Heath-Brown, Proc. London Math. Soc. (3) 64 (1992) 265–338. Page numbers
  below are those of the **retained author copy** (99 pp.), not the journal pages. The
  repository notes identify copy p. 5 with journal p. 269. Treat any journal-page
  conversion as unverified.
* **XA** = Xylouris, Acta Arith. 150 (2011) 65–91. It is used only for cross-checks.

**What was verified in this deep dive.** Checks were run in the scratchpad; no repository
file was modified.
* Every printed number used by the code was compared with the extracted page text.
* $V$ was recomputed for both far profiles by independent quadrature (mpmath).
* All 24 roots of H Table 4 were recomputed from H Lemma 8.3, and 5 rows of H Table 7 from
  H Lemma 8.7.
* Four of the 22 degree-5 real rows, the degree-5 polynomial positivity, two complex
  $\lambda_2$ rows and two complex $\lambda'$ rows were recomputed by independent
  quadrature. The alias suprema were sampled.
* X (4.34) was sampled.
* The per-cell $\lambda_3$ refinement was recomputed.
* The source cover was re-validated (340/478/684/2768), and every node type in the 4.30
  inside and outside trees was counted.

Details are in the relevant sections and in Part D.

Notation. $\ell=\log q$. A zero is written $\rho=1-\lambda/\ell+i\mu/\ell=\beta+i\gamma$.
Zeros are counted with multiplicity (X p. 7). $\eta=10^{-6}$. $L=3.99$, $T=.416829$ and
$A=L-2T=3.156342$.

---

## Part A. Far density (PROOF.md §4)

### A.1 The printed lemma

**X §3.2.2 (pp. 25–26), definitions.** Let $0<\lambda\le\lambda_0:=\tfrac13\log\log\ell$
(X writes $L$ for $\ell=\log q$). Put
$$N(\lambda)=\#\{\chi \bmod q:\ L(s,\chi)\text{ has a zero in }\sigma\ge 1-\ell^{-1}\lambda,\ |t|\le 1\}.$$
The corresponding characters are $\chi^{(1)},\dots,\chi^{(N(\lambda))}$. "To each of these
characters $\chi$ (evidently $\chi\ne\chi_0$ for $q$ large enough) we choose a corresponding
zero $\rho(\chi)=\rho^{(k)}$ and set $\rho^{(k)}=\beta^{(k)}+i\gamma^{(k)}$,
$\beta^{(k)}=1-\ell^{-1}\lambda^{(k)}$" (translated). Exactly one zero is chosen per
character. Multiplicity does not create extra summands.

**X Lemma 5.1, (5.19), p. 66 (translated verbatim).**
> Let $\varepsilon,c_1,c_2>0$, $\lambda_0=\frac13\log\log\ell$, $M\in\mathbb N$ and
> $\alpha_i\ge0$ ($i\in\{1,\dots,M\}$) with $\sum_{i\le M}\alpha_i=1$. Put
> $x=\frac23+3c_1+c_2$ and $u_i=\frac13+2c_1+\frac{i c_2}{M}$ ($i\in\{0,\dots,M\}$).
> Let furthermore $w_0:[u_0,x]\to\mathbb R$ be a continuous function which, except at
> finitely many points of $[u_0,x]$, is continuously differentiable. Moreover let
> $1\ll w_0(t)\ll 1$ and $w_0'(t)\ll1$ with certain absolute implied constants. Then there
> is a $q_0$, depending on all chosen parameters, such that for $q\ge q_0$
> $$\sum_{1\le k\le N(\lambda_0)}\Bigl(\int_{u_0}^{x}w_0(t)^2e^{2\lambda^{(k)}t}\,dt\Bigr)^{-1}
> \le\frac{M^2+\varepsilon}{c_1c_2^2}\sum_{i=1}^{M}\alpha_i^2\int_{u_{i-1}}^{x}w_0(t)^{-2}
> \min\{t-u_{i-1},\,u_i-u_{i-1}\}\,dt. \tag{5.19}$$

$M=1$ and $w_0\equiv1$ recover H Lemma 11.1 (X p. 66). The proof is sketched on X
pp. 67–72 via (5.21)–(5.24). It is "practically identical" to H §11 with
$w_\chi=\bigl(w^{-1}\int_{u_0}^x w_0^2e^{2\lambda(\chi)t}\bigr)^{-1}$ (5.21), and it
treats arbitrary chosen zeros with a common threshold.

### A.2 Statement used in the paper

**Theorem A (far density).** Fix $c_1,c_2>0$, $M=10$, rationals $\alpha_1,\dots,\alpha_{10}\ge0$
with $\sum\alpha_i=1$, $\theta>0$ and $\varepsilon_0=10^{-7}$. Put $u=\frac13+2c_1$,
$v=u+c_2$ and $x=\frac23+3c_1+c_2$. Define
$$r(t)=e^{-\theta t}\sqrt{\min(t-u+\varepsilon_0,\;c_2+\varepsilon_0)},\qquad w_0=\sqrt r
\quad\text{(X (6.20), p. 80)},$$
$$w(\lambda)^{-1}=\int_u^x r(t)\,e^{2\lambda t}\,dt,\qquad
V=\frac{100}{c_1c_2^2}\sum_{i=1}^{10}\alpha_i^2\int_{u_{i-1}}^{x}\frac{\min(t-u_{i-1},c_2/10)}{r(t)}\,dt,$$
where $u_i=u+ic_2/10$. Then there is $q_0$ with the following property. Let $q\ge q_0$ and
let $\mathcal S$ be any set of nonprincipal characters mod $q$. Choose for each
$\chi\in\mathcal S$ one zero $\rho_\chi$ with $|\operatorname{Im}\rho_\chi|\le1$ and
$\lambda_\chi\le\lambda_0(q)=\frac13\log\log\ell$. Then
$$\sum_{\chi\in\mathcal S}w(\lambda_\chi)\le(1+\eta)V .$$

*Proof.*
1. **Hypotheses of (5.19).** $w_0$ is continuous on $[u,x]$ and $C^1$ except at $t=v$.
   It satisfies $\varepsilon_0^{1/4}e^{-\theta x/2}\le w_0\le (c_2+\varepsilon_0)^{1/4}$.
   Also $|w_0'|\le \tfrac14\varepsilon_0^{-3/4}+\tfrac\theta2(c_2+\varepsilon_0)^{1/4}$
   off $t=v$, since $w_0'=e^{-\theta t/2}\bigl(\tfrac14m^{-3/4}-\tfrac\theta2m^{1/4}\bigr)$
   with $m=\min(t-u+\varepsilon_0,c_2+\varepsilon_0)$ on $t<v$.
   These constants are fixed. X's own application (6.20)–(6.21), p. 80, uses this same
   family with the same $\varepsilon_0=10^{-7}$. So "absolute implied constants" is met in
   the sense X himself uses. The Lean predicate `ProfileCondition` proves these conditions
   (`FarProfile.profileCondition`).
2. **Sets and zeros.** Each $\rho_\chi$ is an admissible choice in the sense of §3.2.2,
   since $\lambda_\chi\le\lambda_0$ and $|\operatorname{Im}\rho_\chi|\le1$. Extend the
   choice arbitrarily to the other characters counted by $N(\lambda_0)$. All summands of
   (5.19) are positive, so the sum over $\mathcal S$ is at most the full left side. The
   principal character contributes nothing: $L(s,\chi_0)$ has no zero in the region for
   large $q$, by the classical zero-free region of $\zeta$; see X p. 21, fn. 4.
3. **Identification.** $\int_{u_0}^x w_0^2e^{2\lambda t}=w(\lambda)^{-1}$. Also
   $w_0^{-2}=1/r$ and $u_i-u_{i-1}=c_2/10$.
4. **Constant.** Take $\varepsilon=100\eta=10^{-4}$. Then
   $(M^2+\varepsilon)/(c_1c_2^2)=(1+\eta)\cdot100/(c_1c_2^2)$.
5. **Choice of zeros.** $q_0$ depends only on the fixed parameters. The chosen zeros vary
   with $q$. The printed text fixes "a" choice. The proof (X pp. 67–72, and H §11) works
   for arbitrary eligible choices with one threshold, so $q_0$ is uniform in the choice.
   See D.5 for a reading that needs no uniformity. ∎

**Closed forms used by the code** (`base_enclosures.RigorousWeights.winv`, `J_i`).
Substitute $\rho=\sqrt{t-u+\varepsilon_0}$ on $[u,v]$. Then
$$w(\lambda)^{-1}=2e^{a(u-\varepsilon_0)}\int_{\sqrt{\varepsilon_0}}^{\sqrt{c_2+\varepsilon_0}}\rho^2e^{a\rho^2}d\rho+\sqrt{c_2+\varepsilon_0}\int_v^x e^{at}dt,\qquad a=2\lambda-\theta .$$
With $h=c_2/10$, $\rho_a=\sqrt{ih+\varepsilon_0}$, $\rho_b=\sqrt{(i+1)h+\varepsilon_0}$ and
$\rho_v=\sqrt{c_2+\varepsilon_0}$, the $i$-th integral of $V$ (index $i=0,\dots,9$) is
$$J_i=2e^{\theta(u-\varepsilon_0)}\Bigl[\int_{\rho_a}^{\rho_b}(\rho^2-ih-\varepsilon_0)e^{\theta\rho^2}d\rho+h\int_{\rho_b}^{\rho_v}e^{\theta\rho^2}d\rho\Bigr]+\frac{h}{\rho_v}\int_v^xe^{\theta t}dt .$$
Both formulas were checked by hand against the definitions. The Taylor-series enclosures
use explicit remainders and `mpmath.iv` intervals.

### A.3 The two profiles (exact data from the code)

| | inherited (`config_v4.py`: `C1,C2,THETA,EPS0,ALPHA`) | retuned (`far_enclosures.CANDIDATE`) |
|---|---|---|
| $c_1$ | $.09035$ | $.0821922$ |
| $c_2$ | $.235968$ | $.2170903$ |
| $\theta$ | $1.28683$ | $1.4964274$ |
| $\varepsilon_0$ | $10^{-7}$ | $10^{-7}$ |
| $\alpha_1..\alpha_{10}$ | .0788827218, .0849386148, .0895629779, .0938231516, .0979710491, .1021284916, .1063732939, .1107651869, .1153565492, $1-\sum_{i\le9}=75123727/625000000$ | .0806195583, .0862705300, .0905489307, .0944644867, .0982543287, .1020315591, .1058668825, .1098131140, .1139152197, .1182153903 (sum exactly 1) |
| $u$, $x$ | .5140333…, 1.1736847… | .4977177…, 1.1303336… |
| $2x$ | 2.3473693… | 2.2606671… |
| $V$ | **175.26640331471829395883…** | **243.32098105220588442977…** |
| $w(0)^{-1}$ | .0934101462602… | .0759127165228… |
| $V/w(0)$ | 16.37166 | 18.47116 |
| $w(.44),w(.7),w(1),w(1.5),w(2),w(3)$ | 5.0535, 3.2071, 1.8786, .75234, .29297, .041239 | 6.4206, 4.1561, 2.4925, 1.03979, .42245, .064937 |

The $V$ values agree to at least 20 digits between the code's interval enclosure and an
independent mpmath quadrature (`scratchpad/deep/far_check.py`).
* The 4.30 inside and outside trees use only these two parameter sets. A scan of every
  `far_parameters` field found only CANDIDATE: 2,027 occurrences in the inside/outside
  trees and 508 in `far_full_4.30`. The inherited profile is the default `wgt(L)`.
* The $\alpha_i$ are not X's (5.16) optimum. Any nonnegative $\alpha$ with sum 1 is
  allowed by the lemma.

### A.4 Far budget and negative-budget exclusion

**Lemma A.4 (budget).** In a leaf, let the following hold.
* $\lambda_1\in[a,b]$, and $n\in\{1,2\}$ is the number of first-family characters
  (2 iff $\chi_1$ is nonreal).
* Optionally a reserved family of $n_2$ characters has height-one representatives with
  $\nu_2\in[lo_2,hi_2]$.
* Every ordinary character (nonfirst, nonreserved) with a zero in $R_P$ is represented by
  its $T^*$-representative $\rho_\chi$.
* In the outside model, every first-family character with a zero in $R_P$ other than
  $\rho_1,\bar\rho_1$ is represented by its rightmost such zero (the hidden column).

Then for $q\ge q_0$
$$\sum_{\text{ord}}w(\lambda_\chi)+\sum_{\text{hidden}}w(t_h)\le F:=\overline{(1+\eta)V}-\mathbf 1_{\rm inside}\,n\,\underline{w(b)}-n_2\,\underline{w(hi_2)},$$
where overline and underline denote outward roundings at scale $10^{-16}$. If $F<0$ the
leaf is empty (exclusion).

*Proof.*
1. **Inside.** $\rho_1\in R_B$ gives $|\gamma_1|\le C_B/\ell\le1$. Since $\lambda_1$ is
   the global minimum over $R(l)\supset\{|t|\le1,\lambda\le\lambda_0\}$, $\rho_1$ is
   $\chi_1$'s height-one representative, and $\bar\rho_1$ is $\bar\chi_1$'s.
2. **Reserved family.** Its $n_2$ characters are distinct from the first family and use
   their height-one representatives $\nu_2$. Conjugates have equal $\nu$, because every
   region used is symmetric in $t$.
3. **Ordinary characters.** $|\gamma|\le T^*\le1$.
4. **Hidden zeros.** They lie in $R_P$, so $|\gamma|\le C_P/\ell\le 1$.
5. **Eligibility.** All these zeros have $\lambda\le\max(C_P,2)<\lambda_0(q)$ for large $q$.
   Characters with no zero in $R_P$ cost nothing and are dropped from the configuration.
   Every LP constraint is monotone under dropping characters: all far, count and near
   costs are $\ge0$.
6. **Apply Theorem A** to this set, with one zero per character. $w$ is decreasing
   (`FarProfile.w_antitone`), so $w(\lambda_1)\ge w(b)$ and $w(\nu_2)\ge w(hi_2)$.
   Rounding is in the safe direction.
7. **Exclusion.** If $F<0$, then $n\,w(b)+n_2w(hi_2)>(1+\eta)V$, which contradicts
   Theorem A. ∎

**Code.**
* `published_single_inputs.make_single`:
  `far=upper((1+ETA)V)-n*lower(w(b))` [inside] `-n2*lower(w(hi2))`.
* `far_enclosures.replace_far` does the same with the retuned profile.
* `first_outside_blocks.first_out_input` does the same outside. In subcase `height_one`
  it also subtracts $n\,w(b)$, which is valid only when $|\gamma_1|\le1$, as that subcase
  assumes. The hidden rows have far cost $\underline{w(r)}$.
* `graded_leaves.second_columns` adds back $n_2\underline{w(hi_2)}$ and charges sub-bins
  $[l_j,r_j]$ at $\underline{w(r_j)}$ with $\sum z_j=n_2$. The actual family (mass $n_2$
  on $\nu_2$'s column) is feasible.
* PROOF.md's "$\lceil(1+\eta)V\rceil$" means outward rounding at scale $10^{-16}$, not an
  integer ceiling (D.14).

### A.5 Tail column

**Lemma A.5.** If $A\ge2x$, then $\lambda\mapsto e^{-A\lambda}/w(\lambda)$ is nonincreasing
on $\mathbb R$. If moreover $B\ge0$ is nonincreasing and $G(\lambda)=e^{-A\lambda}B(\lambda)$,
then $G(\lambda)/w(\lambda)\le G(R)/w(R)$ for $\lambda\ge R$.

*Proof.* We have $e^{-A\lambda}w(\lambda)^{-1}=\int_u^x r(t)e^{-(A-2t)\lambda}dt$. Here
$r\ge0$ and $A-2t\ge A-2x\ge0$ on $[u,x]$. So the integrand is nonincreasing in $\lambda$.
Then $G/w=B\cdot(e^{-A\lambda}/w)$ is a product of nonnegative nonincreasing functions.
Lean: `FarProfile.tail_antitone`, `tail_antitone_of_L`. ∎

**Use.** Bins cover $[r_0,R]$ with $R=\max(3,r_0)$ (asserted in
`verify_progress.scenario`: `pos==max(3,ordinary_lower)`). The tail variable is
$x_\infty:=\sum_{\lambda_\chi\ge R}w(\lambda_\chi)$, with far coefficient 1. Its objective
coefficient is $\overline{G(R)w(R)^{-1}}$ (`rows_for`, `single_rows`, `replace_far`). Its
count cost is 0 and its near feature is $\le0$ (omitted).
* Validity: $\sum_{\lambda\ge R}G(\lambda)\le\frac{G(R)}{w(R)}\sum w(\lambda)$ by Lemma
  A.5, since $B=B_{1/3}$ is positive and decreasing (§3 of PROOF.md).
* Count cost 0 is valid because $R\ge3>1.5\ge$ every $\lambda_3$ lower bound.
* At $L=3.99$, $A=3.156342$, against $2x=2.3474$ (inherited) and $2.2607$ (retuned).
  Checked with outward arithmetic in `replace_far` and `global_checks`.

**Corollary A.5' (error summation, used by PROOF.md §2 E2).** For the representatives of
Theorem A and $\lambda\ge0$, $e^{-A\lambda}\le w(\lambda)/w(0)$. Hence
$\sum_\chi e^{-A\lambda_\chi}\le(1+\eta)V/w(0)$. This is $<16.38$ (inherited) and
$<18.48$ (retuned), both $<19$.

### A.6 Strip representatives $T^*$

**Setting.** Let $s_{\max}$ be a fixed number at least every response anchor used by an
ordinary entry of any row. The anchors form a finite rational menu, e.g. up to 2.3. Let
$\delta\in(0,1)$ be the disc radius of X Lemma 3.2 for the finitely many tests. In fact
$\delta\le1/6$ (PROOF.md §3, from H p. 14).

**Lemma A.6.1 ($K_0$).** There are $K_0=K_0(s_{\max})$ and $q_1$ such that for $q\ge q_1$
$$\#\{\rho:\ L(\rho,\chi)=0\text{ for some }\chi\bmod q,\ \lambda_\rho\le s_{\max},\ |\operatorname{Im}\rho|\le2\}\le K_0\qquad(\text{with multiplicity}).$$
*Proof.* Use a log-free density estimate. Jutila (1977, Thm 1, (1.7)), as quoted in the
proof of H Lemma 6.1 (p. 26), gives
$$\textstyle\sum_{\chi}N(\sigma,T,\chi)\ll_\epsilon(qT)^{(2+\epsilon)(1-\sigma)}\qquad(4/5\le\sigma\le1,\ T\ge1).$$
H (1.4) (p. 5) is an alternative. With $1-\sigma=s_{\max}/\ell$, $T=2$ and $\epsilon=1$,
the count is $\ll e^{3s_{\max}}$. ∎

**Lemma A.6.2 (pigeonhole).** Let $M\ge1$ and suppose $\ell>4M(K_0+1)$. Then there is
$T^*\in[\frac12,1]$ such that no zero counted in A.6.1 satisfies
$\bigl||\operatorname{Im}\rho|-T^*\bigr|<M/\ell$.

*Proof.* Each counted zero excludes an open $T^*$-interval of length $2M/\ell$. The union
has measure $\le2MK_0/\ell<\frac12=|[\frac12,1]|$. ∎

**Definition.** The $T^*$-representative of $\chi$ is a rightmost zero (least $\lambda$) of
$L(s,\chi)$ with $|\operatorname{Im}\rho|\le T^*$ and $\lambda\le\lambda_0$, if one exists.

**Lemma A.6.3 (properties).** For $q\ge q_0$:
1. The $T^*$-representative is eligible in Theorem A.
2. Its parameter is at least the height-one representative's parameter.
3. Consider an ordinary entry at the representative's height $\gamma_j$ with anchor
   $s_j\le\min(lo,s_{\max})\le\lambda_j$. Every zero $\rho$ of $\chi$ in the disc
   $|1+i\gamma_j-\rho|\le\delta$ with $\lambda_\rho<s_j$ has
   $|\mu_\rho-\gamma_j\ell|\ge M$. At most $K_0$ such zeros exist.
4. Every zero in the height-0 disc $|1-\rho|\le\delta$ has $|\operatorname{Im}\rho|<T^*$.

*Proof.*
1. Immediate, since $T^*\le1$.
2. The $T^*$-strip is contained in the height-one strip.
3. Such $\rho$ has $\lambda_\rho<s_j\le\lambda_j$. So $|\operatorname{Im}\rho|>T^*$,
   since $\rho_j$ is rightmost in the strip. Also
   $|\operatorname{Im}\rho|\le T^*+\delta<2$ and $\lambda_\rho<s_{\max}$, so $\rho$ is
   counted in A.6.1. By A.6.2, $|\operatorname{Im}\rho|\ge T^*+M/\ell$. Hence
   $\ell|\operatorname{Im}\rho-\gamma_j|\ge\ell(|\operatorname{Im}\rho|-T^*)\ge M$.
4. $|\operatorname{Im}\rho|\le\delta\le1/6<1/2\le T^*$. ∎

**Consequences.**
* Count rule and ordinary lower bound survive: both are lower bounds for height-one
  representatives, and (2) moves representatives right.
* The far row is unchanged: any eligible zero may be chosen.

**Quantifier order** (matches PROOF.md §10, items 4–6).
1. $s_{\max}$ (fixed menu).
2. $K_0(s_{\max})$, a bound valid for $q\ge q_1$.
3. $M$, from $K_0$ and the tests: $|F(x+iY)|\le\eta'/(2K_0)$ and
   $|G_1(-\sigma+iY)|\le\eta'/4$ for $|Y|\ge M$.
4. $C_B$.
5. The tolerances, which fix $\delta<1$.
6. $q_0\ge q_1$ with $\ell>4M(K_0+1)$.
7. For each $q$, $T^*(q)$.

Counting to height 2 rather than $1+\delta$ is what breaks the apparent circularity: $\delta$
is fixed after $M$, and $M$ after $K_0$.
* This is sound.
* `SOURCE_INTERFACES.md` still says "height $\le1+\delta$" (D.10).

### A.7 Code correspondence (far part)

| Item | Code | Status |
|---|---|---|
| $w^{-1}$, $J_i$, $V$ closed forms | `core/code/base_enclosures.py` (`RigorousWeights.winv`, `J_i`), reused by `enclosures.RigorousWeights` (inherited) and `frontier/far_enclosures.RigorousFar` (retuned) | matches A.2. $V$ uses $100/(c_1c_2^2)$; the $\varepsilon$ of (5.19) is in the $(1+\eta)$ factor |
| $\sum\alpha=1$, $\alpha>0$ | `config_v4.ALPHA` (last entry defined as $1-\sum$), `RigorousFar.__init__` asserts | exact |
| budget | `make_single`, `replace_far`, `first_out_input`, `second_columns` | A.4 |
| tail | `single_rows` (end $=\max(3,r)$), `replace_far` (`row[2]=S`, objective $G(R)w(R)^{-1}$); decay `lower(A-2x)>0` asserted | A.5 |
| $T^*$ | no code: the representatives are an argument, not a computed object | A.6 |
| Lean | `GradedNear/Far.lean` (`XylourisLemma51`, stated as printed, with $q_0$ before $\forall$ choices), `FarFacts.lean` (profile conditions, monotonicity, tail, `far_bound_corpus`) | consistent with A.2 and A.5 |

---

## Part B. Zero location (PROOF.md §5)

### B.1 Conventions and the specification semantics

**Height and rectangle** [X Lemma 3.3 = H Lemma 6.1; X (3.7), p. 18; H (6.1), p. 26].
For $q\ge q_0$ there is an integer $1\le l=l(q)\le\ell/10$ such that
$\prod_\chi L(s,\chi)$ has no zeros in $R(10l)\setminus R(l)$. Here
$R(x)=\{1-\frac{\log\log\ell}{3\ell}\le\sigma\le1,\ |t|\le x\}$. Fix one such function
$l(q)$ once and for all; see D.6.

**Selection** [X (3.11)–(3.12), p. 21; H p. 26].
* $\rho_1$ is a zero of $\prod_\chi L(s,\chi)$ in $R(l)$ with maximal real part, and
  $\chi_1$ is a corresponding character.
* $\rho_k$ is a zero of maximal real part of
  $\prod_\chi L(s,\chi)\big/\prod_{i<k}L(s,\chi_i)L(s,\bar\chi_i)$ in $R(l)$.
* Then $\chi_i\ne\chi_j,\bar\chi_j$ for $i\ne j$.
* (3.12): if $\chi\ne\chi_i,\bar\chi_i$ for all $i<k$ and $L(\rho,\chi)=0$, then
  $\operatorname{Re}\rho\le\operatorname{Re}\rho_k$ or $|\operatorname{Im}\rho|\ge10l$.

So $\lambda_1\le\lambda_2\le\lambda_3$ are the successive family minima over $R(l)$.

**The additional first-family zero** [X pp. 21–22 (Fall 1–3); H p. 28 ($\rho_0$)].
$\rho'=\rho_1$ if $\rho_1$ has multiplicity $\ge2$ (Fall 1). Otherwise:
* $\rho'$ maximizes $\operatorname{Re}$ over the zeros of $L(s,\chi_1)$ in $R(l)\setminus\{\rho_1,\bar\rho_1\}$
  if $\chi_1$ is real and $\rho_1$ nonreal (Fall 2);
* over $R(l)\setminus\{\rho_1\}$ otherwise (Fall 3).

$\lambda'$ is its parameter; X and H write $\lambda_0$. For nonreal $\chi_1$ this is the
least parameter of another zero occurrence of $\chi_1$ or $\bar\chi_1$, since zeros of
$L(s,\bar\chi_1)$ are the conjugates of those of $L(s,\chi_1)$. So it agrees with
PROOF.md §1.

**Types.**
* rr: $\chi_1,\rho_1$ real.
* rc: $\chi_1$ real, $\rho_1$ nonreal.
* complex: $\chi_1$ nonreal. Then $n=2$, and $n=1$ otherwise.

**Height-one representative** of a character: a zero of least $\lambda$ with
$|\operatorname{Im}\rho|\le1$ (and $\lambda\le\lambda_0$). $\nu(F)$ denotes its parameter for
a family $F$; conjugates share it.

**Specification.** A specification is
$S=(\tau,[a,b],lp,\mathrm{gap},\mathrm{source\_l2},r,\mathrm{second})$.
A configuration **satisfies** $S$ iff all of the following hold.
1. The type is $\tau$ and $\lambda_1\in[a,b]$.
2. $\lambda'\ge lp$, and $\lambda'\in[\mathrm{gap.lo},\mathrm{gap.hi}]$ when a gap is
   recorded ($\mathrm{hi}=\infty$ allowed; "$\lambda'=\infty$" means no such zero).
3. $\lambda_2\ge\mathrm{source\_l2}$.
4. If $\mathrm{second}=(lo_2{=}r,hi_2,n_2)$: some non-first family $F_r$ minimizes $\nu$
   over non-first families, consists of $n_2$ characters ($n_2=1$ real, $n_2=2$ nonreal
   pair), and $\nu(F_r)\in[lo_2,hi_2]$. Every other non-first family then has
   $\nu\ge r$.
5. If $\mathrm{second}=$ none: every non-first family has $\nu\ge r$.

Field $r$ is `ordinary_lower`. By A.6.3(2), items 4–5 also hold for $T^*$-representatives.

### B.2 The $\varepsilon$-convention for printed tables

All printed zero-location values are used as exact implications for $q\ge q_0$.
Justification by source:
* **X.** Each row is obtained by showing that the relevant inequality is negative after
  $\varepsilon$ is dropped: "wir erhalten einen negativen Wert … Für hinreichend kleines
  $\varepsilon>0$ ist dies ein Widerspruch. Also haben wir für $q\ge q_0(f,k,\varepsilon)$
  bewiesen, dass aus $\lambda_1\in[0.34,0.36]$ die Abschätzung $\lambda_0>2.06$ folgt"
  (X p. 43). Tables are statements "$\lambda_1\le\lambda_{12}\Rightarrow\lambda_0>c_2$"
  (X p. 44). The same "etwas Negatives" argument is on X p. 57 (Table 9) and p. 59
  (Table 10, "$\lambda_3>\lambda_{32}=1.176$"). Lemmas 4.4 and 4.5 are stated with a
  $q_0$ and no $\varepsilon$ (X pp. 55, 61).
* **H.** X fn. 2, p. 45: "for any bounds of [H] presented as $\lambda\ge c$, in reality
  $\lambda>c$ was shown … by continuity, if $\lambda\ge c$ was shown by the above method,
  then also $\lambda\ge c+\varepsilon$". For Tables 2–3, H p. 38 says the printed
  $\lambda_0$ are "calculated values a little below $\lambda_{0b}$", with
  $\lambda_0\ge\lambda_{0b}-\varepsilon$ for $q\ge q(\varepsilon,b)$.
  * For **H Tables 4 and 7** H states no convention. I recomputed the roots:
    * **Table 4** (H Lemma 8.3, (8.7) with $P_3(X)=X+X^2+\frac23X^3$ and the printed
      $a,K$): all 24 roots exceed the printed values by $3.8\times10^{-5}$ (row 1.05:
      1.439038) to $9.2\times10^{-4}$. (8.6) holds at $(\lambda_1,\lambda_0)=(B,\text{root})$
      with margins $\ge2.0\times10^{-5}$. (8.8) holds at the previous row. Script:
      `scratchpad/deep/h_table4.py`.
    * **Table 7** (H Lemma 8.7, (8.11), Lemma 7.1 test with $\theta=1$, printed $\lambda$,
      $k=.98-.15\lambda_1$): rows .20, .35, .55, .60, .745 give roots 2.010146, 1.428584,
      1.000358, .924011 and .745516. All exceed the printed values. Script
      `h_table7.py`.
  * H Lemma 8.8 ($\lambda_2\ge.745$) and H Lemma 8.4 ($\lambda_0\ge1.294$) have roots
    .74552 and 1.29465.
  * These agree with `notes/source-table-audit-2026-09-29.md`.
* **Inputs of the form $c-\varepsilon$:** H Lemma 10.3 ($\frac67-\varepsilon$) is used
  as $.857<6/7$.

### B.3 Types and first-zero bounds

**X Lemma 4.5 (p. 61; Table 11, p. 60), translated.** "Let $\chi_1$ or $\rho_1$ be complex.
Then there is a $q_0$ such that for $q\ge q_0$: $\lambda_1>0.440$ if
$\operatorname{ord}\chi_1\ge6$; $>0.493$ if $=5$; $>0.478$ if $=4$; $>0.498$ if $=3$;
$>0.628$ if $=2$."

**Corollary B.3.**
* Type complex ($\operatorname{ord}\chi_1\ge3$): $\lambda_1>.44$.
* Type rc ($\chi_1$ real, so order 2, with $\rho_1$ nonreal): $\lambda_1>.628$.
* So $\lambda_1\le.44$ forces type rr.

H Lemma 9.5 (p. 59) alone gives only .348–.518.

**Cover starts.** rr at .1 (smaller $\lambda_1$ is the separate small branch, PROOF.md §9),
rc at .628, complex at .44. The code checks this with `check_first_cover`; the
complementary regimes are not in my scope.

### B.4 Printed table inputs (value, scope, page) and the parent table

**Heath-Brown (type rr unless stated).** H's $\lambda_0$ is our $\lambda'$.
* **H Table 4 (p. 44; meaning p. 43).** "The entry 0.7, 1.724, 4.5, 0.85 indicates that
  $\lambda_0\ge1.724$ whenever $\lambda_1\le0.7$." Rows ($\lambda_1\le t\Rightarrow\lambda_0\ge c$):
  .3/2.293, .35/2.195, .4/2.108, .45/2.030, .5/1.958, .55/1.893, .6/1.832, .65/1.776,
  .7/1.724, .75/1.676, .8/1.630, .85/1.587, .9/1.547, .95/1.509, 1/1.473, 1.05/1.439,
  1.1/1.406, 1.15/1.375, 1.175/1.360, 1.2/1.346, 1.225/1.331, 1.25/1.318, 1.275/1.304,
  1.294/1.294.
  * Validity for real $\rho_0$ comes from H Lemma 8.2 ($\lambda_0\ge2.427$, p. 38).
  * Validity for smaller $\lambda_1$ comes from better bounds there (X pp. 23–24).
  * Code `cover_v5.H_PRIME`: all 24 match.
* **H Lemma 8.4 (p. 43).** "Let $\chi_1$ and $\rho_1$ be real … Moreover
  $\lambda_0\ge\max(\frac32\log\lambda_1^{-1},1.294)$ for all sufficiently large $q$ and
  any $\lambda_1$."
* **H Table 7 (p. 48; Lemma 8.7 p. 47).** Rows: .12/2.56, .14/2.39, .16/2.25, .18/2.12,
  .2/2.01, .25/1.77, .3/1.58, .35/1.42, .4/1.29, .45/1.18, .5/1.08, .55/1.00, .6/.92,
  .65/.85, .7/.79, .745/.745.
  * H p. 47: "the values in Table 7 apply whether $\chi_2^4\ne\chi_0$ or not", and the
    condition $\lambda_2\le\lambda_0$ is redundant.
  * X p. 24: valid in all cases except $\lambda_1\le.10$. The row .10 (2.76) is not used.
  * `cover_v5.H_SECOND`: all 16 match.
* **H Lemma 8.8 (p. 48).** "… Moreover $\lambda_2\ge0.745$ for all sufficiently large $q$."
* **H Table 10 (p. 57) with Lemma 9.4 (p. 56)**, complex case ($\chi_1$ or $\rho_1$
  complex). "The bounds given in Table 10 apply in all cases. In particular we have
  $\lambda_2\ge0.702$." Used rows: $\lambda_1\le.70\Rightarrow\lambda_2\ge.704$, and
  $\lambda_2\ge.702$ for all $\lambda_1$ (for $\lambda_1>.702$ by ordering).
* **H Lemma 10.3 (p. 67).** "Let $\varepsilon>0$. Then if $q$ is sufficiently large we have
  $\lambda_3\ge\frac67-\varepsilon$." This is for all types.

**Xylouris.**
* **X Table 2′ (p. 62)** ($\chi_1$ or $\rho_1$ complex; uses $\lambda_1\ge.44$).
  $\lambda_1\le$ .46/.48/.50/.52/.54/.56/.58/.60/.62/.64/.66/.68/.70/.72/.74/.76/.78/.80/.82/.827
  gives $\lambda'>$ 1.85/1.76/1.67/1.59/1.51/1.44/1.36/1.29/1.22/1.15/1.08/1.02/.96/.93/.91/.89/.86/.84/.83/.827.
  Used rows: .58, .64, .66, .68, .70, .72, .74, .76, .78, .80, .82 and .827.
* **X Table 3 (p. 45)** ($\chi_1$ or $\rho_1$ complex, $\operatorname{ord}\chi_1\in\{2,3,4\}$).
  $\lambda_1\le$ .38/.42/.46/.50/.54/.58/.62/.66/.70/.74/.78/.82/.86/.90/.94/.98/1.02/1.06/1.099
  gives $\lambda'>$ 2.53/2.35/2.20/2.06/1.94/1.84/1.75/1.67/1.59/1.52/1.46/1.40/1.35/1.30/1.25/1.21/1.17/1.13/1.099.
  * Used for rc: `cover_v4.REAL_COMPLEX_PRIME`, all 12 match.
  * Used for complex of order 3 or 4: row .86 $\Rightarrow\lambda'>1.35$ (B.8).
* **X Table 6 (p. 53)** (rc, Fall 7 = order 2): $\lambda_1\le$ .54/.58/.62/.66/.70/.74/.78/.82
  gives $\lambda_2>$ 1.43/1.36/1.28/1.20/1.11/1.02/.93/.82. Used: .78 → .93 and .82 → .82.
* **X Table 7 (p. 53)** ($\chi_1$ or $\rho_1$ complex, all cases, minimum of Tables 4–6).
  Used: .58 → 1.04, .64 → .85, .66 → .79, .68 → .74.
* **X Table 8 (p. 55)** ($\chi_1$ or $\rho_1$ complex; column "alle Fälle" = min of the
  Fall columns). $\lambda_1\le$ .52/.54/.56/.58/.60/.62 gives $\lambda_3>$
  1.320/1.243/1.160/1.079/1.001/.933. For $\lambda_1\le.50$, Table 7 gives
  $\lambda_3\ge\lambda_2\ge1.36$ (X p. 54).
* **X Lemma 4.4 / Table 10 (p. 55)** ($\chi_1,\rho_1$ real):
  $\lambda_1\in[.44,.60]\Rightarrow\lambda_3>1.176$; $[.60,.70]\Rightarrow1.055$;
  $[.70,.80]\Rightarrow.952$.
* **X (4.28)–(4.29) (pp. 56–57)** and **(4.31)–(4.34) (pp. 58–59)**: see B.11.

**Parent table.** Code: `case_cover.PARENTS`, refined by `cover_v4` (X Table 2′ rows
.76, .80; X Table 3) and `cover_v5` (H Tables 4, 7). Each refined subcell takes the
maximum over all rows with breakpoint $\ge$ its right end. `cell()` then sets
$lp=\max(p,lo)$ and $\mathrm{source\_l2}=\max(r,lo)$, by the ordering
$\lambda',\lambda_2\ge\lambda_1$. There are 58 parents $[a,b)$, listed as
$(p=\lambda'\text{ bound},\ r=\lambda_2\text{ bound})$:

* **rr.** [.1,.12) (2.293, 2.56); [.12,.14) (2.293, 2.39); [.14,.16) (2.293, 2.25);
  [.16,.18) (2.293, 2.12); [.18,.2) (2.293, 2.01); [.2,.25) (2.293, 1.77);
  [.25,.3) (2.293, 1.58); [.3,.348) (2.195, 1.42); [.348,.35) (2.195, 1.42);
  [.35,.4) (2.108, 1.29); [.4,.45) (2.03, 1.18); [.45,.5) (1.958, 1.08);
  [.5,.55) (1.893, 1.0); [.55,.6) (1.832, .92); [.6,.65) (1.776, .85);
  [.65,.7) (1.724, .79); [.7,.745) (1.676, .745); [.745,.75) (1.676, .745);
  [.75,.8) (1.63, .745); then [.8,.85) through [1.294,1.5) with
  $p=$1.587, 1.547, 1.509, 1.473, 1.439, 1.406, 1.375, 1.36, 1.346, 1.331, 1.318,
  1.304, 1.294, 1.294 (H Table 4 / Lemma 8.4) and $r=.8$ (ordering).
* **rc.** [.628,.66) (1.67, .93); [.66,.7) (1.59, .93); [.7,.74) (1.52, .93);
  [.74,.78) (1.46, .93); [.78,.82) (1.40, .82); [.82,.86) (1.35, .82);
  [.86,.9) (1.30, .82); [.9,.94) (1.25, .82); [.94,.98) (1.21, .82);
  [.98,1.02) (1.17, .82); [1.02,1.06) (1.13, .82); [1.06,1.099) (1.099, .82);
  [1.099,1.5) (1.099, .82).
* **complex.** [.44,.58) (1.36, 1.04); [.58,.64) (1.15, .85); [.64,.66) (1.08, .79);
  [.66,.68) (1.02, .74); [.68,.70) (.96, .704); [.70,.72) (.93, .702); [.72,.74) (.91, .72);
  [.74,.76) (.89, .74); [.76,.78) (.86, .74); [.78,.80) (.84, .78); [.80,.82) (.83, .78);
  [.82,1.5) (.827, .82).

I checked every number against the page text above. None exceeds a printed value, and each
source row is used only at a breakpoint $\ge$ the cell's right end.

**Proposition B.4 (source cover).** Let $q\ge q_0$ and $.1\le\lambda_1<1.5$. Then the
configuration satisfies at least one of the 2768 specifications of
`computations/core/results/source_cover.json.gz`.

*Proof.*
1. **Type and first zero.** By B.3 the pair (type, $\lambda_1$) lies in the type's range.
   The 340 roots (width-.01 subcells of the parents) are subdivided into 478 cells that
   partition it: $[.1,1.5)$ for rr, $[.628,1.5)$ for rc, $[.44,1.5)$ for complex. Boundary
   points are covered, since the closed cells overlap.
2. **Parent bounds.** A cell $\subseteq$ parent $[a,b)$ inherits valid $lp$ and
   $\mathrm{source\_l2}$ by the tables of this section.
3. **Gap partition.** In `gap_mode='partition'` (complex only) the gap intervals
   partition $[lp,\infty)\ni\lambda'$. Otherwise one proof has gap none.
4. **Second-family partition.** Let $\nu^*=\min\{\nu(F)\}$ over non-first families
   ($+\infty$ if none). Since the height-one strip at $\lambda\le\lambda_0$ lies in $R(l)$,
   $\nu^*\ge\lambda_2\ge\mathrm{source\_l2}$.
   * In mode `unreserved`, the single record has $r=\mathrm{source\_l2}$.
   * In mode `reserved`, the records are pairs ($n_2=1$, $n_2=2$) over half-open
     intervals partitioning $[\mathrm{source\_l2},\mathrm{tail\_start})$, followed by an
     unreserved record with $r=\mathrm{tail\_start}$.
   * If $\nu^*<\mathrm{tail\_start}$, take the interval containing $\nu^*$ and the
     record matching the minimizer's size (a real character, or a nonreal pair).
     Otherwise take the last record.

   All other families have $\nu\ge\nu^*\ge lo_2=r$. The records satisfy
   $\mathrm{source\_l2}\le r\le3$ and $hi_2\le2$.

`refinement_cover.validate_source_cover` + `verify_v5.check_leaf/check_density` check
this structure. I re-ran it: 340 roots, 478 cells, 684 gap cases, 2768 specifications
(1083 rr, 115 rc, 1570 complex).
* Reserved: rr 444+444, complex 598+598.
* Unreserved: rr 195, complex 374, rc 115. ∎

### B.5 Explicit-formula toolkit and the positivity method

**Printed inputs (translated).**
* **$\varphi$ (X p. 17).** For $\chi\ne\chi_0$: $\varphi(\chi)=\frac14$ if $q$ is
  cube-free or $\operatorname{ord}\chi\le\ell$, and $\frac13$ otherwise. This is the same
  as H Lemma 2.5, p. 10.
* **Conditions 1–2 (X pp. 17–18).**
  * Condition 1: $f$ continuous on $[0,\infty)$, $f=0$ on $[x_0,\infty)$, $C^2$ on
    $(0,x_0)$ with $|f''|\le B$.
  * Condition 2: $f\ge0$ and $\operatorname{Re}F(z)\ge0$ for $\operatorname{Re}z\ge0$.
* **Test $f_\gamma$.** The parabolic autocorrelation (X (3.17), p. 23):
  $f_\gamma(t)=-\frac{t^5}{30}+\frac{2\gamma^2}3t^3-\frac{4\gamma^3}3t^2+\frac{16\gamma^5}{15}$
  on $[0,2\gamma)$, and 0 beyond. Its transform is X (3.18). It satisfies Conditions 1–2
  (X Lemma 3.6). The code's form $\frac{16\gamma^5}{15}(1-u)^3(1+3u+u^2)$ with
  $u=t/2\gamma$ is identical. In particular $f_\gamma(0)=16\gamma^5/15$, and $F$ is
  decreasing on $\mathbb R$.
* **X Lemma 3.1 (p. 18) = H Lemma 5.3.** For $|\sigma-1|\le(\log\ell)^{1/2}/\ell$ and
  $|t|\le\ell$:
  $\sum_n\Lambda(n)\chi_0(n)n^{-s}f(\ell^{-1}\log n)=\ell F((s-1)\ell)+O_f(\ell/\log\ell)$.
* **X Lemma 3.4 (p. 19), "working version" of H Lemma 5.2.** Let $\chi\ne\chi_0$ and
  $s\in R(9l)$. Suppose $A_1:=\{\rho\in R:L(\rho,\chi)=0,\operatorname{Re}\rho>\operatorname{Re}s\}$
  has $\#A_1\le10$, and $A_2\subseteq\{\rho\in R:L(\rho,\chi)=0,\operatorname{Re}\rho\le\operatorname{Re}s\}$
  has $\#A_2\le10$, both with multiplicity. If $f$ satisfies Conditions 1–2, then for all
  $\varepsilon>0$ and $q\ge q_0(f,\varepsilon)$,
  $$K(s,\chi):=\sum_n\Lambda(n)\operatorname{Re}\frac{\chi(n)}{n^s}f(\ell^{-1}\log n)\le-\ell\sum_{\rho\in A_1\cup A_2}\operatorname{Re}F((s-\rho)\ell)+f(0)\frac\varphi2\ell+\varepsilon\ell.$$
  "10" may be any fixed $N$ (X p. 21).

**Lemma P (positivity method).** Let the following be fixed:
* $a\in[0,\log\log\ell/3]$ with $a\le\lambda_1$;
* finitely many triples $(c_j,\psi_j,\tau_j)$ with $c_j>0$, $\psi_j$ a character mod $q$
  and $|\tau_j|\le9l$, where each $\tau_j$ is a fixed integer combination of chosen zero
  heights;
* a multiset $A_2(j)$ of at most 10 zeros of $L(s,\psi_j)$ in $R(l)$ for each nonprincipal
  $\psi_j$.

Suppose $\sum_jc_j\operatorname{Re}(\psi_j(n)n^{-i\tau_j})\ge0$ for all $(n,q)=1$. Then
for every $\varepsilon>0$ and $q\ge q_0$,
$$\sum_{\psi_j=\chi_0}c_j\operatorname{Re}F(-a+i\tau_j\ell)\;-\sum_{\psi_j\ne\chi_0}c_j\!\!\sum_{\rho\in A_2(j)}\!\!\operatorname{Re}F\bigl((1-\tfrac a\ell+i\tau_j-\rho)\ell\bigr)\;+\;\frac{f(0)}2\sum_{\psi_j\ne\chi_0}c_j\varphi(\psi_j)\;+\;\varepsilon\ \ge0 .$$

*Proof.* Multiply by $\Lambda(n)n^{-(1-a/\ell)}f(\ell^{-1}\log n)\ge0$ and sum. For
$(n,q)>1$ every term vanishes, including $\chi_0$. Then:
1. The principal terms follow from X Lemma 3.1, since $|\tau_j|\le9l\le\ell$ and
   $a/\ell\le(\log\ell)^{1/2}/\ell$.
2. For the others, $s_j=1-a/\ell+i\tau_j\in R(9l)$ because $0\le a\le\log\log\ell/3$, and
   $A_1=\emptyset$ because every zero in $R(l)$ has $\lambda\ge\lambda_1\ge a$. Apply
   X Lemma 3.4.
3. Divide by $\ell$ and adjust $\varepsilon$. ∎

**How rows are proved.** Assume the conclusion fails. Bound the retained terms below using
monotonicity of $F$ on $\mathbb R$ ($F(x)\ge F(x')$ for $x\le x'$) and enclosures of the
correlation terms over all real heights. The left side of Lemma P then becomes
$\le-\text{margin}\cdot f(0)<0$. Choose $\varepsilon$ below every margin; the menu is
finite.

### B.6 Refined conductor coefficient (the $1/108$ saving) [R/PD]

This input is behind all 300 `real_location` nodes of the tree.

**Lemma C.** Let $v=\prod_{p^e\Vert q,\,e\ge3}p^e$ and $\theta_q=\log v/\log q\in[0,1]$.
Fix $\epsilon>0$. Lemma P remains valid, with $q_0$ depending also on $\epsilon$, if
$\varphi(\psi_j)$ is replaced as follows:
* $\varphi(\chi_1)\to\frac14-\frac{\theta_q}6+\epsilon$ for a real $\chi_1$;
* $\varphi(\psi)\to\min(\frac13,\frac14+\frac34\theta_q)+\epsilon$ for every other
  nonprincipal $\psi$.

Consequently, suppose $\sum_{\psi_j\ne\chi_0}c_j\varphi(\psi_j)$ has the shape
$\varphi(\chi_1)+2\Sigma\varphi_{\rm gen}$ with $\Sigma\ge\frac19$. Then the conductor term
may be taken as
$$\Bigl(\frac18+\frac\Sigma3-\frac1{108}\Bigr)f(0).$$

*Derivation.*
1. **H §16(4) (pp. 93–94), translated.** With $q_1=\prod_{p\mid q}p$ and $q_2=v^3q$,
   "it is apparent from the work of §2, and from Lemma 2.3 in particular, that the bound
   on the right of (2.5) may be replaced by
   $q_1^{\frac14(1-\sigma)(1+k^{-1})+\varepsilon}(1+|t|)$ for $\chi$ real, and either
   $q^{\frac13(\dots)}$ or $q_2^{\frac14(\dots)}$ in general. Thus we may estimate $\psi$
   as $\frac18\frac{\log q_1}{\log q}+\min(\frac13,\frac14\frac{\log q_2}{\log q})$", which
   H then bounds by $\frac{97}{216}$.
2. **Reconstruction of the Burgess input.**
   * *Real case.* A real primitive $\chi^*$ has conductor $q^*=|D|\le4q_1$. Its order is
     $2\le\ell$, so H Lemma 2.4 allows every $k$. H (2.2)–(2.4) give
     $L(s,\chi^*)\ll q^{*\,(1-\sigma)(\frac14+\frac1{4k})+\varepsilon}(1+|t|)$. Also
     $L(s,\chi)\ll q^\varepsilon L(s,\chi^*)$ (H p. 10).
   * *General case.* H Lemma 2.3 (p. 8) gives a character sum bound
     $v^{(3k-1)/4k^2}q^{(k+1)/4k^2+\varepsilon}H^{1-1/k}\le(v^3q)^{(k+1)/4k^2}q^\varepsilon H^{1-1/k}$.
     The same partial summation with cut $q_1'=(v^3q)^{(k+1)/4k}$ gives
     $(v^3q)^{\frac14(1-\sigma)(1+1/k)+\varepsilon}$. For an inducing $\chi^*\bmod q^*$,
     $q^*\le q$ and $v(q^*)\le v(q)$.
3. **Arithmetic.** $\operatorname{rad}(q)\le q v^{-2/3}$, since $p\le(p^e)^{1/3}$ for
   $e\ge3$. So $\frac14\frac{\log q_1}{\log q}\le\frac14-\frac\theta6+o(1)$ and
   $\frac14\frac{\log q_2}{\log q}=\frac14+\frac34\theta$.
4. **Explicit formula with $q$-dependent $\varphi$.** H Lemma 3.1 (hence H Lemma 5.2 and
   X Lemmas 3.2/3.4) uses the bound (2.5) only through a fixed growth coefficient. Split
   the moduli into finitely many classes $\{q:\varphi^*(q)\le\varphi_i\}$, where
   $\varphi_i$ is a $\epsilon$-net of $[0,\frac13]$. Apply the proof with the constant
   $\varphi_i$ in each class and take the largest $q_0$. The error is
   $\le\epsilon f(0)$.
5. **Maximization.** $g(\theta)=\frac18-\frac\theta{12}+\Sigma\min(\frac13,\frac14+\frac34\theta)$
   has slope $-\frac1{12}+\frac34\Sigma\ge0$ on $[0,\frac19]$ when $\Sigma\ge\frac19$, and
   slope $-\frac1{12}$ after. So $\max_{[0,1]}g=g(\frac19)=\frac18+\frac\Sigma3-\frac1{108}$.
   For $\Sigma=1$ this is H's $\frac{97}{216}$.

Steps 2 and 4 are not printed anywhere as proofs; see D.1.

### B.7 Real-first rows (type rr): $\lambda_2$ lower bounds [R]

**Setting.** $\chi_1,\rho_1$ real, $\lambda_1\in[a,b]$, and $\chi_2$ is the character of the
global second family with zero $\rho_2$ ($\lambda_2$, height $\gamma_2$, $|\gamma_2|\le l$).
Let $z_n=\chi_2(n)n^{-i\gamma_2}$ and let $P(z)=1+\sum_kc_k\operatorname{Re}z^k\ge0$ on
$|z|=1$. Apply Lemma P to $\chi_0(n)(1+\chi_1(n))P(z_n)\ge0$ with anchor $a$. Retain $\rho_1$
in the $\chi_1$ term at height 0, and $\rho_2$ in the $c_1$-term $\chi_2$ at height
$\gamma_2$.

**Proposition B.7 (four cases).** Suppose $\lambda_2\le h$. Then:

1. **$\chi_2$ nonreal, no principal alias** (none of $\chi_2^k,\chi_1\chi_2^k$,
   $k\in K$, is principal):
   $$F(\lambda_1-a)+c_1F(\lambda_2-a)\le F(-a)+\Bigl(\tfrac18+\tfrac{\sum_kc_k}3-\tfrac1{108}\Bigr)f(0)+o(1)$$
   by Lemma C. Without Lemma C, drop the $-\frac1{108}$.
2. **$\chi_2^2=\chi_1$ (order 4).** $\chi_1\chi_2=\bar\chi_2$ and $\chi_1\chi_2^2=\chi_0$
   (principal at height $2\gamma_2$). $\chi_2^2=\chi_1$ at height $2\gamma_2$ retains $\rho_1$;
   $\bar\chi_2$ at height $\gamma_2$ retains $\bar\rho_2$. With $\Delta=2\mu_2$:
   $$F(\lambda_1-a)+c_1F(\lambda_2-a)\le F(-a)+\Bigl(\tfrac{1+c_2}8+\tfrac{c_1+c_5}3\Bigr)f(0)+R(\Delta)+o(1),$$
   $$R(\Delta)=c_2\{\operatorname{Re}F(-a+i\Delta)-\operatorname{Re}F(\lambda_1-a+i\Delta)\}-c_1\operatorname{Re}F(\lambda_2-a+i\Delta).$$
   The $c_5$ characters $\chi_2^5=\chi_2$ and $\chi_1\chi_2^5=\bar\chi_2$ are nonprincipal,
   charged $\frac13$, with zeros dropped. $\chi_2$ has order 4, so $\frac14$ would be
   allowed; $\frac13$ is conservative.
3. **$\chi_2^5\in\{\chi_0,\chi_1\}$ (order 5 or 10)**, degree 5 only. Exactly one term
   ($c_5$) is principal, bounded by $c_5\operatorname{Re}F(-a+i\cdot5\mu_2)\le c_5F(-a)$
   since $f\ge0$. All other characters have order $\le10\le\ell$, so $\varphi=\frac14$:
   $$F(\lambda_1-a)+c_1F(\lambda_2-a)\le(1+c_5)F(-a)+\Bigl(\tfrac{1+c_5}8+\tfrac{c_1+c_2}4\Bigr)f(0)+o(1).$$
4. **$\chi_2$ real** ($\ne\chi_1$). Use $(1+\chi_1)(1+\operatorname{Re}z_n)\ge0$. The three
   nonprincipal characters are real ($\varphi=\frac14$), and $\rho_2$ may be nonreal:
   $F(\lambda_1-a)+F(\lambda_2-a)\le F(-a)+\frac38f(0)+o(1)$.

*Exhaustiveness.* The nonzero frequencies are $K\subseteq\{1,2,5\}$ and
$\chi_2\ne\chi_1$.
* $\chi_2^k=\chi_0$ with $k\in\{1,2,5\}$ means $\chi_2$ real ($k\le2$) or of order 5.
* $\chi_1\chi_2^k=\chi_0$ means $\chi_2^k=\chi_1$: impossible for $k=1$, order 4 for
  $k=2$, order 10 for $k=5$ ($\chi_2^{10}=\chi_0$, and $\chi_2^5=\chi_1$ is real).
* Cases 2 and 3 cannot co-occur. Case 2 gives $\chi_2^4=\chi_1^2=\chi_0$, and case 3
  gives $\chi_2^{10}=\chi_0$. So $\chi_2^{\gcd(4,10)}=\chi_2^2=\chi_0$, which contradicts
  $\chi_2^2=\chi_1\ne\chi_0$.

*Heights.* All are $\le5l\le9l$.

*Conclusion.* Each inequality is contradicted, with $\lambda_1\le b$, $\lambda_2\le h$ and
$F$ decreasing, once the enclosed left side minus right side is $>0$. Hence
$\lambda_2>h$.

**Rows actually used.**
* **The degree-2 row** (`core/code/new_positivity.lambda2_row`, applied in
  `endgame.reduced_spec` to every rr cell $\subseteq[.700,.7025]$). $P=(7/8+\cos\vartheta)^2/(81/64)$,
  so $c_1=\frac{112}{81}$ and $c_2=\frac{32}{81}$; $\gamma=1.09$; no Lemma C. Result
  $\lambda_2>.762$. Normalized margins: generic $3.6257\times10^{-4}$, order 4 .08207
  (with $\sup R\le.009755$), real ($\gamma=.82$) .03367.
* **Degree-5 rows** (`frontier/polynomial5_rows.py`,
  `inside_polynomial5_rows_.700_.755.json`, 22 cells of width .0025 on $[.700,.755]$).
  * $P=1+c_1T_1+c_2T_2+c_5T_5$ with $(c_1,c_2,c_5)=(1.41866466,.43287503,.01421037)/1.000001$
    and $\Sigma=1.86575$.
  * Nonnegativity: exact sampling at $x=j/2000$ plus a second-derivative bound
    ($|P''|\le4c_2+440c_5$) gives $P\ge6.9\times10^{-7}$. Independently, the critical points
    of $P$ on $[-1,1]$ are $-.94765$ and $-.83924$, with $\min P=9.27\times10^{-7}$ at
    $-.83924$ (my check).
  * Example $[.700,.7025]$: $h=.7793$, $\gamma=548121/500000$. Margins: generic
    $1.0198\times10^{-4}$, order 4 .08036, orders 5/10 .12800, real .02891.
  * Last cell $[.7525,.755]$: $h=.7579$.
  * I recomputed the four margins of rows 1, 2, 3 and 22 by mpmath quadrature. The generic
    margins agree to $\ge10$ digits. The alias supremum sampled on $\Delta\in[0,15]$ is
    $\approx-.0025<0$; the code's bound is dominated by the $|\Delta|\ge30$ tail estimate.
* **Degree-2 families.** `inside_real_rows_*` (16 rows, no saving) and
  `inside_conductor_rows_*` (21 rows, with Lemma C) are regenerated by `real_rows()` but
  **not used** in the tree. All 300 `real_location` nodes carry `kind='degree5-conductor'`
  (my scan).

**Enclosure method** (`certify_row5`, `certify_row`, `new_positivity.check`).
1. $R(\Delta)$ is sampled at the four $(\lambda_1,\lambda_2)$ corners on $\Delta=j/200$,
   $0\le\Delta\le30$, by the directed-rounding interval library `vector_intervals`
   (Taylor range reduction, `nextafter` outward).
2. Height interpolation error:
   $\bigl(c_2m_2(a)+(c_1+c_2)m_2(0)\bigr)/(8\cdot200^2)$, where
   $m_2(d)=\int t^2fe^{dt}$.
3. Parameter error: $(c_2(b-a)^2+c_1(h-a)^2)m_2(0)/8$. $R$ is separable in
   $(\lambda_1,\lambda_2)$, so corner maxima plus coordinate errors bound it.
4. The tail $|\Delta|\ge30$ uses the closed form (3.18):
   $|F(\sigma+iY)|\le\frac{f_0|\sigma|}{Y^2}+\frac{8\gamma^3}{3Y^3}+\frac{4\gamma^2(1+e^{-2\gamma\sigma})}{Y^4}+\frac{4(1+e^{-2\gamma\sigma})}{Y^6}+\frac{8\gamma e^{-2\gamma\sigma}}{Y^5}$.

All four steps are correct as bounds.

### B.8 Complex-first rows [R]: $\lambda_2$ rows (25) and $\lambda'$ rows (69)

Let $P_t(e^{i\vartheta})=\frac{(t+\cos\vartheta)^2}{t^2+1/2}=1+c_1\cos\vartheta+c_2\cos2\vartheta$,
with $c_1=\frac{2t}{t^2+1/2}$, $c_2=\frac{1/2}{t^2+1/2}$ and $c_1/c_2=4t$.

**Proposition B.8.1 ($\lambda_2$ rows).** Let $\chi_1$ be nonreal, $\lambda_1\in[a,b]$,
$a\le b\le h$, and let $\chi_2\notin\{\chi_1,\bar\chi_1\}$ carry $\rho_2$. Suppose
$\lambda_2\le h$. Then:
* **(i) $\chi_2$ nonreal.** Assume
  $\sup_{\lambda\in[a,h],y\in\mathbb R}\operatorname{Re}\{F(-a+iy)-4tF(\lambda-a+iy)\}\le f(0)/6$
  (4.3). Then
  $c_1\{F(\lambda_1-a)+F(\lambda_2-a)\}\le F(-a)+\frac{(1+c_1+c_2)^2-1}6f(0)+o(1)$.
* **(ii) $\chi_2$ real**, with parameter $t'$ ($c_1',c_2'$). Assume (4.3) with $t'$ and
  $\lambda\in[a,b]$. Then
  $c_1'F(\lambda_1-a)+F(\lambda_2-a)\le F(-a)+(\frac18+\frac{c_1'+c_2'}3)f(0)+o(1)$.

*Proof of (i).*
1. **Expansion.** $P_t(\chi_1(n)n^{-i\gamma_1})P_t(\chi_2(n)n^{-i\gamma_2})=\sum_{w\in\{-2..2\}^2}a_{|w_1|}a_{|w_2|}\chi^w(n)n^{-iw\cdot\gamma}$,
   with $a_0=1$, $a_1=c_1/2$ and $a_2=c_2/2$.
2. **Conductor.** Total mass is $(1+c_1+c_2)^2$; the nonprincipal mass is charged
   $\varphi/2\le1/6$.
3. **Retained zeros.** $w=(\pm1,0)$ retains $\rho_1$ (resp. $\bar\rho_1$), and
   $w=(0,\pm1)$ retains $\rho_2$ (resp. $\bar\rho_2$).
4. **Principal indices.** A nonzero principal index $w$:
   * cannot lie on an axis ($\chi_1,\chi_2$ nonreal);
   * cannot have $|w_1|,|w_2|\le1$ (this would force $\chi_2\in\{\chi_1,\bar\chi_1\}$);
   * so some $|w_i|=2$. Take $i=1$ on ties.
5. **Matching.** Map $w\mapsto T(w)=w-\operatorname{sgn}(w_i)e_i$. Then:
   * $\chi^{T(w)}=\chi_i^{-\operatorname{sgn}w_i}$ is nonprincipal and not a baseline
     index;
   * its coefficient is $4t\cdot a_w$;
   * its test point is at height $w\cdot\gamma-\operatorname{sgn}(w_i)\gamma_i$, where the
     selected zero of $\chi_i^{-\operatorname{sgn}w_i}$ sits at normalized offset
     $w\cdot\mu$.
6. **Injectivity.** The only possible collision is between $(2s,\tau)$ and $(s,2\tau)$;
   if both were principal, then $\chi_1^s=\chi_2^\tau$, which is excluded.
7. **Alias cost.** Each principal $w$ changes the right side by
   $a_w[\operatorname{Re}F(-a+iy)-f(0)/6-4t\operatorname{Re}F(\lambda_i-a+iy)]\le0$, using
   (4.3) and $\lambda_i\in[a,h]$ (retain the zero at $T(w)$).

*(ii).* Same argument. The only principal indices are $(\pm2,\pm1)$
($\chi_2=\chi_1^{\mp2}$), matched to $(\pm1,\pm1)$ with target $\rho_1$. So (4.3) is needed
on $[a,b]$.

**Proposition B.8.2 ($\lambda'$ rows).** Let $\chi_1$ be nonreal of order $\ge5$ with zeros
$\rho_1,\rho'$ (one zero counted twice if multiple). Put $x=\lambda_1-a$, $y=\lambda'-a$
and $\Delta=\ell(\gamma_1-\gamma')$. Use
$P_t(\chi_1n^{-i\gamma_1})P_t(\chi_1n^{-i\gamma'})\ge0$. Then
$$c_1[F(x)+F(y)]\le F(-a)+\frac{M}6f(0)+R(\Delta)+o(1),$$
with
* $M=(1+c_1+c_2)^2-1-\frac{c_1^2+c_2^2}2$;
* $R=p_1\operatorname{Re}F(-a+i\Delta)+p_2\operatorname{Re}F(-a+2i\Delta)-q_1\operatorname{Re}[F(x+i\Delta)+F(y+i\Delta)]-q_2\operatorname{Re}[F(x+2i\Delta)+F(y+2i\Delta)]$;
* $p_1=\frac{c_1^2}2$, $p_2=\frac{c_2^2}2$, $q_1=c_1(1+\frac{c_2}2)$ and $q_2=\frac{c_1c_2}2$.

*Proof.* Order $\ge5$ and $|k+l|\le4$ mean that the principal indices are exactly
$k+l=0$: $(\pm1,\mp1)$ gives mass $p_1$ and $(\pm2,\mp2)$ gives $p_2$. In every term with
$k+l=\pm1$, both $\rho_1$ and $\rho'$ are retained (X Lemma 3.4, $A_2$ with multiplicity).
* $(1,0),(0,1)$ and conjugates give $-c_1[F(x)+F(y)]-c_1\operatorname{Re}[F(x+i\Delta)+F(y+i\Delta)]$.
* $(2,-1),(-1,2)$ and conjugates give
  $-\frac{c_1c_2}2\operatorname{Re}[F(x+i\Delta)+F(y+i\Delta)+F(x+2i\Delta)+F(y+2i\Delta)]$. ∎

*Orders 3–4* are covered by X Table 3 row .86 ($\lambda'>1.35$). The code asserts
$b\le.86$ and $h<1.35$.

**Rows** (`core/results/polynomial_table.json`, 94 rows = 25 `second` + 69 `additional`,
cells in $[.62,.86]$; regenerated by `poly_rows.verify_polynomial_table`). Minimum
normalized margin $8.27\times10^{-4}$. I recomputed rows 0 and 24 of each type by quadrature:
* $\lambda_2$ generic margins agree to 10 digits; sampled alias margins .168 are at least
  the enclosed .1637;
* $\lambda'$ margins with sampled $R$: .00259 and .00265, at least the enclosed .00180 and
  .00166.

`inside_complex_rows.propose_complex_row` re-evaluates the same inequalities on the actual
cell (11 `complex_location` nodes; `complex_second_row` regenerates them).

### B.9 Real positivity exclusion [R] (197 nodes)

**Proposition B.9.** Let the type be rr, $\lambda_1\in[a,b]$, and let the reserved family be
one real character $\chi_2$ with height-one representative $\nu_2\le hi_2$. If
$\bigl(F(b-a)+F(hi_2-a)-F(-a)\bigr)/f(0)-\frac38>0$, the case is empty.

*Proof.* Lemma P applies to $(1+\chi_1(n))(1+\operatorname{Re}\chi_2(n)n^{-i\gamma_2})\ge0$.
Its three nonprincipal characters $\chi_1,\chi_2,\chi_1\chi_2$ are real ($\varphi=\frac14$).
Retain $\rho_1$ and $\chi_2$'s representative, which lies in $R(l)$ since $|\gamma_2|\le1$.
This gives $F(\lambda_1-a)+F(\nu_2-a)\le F(-a)+\frac38f(0)+o(1)$. ∎

Code: `extension_enclosures.positivity_proof` asserts type rr, $n_2=1$ and margin
$>2\times10^{-5}$. The smallest recorded margin is $7.81\times10^{-5}$ (near-refinements
§5).

### B.10 Application of rows; exclusion counts

**Lemma B.10 (updates).** Suppose a row proves $\lambda_2>h$ on $[a',b']\supseteq[a,b]$.
Then in the specification:
* $\mathrm{source\_l2}$ and $r$ may be raised to $\max(\cdot,h)$;
* a reserved $lo_2$ may be raised to $r$;
* a specification with a reserved family and $hi_2\le h$ is empty.

Suppose a row proves $\lambda'>h$. Then $lp$ and gap.lo may be raised to $h$, and a finite
gap with $\mathrm{gap.hi}\le h$ is empty.

*Proof.* Every non-first family has all zeros in $R(l)$ at $\lambda\ge\lambda_2>h$. In
particular its height-one and $T^*$ representatives, and the reserved $\nu_2$, are $>h$. ∎

Code: `endgame.reduced_spec` (the .762 row and the polynomial table),
`inside_repair.real_update` and `inside_complex_rows.complex_update`. All assert
$a'\le a\le b\le b'$.

**Node counts** (my scan of `frontier/collective_full_4.30/roots.jsonl.gz` and
`near/results/outside_regime_4.30.jsonl.gz`; equal to `mechanisms.json`):

| node | inside | outside |
|---|---|---|
| `positivity` | 197 | 0 |
| `second_exclusion` (`reduced_spec` returns `None`: the .762 row or polynomial rows) | 352 | 70 |
| `real_location`, excluded | 75 | — |
| `real_location`, restriction | 225 | — |
| `complex_location`, restriction | 11 | — |
| outside roots / specs | — | 1685 (= 1570 complex + 115 rc) |

Every one of these nodes is re-checked during replay (`graded_verify` →
`collective_cover.verify_inner`, `inside_repair.verify_leaf`, `verify_progress.verify_tree`
and `outside_regime`, with `regenerate(row)==row` or `reduced_spec` recomputation).

### B.11 $\lambda_3$ rules (`triple_inputs.third_bound`, `sieve_near/third_refine.rr_third`)

**Proposition B.11.** Let a cell $[a,b]$ of type $\tau$ be given. Let $h$ be the upper end
of a reserved height-one family, if any, and $h=\infty$ otherwise. Then $\lambda_2\le h$,
because $\lambda_2\le\nu_2\le h$ and the representative lies in $R(l)$. Moreover
$\lambda_3>r_3$, where $r_3$ is the largest of the applicable values:

1. $r_3=.857$ always [H Lemma 10.3, p. 67: $\lambda_3\ge\frac67-\varepsilon$; $.857<\frac67$].
2. $\tau=$ rr and $[a,b]\subseteq[.44,.60],[.60,.70],[.70,.80]$: $r_3=1.176, 1.055, .952$
   [X Table 10, p. 55; strict].
3. $\tau\ne$ rr and $b\le\beta\in\{.52,.54,.56,.58,.60,.62\}$: $r_3=1.320,1.243,1.160,1.079,1.001,.933$
   (smallest admissible $\beta$) [X Table 8, "alle Fälle", p. 55]. It never fires for rc,
   whose cells start at .628.
4. $\tau=$ complex, $.44\le a\le b\le.85$, $\gamma=\frac54$: $r_3=t$ for any $t$ with
   $$\Phi(t):=\frac{F(t-b)+F(\min(t,h)-a)-F(-b)+F(0)}{f(0)}-\frac76>10^{-5}.$$
5. $\tau=$ rr, $.44\le a\le b\le.80$, $t\in[.952,1.176]$, $\gamma=\frac{26}{25}$: $r_3=t$
   whenever $[a,\min(t,h)]$ is covered by cells $[c,c']$ with
   $$\Psi_t(c,c'):=\frac{F(-c')-F(t-c')-F(0)-F(b-c)}{f(0)}+\frac98<-10^{-5}.$$

*Printed inputs for 4 and 5.*
* **X (4.28) (p. 56), $\chi_1$ complex.**
  $0\le F(-\lambda_1)-F(\lambda_3-\lambda_1)-F(\lambda_2-\lambda_1)-F(0)+\frac76f(0)+\varepsilon$.
  * Fall 1 (no principal character in $\Sigma_3$) comes from H (10.2)–(10.6) via X Lemmas
    3.1 and 3.4.
  * Fall 2 needs $\lambda_1\in[.44,.85]$ and (4.29):
    $\sup_t\operatorname{Re}\{F(-\lambda_1+it)-2F(it)\}\le\frac16f(0)$ (X p. 57; X
    computed $<0.18<0.54$ with $\gamma=1.25$).
  * The repository regenerates (4.29) rigorously for $\lambda\in[.44,.85]$
    (`alias_check.py`): $\sup\le.003343$ against $f(0)/6=.54253$.
* **X (4.31) (p. 58), $\chi_1,\rho_1$ real, anchor $\beta_2$.**
  $0\le F(-\lambda_2)-F(\lambda_3-\lambda_2)-F(0)-F(\lambda_1-\lambda_2)+\frac98f(0)+\varepsilon$.
  * It assumes $\lambda_2\le1.294$, so that $\lambda'\ge\lambda_2$ by H Lemma 8.4.
  * Fall 2 needs (4.34):
    $\sup_t\operatorname{Re}\{F(-\lambda_2+it)-F(\lambda_1-\lambda_2+it)-F(it)\}-\frac5{48}f(0)\le0$
    on $\lambda_1\in[.44,.80]$, $\lambda_2\in[.44,1.176]$ with $\gamma=1.04$.
  * X states (p. 59) "$<0.10<0.13=\frac5{48}f(0)$". Hence "(4.31) always holds in the case
    $\chi_1,\rho_1$ real (for $\gamma=1.04$)", within that box.

*Proof of 4.* Suppose $\lambda_3\le t$. Then $\lambda_2\le\min(t,h)$.
1. $\lambda\mapsto F(-\lambda)-F(t-\lambda)=\int f(u)e^{\lambda u}(1-e^{-tu})du$ is
   nondecreasing. X uses the same fact on p. 57. So
   $F(-\lambda_1)-F(\lambda_3-\lambda_1)\le F(-\lambda_1)-F(t-\lambda_1)\le F(-b)-F(t-b)$.
2. $F(\lambda_2-\lambda_1)\ge F(\min(t,h)-a)$.
3. The right side of (4.28) is then $\le-10^{-5}f(0)+\varepsilon<0$. Contradiction.

*Proof of 5.* Suppose $\lambda_3\le t\le1.176$. Then $\lambda_2\in[a,\min(t,h)]\subseteq[.44,1.176]$,
$\lambda_1\in[.44,.80]$, and $\lambda_2\le1.294$, so (4.31) applies. Take the cover cell
$[c,c']\ni\lambda_2$.
1. By the same monotonicity, $F(-\lambda_2)-F(\lambda_3-\lambda_2)\le F(-c')-F(t-c')$.
2. $F(\lambda_1-\lambda_2)\ge F(b-c)$.
3. So the right side of (4.31) is $<-10^{-5}f(0)+\varepsilon$. Contradiction. ∎

*Checks.*
* `rr_third` on X's intervals returns $1.176$ (the cap), $1.0558$ and $.9524$, which
  reproduces Table 10.
* On $[.7025,.705]$ it returns **1.0502 without a cap**. With cap $h=.76,.80,.85,.9$ it
  returns 1.1039, 1.0974, 1.0888, 1.0798. PROOF.md's example "$\lambda_3>1.0884$ on
  $[.7025,.705]$" therefore needs a reserved cap $h\lesssim.85$ (D.3).
* My quadrature check of $\max_{\lambda_2}\Psi$ gives $-7.9\times10^{-5}$ at $t=1.0502$ and
  $+9.3\times10^{-4}$ at $t=1.052$. The binding point is $\lambda_2=t$.
* Sampling (4.34) ($\gamma=1.04$, $\lambda_1,\lambda_2$ on a .01 grid, $t\in[0,60]$ step
  .01) gives $\sup\approx.0021$, against $\frac5{48}f(0)=.1352$
  (`scratchpad/deep/x434.py`). This is non-rigorous but consistent with X.
* Examples of `third_bound`: complex $[.44,.45]\to1.32$ (Table 8), $[.62,.63]\to.9008$
  ((4.28)), $[.70,.7025]\to.8866$, $[.80,.8025]\to.8623$; rr $[.70,.7025]\to.952$;
  rc $\to.857$.

### B.12 Count rule (4.33 §3)

**Proposition B.12.** Let $\lambda_3>r_3$, and let representatives be height-one or $T^*$
(A.6.3(2)).
1. **Unreserved.** At most two non-first characters have a representative with parameter
   $\le r_3$.
2. **Reserved.** Let $F_r$ be a $\nu$-minimal non-first family. Then every non-first
   character outside $F_r$ has representative parameter $\ge\lambda_3>r_3$.

*Proof.*
1. By (3.11)–(3.12), every zero in $R(l)$ of a character outside the first family and the
   global second family $G$ has $\lambda\ge\lambda_3$. A representative with
   $\lambda\le\lambda_0$ lies in $R(l)$. $G$ has at most 2 characters.
2. If $F_r=G$, argue as in 1. If $F_r\ne G$, then $F_r$'s zeros in $R(l)$ have
   $\lambda\ge\lambda_3$, so $\nu(F_r)\ge\lambda_3$. For every other non-first $F$,
   $\nu(F)\ge\nu(F_r)$. $T^*$-representatives are $\ge$ height-one representatives. ∎

**LP form.**
* Unreserved: $\sum_{hi_i\le r_3}x_i\le2$. A character in such a bin has representative
  $\le r_3<\lambda_3$.
* Reserved: bins with $hi_i\le r_3$ are deleted.
* Code: `input_with_third` (`count_cost=S` on rows with right $\le r_3$, budget $2S$),
  `refine_third`. Outside leaves get it through `make_endgame` in
  `first_outside_blocks.first_out_input`. First-family (hidden) columns carry no count
  cost, which is correct since they are not "non-first".
* In the reservation split (§8) the reserved child uses cap $h$. This is valid since
  $\lambda_2\le\nu<h$, and the proof above needs only minimality.

### B.13 Inside/outside split

For type rr, $\mu_1=0$, so $\rho_1\in R_B$ (since $\lambda_1<1.5<C_B$). For rc and complex,
every configuration has $|\mu_1|\le C_B$ (inside) or $|\mu_1|>C_B$ (outside).
* **Inside.** $|\gamma_1|\le C_B/\ell<\frac12\le T^*$, and $\lambda_1$ is the global
  minimum. So $\rho_1$ ($\bar\rho_1$) is $\chi_1$'s ($\bar\chi_1$'s) height-one and
  $T^*$-representative.
* **Outside.** $\rho_1\notin R_P$, since $C_P<C_B$. Every other first-family zero in $R_P$
  has $\lambda\ge\lambda'\ge lp$ (for rc also $\bar\rho_1\notin R_P$). These zeros are the
  hidden columns, at most one per character.
* The 1685 outside roots are exactly the 1570 complex and 115 rc specifications.
* The outside replay (`outside_regime.py`) uses only subcase `outside_buffer`. The
  `height_one` subcase of `first_out_input`, which subtracts $n\,w(b)$, is not used.

---

## Part C. Literature inputs: printed statement, hypotheses, page, our use

| # | Input | Printed statement (translated where German) | Hypotheses / scope | Page | Our use: match? |
|---|---|---|---|---|---|
| 1 | X Lemma 5.1 (5.19) | see A.1 | $c_1,c_2,\varepsilon>0$, $M\in\mathbb N$, $\alpha_i\ge0$ with $\sum=1$; $w_0$ continuous, $C^1$ off finitely many points, $1\ll w_0\ll1$, $w_0'\ll1$; one chosen zero per character in $\sigma\ge1-\lambda_0/\ell$, $\lvert t\rvert\le1$; $q\ge q_0$(all parameters) | X p. 66 (defs pp. 25–26; proof pp. 67–72) | Yes: Theorem A. $M=10$, $\varepsilon=10^{-4}$, profile X (6.20) p. 80 |
| 2 | X (6.20)–(6.21) | $w_0(t)=e^{-\theta t/2}\min\{t-u_0+\varepsilon_0,u_{10}-u_0+\varepsilon_0\}^{1/4}$, $\varepsilon_0=10^{-7}$ | – | X p. 80 | Both profiles have exactly this shape |
| 3 | X §3.2.2 | $N(\lambda)$ counts characters with a zero in $\sigma\ge1-\lambda/\ell$, $\lvert t\rvert\le1$; one zero $\rho(\chi)$ chosen per character | $0<\lambda\le\lambda_0=\frac13\log\log\ell$ | X pp. 25–26 | One zero per character; $\chi_0$ excluded |
| 4 | X Lemma 3.3 = H Lemma 6.1 | exists $l\le\ell/10$ with no zeros in $R(10l)\setminus R(l)$ | $q\ge q_0$; $l$ is existential | X p. 19; H p. 26 | One fixed $l(q)$ for all tables (D.6) |
| 5 | X (3.11)–(3.12), $\rho'$ Fall 1–3 | family-by-family selection; (3.12) | – | X pp. 21–22; H pp. 26, 28 | Definitions of $\lambda_1,\lambda_2,\lambda_3,\lambda'$ |
| 6 | X Lemma 3.1 = H Lemma 5.3 | principal prime sum $=\ell F((s-1)\ell)+O(\ell/\log\ell)$ | $\lvert\sigma-1\rvert\le(\log\ell)^{1/2}/\ell$, $\lvert t\rvert\le\ell$, Condition 1 | X p. 18 | Lemma P, principal terms |
| 7 | X Lemma 3.4 (from H Lemma 5.2) | see B.5 | $s\in R(9l)$, $\#A_1,\#A_2\le10$ (any fixed $N$, p. 21), Conditions 1–2 | X pp. 19–21 | Lemma P, with $A_1=\emptyset$ |
| 8 | $\varphi(\chi)$ | $\frac14$ if $q$ cube-free or $\operatorname{ord}\chi\le\ell$; else $\frac13$ | $\chi\ne\chi_0$ | X p. 17; H Lemma 2.5 p. 10 | $\frac14$ for real and bounded-order characters, $\frac13$ otherwise |
| 9 | H Lemmas 2.3–2.4 and §16(4) | character-sum bounds with $v$ and with order; "$\psi\le\frac{97}{216}$" | primitive $\chi$ | H pp. 8–9, 93–94 | Lemma C [R/PD], D.1 |
| 10 | X Lemma 4.5 / Table 11 | $\lambda_1>.440/.493/.478/.498/.628$ for orders $\ge6/5/4/3/2$ | $\chi_1$ or $\rho_1$ complex; $q\ge q_0$ | X pp. 60–61 | Type bounds .44 and .628 |
| 11 | H Table 4, Lemma 8.2, Lemma 8.4 | $\lambda_1\le t\Rightarrow\lambda_0\ge c$; $\lambda_0\ge2.427$ for real $\rho_0$; $\lambda_0\ge\max(\frac32\log\lambda_1^{-1},1.294)$ | rr | H pp. 38, 43–44 (explained X pp. 23–24) | rr $lp$; exactness recomputed (B.2) |
| 12 | H Table 7, Lemma 8.8 | $\lambda_1\le t\Rightarrow\lambda_2\ge c$; $\lambda_2\ge.745$ | rr; all $\chi_2$ (H p. 47); not $\lambda_1\le.10$ (X p. 24) | H pp. 47–48 | rr source\_l2; exactness recomputed |
| 13 | H Table 10 + Lemma 9.4 | $\lambda_1\le.70\Rightarrow\lambda_2\ge.704$; $\lambda_2\ge.702$ always | $\chi_1$ or $\rho_1$ complex | H pp. 56–57 | complex $[.68,.72)$ |
| 14 | H Lemma 10.3 | $\lambda_3\ge\frac67-\varepsilon$ | all | H p. 67 | $r_3\ge.857$ |
| 15 | X Table 2′ | $\lambda_1\le t\Rightarrow\lambda'>c$ | $\chi_1$ or $\rho_1$ complex (uses $\lambda_1\ge.44$) | X p. 62 | complex $lp$ |
| 16 | X Table 3 | same form | $\chi_1$ or $\rho_1$ complex, ord $\in\{2,3,4\}$ | X p. 45 | rc $lp$; order 3–4 in B.8.2 |
| 17 | X Tables 6, 7 | $\lambda_1\le t\Rightarrow\lambda_2>c$ | T6: rc (Fall 7); T7: $\chi_1$ or $\rho_1$ complex | X p. 53 | rc and complex source\_l2 |
| 18 | X Table 8 | $\lambda_1\le t\Rightarrow\lambda_3>c$ ("alle Fälle") | $\chi_1$ or $\rho_1$ complex | X p. 55 | B.11(3) |
| 19 | X Lemma 4.4 / Table 10 | $\lambda_1\in I\Rightarrow\lambda_3>c$ | $\chi_1,\rho_1$ real | X p. 55 | B.11(2) |
| 20 | X (4.28), (4.29) | B.11 | $\chi_1$ complex; Fall 2 needs $\lambda_1\in[.44,.85]$ and (4.29) | X pp. 56–57 | B.11(4); (4.29) regenerated |
| 21 | X (4.31), (4.34) | B.11 | $\chi_1,\rho_1$ real; $\lambda_2\le1.294$; box $[.44,.80]\times[.44,1.176]$, $\gamma=1.04$ | X pp. 58–59 | B.11(5); (4.34) not regenerated (D.2) |
| 22 | $\varepsilon$-convention | H p. 38 (Tables 2–3); X pp. 43–44, fn. 2 p. 45, pp. 57, 59 | – | – | B.2 |
| 23 | Jutila (1977) Thm 1 / H (1.4) | log-free density $\sum_\chi N(\sigma,T,\chi)\ll(qT)^{c(1-\sigma)}$ | $4/5\le\sigma\le1$, $T\ge1$ | quoted in H Lemma 6.1 proof p. 26; H (1.4) p. 5 | $K_0=O(1)$ (A.6.1). Jutila's scan was not text-extractable here, so it was read via H's quotation |
| 24 | X (3.17)–(3.18), Lemma 3.6 | parabolic test $f_\gamma$ and its transform; Condition 2 | – | X pp. 22–23 | all rows |

---

## Part D. HOLES AND CONCERNS

Overall verdict:
* **No blocking error was found** in §§4–5. Every rule in scope is a valid implication
  from its stated premises.
* The code implements each rule as stated in every place checked:
  * all 58 parent rows and all transcribed table values;
  * far constants, budget and tail;
  * the $\lambda_3$ rules and the count rule;
  * the update and exclusion rules, and the degree-5, degree-2 and complex polynomial rows.
* One load-bearing repository deduction still rests on an unproved remark in the
  literature (D.1).
* The rest are documentation, citation and reproducibility gaps.

**D.1 [MAJOR, load-bearing; needs a written proof] The $1/108$ conductor saving (Lemma C).**
* **Where it is used.** Every one of the 300 `real_location` nodes of the 4.30/3.99 inside
  tree uses a degree-5 row whose generic branch takes the conductor coefficient
  $\frac18+\frac\Sigma3-\frac1{108}$. That is 75 exclusions and 225 restrictions, e.g.
  $\lambda_2>.7793$ on $[.700,.7025]$.
* **Why it is load-bearing.** The generic margins are only $4\times10^{-5}$–$1\times10^{-4}$,
  while the saving is $1/108\approx9.3\times10^{-3}$. Without it these rows fall back to
  roughly the degree-2 value .7624 on $[.700,.7025]$. The 75 exclusions and the raised
  $\lambda_2$ bounds of the 225 restrictions would then be unavailable, and the affected
  leaves would need new certificates.
* The unused `inside_conductor_rows_*` family also depends on it.
* **What the literature provides.** The source is Heath-Brown's §16 item 4 (pp. 93–94),
  a "small improvement" remark. It says the refined bounds are "apparent from the work of
  §2 … Lemma 2.3", without proof.
* **What the repository adds** (`arguments/real-conductor-rows.md`):
  1. weights $c_k\ne1$;
  2. the use of a $q$-dependent growth coefficient inside X Lemma 3.2/3.4 (H Lemmas 3.1,
     5.2), whose printed statements have $\varphi\in\{\frac14,\frac13\}$ fixed.
* **My assessment.** I reconstructed the argument in B.6: the Burgess input, the
  rad-inequality, the finite-net uniformization and the maximization. I believe it is
  correct.
* **Fix.** The paper must contain Lemma C with a full proof:
  1. the refined bounds $L(s,\chi)\ll q_1^{\frac14(1-\sigma)(1+1/k)+\varepsilon}(1+|t|)$
     (real $\chi$) and $\ll(v^3q)^{\frac14(1-\sigma)(1+1/k)+\varepsilon}(1+|t|)$, from H
     Lemmas 2.3–2.4 and H pp. 9–10;
  2. the version of H Lemma 3.1 / X Lemma 3.2 with $q$-dependent $\varphi$ (finite net of
     $\varphi$-values, per-class thresholds);
  3. the maximization over $\theta$.
* Status: currently [R] and reviewed only by AI agents.

**D.2 [MINOR–MODERATE] X (4.34) is not regenerated, and (4.31) is used pointwise from a
proof.**
* The refined rr $\lambda_3$ rule (B.11(5)) is applied to every rr leaf with
  $\lambda_1\in[.44,.80]$ (`graded_leaves.inside_input` → `refine_third`), whenever it
  beats Table 10. It feeds the count row and the deletion of reserved-case bins.
* It rests on (4.31) and on X's numerical claim (p. 59) that (4.34) holds on the box with
  $\gamma=1.04$ ("$<0.10<0.13$").
* The repository regenerates the analogous (4.29) rigorously, but **not (4.34)**. The
  audit note lists (4.31) only with "margin $10^{-5}f(0)$".
* My sampled check gives $\sup\approx.0021\ll.1352$, so it is almost certainly true.
* Also, (4.31) is displayed inside the proof of Lemma 4.4, not in its statement, so the
  per-cell use is [PD]. That is legitimate: X says "(4.31) gilt immer … (für
  $\gamma=1.04$)" on that box.
* **Fix.** Add a rigorous enclosure of (4.34) in the style of `alias_check.py`. Grid it
  over $(\lambda_1,\lambda_2,t)$ with second-derivative slack in all three variables and a
  closed-form tail; the margin is huge.

**D.3 [MINOR, documentation] Wrong example in PROOF.md §5.** "$\lambda_3>1.0884$ on
$[.7025,.705]$".
* The unconditional per-cell value is **1.0502**.
* 1.0884 needs a reserved-family cap $h\le.85$ (`rr_third('.7025','.705','.85')` gives
  1.0888).
* The code is correct: it uses the cap only when a family is reserved.
* **Fix.** State the cap, or quote 1.0502.

**D.4 [MINOR] Incomplete statement of X Lemma 5.1 in PROOF.md §4.**
* Missing hypotheses: $w_0$ bounded **above**; $w_0'$ bounded off finitely many points;
  eligibility $\lambda\le\lambda_0=\frac13\log\log\ell$; $q_0$ depends on
  $(c_1,c_2,M,\alpha,w_0,\varepsilon)$; the explicit $\varepsilon=100\eta$.
* **Notation clash.** $M$ denotes both X's number of sieve pieces (10) and the separation
  distance of §4/§6.
* The Lean statement is complete. **Fix.** Use Theorem A as stated in A.2, and rename the
  separation constant.

**D.5 [MINOR, interpretive] Uniformity of $q_0$ in the choice of zeros (X Lemma 5.1).**
* The print fixes "a" choice per character (§3.2.2), and says $q_0$ depends on "all
  chosen parameters". The Lean version quantifies $\forall$ choices after $\exists q_0$.
  This is proof-derived; H §11's proof is manifestly uniform.
* **Weakest-reading fix.** The paper only needs finitely many *intrinsic* choice rules:
  * first family: $\rho_1$ / $\bar\rho_1$ (inside), or the rightmost $R_P$ zero other than
    $\rho_1,\bar\rho_1$ (outside);
  * the $\nu$-minimal non-first family (when reserved): height-one representatives;
  * all other characters: $T^*(q)$-representatives, with $T^*(q)$ defined by a fixed rule,
    e.g. the least admissible $T^*$ on a grid of step $M/\ell$.

  Each rule is one choice function $q\mapsto$ zeros, so even the weakest reading applies.
  Take the maximum of the finitely many $q_0$. Say this explicitly.

**D.6 [MINOR, interpretive] One height function $l(q)$ for all tables.**
* H's $L$ (Lemma 6.1) and X's $l$ (Lemma 3.3) are existential.
* H's tables are proved for H's rectangle and X's for X's. They coincide only if the
  **same** admissible $l(q)$ is used.
* All proofs use only the annulus property $R(10l)\setminus R(l)$ zero-free. So every
  table holds for any admissible choice, with thresholds depending on fixed data only.
* The repository's `notes/source-dictionary.md` records this as a "joint witness" premise.
  PROOF.md §1 does not mention it.
* **Fix.** Fix one $l(q)$ (e.g. the least admissible integer) in the paper and add one
  sentence: "all cited zero-location results are proved for an arbitrary integer $l$ with
  the annulus property; we apply them with this fixed $l(q)$".

**D.7 [MINOR, citation] $\varepsilon$-convention sources.**
* PROOF.md cites "X p. 55 … 'etwas Negatives'". The phrase is on **X p. 57** (Table 9) and
  **p. 59** (Table 10: "$\lambda_3>\lambda_{32}=1.176$"). p. 55 contains only the tables.
* The cleanest statements of the convention are X p. 43 ("für $q\ge q_0(f,k,\varepsilon)$
  bewiesen … $\lambda_0>2.06$"), X p. 44 (table semantics "$\lambda_1\le\lambda_{12}\Rightarrow\lambda_0>c_2$")
  and **X p. 45 fn. 2** (H's "$\ge c$" are really "$>c$", with room $\varepsilon$).
* **Fix.** Cite these pages, and add the recomputation results of B.2 for H Tables 4/7.

**D.8 [MINOR, reproducibility] The audit scripts are not in the repository.**
* `notes/source-table-audit-2026-09-29.md` cites scripts in "the session scratchpad
  (`table_audit/`)" that are not committed. I could not find them anywhere.
* I re-derived all of H Table 4 and five rows of H Table 7 (B.2). The results agree with
  the audit (e.g. 1.43904, 2.01015, 1.00036).
* The X-table reproductions claimed by the audit (sup bounds $C$, Table 3 reading) remain
  unreproducible from the repository.
* **Fix.** Commit the scripts, or cite the printed values as inputs without the
  reproduction claim.

**D.9 [MINOR, documentation] Node counts and row inventory in PROOF.md §5.**
* "Real conductor rows: 75 nodes" counts only the **excluded** `real_location` nodes.
  There are 225 more `real_location` **restrictions** and 11 `complex_location`
  restrictions. All 300 real nodes use the **degree-5** rows.
* The degree-2 families `inside_real_rows_*` (16 rows) and `inside_conductor_rows_*`
  (21 rows, with $1/108$) are regenerated by `inside_repair.real_rows()` but unused.
* The 69 **$\lambda'$ rows** (`additional`) of `polynomial_table.json` are location inputs
  used by `reduced_spec`, both as restrictions and inside the 352+70 `second_exclusion`
  nodes. §5 lists only the 25 $\lambda_2$ rows.
* "A degree-2 row" means the .762 row applied in `reduced_spec`.
* **Fix.** Update §5's inventory: 22 degree-5 real rows, the .762 row, 25 complex
  $\lambda_2$ rows, 69 complex $\lambda'$ rows, and the node counts in the B.10 table.

**D.10 [MINOR, documentation] Inconsistent $T^*$ statement across documents.**
`SOURCE_INTERFACES.md` ("Strip representatives") still counts zeros to height $\le1+\delta$.
PROOF.md §4 correctly uses height 2, with the circularity explanation. **Fix.** Align.

**D.11 [MINOR] $K_0$ and $s_{\max}$ are not pinned down.**
* PROOF.md says "$K_0$ is $O(1)$ by a log-free density estimate" without a reference, and
  never fixes $s_{\max}$.
* **Fix.** Cite Jutila (1977) Thm 1 (log-free, $4/5\le\sigma\le1$, as quoted in H p. 26)
  or H (1.4). Define $s_{\max}$ as the largest response anchor of any ordinary entry in
  the finite row menu.
* Note: I could not read Jutila's paper directly; the retained PDF is a scan without a text
  layer. Its statement was taken from H's quotation and the repository's
  `notes/source-dictionary.md`.

**D.12 [MINOR, interpretive] "absolute implied constants" in X Lemma 5.1.**
* For our profiles, $|w_0'|$ reaches about $\frac14\varepsilon_0^{-3/4}\approx4.4\times10^4$
  near $t=u$, and $w_0\ge\varepsilon_0^{1/4}e^{-\theta x/2}\approx8\times10^{-3}$.
* "absolute" cannot mean universal, since $q_0$ depends on $w_0$. X's own proof of
  Theorem 2.1 uses exactly this regularized profile (X (6.20), $\varepsilon_0=10^{-7}$).
* **Fix.** Record this in the paper as the justification.

**D.13 [MINOR, remark] (4.28) is derived via H (10.2)–(10.6).**
* H §10 opens with "assuming throughout that $\lambda_3\le6/7$".
* The derivation of (10.6) does not use this assumption; it is used only in the
  subsequent contradiction.
* X applies (4.28) to prove $\lambda_3$ bounds up to 1.054 > 6/7 (Table 9). So its use for
  $t>6/7$ is consistent with X, but the paper should say so.

**D.14 [MINOR, notation] Budget rounding.** PROOF.md writes
$F=\lceil(1+\eta)V\rceil-\dots$. The code uses outward rounding at scale $10^{-16}$
(`upper(...)`), not an integer ceiling, and "far cost 1" for the tail means the scaled
unit $S=10^{16}$. **Fix.** Say "rounded outward at $10^{-16}$".

**D.15 [MINOR] E2 constant.**
* The error summation of PROOF.md §2 needs $(1+\eta)V/w(0)<19$. This holds, but with
  18.47 for the retuned profile it is not far from the limit, and PROOF.md never displays
  the numbers.
* **Fix.** State Corollary A.5' with both numbers (16.372, 18.471).

**D.16 [MINOR, documentation] Representatives of the outside first family.**
PROOF.md §4 ("Any one zero per character…") lists ordinary, reserved and inside-first
representatives, but not the **hidden-column** zeros (rightmost $R_P$ zero other than
$\rho_1,\bar\rho_1$) that the outside model charges in the far row. **Fix.** Add them; the
justification is in Lemma A.4.

**Non-issues checked** (for the record):
* The inherited $\alpha_{10}$ is defined as $1-\sum_{i\le9}\alpha_i=.1201979632$ exactly,
  matching 4.33 §1.
* The retuned $\alpha$ sums exactly to 1.
* Only two far profiles occur in the corpus.
* Tail decay holds, with $A-2x\ge.808$.
* The negative-far-budget exclusion is sound.
* The `height_one` outside subcase is unused.
* The count rule is correct with $T^*$-representatives and in the outside model.
* The inside/outside split is exhaustive.
* X Table 8 is used from the "alle Fälle" column. It is the minimum of the Fall columns,
  so it is valid in all cases.
* The polynomial-row exclusions and the real positivity exclusion are sound.
* The order-4, order-5 and order-10 alias cases of the degree-5 rows are exhaustive and
  disjoint.
* The complex principal-index matching is injective.

---

## Part E. References

1. **[H]** D. R. Heath-Brown, *Zero-free regions for Dirichlet $L$-functions, and the least
   prime in an arithmetic progression*, Proc. London Math. Soc. (3) **64** (1992), no. 2,
   265–338. doi:10.1112/plms/s3-64.2.265.
   * Pages cited are those of the author's copy (Oxford ORA, 99 pp.) retained as
     `literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf`.
   * Journal page numbers are **not** verified. The repository notes suggest an offset of
     +264 (copy p. 5 ↔ journal p. 269). Treat this as uncertain.
2. **[X]** T. Xylouris, *Über die Nullstellen der Dirichletschen L-Funktionen und die
   kleinste Primzahl in einer arithmetischen Progression*, Dissertation, Rheinische
   Friedrich-Wilhelms-Universität Bonn, 2011 (defended 16 Nov 2011); also Bonner
   Mathematische Schriften **404**. 110 pp.; printed pages = PDF pages.
3. **[XA]** T. Xylouris, *On the least prime in an arithmetic progression and estimates for
   the zeros of Dirichlet $L$-functions*, Acta Arith. **150** (2011), no. 1, 65–91.
   doi:10.4064/aa150-1-4. Used only for cross-checks, e.g. the $\varphi$ definition on
   printed p. 67 (PDF p. 3).
4. T. Xylouris, *Linniks Konstante ist kleiner als 5*, Chebyshevskii Sb. **19** (2018),
   no. 3, 80–94. doi:10.22405/2226-8383-2018-19-3-80-94. Background only.
5. **[J]** M. Jutila, *On Linnik's constant*, Math. Scand. **41** (1977), 45–62. Thm 1,
   (1.7), p. 46 per the repository's notes. I read it only via H's quotation (H p. 26);
   the retained PDF is a scan.
6. D. A. Burgess, *On character sums and $L$-series*, Proc. London Math. Soc. (3) **12**
   (1962), 193–206, and *II*, ibid. **13** (1963), 524–536. Cited via H Lemma 2.1;
   bibliographic details are from memory and should be checked.
7. H. Davenport, *Multiplicative Number Theory*, 2nd ed., Springer GTM 74 (1980), §13.
   Classical zero-free region for $\zeta$, for the exclusion of $\chi_0$. Edition/section
   from the repository notes; unverified here.

**Repository code and data referenced** (paths relative to `computations/`):
* `core/code/{base_enclosures,enclosures,config_v4,case_cover,cover_v4,cover_v5,refinement_cover,verify_v5,input_bounds,published_single_inputs,two_test_enclosures,extension_enclosures,vector_intervals,endgame,triple_inputs,poly_rows,build_poly_table,new_positivity,alias_check,verify_progress}.py`
* `frontier/{far_enclosures,inside_real_rows,inside_conductor_rows,polynomial5_rows,inside_repair,inside_complex_rows,collective_cover,far_full}.py`
* `frontier/inside_polynomial5_rows_.700_.755.json`
* `core/results/{source_cover.json.gz,polynomial_table.json}`
* `sieve_near/third_refine.py`
* `near/code/{first_outside_blocks,outside_regime,verify_auxiliary_inputs}.py`
* `graded/{graded_leaves,graded_verify}.py`
* Lean: `lean-graded/GradedNear/{Far,FarFacts}.lean`

**Scratch checks** (not committed), in
`/tmp/claude-1000/-home-naslund-eric-src-enaslund-linniks-constant-master/4876f15a-dad1-49ec-8f95-ac53e5648049/scratchpad/deep/`:
* `far_check.py` ($V$, $w$, tail);
* `h_table4.py`, `h_table7.py` (H roots);
* `rows_check.py` (degree-5 rows);
* `poly5.py` (degree-5 positivity);
* `poly_check.py` (complex rows);
* `third_check.py` ($\lambda_3$ refinement);
* `x434.py` ((4.34)).
