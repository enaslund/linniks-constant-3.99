# Deep dive: the graded near lemma, its rows, and the inherited two-test row

Component of the paper "Linnik's constant satisfies $L\le 3.99$" corresponding to
`research/PROOF.md` §6 (6.1–6.6). Written 2026-09-30 from the repository at commit `3e63657`
(read-only), the Lean package `lean-graded/`, the row builders in `computations/`, and the
literature texts in the session's `lit/` folder.

**Verdict in one paragraph.** The graded near lemma (Theorem 3.3 below), the response lemma
(Lemma 4.1), the threshold form and the builders' normalization (§5) are correct as mathematics;
I re-derived every step, every exponent and every uniformity claim, and found no error that can
affect a certificate. Every row type of PROOF.md §6.5 is a valid instance (§6), and the row
generators (`sieve_inputs.py`, `leaf_driver.graded_row`, `graded_leaves.py`) produce exactly the
features, diagonals and radii that the analysis licenses (§6.4). The inherited two-test row
(PROOF.md §6.6) is also valid in all three variants actually used (single test, detector mixture,
paired first family), and its embedding in the graded LP is correct (§7). What I found are
citation errors, imprecisely stated hypotheses and scope gaps (§9); the most substantive ones are:
a wrong citation for the pointwise Burgess bound (X Lemma 5.2 is not that statement); a missing
citation for the zero count $K_0$; the response lemma stated without multiplicities in PROOF.md;
"$\omega>0$ on $\operatorname{supp} f$" where a uniform positive lower bound is needed; Gram
points to the right of $\operatorname{Re}s=1$ described as lying in $R(9l)$; the inherited
two-test row being outside the Lean row checker; and Heath-Brown citations that use the
preprint's pagination rather than the printed PLMS pages.

Throughout, **X** is Xylouris's dissertation (Bonner Math. Schriften 404, 2011; printed page
numbers coincide with the PDF pages of the text used here), and **H** is Heath-Brown, *Zero-free
regions for Dirichlet $L$-functions, and the least prime in an arithmetic progression*, Proc.
London Math. Soc. (3) 64 (1992) 265–338. The H text available is the author's preprint; I cite H
by lemma/equation number and **preprint** page ("H p. 24 (pp)"), plus the PLMS page where X gives
it. See §9, item C1.

---

## 1. Notation and test functions

### 1.1 Notation

$q$ is the modulus, $\mathcal L=\log q$, $t_n=\log n/\mathcal L$. A zero of $L(s,\chi)$ is written
$\rho=1-\lambda_\rho/\mathcal L+i\gamma_\rho=1-\lambda_\rho/\mathcal L+i\mu_\rho/\mathcal L$:
$\lambda_\rho$ is its normalized distance from $\operatorname{Re}s=1$, $\gamma_\rho$ its physical
height and $\mu_\rho=\gamma_\rho\mathcal L$ its normalized height. Zeros are counted with
multiplicity $m_\rho$. $\chi_0$ is the principal character mod $q$; all characters are mod $q$
(possibly imprimitive, with $\chi(n)=0$ for $(n,q)>1$). For $x>0$,
$$R(x)=\Bigl\{\sigma+it:\ 1-\frac{\log\log\mathcal L}{3\mathcal L}\le\sigma\le 1,\ |t|\le x\Bigr\}\qquad\text{(X (3.7), p. 18)},$$
and $l=l(q)$ is the integer of X Lemma 3.3 (§2), $1\le l\le\mathcal L/10$. For a zero set, "to the
left of the anchor $\sigma$" means $\lambda_\rho\ge\sigma$.

The **Laplace transform** of $f:[0,\infty)\to\mathbb R$ is $F(z)=\int_0^\infty f(t)e^{-zt}\,dt$;
$G_1$ is that of $g_1$. For real $f$, $\operatorname{Re}F(\bar z)=\operatorname{Re}F(z)$.

### 1.2 Conditions 1 and 2

**Condition 1** (H p. 20 (pp) = PLMS p. 280; X Bedingung 1, p. 17). $f:[0,\infty)\to\mathbb R$ is
continuous, $f(t)=0$ for $t\ge x_0$ (some $x_0>0$), $f$ is twice differentiable on $(0,x_0)$ and
$|f''|\le B$ there (H also requires $f''$ continuous).

**Condition 2** (H p. 27 (pp) = PLMS p. 286; X Bedingung 2, p. 18). $f\ge0$ on $[0,\infty)$ and
$\operatorname{Re}F(z)\ge0$ for $\operatorname{Re}z\ge0$.

A function satisfying both is **admissible**.

Two elementary facts used repeatedly:

* **(F1) Monotonicity.** If $f\ge0$, $f\not\equiv0$, then $x\mapsto F(x)$ is strictly decreasing
  and positive on all of $\mathbb R$ (not only on $x\ge0$): $F'(x)=-\int tf(t)e^{-xt}dt<0$.
* **(F2) Decay.** If $f$ satisfies Condition 1, then for $z\ne0$,
  $F(z)=f(0)/z+z^{-1}\int_0^{x_0}f'(t)e^{-zt}dt$, hence for $\operatorname{Re}z\ge-\sigma_{\max}$
  $$|F(z)|\le\frac{A_f(\sigma_{\max})}{|\operatorname{Im}z|},\qquad
  A_f(\sigma_{\max})=|f(0)|+e^{\sigma_{\max}x_0}\int_0^{x_0}|f'|.$$

### 1.3 The parabolic autocorrelation test

For $c>0$ put
$$P(u)=(1-u)^3(1+3u+u^2)=1-5u^2+5u^3-u^5,\qquad
f_c(t)=\begin{cases}P(t/c),&0\le t\le c,\\0,&t\ge c.\end{cases}$$
The repository's detector "$f_\gamma$ normalized" is $f_{2\gamma}$ (support $[0,2\gamma]$) and its
Gram test "$g_1$" is $f_{2g_1}$; both are normalized to value $1$ at $0$. (In
`base_enclosures.RigorousTest` the unnormalized $\tfrac{16\gamma^5}{15}P(t/2\gamma)$ is used and
every transform is divided by `f0`$=16\gamma^5/15$.)

**Lemma 1.1 (parabolic test).** Let $c>0$ and $F_c$ be the transform of $f_c$.

1. $f_c\ge0$, $f_c(0)=1$, $f_c$ is decreasing on $[0,c]$
   ($P'(u)=-5u(2+u)(1-u)^2$), $f_c\in C^2([0,\infty))$ after extension by $0$ (the factor
   $(1-u)^3$), and $|f_c''|\le 10/c^2$. So Condition 1 holds with $x_0=c$, $B=10/c^2$.
2. $f_c=\tfrac{15}{16\gamma^5}\,(h_\gamma*h_\gamma)|_{[0,\infty)}$ with $c=2\gamma$ and
   $h_\gamma(x)=(\gamma^2-x^2)_+$.
3. $F_c(z)=c\,\Phi(cz)$ where, for $w\ne0$,
   $$\Phi(w)=\int_0^1P(s)e^{-ws}ds=\frac1w-\frac{10}{w^3}+\frac{30(1+e^{-w})}{w^4}+\frac{120e^{-w}}{w^5}-\frac{120(1-e^{-w})}{w^6},$$
   and $\Phi(w)=\sum_{k\ge0}\frac{30\,(-w)^k}{(k+1)(k+3)(k+4)(k+6)\,k!}$ (entire).
4. $\operatorname{Re}F_c(iy)=c\int_0^1P(s)\cos(cys)ds=\dfrac{60c\,\bigl(cy\cos\frac{cy}{2}-2\sin\frac{cy}{2}\bigr)^2}{(cy)^6}\ge0$
   ($y\ne0$), $F_c(0)=5c/12$.
5. $f_c$ satisfies Condition 2, so it is admissible.
6. (Moments) $\int_0^\infty t^kf_c(t)e^{dt}dt=c^{k+1}\sum_{j\ge0}\frac{(dc)^j}{j!}\,\frac{30}{(k+j+1)(k+j+3)(k+j+4)(k+j+6)}$.
7. (Derivatives) For $x\ge -d$ ($d\ge0$) and real $y$:
   $|\partial_y^2\operatorname{Re}F_c(x+iy)|\le\int t^2f_ce^{dt}$; for $x\ge0$:
   $|\partial_x\operatorname{Re}F_c(x+iy)|\le\int tf_c$ and
   $|\partial_x^2\operatorname{Re}F_c(x+iy)|\le\int t^2f_ce^{-xt}$.
8. (Tails) Let $R(u,E)=\frac{10}{u^3}+\frac{30}{u^4}+\frac{120}{u^6}+E\bigl(\frac{30}{u^4}+\frac{120}{u^5}+\frac{120}{u^6}\bigr)$.
   For $d\ge0$ and $|y|\ge U>0$:
   $$\operatorname{Re}F_c(-d+iy)\le c\,R(cU,e^{cd}),\qquad -\operatorname{Re}F_c(-d+iy)\le\frac{d}{U^2}+c\,R(cU,e^{cd}).$$
9. (Minimum principle) For $d\ge0$ put $C(d)=\sup_{\operatorname{Re}z\ge-d}(-\operatorname{Re}F_c(z))$.
   Then $C(d)=\max\bigl(0,\sup_{y\in\mathbb R}(-\operatorname{Re}F_c(-d+iy))\bigr)<\infty$, and $C(0)=0$.

*Proof.* (1)–(3), (6), (7) are direct computations: (3) by five integrations by parts using
$P(1)=P'(1)=P''(1)=0$, $P'''(1)=-30$, $P^{(4)}(1)=-120$, $P(0)=1$, $P''(0)=-10$, $P'''(0)=30$,
$P^{(5)}\equiv-120$; the series from $\int_0^1s^rP(s)ds=\frac1{r+1}-\frac5{r+3}+\frac5{r+4}-\frac1{r+6}=\frac{30}{(r+1)(r+3)(r+4)(r+6)}$.
(4) is the same computation at $w=icy$ (it is the Lean lemma `integral_P_cos`).
(5): by (2) and X Lemma 3.6 (p. 22; H p. 31 (pp) = PLMS p. 289), which derives Condition 2 for
autocorrelations of even nonnegative compactly supported $h$ from $\operatorname{Re}F(iy)=2(\int_0^\infty h\cos)^2\ge0$
and X Lemma 3.5 (= H Lemma 4.1, H p. 18 (pp)) with $F_1=F$, $F_2=0$; $F\to0$ uniformly in
$\operatorname{Re}z\ge0$ by (F2). Scaling by a positive constant preserves admissibility.
(8): $c\operatorname{Re}\frac1{cz}=\operatorname{Re}\frac1z=\frac{-d}{d^2+y^2}\le0$ for $z=-d+iy$,
and every other term of $c\Phi(cz)$ is bounded in modulus by the corresponding term of
$cR(c|z|,|e^{-cz}|)$, with $|z|\ge|y|\ge U$, $|e^{-cz}|=e^{cd}$; $R$ decreases in $u$. The second
inequality adds $d/(d^2+y^2)\le d/U^2$.
(9): $-\operatorname{Re}F_c(z-d)$ is harmonic on $\operatorname{Re}z>0$, continuous up to the boundary,
and $\to0$ uniformly as $|z|\to\infty$ in $\operatorname{Re}z\ge0$ (by (3) or (F2)); the maximum
principle on half-discs gives the claim; $C(0)=0$ by (5). $\square$

I checked (2), (3) and (4) numerically to 30 digits and (8) on a grid (script
`scratchpad/deep/checks1.py`); (3)–(4) and (8)–(9) are also proved in Lean (`laplace_fpar_eq`,
`PhiC_eq_closed`, `integral_P_cos`, `tail_re_le`, `tail_neg_re_le`, `re_ge_of_line`).

---

## 2. Literature inputs

| Tag | Printed statement (abridged; hypotheses in full) | Where | How used here | Match |
| --- | --- | --- | --- | --- |
| **X3.1** | Let $s=\sigma+it$, $\lvert\sigma-1\rvert\le(\log\mathcal L)^{1/2}/\mathcal L$, $\lvert t\rvert\le\mathcal L$, and $f$ satisfy Condition 1. Then $\sum_n\Lambda(n)\chi_0(n)n^{-s}f(\mathcal L^{-1}\log n)=\mathcal LF((s-1)\mathcal L)+O(\mathcal L/\log\mathcal L)$, the implied constant depending only on $f$. | X Lemma 3.1, p. 18 = H Lemma 5.3, p. 25 (pp) | Gram diagonal, separated same-character pairs, controlled pairs (§3.4 Step 3); two-test diagonals (§7) | exact; $\chi_0$ mod $q$ (so $(n,q)=1$); heights $\le2l\le\mathcal L/5$ |
| **X3.2** | Let $\chi\ne\chi_0$ mod $q$, $\varphi=\varphi(\chi)\in\{\frac14,\frac13\}$ (X p. 17), $s$ as in X3.1, $f$ Condition 1 with $f(0)\ge0$. For every $\varepsilon>0$ there is $\delta\in(0,1)$ depending on $f$ but not on $\chi,q,s$, and $q_0(f,\varepsilon)$, with, for $q\ge q_0$: $\sum_n\Lambda(n)\operatorname{Re}(\chi(n)n^{-s})f(\mathcal L^{-1}\log n)\le-\mathcal L\sum_{\lvert1+it-\rho\rvert\le\delta}\operatorname{Re}F((s-\rho)\mathcal L)+\frac{\varphi}{2}f(0)\mathcal L+\varepsilon\mathcal L$ (nontrivial zeros, with multiplicity). | X Lemma 3.2, p. 18 = H Lemma 5.2, p. 24 (pp) (H's print omits $\Lambda(n)$ and has $f(0)(\frac\varphi2+\varepsilon)\mathcal L$) | Responses (Lemma 4.1); off-diagonal Gram entries of distinct characters (§3.4); two-test (§7) | exact; used with $\varphi\le\frac13$ (and $\varphi=\frac14$ for real $\chi$, order $2\le\mathcal L$, only in §7) |
| **X3.3** | There are $q_0$ and $l=l(q)\in\mathbb N$, $l\le\mathcal L/10$, such that for $q\ge q_0$ $\prod_{\chi}L(s,\chi)$ has no zeros in $R(10l)\setminus R(l)$. | X Lemma 3.3, p. 19 = H Lemma 6.1, p. 26 (pp) | Lemma 3.4 (safe anchor up to height $10l$); disc zeros of all entries are in $R(l)$ or far left | exact |
| **X3.5/3.6** | Maximum principle lemma; autocorrelations $f=h*h$ ($h$ even, $\ge0$, continuous, compact support) satisfying Condition 1 satisfy Condition 2. | X pp. 22; H Lemma 4.1, p. 18 (pp); H PLMS p. 289 | Lemma 1.1(5) | exact |
| **B** | Let $q\ge1$, $\chi$ primitive mod $q$, $N\ge1$, $1\le H\le q$. For $\varepsilon>0$, $\sum_{N<n\le N+H}\chi(n)\ll_{\varepsilon,k}q^{(k+1)/(4k^2)+\varepsilon}H^{1-1/k}$ for $k=2,3$. | H Lemma 2.1, p. 7 (pp); Burgess 1963 | Sieve off-diagonal (§3.4 Step 4), with $k=3$: $q^{1/9+\varepsilon}H^{2/3}$; extended to imprimitive $\psi$ in Lemma 3.5 | exact (Lean `BurgessPrimitive`, `burgessBound_of_primitive`) |
| **G** | With $\psi_d$ of H (11.6) ($U=1$: $\psi_d=\mu(d)\log(V/d)/\log V$ for $d\le V$, $0$ else): $\sum_{n\le N}(\sum_{d\mid n}\psi_d)^2=N/\log V+O(N/\log^2V)$ for $N\ge V$. | H (11.13), p. 72 (pp), citing Graham, J. Number Theory 10 (1978) p. 84 | Sieve diagonal (§3.4 Step 4) | exact (the case $N\ge V$, $U=1$) |
| **Mer** | $\sum_{n\le x}\Lambda(n)/n=\log x+O(1)$. | Mertens (e.g. Montgomery–Vaughan, *Multiplicative Number Theory I*, Thm 2.7) | First factor (§3.4 Step 2) | standard; PROOF.md cites the PNT, which is stronger than needed |
| **LF** | $\sum_{\chi\bmod q}N(\sigma,T,\chi)\le c_3(qT)^{c_4(1-\sigma)}$ for $T\ge1$, $\frac12\le\sigma\le1$, zeros with multiplicity, $c_3,c_4$ effective. | X Prinzip 3, p. 11; Jutila 1977 Thm 1 as quoted in H p. 26 (pp) ($\ll_\varepsilon(qT)^{(2+\varepsilon)(1-\sigma)}$, $\sigma\ge4/5$); Thorner–Zaman Thm 1.2 (explicit) | $K_0=O(1)$ (§6.2) | used with $1-\sigma=s_{\max}/\mathcal L$, $T=2$ |

**Remarks on the inputs.**
(i) X Lemma 3.2 is stated for every non-principal character mod $q$, primitive or not (the
reduction is in H p. 24 (pp)). (ii) X p. 36 records that $\delta$, $q_0$ in X3.2 and the implied
constant in X3.1 depend only on $\varepsilon$ and bounds for $x_0,x_0^{-1},\sup|f|,\sup(|f'|+|f''|)$;
we only use finitely many tests, so this refinement is not needed. (iii) H remarks after Lemma 5.2
(p. 24 (pp)) that one may take $\delta=1/\log\mathcal L$; not needed here. (iv) The Lean
hypotheses `XylourisLemma31`, `XylourisLemma32`, `BurgessPrimitive`, `GrahamEstimate`
(`lean-graded/Challenge.lean` lines 138–203) are faithful transcriptions or special cases of X3.1,
X3.2 (with $\varphi=\frac13$), B ($k=3$, integer $N,H$) and G.

---

## 3. The graded near lemma

### 3.1 Data

**Definition 3.1 (row data).** Fix, independently of $q$:

* a **detector** $f$, admissible, $f\not\equiv0$, supported in $[0,x_f)$;
* a **short Gram test** $g_1$, admissible, with $g_1(0)>0$; put $d_1=g_1(0)/6$;
* **anchors** $s_1\le s$ (real);
* a **sieve margin** $\varepsilon'>0$, **cells** $t_0<t_1<\dots<t_m$ with $t_0>\frac13+2\varepsilon'$,
  **heights** $h_k\ge0$, $H(t)=\sum_{k<m}h_k\mathbf 1_{[t_k,t_{k+1})}(t)$, and levels
  $\delta_k=\frac{t_k-1/3}{2}-\varepsilon'>0$;
* the **weight** $\omega(t)=g_1(t)e^{s_1t}+H(t)$, subject to
  $$\inf\{\omega(t):0\le t<x_f,\ f(t)\ne0\}>0;\tag{W}$$
* a finite set $\Delta\subset[0,\infty)$ of **offsets**, and a **separation** $M_2>0$ such that
  $|G_1(-\sigma+iY)|\le d_1$ for $|Y|\ge M_2$ and $\sigma\in\{s_1-\delta-\delta':\delta,\delta'\in\Delta\}$
  (exists by (F2)).

Put
$$I_B(s)=\int_0^\infty\frac{e^{2st}f(t)^2}{\omega(t)}dt,\qquad
D(\delta)=\int_0^\infty g_1(t)e^{(s_1-2\delta)t}dt+\sum_{k<m}h_ke^{-2\delta t_k}\frac{t_{k+1}^2-t_k^2}{2\delta_k}.$$
$D$ is decreasing in $\delta\ge0$.

### 3.2 Entries

**Definition 3.2 (admissible entry family).** For a modulus $q$, a finite family
$E=(\chi_j,\gamma_j,\delta_j)_{j\in J}$ with $\chi_j$ nonprincipal mod $q$, $|\gamma_j|\le l(q)$,
$\delta_j\in\Delta$, and **response anchor** $s_j=s-\delta_j$, such that for $j\ne k$ with
$\chi_j=\chi_k$ one of the following holds:

* **(kind 2, separated heights)** $|\gamma_j-\gamma_k|\mathcal L\ge M_2$;
* **(kind 3, controlled pair)** $\delta_j=\delta_k=0$ and $|\gamma_j-\gamma_k|\mathcal L\in Y_{jk}$,
  a stated set; each $j$ lies in at most one controlled pair;

and, if $H\not\equiv0$, the $\chi_j$ are pairwise distinct (kind 1 only). The **response** of $j$ is
$$R_j=-\mathcal L^{-1}\sum_{n\ge1}\Lambda(n)\operatorname{Re}\bigl(\chi_j(n)n^{-(1-s_j/\mathcal L+i\gamma_j)}\bigr)f(t_n).$$

### 3.3 Statement

**Hypothesis (SA) (safe anchor).** Every zero $\rho\in R(l)$ of every nonprincipal $L(s,\chi)$
mod $q$ has $\lambda_\rho\ge s_1$.

**Theorem 3.3 (graded near lemma).** Let the data of Definition 3.1 be fixed and $\eta'>0$. For
each controlled pair $\{j,k\}$ let $c^{\rm hi}_{jk}\ge\sup_{y\in Y_{jk}}\operatorname{Re}G_1(-s_1+iy)$
and put $e_j=e_k=(c^{\rm hi}_{jk}-d_1)_+$; put $e_j=0$ for entries in no controlled pair. There is
$q_0$, depending only on the data and $\eta'$, such that for every $q\ge q_0$ satisfying (SA),
every admissible entry family and every $a\in[0,\infty)^J$,
$$\Bigl(\sum_ja_jR_j\Bigr)_+^2\le(1+\eta')\,I_B(s)\Bigl[\sum_j\bigl(D(\delta_j)-d_1+e_j\bigr)a_j^2+(d_1+\eta')\Bigl(\sum_ja_j\Bigr)^2\Bigr].$$
The number of entries is unrestricted (it may grow with $q$).

*Formal counterpart.* `GradedNear.graded_near_lemma` (Challenge.lean l. 585) proves a slightly
more general statement: same-character pairs of any kind, with the exact excess
$e_j=\sum_{k\ne j,\chi_k=\chi_j}(\operatorname{Re}G_1(-\sigma_{jk}+i(\gamma_j-\gamma_k)\mathcal L)-d_1)_+$;
heights $|\gamma_j|\le T\le\mathcal L/3$; and the zero-free hypothesis `SafeAnchor q s₁ (2T+1)`
in place of (SA). Lemma 3.4 below derives the latter from (SA) with $T=l$.

### 3.4 Proof

**Lemma 3.4 (safe anchor up to height $10l$).** Assume X3.3 and (SA). For $q\ge q_0(s_1)$, every
zero $\rho$ of a nonprincipal $L(s,\psi)$ mod $q$ with $|\operatorname{Im}\rho|\le10l$ has
$\lambda_\rho\ge s_1$.

*Proof.* Nontrivial zeros have $\operatorname{Re}\rho<1$. If $\rho\in R(l)$, use (SA). Otherwise
either $|\operatorname{Im}\rho|\le l$ and $\operatorname{Re}\rho<1-\frac{\log\log\mathcal L}{3\mathcal L}$,
or $l<|\operatorname{Im}\rho|\le10l$, in which case $\rho\notin R(10l)$ by X3.3 and again
$\operatorname{Re}\rho<1-\frac{\log\log\mathcal L}{3\mathcal L}$. Then
$\lambda_\rho>\frac13\log\log\mathcal L\ge s_1$ once $q$ is large. $\square$

**Step 0 (constants).** Fix $\varepsilon_1>0$ (to be taken small in terms of $\eta'$, $I_B(s)$,
$d_1$). All $q_0$'s below depend only on the data and $\varepsilon_1$. Let
$\sigma_{\max}=|s_1|+2\max\Delta+|s|$.

**Step 1 (one sum and Cauchy–Schwarz).** Since $n^{-(1-s_j/\mathcal L+i\gamma_j)}=n^{-1}e^{st_n}e^{-\delta_jt_n}n^{-i\gamma_j}$,
$$\sum_ja_jR_j=-\operatorname{Re}\,\mathcal L^{-1}\sum_n\frac{\Lambda(n)}ne^{st_n}f(t_n)Y_n,\qquad
Y_n=\sum_ja_je^{-\delta_jt_n}\chi_j(n)n^{-i\gamma_j},$$
and $Y_n=0$ if $(n,q)>1$. Since $\omega\ge0$ everywhere and (W) holds, Cauchy–Schwarz gives
$$\Bigl(\sum_ja_jR_j\Bigr)_+^2\le\underbrace{\Bigl(\mathcal L^{-1}\sum_n\frac{\Lambda(n)}n\frac{e^{2st_n}f(t_n)^2}{\omega(t_n)}\Bigr)}_{\Sigma_1}\ \underbrace{\Bigl(\mathcal L^{-1}\sum_{(n,q)=1}\frac{\Lambda(n)}n\,\omega(t_n)\,|Y_n|^2\Bigr)}_{\Sigma_2}.$$

**Step 2 (first factor).** $\varphi(t)=e^{2st}f(t)^2/\omega(t)$ is bounded on $[0,x_f]$ by (W),
vanishes for $t\ge x_f$, and is continuous except at the finitely many $t_k$ and possibly where
$g_1$'s support ends; hence Riemann integrable. Given $\varepsilon_1$, choose a partition
$0=u_0<\dots<u_K=x_f$ with $\sum_i(u_{i+1}-u_i)\sup_{[u_i,u_{i+1}]}\varphi\le I_B(s)+\varepsilon_1/2$. By
Mer, $\mathcal L^{-1}\sum_{q^{u_i}<n\le q^{u_{i+1}}}\Lambda(n)/n=u_{i+1}-u_i+O(1/\mathcal L)$; so
$\Sigma_1\le I_B(s)+\varepsilon_1$ for $q\ge q_0$ (the terms $n\le1$ vanish). This is exactly the
Lean route (`FirstFactor.riemann_upper`); PROOF.md's appeal to the prime number theorem also works
but is not needed.

**Step 3 (the Gram part $Q_1$).** Write $\Sigma_2=Q_1+Q_2$ according to $\omega=g_1e^{s_1t}+H$.
Expanding $|Y_n|^2$ and using that $Q_1$ is real,
$$Q_1=\sum_{j,k}a_ja_k\operatorname{Re}\Gamma_{jk},\qquad
\Gamma_{jk}=\mathcal L^{-1}\sum_n\Lambda(n)\psi_{jk}(n)\,n^{-s_{jk}}g_1(t_n),$$
$$\psi_{jk}=\chi_j\bar\chi_k,\quad s_{jk}=1-\frac{\sigma_{jk}}{\mathcal L}+i(\gamma_j-\gamma_k),\quad\sigma_{jk}=s_1-\delta_j-\delta_k\le s_1 .$$
For $q\ge q_0$, $|\sigma_{jk}|\le\sigma_{\max}\le(\log\mathcal L)^{1/2}$ and
$|\gamma_j-\gamma_k|\le2l\le\mathcal L/5$, so every $s_{jk}$ lies in the region of X3.1/X3.2. Note
$\psi_{jk}$ is a character mod $q$, so $\psi_{jj}=\chi_0$ exactly.

* *Diagonal.* By X3.1, $\Gamma_{jj}=G_1(-(s_1-2\delta_j))+O(1/\log\mathcal L)=\int g_1e^{(s_1-2\delta_j)t}+o(1)$.
* *Distinct characters* ($\chi_j\ne\chi_k$). $\psi_{jk}\ne\chi_0$. By X3.2 (test $g_1$, $\varepsilon=\varepsilon_1$),
  $\operatorname{Re}\Gamma_{jk}\le-\sum_{\rho\in\mathfrak D}m_\rho\operatorname{Re}G_1((s_{jk}-\rho)\mathcal L)+d_1+\varepsilon_1$,
  $\mathfrak D$ the disc $|1+i(\gamma_j-\gamma_k)-\rho|\le\delta<1$. Every $\rho\in\mathfrak D$ has
  $|\operatorname{Im}\rho|<2l+1\le10l$, so $\lambda_\rho\ge s_1\ge\sigma_{jk}$ by Lemma 3.4, i.e.
  $\operatorname{Re}((s_{jk}-\rho)\mathcal L)=\lambda_\rho-\sigma_{jk}\ge0$, and Condition 2 for
  $g_1$ lets us drop every zero: $\operatorname{Re}\Gamma_{jk}\le d_1+\varepsilon_1$. When
  $\sigma_{jk}<0$ the test point lies to the right of $\operatorname{Re}s=1$; X3.2 allows
  $|\sigma-1|\le(\log\mathcal L)^{1/2}/\mathcal L$ on both sides, so nothing changes. (This is
  where PROOF.md's "inside $R(9l)$" is inaccurate — $R(9l)$ requires $\operatorname{Re}s\le1$ — but
  only X3.2 and X3.3 are used, never X Lemma 3.4; see §9, A4.)
* *Separated heights* (kind 2). $\psi_{jk}=\chi_0$; by X3.1,
  $\Gamma_{jk}=G_1(-\sigma_{jk}+i(\gamma_j-\gamma_k)\mathcal L)+o(1)$, and $|G_1(\cdot)|\le d_1$ by the
  choice of $M_2$. So $\operatorname{Re}\Gamma_{jk}\le d_1+o(1)$.
* *Controlled pair* (kind 3). $\psi_{jk}=\chi_0$, $\sigma_{jk}=s_1$; by X3.1,
  $\operatorname{Re}\Gamma_{jk}=\operatorname{Re}G_1(-s_1+iy)+o(1)\le c^{\rm hi}_{jk}+o(1)$ with
  $y=(\gamma_j-\gamma_k)\mathcal L\in\pm Y_{jk}$ (and $\operatorname{Re}G_1$ is even in $y$).

All $o(1)$ are uniform in the characters, heights and the number of entries (X3.1's constant
depends only on $g_1$). Since $a\ge0$ and $2a_ja_k\le a_j^2+a_k^2$,
$$Q_1\le\sum_j\Bigl(\int g_1e^{(s_1-2\delta_j)t}-d_1+e_j\Bigr)a_j^2+d_1\Bigl(\sum_ja_j\Bigr)^2+2\varepsilon_1\Bigl(\sum_ja_j\Bigr)^2\quad(q\ge q_0).$$

**Step 4 (the sieve part $Q_2$; only when $H\not\equiv0$, so all $\chi_j$ distinct).**
$Q_2=\sum_kh_k\,\mathcal L^{-1}\sum_{q^{t_k}\le n<q^{t_{k+1}},(n,q)=1}\frac{\Lambda(n)}n|Y_n|^2$. Fix a
cell $k$, let $D_k=q^{\delta_k}$, $\lambda_d=\mu(d)\frac{\log(D_k/d)}{\log D_k}$ for $d\le D_k$ and
$0$ otherwise ($|\lambda_d|\le1$), and $\nu_k(n)=(\sum_{d\mid n}\lambda_d)^2\ge0$.

* *Majorant.* For a prime $p\ge q^{t_k}>D_k$, $\nu_k(p)=\lambda_1^2=1$, so $\Lambda(p)=(\log p)\nu_k(p)$;
  for composite non-prime-powers $\Lambda=0\le(\log n)\nu_k(n)$. Prime powers $p^r$, $r\ge2$, in the
  cell contribute at most $\mathcal L^{-1}(\sum_ja_j)^2\sum_{p^r\ge q^{t_k},r\ge2}\frac{\log p}{p^r}\ll q^{-t_k/2}(\sum a_j)^2$
  (using $|Y_n|\le\sum_ja_j$). Hence, with $\tau_{jj'}=\gamma_j-\gamma_{j'}$,
  $$Q_2\le\sum_kh_k\sum_{j,j'}a_ja_{j'}\operatorname{Re}T^{(k)}_{jj'}+o(1)\Bigl(\sum a_j\Bigr)^2,\quad
  T^{(k)}_{jj'}=\mathcal L^{-1}\!\!\sum_{q^{t_k}\le n<q^{t_{k+1}}}\!\frac{\log n}{n}\nu_k(n)e^{-(\delta_j+\delta_{j'})t_n}\psi_{jj'}(n)n^{-i\tau_{jj'}} .$$
* *Diagonal.* $\psi_{jj}=\chi_0$; dropping $(n,q)=1$ (all terms $\ge0$) and using
  $e^{-2\delta_jt_n}\le e^{-2\delta_jt_k}$: $T^{(k)}_{jj}\le e^{-2\delta_jt_k}\mathcal L^{-1}\sum_{q^{t_k}\le n<q^{t_{k+1}}}\frac{\log n}n\nu_k(n)$.
  By G (valid since every $x$ in the cell exceeds $V=D_k$), $S(x):=\sum_{n\le x}\nu_k(n)=x/\log D_k+E(x)$,
  $|E(x)|\le Cx/\log^2D_k$. Stieltjes integration of $\log u/u$ against $dS$ over
  $[q^{t_k},q^{t_{k+1}})$ gives the main term $\frac{\log^2q^{t_{k+1}}-\log^2q^{t_k}}{2\log D_k}=\mathcal L\frac{t_{k+1}^2-t_k^2}{2\delta_k}$,
  boundary terms $\le\frac{\log x}{x}|E(x)|\le\frac{C\,t_{k+1}\mathcal L}{\delta_k^2\mathcal L^2}=O(1/\mathcal L)$ and an integral term
  $\le\frac{C}{\log^2D_k}\int_{q^{t_k}}^{q^{t_{k+1}}}\frac{\log u}u\,du=\frac{C(t_{k+1}^2-t_k^2)}{2\delta_k^2}=O(1)$.
  After the factor $\mathcal L^{-1}$:
  $T^{(k)}_{jj}\le e^{-2\delta_jt_k}\frac{t_{k+1}^2-t_k^2}{2\delta_k}+O(1/\mathcal L)$.
* *Off-diagonal* ($j\ne j'$, $\psi=\psi_{jj'}\ne\chi_0$, $a:=(\delta_j+\delta_{j'})/\mathcal L$, $\tau=\tau_{jj'}$).
  Opening the square, $T^{(k)}_{jj'}=\sum_{d,e\le D_k}\lambda_d\lambda_e\psi([d,e])\,\Sigma_{d,e}$ with
  $$\Sigma_{d,e}=\sum_{M_0\le m<M_1}\psi(m)W(m[d,e]),\quad W(v)=\mathcal L^{-1}(\log v)\,v^{-1-a-i\tau},\quad M_0=\frac{q^{t_k}}{[d,e]},\ M_1=\frac{q^{t_{k+1}}}{[d,e]}.$$
  Since $[d,e]\le D_k^2=q^{2\delta_k}$ and $2\delta_k=t_k-\frac13-2\varepsilon'$: $M_0\ge q^{1/3+2\varepsilon'}$.
  With $c=[d,e]$, $v=uc\in[q^{t_k},q^{t_{k+1}}]$: $|W(uc)|\le t_{k+1}/(uc)$ and, from
  $W'(v)=\mathcal L^{-1}v^{-2-a-i\tau}\bigl(1-(1+a+i\tau)\log v\bigr)$,
  $|\tfrac{d}{du}W(uc)|=c|W'(uc)|\le(2+|\tau|)(1+t_{k+1})/(u^2c)$ for $q\ge q_0$ (as $a\le1$). Let
  $S(u)=\sum_{M_0\le m\le u}\psi(m)$. Abel summation and Lemma 3.5 give
  $$|\Sigma_{d,e}|\le|S(M_1)W(M_1c)|+\int_{M_0}^{M_1}|S(u)|\,|\tfrac{d}{du}W(uc)|\,du\ll_\varepsilon q^{1/9+2\varepsilon}(2+|\tau|)\,c^{-1}M_0^{-1/3}=q^{1/9+2\varepsilon-t_k/3}(2+|\tau|)\,[d,e]^{-2/3}.$$
  Using $\sum_{d,e\le D}[d,e]^{-2/3}\le\sum_{g\le D}g^{-2/3}\bigl(\sum_{d'\le D/g}d'^{-2/3}\bigr)^2\le9\zeta(\tfrac43)D^{2/3}$,
  $$|T^{(k)}_{jj'}|\ll(2+|\tau|)\,q^{1/9+2\varepsilon-t_k/3+2\delta_k/3}=(2+|\tau|)\,q^{2\varepsilon-2\varepsilon'/3}\le\mathcal L\,q^{2\varepsilon-2\varepsilon'/3}.$$
  (Exactly: $\frac19-\frac{t_k}3+\frac23\delta_k=-\frac23\varepsilon'$.) Taking the Burgess
  $\varepsilon=\varepsilon'/6$ gives $\ll\mathcal Lq^{-\varepsilon'/3}=o(1)$, uniformly in $j,j'$,
  the characters and the heights ($|\tau|\le2l\le\mathcal L$).
* *Why pointwise Abel summation is necessary.* Bounding by $\sup|S|\cdot(\|W\|_\infty+\operatorname{Var}W)$
  loses $(M_1/M_0)^{2/3}=q^{2(t_{k+1}-t_k)/3}$, fatal for cells wider than about $\varepsilon'$ (the
  code's cells have width $(2\gamma-t_0)/2000\approx8\cdot10^{-4}>\varepsilon'=5\cdot10^{-4}$).

Hence, with $m$ fixed,
$Q_2\le\sum_j\bigl(\sum_kh_ke^{-2\delta_jt_k}\frac{t_{k+1}^2-t_k^2}{2\delta_k}\bigr)a_j^2+\varepsilon_1(\sum_ja_j)^2$ for $q\ge q_0$.

**Lemma 3.5 (Burgess for nonprincipal characters, pointwise).** For $\varepsilon>0$ there is
$C_\varepsilon$ such that for every $q$, every nonprincipal $\psi$ mod $q$ and all real
$1\le N_0\le u$: $\bigl|\sum_{N_0\le m\le u}\psi(m)\bigr|\le C_\varepsilon q^{1/9+2\varepsilon}u^{2/3}$.

*Proof.* Let $\psi$ be induced by the primitive $\psi^*$ mod $q^*$ ($q^*>1$), and $P=\prod_{p\mid q,\,p\nmid q^*}p$.
Then $\psi(m)=\psi^*(m)\sum_{r\mid(m,P)}\mu(r)$, so the sum equals
$\sum_{r\mid P}\mu(r)\psi^*(r)\sum_{N_0/r\le m'\le u/r}\psi^*(m')$. Each inner sum runs over an
interval of length $\le u/r$; removing complete periods mod $q^*$ (each sums to $0$) leaves an
interval of length $\le\min(u/r,q^*)$, bounded by B ($k=3$; split off $m'=1$ if the interval
starts below $1$) by $\ll_\varepsilon q^{*1/9+\varepsilon}\min(u/r,q^*)^{2/3}\le q^{1/9+\varepsilon}u^{2/3}$.
There are $2^{\omega(P)}\le\tau(q)\ll_\varepsilon q^\varepsilon$ values of $r$. $\square$
(Lean: `burgessBound_of_primitive`.)

**Step 5 (assembly).** Adding Steps 3–4, $\Sigma_2\le\sum_j(D(\delta_j)-d_1+e_j)a_j^2+(d_1+3\varepsilon_1)(\sum a_j)^2=:B_a$,
and $B_a\ge\Sigma_2\ge0$. With Step 2, $(\sum a_jR_j)_+^2\le(I_B(s)+\varepsilon_1)B_a$. Choose
$\varepsilon_1\le\min(\eta'I_B(s),\eta'/3)$; then $(I_B+\varepsilon_1)B_a\le(1+\eta')I_B[\sum_j(D(\delta_j)-d_1+e_j)a_j^2+(d_1+\eta')(\sum a_j)^2]$,
because $B_a\ge0$ and $3\varepsilon_1\le\eta'$. $\blacksquare$

---

## 4. The response lemma

**Lemma 4.1 (responses).** Let $f$ be admissible, $\sigma_{\max}\ge0$, $K_0\in\mathbb N$, $\eta'>0$.
Put $\delta=\delta(f,\eta'/2)\in(0,1)$ from X3.2 and choose $M>0$ with
$A_f(\sigma_{\max})/M\le\eta'/(2\max(K_0,1))$ (F2). There is $q_0$ such that for $q\ge q_0$, every
nonprincipal $\chi$, every $\sigma\in[-\sigma_{\max},\sigma_{\max}]$, every $|\gamma|\le\mathcal L$
and every finite set $S$ of zeros of $L(s,\chi)$ in $\mathfrak D=\{\rho:|1+i\gamma-\rho|\le\delta\}$ with

* (i) every $\rho\in\mathfrak D\setminus S$ with $\lambda_\rho<\sigma$ satisfies $|\gamma\mathcal L-\mu_\rho|\ge M$, and
* (ii) the zeros $\rho\in\mathfrak D\setminus S$ with $\lambda_\rho<\sigma$ number at most $K_0$, with multiplicity,

the response $R(\chi,\gamma,\sigma)=-\mathcal L^{-1}\sum_n\Lambda(n)\operatorname{Re}(\chi(n)n^{-(1-\sigma/\mathcal L+i\gamma)})f(t_n)$
satisfies
$$R(\chi,\gamma,\sigma)\ \ge\ \sum_{\rho\in S}m_\rho\operatorname{Re}F\bigl((\lambda_\rho-\sigma)+i(\gamma\mathcal L-\mu_\rho)\bigr)-\frac{f(0)}6-\eta'.$$

*Proof.* The point $s=1-\sigma/\mathcal L+i\gamma$ lies in X3.2's region for $q\ge q_0(\sigma_{\max})$,
and $(s-\rho)\mathcal L=(\lambda_\rho-\sigma)+i(\gamma\mathcal L-\mu_\rho)=:z_\rho$. X3.2 with
$\varepsilon=\eta'/2$ and $\frac\varphi2f(0)\le\frac{f(0)}6$ gives
$R\ge\sum_{\rho\in\mathfrak D}m_\rho\operatorname{Re}F(z_\rho)-\frac{f(0)}6-\frac{\eta'}2$. Zeros of
$\mathfrak D\setminus S$ with $\lambda_\rho\ge\sigma$ have $\operatorname{Re}z_\rho\ge0$, hence
$\operatorname{Re}F(z_\rho)\ge0$ (Condition 2): drop them. Zeros of $\mathfrak D\setminus S$ with
$\lambda_\rho<\sigma$ have $\operatorname{Re}z_\rho\in[-\sigma_{\max},0)$ (nontrivial zeros have
$\lambda_\rho>0$) and $|\operatorname{Im}z_\rho|\ge M$ by (i), so $|F(z_\rho)|\le\eta'/(2K_0)$ by
(F2), and by (ii) their total is $\ge-\eta'/2$. The zeros in $S$ are kept with their
multiplicities. $\square$

*Remarks.* (a) The multiplicities $m_\rho$ are essential when a kept zero has $\lambda_\rho<\sigma$
(its term can be negative); PROOF.md §6.2 omits them (§9, A2). (b) The Lean
`GradedNear.response_lemma` counts in (ii) only zeros *not in* $S$ (a weaker hypothesis than
PROOF.md's "at most $K_0$ disc zeros with $\lambda_\rho<\sigma$"). (c) For the uses below,
$\sigma_{\max}=s_{\max}$, the largest anchor of any row ($s_{\max}=2.9$ covers the driver's menu).

---

## 5. Threshold form, normalization, binning

**Lemma 5.1 (threshold identity; two-test foundation §3; Lean `Near.common_threshold_iff`).** Let
$d>0$, $D_1,\dots,D_N>0$, $v\in\mathbb R^N$. The following are equivalent:

* (TT) $(\sum_ja_jv_j)_+^2\le\sum_jD_ja_j^2+d(\sum_ja_j)^2$ for all $a\in[0,\infty)^N$;
* (T) there is $\tau\in[0,\sqrt d]$ with $\sum_j(v_j-\tau)_+^2/D_j\le1-\tau^2/d$.

*Proof.* (T)⇒(TT): with $A=\sum a_j$, $\sum a_jv_j\le\sum_ja_j(v_j-\tau)_++\tau A$, and by
Cauchy–Schwarz in $\mathbb R^{N+1}$ this is
$\le\bigl(\sum(v_j-\tau)_+^2/D_j+\tau^2/d\bigr)^{1/2}\bigl(\sum D_ja_j^2+dA^2\bigr)^{1/2}\le(\sum D_ja_j^2+dA^2)^{1/2}$.
(TT)⇒(T): $J(\tau)=\tau^2/d+\sum(v_j-\tau)_+^2/D_j$ is convex, $C^1$ and coercive; at a minimizer
$\tau^*$, $J'(\tau^*)=0$ gives $\tau^*=d\sum a_j^*$ with $a_j^*=(v_j-\tau^*)_+/D_j\ge0$. Then
$\sum a_j^*v_j=\sum a_j^*(v_j-\tau^*)+\tau^*\sum a_j^*=J(\tau^*)=\sum D_ja_j^{*2}+d(\sum a_j^*)^2$,
and (TT) gives $J^2\le J$, i.e. $J(\tau^*)\le1$; moreover $\tau^*\ge0$ and $\tau^{*2}\le dJ\le d$. $\square$

(I checked $\min_\tau J=\sup_{a\ge0}\frac{(a\cdot v)_+^2}{a^TQa}$, $Q=\operatorname{diag}D+d\mathbf 1\mathbf 1^T$,
on 400 random instances; `checks2.py`.)

**Corollary 5.2 ((T) for kept zeros).** In the setting of Theorem 3.3, let each entry $j$ satisfy
the hypotheses of Lemma 4.1 with a kept set $S_j$, and put
$r_j=\sum_{\rho\in S_j}m_\rho\operatorname{Re}F((\lambda_\rho-s_j)+i(\gamma_j\mathcal L-\mu_\rho))-f(0)/6$.
Let $D_n>0$ be any normalizer and $N=\sqrt{(1+\eta')I_B(s)D_n}$. If $D_j^{+}\ge D(\delta_j)-d_1+e_j$
and $D_j^+>0$ for all $j$, then (T) holds for
$v_j=(r_j-\eta')/N$, diagonals $D_j^+/D_n$, radius $d=(d_1+\eta')/D_n$.

*Proof.* $a\ge0$ and $R_j\ge r_j-\eta'$ give $(\sum a_j(r_j-\eta'))_+\le(\sum a_jR_j)_+$; divide
Theorem 3.3 by $N^2$ and enlarge the diagonals to $D_j^+$; apply Lemma 5.1. $\square$

Note that only $D_j^+>0$ is needed, not positivity of the true numerator $D(\delta_j)-d_1+e_j$ (the
Lean `builder_threshold` assumes the latter; §9, A6). Entries with $v_j\le0$ contribute nothing
(since $\tau\ge0$) and entries may be omitted ($a_j=0$).

**Corollary 5.3 (the builders' normalization; Lean `GradedNear.builder_threshold`).** Let
$I_u\ge I_B(s)$, $D_u>0$, and for each entry a number $r_j$ with either $r_j\le$ its kept-zero main
term or $r_j\le0$, and $D_j^+\ge D(\delta_j)-d_1+e_j$, $D_j^+>0$. Then (T) holds for the **builder
quantities**
$$v_j^{\rm b}=\frac{r_j}{\sqrt{I_uD_u}}-\eta',\qquad D_j^{\rm b}=\frac{(1+\eta')D_j^+}{D_u},\qquad d^{\rm b}=(1+\eta')\Bigl(\frac{d_1}{D_u}+\eta'\Bigr).$$

*Proof.* Apply Corollary 5.2 with $\eta''=\eta'\min(1,\sqrt{I_BD_u},D_u)$ in place of $\eta'$ and
$D_n=D_u/(1+\eta'')$, so that $N^2=I_BD_u$. Then:
$v_j=\frac{r_j-\eta''}{\sqrt{I_BD_u}}\ge\frac{r_j}{\sqrt{I_BD_u}}-\eta'\ge v_j^{\rm b}$ if $r_j\ge0$ (as
$\eta''\le\eta'\sqrt{I_BD_u}$ and $I_u\ge I_B$), while $v_j^{\rm b}<0$ contributes nothing if $r_j<0$;
$D_j^{\rm b}\ge(1+\eta'')D_j^+/D_u$; $d^{\rm b}\ge(1+\eta'')(d_1+\eta'')/D_u$ (as $\eta''\le\eta'D_u$).
(T) is monotone: smaller features, larger diagonals and a larger radius preserve it (and
$\tau\le\sqrt{d}\le\sqrt{d^{\rm b}}$). $\square$

No relation between $D_u$ and $D(0)$ is needed. In code (`sieve_inputs.SieveNearTest`):
`feature`/`feature_at` $=v^{\rm b}$ with $r=F(\cdot)/f(0)-1/6$ (normalized $f(0)=1$), `diag_norm(δ)`
$=(1+\eta')(\texttt{diag\_up}(\delta)-d_1)/D_u$ with `diag_up`$\ge D(\delta)$, `gram()` $=(d^{\rm b},D^{\rm b}(0))$,
all rounded outward to the $10^{-16}$ grid; $\eta'=10^{-6}$.

**Lemma 5.4 (binning; Lean `Cert.near_row_of_bins`).** If entries satisfying (T) with
$(v_j,D_j,d)$ are assigned to LP columns and family terms so that each entry's feature is $\ge$ its
column's (or the column's is $\le0$), its diagonal $\le$ the column's, each family term $(n,v,D)$
receives $\ge n$ entries, and the row radius is $\ge d$, then the LP's near row holds at every
column vector $x\ge0$ with $x_c\le\#\{\text{entries binned to }c\}$ on positive-feature columns. The
proof is the monotonicity of (T).

---

## 6. The rows used (PROOF.md §6.5): actual-zero realization

### 6.1 Configuration hypotheses

A leaf is a set of zero configurations. For a configuration in the leaf, $q\ge q_0$:

* **(Z1)** $\lambda_1=\min\{\lambda_\rho:\rho\in R(l),\ L(\rho,\chi)=0,\ \chi\ne\chi_0\}\in[a,b]$. The
  **safe anchor** is $s_1=\lfloor a\rfloor_{1/50}\le a\le\lambda_1$, so (SA) holds.
* **(Z2)** The first family $\{\chi_1,\bar\chi_1\}$ ($n=2$ if $\chi_1$ is nonreal, else $n=1$), with
  $\rho_1$ of height $\gamma_1$; $\lambda'$ is the least parameter of another zero occurrence of
  $\chi_1$ in $R(l)$ (X pp. 21–22: $\rho'=\rho_1$ if $\rho_1$ is multiple; for real $\chi_1$ with
  nonreal $\rho_1$, $\bar\rho_1$ is excluded); the leaf gives $\lambda'\ge p$ or $\lambda'\in[p,p^{\rm hi}]$.
* **(Z3)** Every zero in $R(l)$ of a character outside the first family has $\lambda\ge\lambda_2\ge\ell_2$
  (`source_l2`); this is a premise of the zero-location component (inherited from 4.30).
* **(Z4)** $T^*\in[\frac12,1]$ is chosen by Lemma 6.1; each ordinary character $\chi$ (neither first
  family nor reserved) with a zero in $|\operatorname{Im}\rho|\le T^*$ has its **$T^*$ representative**
  $\rho_\chi$ = a zero of maximal real part among those with $|\operatorname{Im}\rho|\le T^*$;
  $x_i$ counts ordinary characters with $\lambda_{\rho_\chi}\in[\mathrm{lo}_i,\mathrm{hi}_i]$.
* **(Z5)** A reserved second family: $n_2$ characters (one real, or a conjugate pair) with common
  height-one representative parameter $\nu_2\in[\mathrm{lo}_2,\mathrm{hi}_2]$.
* **(Z6)** Inside: $|\mu_1|\le C_B$. Outside: $|\mu_1|>C_B$; hidden columns are, per first-family
  character, its rightmost zero $\rho_h$ in $R_P=\{\lambda\le C_P,|\mu|\le C_P\}$, $\lambda_h\in[\mathrm{lo}_h,\mathrm{hi}_h]$.
  $C_B>C_P+\max(M,M_2)$.

**Lemma 6.1 ($T^*$).** Let $s_{\max}$ bound every anchor, and let $K_0$ bound, uniformly in $q$, the
number of zeros (all characters mod $q$, with multiplicity) with $\lambda\le s_{\max}$ and
$|\operatorname{Im}\rho|\le2$. Such $K_0$ exists by LF: with $1-\sigma=s_{\max}/\mathcal L$, $T=2$,
$\sum_\chi N\le c_3(2q)^{c_4s_{\max}/\mathcal L}\le c_3e^{2c_4s_{\max}}$. If $\mathcal L>4M(K_0+1)$
there is $T^*\in[\frac12,1]$ with $\bigl||\operatorname{Im}\rho|-T^*\bigr|\ge M/\mathcal L$ for every such zero.
Consequently, for an ordinary $\chi$ with representative $\rho_\chi$ ($|\gamma_\chi|\le T^*$) and any
$\sigma\le\lambda_{\rho_\chi}$, $\sigma\le s_{\max}$: every zero $\rho$ of $\chi$ with
$\lambda_\rho<\sigma$ and $|\operatorname{Im}\rho|\le2$ satisfies $|\gamma_\chi\mathcal L-\mu_\rho|\ge M$.

*Proof.* The excluded set has measure $\le2MK_0/\mathcal L<\frac12$. If $\lambda_\rho<\sigma\le\lambda_{\rho_\chi}$
then $|\operatorname{Im}\rho|>T^*$ (maximality of $\rho_\chi$), hence $|\operatorname{Im}\rho|\ge T^*+M/\mathcal L$,
and $|\operatorname{Im}\rho-\gamma_\chi|\ge|\operatorname{Im}\rho|-|\gamma_\chi|\ge M/\mathcal L$. $\square$

The disc of Lemma 4.1 at height $|\gamma|\le1$ has radius $\delta<1$, so its zeros have height $<2$
and are counted by $K_0$; counting to height 2 (not $1+\delta$) avoids the circularity noted in
interface-closure §5.

### 6.2 The generic verification

For each entry below I give $(\chi,\gamma,\sigma,\delta=s-\sigma)$, the kept set $S$, the reason the
hypotheses (i)–(ii) of Lemma 4.1 hold, the resulting lower bound $r$ (so $R\ge r-\eta'$), and the
diagonal numerator. "No zero to the right" means every zero $\rho$ of $\chi$ in the disc has
$\lambda_\rho\ge\sigma$; then (i)–(ii) are vacuous. By Lemma 3.4 this holds whenever
$\sigma\le\lambda_1$ (heights $\le10l$). All heights are $\le l$, as Definition 3.2 requires. For
kept zeros with $\lambda_\rho\ge\sigma$, every term is $\ge0$, so multiplicities only help. In all
rows the sieve part is nonzero only in graded rows, which contain distinct characters only.

### 6.3 Entry catalogue

**(a) Ordinary character, bin $[\mathrm{lo},\mathrm{hi}]$** (every row). Entry $(\chi,\gamma_\chi,\sigma)$
with $\sigma=\min(\mathrm{lo},s)\le\mathrm{lo}\le\lambda_\chi$. $S=\{\rho_\chi\}$.
* If $\sigma\le\ell_2$ (family and shifted rows; graded rows with $s\le\ell_2$): no zero to the right,
  by (Z3) and Lemma 3.4.
* In general (graded rows with $s>\ell_2$): Lemma 6.1 gives (i), and $K_0$ gives (ii).

$r\ge m_{\rho_\chi}F(\lambda_\chi-\sigma)-\frac{f(0)}6\ge F(\mathrm{hi}-\sigma)-\frac{f(0)}6$ by (F1).
Diagonal numerator $D(s-\sigma)-d_1$; the builder uses $D(\lfloor s-\sigma\rfloor_{1/200})\ge D(s-\sigma)$
and omits the entry (feature $0$) if that numerator is $\le D_u/1000$.
Code: `graded_row` loop over `inp['rows']`: `lo>=s` → `feature(hi)`, diagonal `D`; else
`feature_at(hi,lo)`, `diag_norm(floor(s-lo))`; tail bin feature $0$.

**(b) First family, inside, one entry per character** (graded rows; family row for `rr` and
non-dz complex leaves; rc leaves outside the family row). Entries $(\chi_1,\gamma_1,\sigma)$ and, if
$n=2$, $(\bar\chi_1,-\gamma_1,\sigma)$, $\sigma=\min(a,s)\le\lambda_1$. $S=\{\rho_1\}$ (resp. $\{\bar\rho_1\}$,
a zero of $\bar\chi_1$). No zero to the right. $r\ge F(b-\sigma)-\frac{f(0)}6$. Diagonal
$D(s-\sigma)-d_1$. For rc in a row with sieve part, only one entry: kind 1. Code:
`_family_term(test, n, b, min(a,s), D)`.

**(c) rc conjugate pair** (family row, $s=s_1$, $H=0$, one $\mu$-range part). Entries
$(\chi_1,\pm\gamma_1,s_1)$, $\delta=0$, a controlled pair (same character, $\chi_1=\bar\chi_1$) with
$|y|=2|\mu_1|$. $S=\{\rho_1,\bar\rho_1\}$ for both; $\bar\rho_1$ lies in the disc because
$|\rho_1-\bar\rho_1|=2|\gamma_1|\le2C_B/\mathcal L$. No zero to the right. Equal multiplicities
(Lean `zmult_conj`), both terms $\ge0$:
$r\ge F(b-s_1)+R_{\rm lo}-\frac{f(0)}6$ with $R_{\rm lo}\le\inf\{\operatorname{Re}F(x+2i\mu):x\in[a-s_1,b-s_1],\mu\in[\mu_{\rm lo},\mu_{\rm hi}]\}$.
Excess $e=(c^{\rm hi}-d_1)_+$ with $c^{\rm hi}\ge\sup\operatorname{Re}G_1(-s_1+2i\mu)$ over the range.
The leaf is split $\mu_1\in[0,1]$, $[1,\infty)$ (by symmetry $\mu_1\ge0$). Enclosure
(`pair_bounds`): values at $x_0=\frac{a+b}2-s_1$ on a $\mu$-grid of step $\le1/50$ on
$[\mu_{\rm lo},\min(\mu_{\rm hi},10)]$; slack $\frac{h^2}8\cdot4\int t^2f$ and $\frac{b-a}2\int tf$
for $R_{\rm lo}$ (Lemma 1.1(7), valid as $x\ge0$), $\frac{h^2}8\cdot4\int t^2g_1e^{s_1t}$ for
$c^{\rm hi}$; for $\mu\ge10$, $R_{\rm lo}$ is replaced by $\min(R_{\rm lo},0)$ (Condition 2) and $c^{\rm hi}$
by $\max(c^{\rm hi},\text{tail at }u=20)$, the tail being Lemma 1.1(8) with an extra nonnegative term;
finally $\max(R_{\rm lo},0)$ is returned, valid since $x\ge0$. Family term $(2,v,D')$ with
$D'=(1+\eta')(D_u-d_1+(c^{\rm hi}-d_1)_+)/D_u$ (`pair_term`). Verifier: `mu_split` parts must be
exactly $[0,1],[1,\infty)$ and the range sits on the family row (`_verify_record`).

**(d) First family's second zero** (family row, $s=s_1$, $H=0$; complex type, finite gap
$\lambda'\in[p,p^{\rm hi}]$, $|y|=|\gamma_1-\gamma'|\mathcal L$ in one of $[0,1],[1,\frac32],[\frac32,2],[2,3],[3,5],[5,\infty)$).
Entries $(\chi_1,\gamma_1,s_1)$, $(\chi_1,\gamma',s_1)$, $(\bar\chi_1,-\gamma_1,s_1)$,
$(\bar\chi_1,-\gamma',s_1)$ where $\rho'=1-\lambda'/\mathcal L+i\gamma'$ is a zero of $\chi_1$ in
$R(l)$ with parameter $\lambda'$ (it exists in a finite-gap branch; $\bar\rho'$ is a zero of
$\bar\chi_1$), $|\gamma'|\le l$. Kept sets $\{\rho_1,\rho'\}$ and $\{\rho',\rho_1\}$ (conjugates for
$\bar\chi_1$), each zero kept only if it lies in the entry's disc. No zero to the right ($s_1\le\lambda_1\le\lambda'$).
$$r_{\gamma_1}\ge F(b-s_1)+R_p-\tfrac{f(0)}6,\qquad r_{\gamma'}\ge F(p^{\rm hi}-s_1)+R_q-\tfrac{f(0)}6,$$
$R_p\le\inf\operatorname{Re}F(x+iy)$ over $x\in[p-s_1,p^{\rm hi}-s_1]$, $R_q$ over $x\in[a-s_1,b-s_1]$,
$|y|$ in the piece. If the other zero is outside the disc, then $|y|\ge\delta\mathcal L/2-O(1)\ge10$,
i.e. the piece is $[5,\infty)$ where $R_p=R_q=0$ (`second_zero_bounds` returns $\max(\cdot,0)$ and
uses $\min(\cdot,0)$ on the tail), so the bound still holds. Pairs: $(\chi_1,\gamma_1)$–$(\chi_1,\gamma')$
and the conjugate pair are controlled pairs (kind 3) with excess $(c^{\rm hi}-d_1)_+$,
$c^{\rm hi}\ge\sup\operatorname{Re}G_1(-s_1+iy)$; cross pairs have quotient $\chi_1^2\ne\chi_0$ (kind 1),
bounded by $d_1$ because all zeros of $\chi_1^2$ have $\lambda\ge s_1$ (Lemma 3.4), even when $\chi_1$
is cubic. Double zero ($\rho'=\rho_1$, $y=0$): two identical vectors; $r\ge m_{\rho_1}F(\lambda_1-s_1)-\frac{f(0)}6\ge F(b-s_1)+R_p-\frac{f(0)}6$
since $m\ge2$, and $c^{\rm hi}$ on $[0,1]$ includes $y=0$ (Lean `keptBound_double`). Enclosures as in
(c) with curvature $\frac{h^2}8\int t^2f$ (no factor 4, since the variable is $y$) and tail at $u=10$.
Family terms $[(n,v_1,D'),(n,v_2,D')]$ (`second_zero_terms`).
*Exclusion on leaf 1285/0.* I recomputed the four family terms with the stored parameters
($\gamma=\frac{911}{848}$, $g_1=\frac{105}{89}$, $s=s_1=0.68$, $\lambda_1\in[.68,.6825]$,
$\lambda'\in[.975,1.06]$): $\min_{\tau\in[0,\sqrt d]}(\tau^2/d+\sum n(v-\tau)_+^2/D')=1.6007$,
$1.4534$, $1.2688$ on $y\in[0,1],[1,\frac32],[\frac32,2]$ and $0.8714$ on $[2,3]$, matching PROOF.md;
the stored certificates exclude the first three pieces in 2–3 boxes through the exact rule
(negative budget, nonnegative costs).

**(e) Shifted first family** (shifted row: $s=\min(1.9,p,\ell_2)$, used only if $s>s_1$ and $s\ge a$).
Entries $(\chi_1,\gamma_1,s)$ [and $(\bar\chi_1,-\gamma_1,s)$ if $n=2$], $\delta=0$. Zeros of $\chi_1$
with $\lambda<s$: only $\rho_1$, and $\bar\rho_1$ for type rc — every other occurrence has
$\lambda\ge\lambda'\ge p\ge s$. (For complex $\chi_1$, if $L(\bar\rho_1,\chi_1)=0$ with $\rho_1$
nonreal then $\bar\rho_1$ is another occurrence, so $\lambda_1=\lambda'\ge s$.) $S=\{\rho_1\}$ (+$\bar\rho_1$
for rc); (i)–(ii) hold with nothing left over. Terms: $F(\lambda_1-s)\ge F(b-s)$ by (F1), valid for
negative arguments; for rc $\operatorname{Re}F(\lambda_1-s+2i\mu_1)\ge-C_Z$ with
$C_Z=C(s-a)$ of Lemma 1.1(9) (zero if $s\le a$). With multiplicity $m$ (equal for $\rho_1,\bar\rho_1$):
$m(F+\operatorname{Re}F)\ge F(b-s)-C_Z$ whenever the right side is $\ge0$; otherwise the builder
feature is $<0$ and contributes nothing (Lean `keptBound_pair_neg_real`). Diagonal $D(0)-d_1$; no
correction because the Gram form sits at $s_1$. Code: `shifted_first_feature`; $C_Z$ from
`RigorousTest.C_upper`: adaptive cells on $\operatorname{Re}z=-d$, $|y|\le20$, curvature
$\frac{h^2}8\int t^2fe^{dt}$, tail Lemma 1.1(8) at $U=20$. Builder asserts $a\le s\le\min(\lambda'_{\rm lo},\ell_2)$.
The ordinary entries in this row have $\sigma\le s\le\ell_2$, so no strip argument is needed.

**(f) Reserved second family** (all rows except the old row). Entries $(\chi,\gamma_\chi,\sigma_2)$ for
its $n_2$ characters at their height-one representatives ($\nu_2\le\mathrm{hi}_2$),
$\sigma_2=\min(\max(a,\min(\ell_2,\mathrm{lo}_2)),s)$. Every zero of these non-first characters in
$R(l)$ has $\lambda\ge\max(\lambda_1,\lambda_2)\ge\max(a,\ell_2)\ge\sigma_2$, and zeros outside
$R(l)$ in the disc are far left: no zero to the right, no strip argument (which would not keep
$\nu_2\le\mathrm{hi}_2$). $r\ge F(\mathrm{hi}_2-\sigma_2)-\frac{f(0)}6$, diagonal $D(s-\sigma_2)-d_1$.
As LP columns (grid $1/400$): column $[l_j,r_j]$ uses $\sigma=\min(\max(a,\min(\ell_2,l_j)),s)$ and
feature at $r_j$; the configuration puts mass $n_2$ on the column containing $\nu_2$
(`_columns_for_second`).

**(g) Outside first family** (family row, $s=s_1$, $H=0$). Global entries $(\chi_1,\gamma_1,s_1)$ [and
$(\bar\chi_1,-\gamma_1,s_1)$], $|\gamma_1|\le l$, $S=\{\rho_1\}$, no zero to the right,
$r\ge F(b-s_1)-\frac{f(0)}6$. Hidden entries $(\chi_h,\gamma_h,s_1)$ for each first-family character
with an $R_P$ zero, $S=\{\rho_h\}$, $r\ge F(\mathrm{hi}_h-s_1)-\frac{f(0)}6$. Same-character pairs:
$|\mu_1-\mu_h|\ge C_B-C_P>M_2$, kind 2 with $e=0$ (Lean `pairExcess_eq_zero`); all other pairs
are distinct characters. Code: `graded_row(families='outside_first', hidden='outside')` (asserts
$s=s_1$, $H=0$).

**(h) Graded rows** ($s$ from the menu, e.g. $1.5,1.6,1.9,2.1,2.3$; $H\ne0$). Entries (a), (b), (f);
all characters distinct (first family: $\chi_1,\bar\chi_1$ once each; rc: one entry). Outside graded
rows carry only (a) and (f).

**(i) Large branch** ($\lambda_1\ge1.5$). $s=s_1=1.5$, $H=0$, only (a), with any one zero per
character of height $\le1$ (no zero to the right since $\lambda_1\ge1.5$). The certified row
(`published_single_inputs.make_large`, $\gamma_G=1.5$, $\gamma_Z=1$) is literally Theorem 3.3 with
$g_1=f_{2\gamma_G}$: $I_B=\int e^{st}f^2/g_1=R_B$, $D(0)=R_G$, $c_G=C(0)/R_G=0$, so its $(v,D,d)$
coincide with the builders' normalization.

### 6.4 Code correspondence (line-by-line check)

| PROOF.md §6.5 item | Generator | Checked |
| --- | --- | --- |
| Ordinary bins, anchor $\min(\mathrm{lo},s)$, diagonal $D(\lfloor s-\mathrm{lo}\rfloor_{1/200})$ | `leaf_driver.graded_row` (loop), `SieveNearTest.feature_at`, `diag_norm` | yes |
| Inside first family at $\min(a,s)$ | `_family_term(test,n,b,min(a,s),D)` | yes |
| rc pair, $\mu$-split | `pair_bounds`, `pair_term`, `graded_driver.RC_MU_SPLIT`, `_verify_record` | yes |
| Second zero, $y$-split | `second_zero_bounds`, `second_zero_terms`, `DZ_SPLIT`, asserts complex/inside/finite gap/$H=0$ | yes |
| Shifted row | `shifted_first_feature`, `C_upper`, `has_shifted` ($s>s_1$, $s\ge a$), builder asserts | yes |
| Reserved family anchor rule | `graded_row(sec_anchor='l2')`, `_columns_for_second` | yes |
| Outside global + hidden | `graded_row(families='outside_first', hidden='outside')` | yes |
| Old two-test row | `graded_leaves.old_row` (2-tuple family term takes the row's $D$) | yes (§7.4) |
| Sieve cells, levels, $\varepsilon'=1/2000$, $t_0>1/3+2\varepsilon'$ | `SieveNearTest.__init__` | yes |
| $I_u\ge I_B$ (upper Riemann sums, 2000+2000 cells, monotonicity of $f$, $g_1$, exponentials, factor $1+2^{-40}$) | `SieveNearTest.__init__` | yes; my mpmath check on one graded row: $I_B=1.03962$, $I_u=1.04148$; $D_u=D(0)$ to 12 digits; `diag_up`$\ge D(\delta)$ at three offsets (`check_IB.py`) |

Corpus census (my scan of the three 3.99 corpora, `scan_rows.py`): inside rows — family 2029
($\mu$-ranges in 230 rows of 115 roots; $y$-ranges in 648 rows), shifted 3120, graded 7052, old 37
(exactly roots 10, 11, 15–18, 20–36, 1198–1201, 1212–1215, 1218, 1219, 2603, 2608, 2613, 2633);
identities nodes — family 87 (60 with $y$-ranges), shifted 322, graded 918; outside — family 1642,
graded 1672. Every family and shifted row has $\mu=10^9$ (so $H=0$) and $g_1>\gamma$ (so (W) holds
through $g_1$ alone); every graded row has $t_0\ge0.33735>\frac13+2\varepsilon'$. Parameter
ranges: graded $\gamma\in[0.894,0.983]$, $g_1\in[1.343,2.888]$, $\mu\in[0.005,0.042]$,
$s\in[1.5,2.3]$; family $\gamma\in[0.853,1.529]$; shifted $s\in[0.7225,1.9]$; $s_1\in[0.1,1.48]$.

---

## 7. The inherited two-test row (PROOF.md §6.6)

This row is not an instance of Theorem 3.3: its Gram form sits at the (possibly unsafe) shift $s$
and pays explicit exceptional-quotient corrections. It is X's proof of Lemma 5.3 ((5.34)–(5.40),
pp. 72–76) with two tests and nonnegative weights.

### 7.1 Single test

**Setting.** An inside leaf: (Z1)–(Z3), (Z5); $s\le\min(p,\ell_2)$ (the code takes
$s=\min(1.9,p,\ell_2)$, with $p$ the gap's lower end when a gap is given). Tests
$f=f_{2\gamma_Z}$, $g=f_{2\gamma_G}$ with $\gamma_G>\gamma_Z$ (so $g>0$ on $\operatorname{supp}f$; any
positive scaling is irrelevant). Put
$$R_G=G(-s),\quad R_B=\int_0^{2\gamma_Z}\frac{f^2}{g}e^{st}dt,\quad N=\sqrt{R_GR_B},\quad
C_G=\sup_{\operatorname{Re}z\ge a-s}(-\operatorname{Re}G(z)),\quad C_Z=\text{same for }F,$$
$d_0=g(0)/(6R_G)$, $c_G=C_G/R_G$, $k=1+\eta$. Features
$$v(\lambda)=\frac{F(\lambda-s)-f(0)/6}N-\eta,\quad v_f=\frac{F(b-s)-\kappa f(0)/6-E\,C_Z}N-\eta,\quad v_2=\frac{F(\mathrm{hi}_2-s)-\kappa_2f(0)/6}N-\eta,$$
$\kappa=\frac34$ for real $\chi_1$ and $1$ otherwise, $E=1$ exactly for type rc, $\kappa_2=\frac34$ iff
$n_2=1$. Diagonals ($d=k(d_0+\eta)$):

| type | $D_o/k$ | $D_f/k$ |
| --- | --- | --- |
| rr | $1-d_0+c_G$ | $1-d_0$ |
| rc | $1-d_0+2c_G$ | $1-d_0$ |
| complex | $1-d_0+2c_G$ | $1-d_0+c_G$ |

**Theorem 7.1 (two-test near inequality).** For $q\ge q_0$ and every configuration of the leaf,
take as entries: every ordinary character at any one of its zeros of height $\le1$ (anchor $s$), the
$n$ first-family characters at $(\chi_1,\gamma_1)$, $(\bar\chi_1,-\gamma_1)$, and the $n_2$ reserved
characters at their height-one representatives. Then (TT) holds with each ordinary feature
$\ge v(\lambda_\chi)$, diagonal $D_o$; first-family features $\ge v_f$ (or the feature is replaced by
$0$ if $v_f<0$), diagonal $D_f$; reserved features $\ge v_2$, diagonal $D_o$; radius $d$. By Lemma
5.1, (T) holds.

*Proof.* Put $\sigma=1-s/\mathcal L$, $A_j(n)=\sqrt{\Lambda(n)n^{-\sigma}g(t_n)}\,\chi_j(n)n^{-i\gamma_j}$ and
$B(n)=\chi_0(n)\sqrt{\Lambda(n)n^{-\sigma}}f(t_n)/\sqrt{g(t_n)}$ (zero off $\operatorname{supp}f$).

*Responses.* $\langle A_j,B\rangle=\sum_n\Lambda(n)\chi_j(n)n^{-(\sigma+i\gamma_j)}f(t_n)$, so
$-\operatorname{Re}\langle A_j,B\rangle=\mathcal L R_j$ with $R_j$ the response of $(\chi_j,\gamma_j)$ at
anchor $s$. Apply Lemma 4.1 (i.e. X3.2). Ordinary and reserved characters: every zero in the disc has
$\lambda\ge s$ (in $R(l)$: $\lambda\ge\lambda_2\ge\ell_2\ge s$ by (Z3); outside $R(l)$: far left, as
in Lemma 3.4), so keep the chosen zero and drop the rest: $R_j\ge F(\lambda_\chi-s)-\frac{\varphi}2f(0)-\varepsilon$.
First family: the zeros of $\chi_1$ with $\lambda<s$ are $\rho_1$ (and $\bar\rho_1$ for rc) — the
others have $\lambda\ge\lambda'\ge p\ge s$; keep them (both lie in the disc, the zero being inside):
$F(\lambda_1-s)\ge F(b-s)$ by (F1) and $\operatorname{Re}F(\lambda_1-s+2i\mu_1)\ge-C_Z$ (Lemma 1.1(9)).
For real characters $\varphi(\chi)=\frac14$ (order $2\le\mathcal L$; X p. 17), which gives
$\kappa=\kappa_2=\frac34$. Hence $R_j\ge N(v_j+\eta)-\varepsilon$ with $v_j$ the listed feature, and for
$a\ge0$: $\mathcal L\sum_ja_jR_j=-\operatorname{Re}\langle\sum a_jA_j,B\rangle\le\|\sum_ja_jA_j\|\,\|B\|$
(X (5.35)–(5.36)).

*Norms.* $\|B\|^2=\sum\Lambda(n)\chi_0(n)n^{-\sigma}f^2/g=\mathcal LR_B(1+o(1))$ by X3.1 applied to
$f^2/g$ (Condition 1: $f^2/g$ is $C^2$ on $[0,2\gamma_Z)$ with bounded second derivative and vanishes
to order $6$ at $2\gamma_Z$; two-test foundation §3). Diagonal Gram entries $\|A_j\|^2=\mathcal LR_G(1+o(1))$ (X3.1).

*Off-diagonal entries.* $\langle A_j,A_k\rangle$ is the $g$-sum for $\psi=\chi_j\bar\chi_k\ne\chi_0$
(each character enters once) at $\sigma+i(\gamma_j-\gamma_k)$, height $\le2$ for ordinary/reserved
pairs and $\le1+C_B/\mathcal L$ with the first family. By X3.2: if $\psi\notin\{\chi_1,\bar\chi_1\}$,
every disc zero has $\lambda\ge s$ (in $R(l)$ by (Z3), outside $R(l)$ far left), so all zeros drop and
$\operatorname{Re}\langle A_j,A_k\rangle\le\mathcal L(d_0R_G+\varepsilon)$.
If $\psi=\chi_1$ (or $\bar\chi_1$), the disc zeros with $\lambda<s$ are $\rho_1$ (resp. $\bar\rho_1$),
and for rc also the conjugate; each contributes $\le C_G$. Graph count (X p. 75): an ordinary vertex
has at most one exceptional neighbour if $\chi_1$ is real ($\chi_k=\chi_j\chi_1$) and two if not; a
real first-family vertex has none ($\chi_1\bar\chi_k=\chi_1$ forces $\chi_k=\chi_0$); a nonreal one
has at most one ($\chi_k=\chi_1^2$). With $2a_ja_k\le a_j^2+a_k^2$ per exceptional edge, the
exceptional corrections give the $c_G$ terms of the table (rc: one edge carrying two zeros).

*Assembly.* $\|\sum a_jA_j\|^2\le\mathcal LR_G[\sum_ja_j^2(1-d_0+\mathrm{exc}_j)+(d_0+\eta)(\sum a_j)^2]$
for $q\ge q_0$ and $a\ge0$; multiply by $\|B\|^2/\mathcal L^2N^2\le1+\eta$. Errors are uniform
(finitely many tests; $o(1)$ per entry absorbed by $-\eta$ in the features, pair errors by the
$\eta(\sum a)^2$ term). For rc the kept first-family term is $m(F+\operatorname{Re}F)$ with equal
multiplicities; if $F(b-s)-C_Z<0$ the feature is clamped to $0$. $\square$

### 7.2 Detector mixture (near-refinements §3)

Replace $f$ by $f_\epsilon=f+\epsilon g$, $\epsilon\ge0$ (stored as `mix`$=t$, $\epsilon=t(\gamma_Z/\gamma_G)^5$
in the unnormalized scaling). $f_\epsilon$ is admissible (sum of admissible functions), and on
$[0,2\gamma_G)$: $f_\epsilon^2/g=f^2/g+2\epsilon f+\epsilon^2g$, a sum of Condition-1 functions, so
$\|B_\epsilon\|^2=\mathcal L(R_B+2\epsilon F(-s)+\epsilon^2R_G)(1+o(1))$ and
$N_\epsilon^2=R_G(R_B+2\epsilon F(-s)+\epsilon^2R_G)$. Features use $F+\epsilon G$ and
$f(0)+\epsilon g(0)$; the rc correction becomes $C_Z+\epsilon C_G$ (since
$-\operatorname{Re}(F+\epsilon G)\le C_Z+\epsilon C_G$ on $\operatorname{Re}z\ge a-s$). The Gram part
($d,D_o,D_f$) is unchanged. Code: `extension_enclosures.mixfeature`, `mixnorm`, `mixrows`.

### 7.3 Paired first family (near-refinements §4; nonreal $\chi_1$, $\lambda'\in[p,h]$)

Use for $\chi_1$ the averaged vector $A_f=\frac12(A_{\chi_1,\gamma_1}+A_{\chi_1,\gamma'})$ ($\rho'$ as in
(Z2)) and its conjugate for $\bar\chi_1$ (still $n=2$ coordinates). With $\Delta=(\gamma_1-\gamma')\mathcal L$:
$$P=\frac{\operatorname{Re}G(-s+i\Delta)}{R_G},\qquad Q=\frac{\operatorname{Re}F(\lambda_1-s+i\Delta)+\operatorname{Re}F(\lambda'-s+i\Delta)}{2N}.$$
*Feature.* Half the sum of the responses at $\gamma_1$ and $\gamma'$, each keeping both zeros
(X Lemma 3.4 permits zeros outside the disc with negligible error, and $\rho_1$ is the only zero of
$\chi_1$ with $\lambda<s$): $\ge\frac{F(b-s)+F(h-s)}{2N}-\frac{f(0)}{6N}+Q-\eta$ (multiplicity: a double
zero gives the same bound).
*Diagonal.* $\|A_f\|^2/(\mathcal LR_G)=\frac{1+P}2+o(1)$ (X3.1 at heights $0$ and $\Delta/\mathcal L$,
$|\Delta|/\mathcal L\le2l$); off-diagonal entries are averages of two admissible entries, so the
same bounds hold; averaging creates no new quotient characters.
*Removing the unknown correlation.* Fix $\zeta>0$ and a bound
$P-\zeta Q\le\mathcal B$ (5) for all $\Delta\in\mathbb R$, $\lambda_1\in[a,b]$, $\lambda'\in[p,h]$.
Since $\lambda'\ge s$, $Q\ge-C_Z/(2N)$; take $e\ge C_Z/(2N)$, $U=Q+e\ge0$,
$m=\frac{F(b-s)+F(h-s)}{2N}-\frac{f(0)}{6N}-\eta-e$, $D_*=k\{\frac{1+\mathcal B}2-d_0+c_G-\frac{\zeta e}2\}$,
$\kappa_*=k\zeta/2$. Then the actual feature is $\ge m+U$ and the actual diagonal is $\le D_*+\kappa_*U$.
If (7) $D_*>0$ and $2D_*\ge\kappa_*\max(m,0)$, then for all $U,\tau\ge0$:
(8) $\frac{(m+U-\tau)_+^2}{D_*+\kappa_*U}\ge\frac{(m-\tau)_+^2}{D_*}$ (derivative
$\frac{(z+U)(2D_*-\kappa_*z+\kappa_*U)}{(D_*+\kappa_*U)^2}\ge0$ with $z=m-\tau\le m$). So (T) with the
actual $(m+U,D_*+\kappa_*U)$ implies (T) with $(m,D_*)$ at the same $\tau$. The bound $\mathcal B$ is
certified (`correlation_bound`) on the grid $\Delta=j/200$, $0\le\Delta\le30$, at the four corners
$(\lambda_1,\lambda')\in\{a,b\}\times\{p,h\}$, plus $\frac{M_\Delta}{8\cdot200^2}$ in $\Delta$ with
$M_\Delta=\frac{M_{g,2}(s)}{R_G}+\frac{\zeta}{2N}(M_{f,2}(s-a)+M_{f,2}(s-p))$,
$M_{f,2}(x)=\int t^2fe^{\max(x,0)t}$, and $\frac{\zeta}{2N}(\frac{(b-a)^2}8M_{f,2}(s-a)+\frac{(h-p)^2}8M_{f,2}(s-p))$
in the real parts (sequential interpolation: first in $\Delta$ at fixed real parts, then in the
separable real parts at grid $\Delta$; no mixed derivative is needed), and the closed-form tail for
$|\Delta|\ge30$ (Lemma 1.1(8) for $G$ and both signs for $F$).
(7) is asserted in `paired_first`. I checked (8) on $2\cdot10^4$ random instances.

### 7.4 The row in the graded LP; claims of PROOF.md §6.6

The LP row (`graded_leaves.old_row`) is the repository constraint divided by $D=D_o$:
$$\exists\tau\in[0,\sqrt d]:\ \sum_ix_i\frac{(V_i-\tau)_+^2}{D}+n\frac{(v_f-\tau)_+^2}{D_f}+n_2\frac{(v_2-\tau)_+^2}{D}\le1-\frac{\tau^2}d,$$
with $V_i=v(\mathrm{hi}_i)$ (`rows[i][4]`), all negative features replaced by $0$.

* **Representatives.** The LP counts ordinary characters by $T^*$ representatives. Theorem 7.1
  allows any one zero of height $\le1$ per ordinary character, all zeros being left of $s$ (Z3), so
  the $T^*$ representative in bin $i$ gives feature $\ge V_i$. $T^*$ representatives are at least
  the height-one ones, hence $\ge$ `ordinary_lower`, so the bins cover them. **Correct.**
* **Reserved family.** Its fixed term uses $v_2$ at $\mathrm{hi}_2$; $F$ decreases, so $v_2$ bounds the
  feature on the whole range; the second-family columns carry feature $0$ in this row
  (`_vs` default), so nothing is double counted. The 2-tuple family term gets the row's $D=D_o$,
  which is the correct diagonal (the reserved characters are ordinary vertices of the graph).
  **Correct.**
* **Clamping.** Features enter only via $(v-\tau)_+$ with $\tau\ge0$. **Exact.**
* **Variants used.** From the 4.30 root records: roots 10, 11, 15–18, 20–36, 1198–1201, 1212–1215
  single; 1218, 1219 mixture ($t=86149/500000$); 2603, 2608, 2613 pair; 2633 single and pair.
  All paired uses are complex (the code also admits kind `rc` with $\rho'=\bar\rho_1$, which
  near-refinements §4 does not derive; unused here).
* The row is used only on inside leaves (`_row_set` returns `None` for `O` outside).

---

## 8. Parameters and rigorous enclosures

* **Tests.** Detector $f_{2\gamma}$, Gram test $f_{2g_1}$, normalized, rational $\gamma,g_1$.
* **Safe anchor** $s_1=\lfloor50a\rfloor/50$ (`leaf_driver.safe_anchor`).
* **Family row** (`family_row.propose`): $s=s_1$; Nelder–Mead in $(\gamma,g_1)$ minimizing the
  floating number of characters the row allows at $\lambda_3$ given the fixed families;
  $\gamma$ rationalized to denominator $\le1000$, $g_1\ge\gamma+\frac1{1000}$, $t_0=\frac{34}{100}$,
  $\mu=10^9$ (so $H\equiv0$).
* **Shifted row** (`family_row.propose_shifted`): the same objective at $s=\min(1.9,p,\ell_2)$.
* **Graded rows** (`propose_params.params(s1,s)`): Nelder–Mead in $(\gamma,g_1,t_0,\log_{10}\mu)$
  minimizing $\log\sum$ of floating crowd bounds $D/(v^2-d)$ at $\lambda=s+.005,s+.1,s+.2,s+.3$,
  subject to $0.3\le\gamma\le2.5$, $0.1\le g_1\le3$, $\frac13+.004<t_0<2\gamma-.05$, $2g_1\ge t_0+.01$;
  $t_0\leftarrow\max(t_0,0.336)$. Reference anchors from the stages $\{1.9\}$, $\{1.5,1.9,2.3\}$,
  $\{1.6,2.1\}$ and the menu $1.1,1.3,\dots,2.9$ (spacing $\ge0.15$).
* **Sieve heights** (water filling): $2000$ equal cells on $[t_0,2\gamma]$,
  $\delta_k=\frac{t_k-1/3}2-\frac1{2000}$, $\kappa_k=\frac{t_{k+1}^2-t_k^2}{2\delta_k(t_{k+1}-t_k)}$,
  $h_k=\bigl(e^{sm_k}f(m_k)/\sqrt{\mu\kappa_k}-g_1(m_k)e^{s_1m_k}\bigr)_+$ at midpoints $m_k$, rationalized
  (denominator $\le10^{12}$). This makes $\omega\approx\max(g_1e^{s_1t},e^{st}f/\sqrt{\mu\kappa})$,
  the Cauchy–Schwarz-optimal shape.
* **Grids.** Bins $1/\mathrm{den}$ ($\mathrm{den}\in\{200,400,500,800,2000\}$), offsets
  $\lfloor\cdot\rfloor_{1/200}$, reserved-family columns $1/400$, rc $\mu$-grid and $y$-grid step
  $\le1/50$.
* **Enclosures.** All floating proposals are discarded after rationalization; `SieveNearTest`
  recomputes $I_u$, $D_u$, `diag_up`, features and special terms with outward interval arithmetic
  and rounds to $10^{-16}$ in the safe direction. The Lean row checker (`RowCheckCore.rowCheck`,
  run natively) recomputes $I_L\ge I_B$, $D(\delta)$, transforms and special terms from the rational
  parameters and verifies every stored feature, diagonal and radius for all 13,528 rows with
  metadata (inside) and 3,314 rows (outside); $I_u$ exceeds $I_L$ by $\approx9\cdot10^{-13}$
  relative. The 37 old rows are not covered by it.

---

## 9. HOLES AND CONCERNS

Severity: **blocking** = the claim does not follow; **major** = a real gap or unverified premise
that must be closed for the paper; **minor** = wording, citation or a hypothesis that is stronger
or weaker than stated but harmless.

**A. The graded near lemma and its proof**

* **A1 (minor; citation).** PROOF.md §6.3 cites "X Lemma 5.2; H Lemma 2.1 with $k=3$" for the pointwise bound
  $|\sum_{M_0\le m\le u}\psi(m)|\ll u^{2/3}q^{1/9+\varepsilon}$. X Lemma 5.2 (pp. 67–68) is a bound
  for $\sum_{n\le T}\chi(n)n^{-s}$ at $\operatorname{Re}s=1-1/k$, not a character-sum bound. The
  correct source is H Lemma 2.1 ($k=3$; primitive $\chi$, $N\ge1$, $1\le H\le q$) plus the reduction
  of Lemma 3.5 (Möbius over primes of $q$ not dividing the conductor, periodicity). Fix: cite H
  Lemma 2.1 and Burgess (1963), and include Lemma 3.5.
* **A2 (minor).** The response lemma in PROOF.md §6.2 omits the multiplicities $m_\rho$ of kept
  zeros; §6.4 and Lean include them. With a kept zero to the right of the anchor (shifted row),
  dropping multiplicity is not justified. Fix: state Lemma 4.1 as above.
* **A3 (minor).** "Assume $\omega>0$ on $\operatorname{supp}f$" (PROOF.md §6.1) does not make the
  first-factor integrand bounded (a one-sided limit of $\omega$ can vanish at a cell end). Needed:
  (W), a uniform positive lower bound, which the code asserts per cell and Lean assumes
  (`omega_lb`); in all stored rows $g_1>\gamma$, so it holds through $g_1$ alone.
* **A4 (minor).** "All test and Gram points ... lie inside X Lemma 3.4's region $R(9l)$": Gram
  points with $\sigma_{jk}<0$ have real part $>1$ and are not in $R(9l)$. The argument only needs X3.2
  (whose region is two-sided) and X3.3 (Lemma 3.4 here). Fix: rephrase as in §3.4 Step 3.
* **A5 (minor; missing citation).** "$K_0$ is $O(1)$ by a log-free density estimate" has no
  reference. Fix: X Prinzip 3 (p. 11), or Jutila's Theorem 1 as quoted on H p. 26 (pp), or
  Thorner–Zaman Theorem 1.2 (explicit); count all characters mod $q$, with multiplicity,
  $\lambda\le s_{\max}$, height $\le2$.
* **A6 (minor; Lean vs informal).** Lean's `builder_threshold`/`graded_near_threshold` require the
  *true* diagonal numerators $D(\delta_j)-d_1+e_j$ to be positive; hence the "finding" in
  near-rows-formalization §4 (positivity tested at the rounded offset). Mathematically only the
  positivity of the builder's upper bound $D_j^+$ is needed (Corollary 5.2), so no certificate was
  ever at risk, and the informal proof should say so.
* **A7 (minor).** PROOF.md uses the prime number theorem for the first factor; Mertens'
  estimate with upper Riemann sums suffices (and is what Lean uses).
* **A8 (minor).** PROOF.md defines kind 2 with the constant $M$ of §10 but the theorem needs
  $|G_1(-\sigma+iY)|\le d_1$ for $|Y|\ge M_2$ over all $\sigma=s_1-\delta-\delta'$, $\delta,\delta'\in\Delta$;
  PROOF.md §10 only imposes $|G_1(-\sigma+iY)|\le\eta'/4$ with "$\sigma$" unspecified. Fix: quantify
  $\sigma$ over the finite set of Gram shifts. Harmless in the corpus (kind 2 occurs only with
  $\delta=0$).
* **A9 (minor).** "Each entry lies in at most one controlled pair" should be part of the definition
  of $e_j$ (true in every row).

**B. Rows and their realization**

* **B1 (minor; scope, not a gap).** The zero-level configuration of each row (which zeros each
  entry keeps, their locations, the $T^*$ choice, separations, counts: Lean `RowZero`) is a
  hypothesis of the Lean chain `checked_leaf_rows_gives_prime`. §6 above supplies the informal
  proof for every row type; it is not formalized.
* **B2 (minor).** The shifted row's requirement $a\le s$ is a condition checked by the driver
  (`has_shifted`) and the builder's assertion, not a consequence of the shift rule (node 1501/1).
  PROOF.md states it correctly after review 11.
* **B3 (minor).** The second-zero entries need a zero $\rho'$ with parameter $\lambda'\in[p,p^{\rm hi}]$,
  which is part of the finite-gap branch's case hypothesis (source cover); if $\rho'$ lies outside
  the entry's disc, the piece $[5,\infty)$ is the only one that can contain $y$ and its enclosures
  use $0$ for the missing term. Both points should be stated in the paper (PROOF.md mentions the
  second).
* **B4 (major, for the paper's completeness; not a mathematical error).** The premise (Z3) — that
  `source_l2` bounds the global $\lambda_2$, and that every zero of a non-first character in $R(l)$
  has $\lambda\ge\ell_2$ — is used by the shifted row, the reserved-family anchor rule, the
  ordinary entries of family/shifted rows and the whole two-test row. It belongs to the zero-location
  component and must be proved there (review 11 records it as a shared premise).

**C. Literature interface**

* **C1 (minor; citation hygiene).** The repository's H page numbers ("H p. 14", "p. 24", "p. 38") are
  pages of the author's preprint, not of PLMS 64 (1992) 265–338; the Lean docstrings mix PLMS pages
  (Condition 1 "p. 280", Condition 2 "p. 286", taken from X) with preprint pages (Lemma 2.1 "p. 7",
  Lemma 5.2 "p. 24"). The offset is not constant (about $+258$ to $+260$ early, about $+247$ in §11 per
  X's own citations). Fix: cite the published pages throughout (lookup needed), or cite by lemma and
  equation number only.
* **C2 (minor).** H's printed Lemma 5.2 omits the factor $\Lambda(n)$ (misprint); cite X Lemma 3.2,
  which has it.
* **C3 (minor).** Condition 2 for the parabolic test: PROOF.md calls $f_\gamma$ "admissible" without
  proof; supply Lemma 1.1(5) (X Lemma 3.6 with X Lemma 3.5, or the closed form of $\operatorname{Re}F(iy)$).

**D. The inherited two-test row**

* **D1 (major for verification scope).** It has no Lean row checker. Its numbers ($d$, $D$, $D_f$,
  $v_f$, bin features, $v_2$, the mixture norm, the paired bound $\mathcal B$ and condition (7)) are
  enclosed only by the 4.30/4.33 Python code (`published_single_inputs`, `two_test_enclosures`,
  `extension_enclosures`), and the (TT) derivation is repository work (two-test foundation §3,
  near-refinements §§3–4) with human-free reviews only. I re-derived all three variants (§7) and
  found them correct; an independent enclosure check of the 37 rows' inputs would close the gap.
* **D2 (minor).** The paired variant is derived only for nonreal $\chi_1$; the code also accepts
  kind `rc`. Unused at 3.99; the paper should restrict the statement.
* **D3 (minor).** PROOF.md §6.6 writes "roots 10–36"; the fallback roots are 10, 11, 15–18,
  20–36 (23 roots); the total of 37 is right.
* **D4 (minor).** PROOF.md §6.6's displayed threshold form is correct, but the reserved second
  family's diagonal in that row is $D=D_o$, not a separate constant; say so explicitly.

**E. PROOF.md §6 versus the Lean statements (all harmless; listed as requested)**

1. Pair excess: Lean uses the exact $e_j=\sum_{k\ne j,\chi_k=\chi_j}(\operatorname{Re}G_1(-\sigma_{jk}+iy_{jk})-d_1)_+$
   over all same-character partners (any offsets); PROOF.md uses constants $c^{\rm hi}$ for
   $\delta=0$ pairs and $0$ for separated pairs. PROOF.md's form follows from Lean's plus
   `pairExcess_eq_zero`.
2. Heights and the safe anchor: Lean assumes $|\gamma_j|\le T\le\mathcal L/3$ and the zero-free
   statement `SafeAnchor q s₁ (2T+1)` for all zeros; PROOF.md assumes (SA) on $R(l)$ only. The
   bridge is Lemma 3.4 (X Lemma 3.3), which PROOF.md invokes only in passing.
3. Lean's `NearData.Valid` requires (W) (`omega_lb`) and $I_B>0$; PROOF.md requires only
   "$\omega>0$ on $\operatorname{supp}f$" (A3).
4. Response lemma: Lean's count hypothesis is on zeros outside $S$ (weaker); Lean has multiplicities (A2).
5. Lean's threshold theorems require positivity of the true diagonal numerators (A6).
6. Lean lets each row have its own $M_k$, $\delta_k$; the informal proof uses one $M$ (take the
   maximum over the finitely many rows).
7. Lean's first factor uses Mertens (A7).
8. The zero-level realization of every row (`RowZero`) is a hypothesis of the Lean chain (B1); §6
   gives its informal proof.

**No blocking issue was found.**

---

## 10. References

* D. A. Burgess, On character sums and $L$-series. II, Proc. London Math. Soc. (3) 13 (1963) 524–536.
* S. W. Graham, An asymptotic estimate related to Selberg's sieve, J. Number Theory 10 (1978) 83–94.
* D. R. Heath-Brown, Zero-free regions for Dirichlet $L$-functions, and the least prime in an
  arithmetic progression, Proc. London Math. Soc. (3) 64 (1992) 265–338 (Lemmas 2.1, 2.5, 3.1, 4.1,
  5.2, 5.3, 6.1; Conditions 1–2; §11 (11.6), (11.13); Lemma 12.1; §16 item 9).
* M. Jutila, On Linnik's constant, Math. Scand. 41 (1977) 45–62 (Theorem 1, as quoted by H).
* H. L. Montgomery, R. C. Vaughan, *Multiplicative Number Theory I*, CUP 2007 (Mertens).
* Y. Motohashi, On a density theorem of Linnik, Proc. Japan Acad. 51 (1975) 815–817 (precedent:
  sieve-weighted large sieve, Lemma 3).
* J. Thorner, A. Zaman, An explicit version of Bombieri's log-free density estimate and Sárközy's
  theorem for shifted primes, arXiv:2208.11123 (Theorem 1.2).
* T. Xylouris, Über die Nullstellen der Dirichletschen $L$-Funktionen und die kleinste Primzahl in
  einer arithmetischen Progression, Bonner Math. Schriften 404 (2011) (Prinzip 3 p. 11; Bedingungen
  1–2 pp. 17–18; Lemmas 3.1–3.6 pp. 18–22; (3.11)–(3.12) and $\rho'$ pp. 21–22; p. 36; Lemmas 5.1–5.3
  pp. 66–76).
