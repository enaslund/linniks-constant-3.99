# Deep dive: leaf LPs and exact certificates (PROOF §7), exterior regimes (§9), join and uniformity (§10), error allowance (§2)

Date: 2026-09-30. Scope: the components of `research/PROOF.md` §§7, 9, 10 and the
`final = 5η` allowance of §2, written up for the paper and checked against the code,
the Lean formalization (`lean-graded/`) and the printed sources.

**Conventions.**
* $q$ is the modulus, $\ell=\log q$, zeros are $\rho=1-\lambda/\ell+i\mu/\ell$, counted with
  multiplicity. $R(x)=\{1-\log\log\ell/(3\ell)\le\sigma\le1,\ |t|\le x\}$ (X (3.7)),
  $l=l(q)$ as in X Lemma 3.3, $R_P=\{\lambda\le C_P,|\mu|\le C_P\}$,
  $R_B=\{\lambda\le C_B,|\mu|\le C_B\}$.
* $\eta=\eta'=10^{-6}$. Integer scales $S=10^{16}$ (data), $T_S=10^{6}$ (threshold ticks),
  $D_S=10^{12}$ (duals), $H_S=S/(2T_S)=5\cdot10^{9}$.
* **Sources and pages.** X = Xylouris, dissertation (Bonner Math. Schriften 404, 2011); its
  printed page numbers coincide with the PDF pages of the retained copy. H = Heath-Brown,
  *Zero-free regions for Dirichlet $L$-functions, and the least prime in an arithmetic
  progression*; **all "H p. n" below are the page numbers printed on the retained ORA preprint,
  not the journal pages** (Proc. London Math. Soc. (3) 64 (1992) 265–338); see hole H-3.
  HB90 = Heath-Brown, *Siegel zeros and the least prime in an arithmetic progression*,
  Quart. J. Math. Oxford (2) 41 (1990) 405–418 (journal pages).
* $\Psi(z)=\int_0^T\psi(t)e^{-zt}dt$ for the 16-step kernel ($T=.416829$, $\kappa=T/16$),
  $H_0=\Psi(0)^2=.03749733756966714\ldots$, $A=L-2T$ ($=3.156342$ at $L=3.99$),
  $G(\lambda)=e^{-A\lambda}B_{1/3}(\lambda)$, $G_\phi(\lambda)=e^{-A\lambda}B_\phi(\lambda)$, and $w$ the
  far weight of the leaf's profile (PROOF §4), which is positive and decreasing.

Everything numerical quoted below was recomputed in this session (§7, verification log).

---

## 1. PROOF §7: the leaf LP

### 1.1 Leaf data

**Definition 7.1 (leaf data).** A *leaf* $\mathcal L$ consists of

1. a finite set of *columns* $\mathcal C=\mathcal C_O\sqcup\mathcal C_H\sqcup\mathcal C_2$ (ordinary,
   hidden, second-family). Each column $c$ carries integers
   $$G_c\ge0,\quad W_c>0,\quad C_c\in\{0,S\},\quad N_c\ge0,\quad E_c\in\{0,S\},$$
   with $C_c=0$ for $c\notin\mathcal C_O$, $N_c=0$ for $c\notin\mathcal C_H$ and $E_c=S\cdot\mathbf 1[c\in\mathcal C_2]$;
2. *near rows* $k=1,\dots,K$. Row $k$ carries an integer radius $d_k>0$, for every column $c$ an
   integer feature $v_{kc}\ge0$ and diagonal $D_{kc}>0$, and a finite list $\mathrm{fam}_k$ of
   *family terms* $(n,v,D)$ with $n,v\in\mathbb Z_{\ge0}$, $D\in\mathbb Z_{>0}$;
3. integers $F$ (far budget), $n_g\ge0$ (hidden count), $n_2\ge0$ (reserved count),
   $\mathrm{first}$ and $\mathrm{final}$.

All quantities are "scaled by $S$": the real number represented by an integer $X$ is $X/S$
(except the counts $n$, $n_g$, $n_2$, which are plain integers).

**Definition 7.2 (the leaf LP).** For $x\in\mathbb R^{\mathcal C}$ and $\tau\in\mathbb R^K$ put
$$
\Phi_k(x;t)=\sum_{c\in\mathcal C}x_c\,\frac{(v_{kc}/S-t)_+^2}{D_{kc}/S}
 +\sum_{(n,v,D)\in\mathrm{fam}_k}n\,\frac{(v/S-t)_+^2}{D/S}+\frac{t^2}{d_k/S}.
$$
The pair $(x,\tau)$ is *feasible* if

* (P0) $x_c\ge0$ for all $c$;
* (P1, far) $\sum_cW_cx_c\le F$;
* (P2, count) $\sum_cC_cx_c\le 2S$;
* (P3, hidden count) $\sum_cN_cx_c\le n_gS$;
* (P4, second family) $\sum_cE_cx_c=n_2S$;
* (P5$_k$, near row $k$) $0\le\tau_k$, $\tau_k^2\le d_k/S$ and $\Phi_k(x;\tau_k)\le1$.

The objective is $\mathrm{Obj}(x)=S^{-1}\bigl(\mathrm{first}+\mathrm{final}+\sum_cG_cx_c\bigr)$.
The leaf is *certified* if $\sup\{\mathrm{Obj}(x):(x,\tau)\text{ feasible}\}<1$.

(P5$_k$) is the threshold form (T) of PROOF §6.4 with the row's own unknown threshold
$\tau_k$: every row has its own $\tau_k$, and the column vector $x$ is shared by all rows.
This is exactly `GradedNear.Cert.Feasible` (`lean-graded/GradedNear/Defs.lean`) and the
constraint set of `graded_cert.py` (docstring and `Leaf`).

### 1.2 The data used in the proof

Each column has a *meaning*: a **bin** $[\ell_c,r_c)$, or a **tail** $[R_c,\infty)$. A
character placed in a bin has mass 1; a character with parameter $\lambda$ placed in a tail
has mass $w(\lambda)$ (Lean `ColSem`, `Cert/Semantics.lean`). The integers are
(notation: $\lceil X\rceil_S=\lceil SX\rceil$ and $\lfloor X\rfloor_S=\lfloor SX\rfloor$ taken at the
upper resp. lower end of an outward enclosure):

| Column | meaning | $G_c$ | $W_c$ | $C_c$ | $N_c$ | features, diagonals |
| --- | --- | --- | --- | --- | --- | --- |
| ordinary bin | $[\ell_i,r_i)$, grid $1/\mathrm{den}$ on $[r_0,R)$ | $\lceil G(\ell_i)\rceil_S$ | $\lfloor w(r_i)\rfloor_S$ | $S$ iff unreserved and $r_i\le\lambda_3^{lo}$ | 0 | $v$ at $r_i$ (rounded down, clamped at 0), $D$ rounded up |
| ordinary tail | $[R,\infty)$, $R=\max(3,r_0)$ | $\lceil G(R)/w(R)\rceil_S$ | $S$ | 0 | 0 | $v=0$ in every row |
| hidden bin | $[\ell_h,r_h)\subset[p_h,R_h)$ | $\lceil e^{-A\ell_h}B_\phi(p_h)\rceil_S$ | $\lfloor w(r_h)\rfloor_S$ | 0 | $S$ | $v$ at $r_h$, anchor $s_1$ (family row only) |
| hidden tail | $[R_h,\infty)$, $R_h=\max(3,p_h)$ | $\lceil e^{-AR_h}B_\phi(p_h)/w(R_h)\rceil_S$ | $S$ | 0 | $\lfloor 1/w(R_h)\rfloor_S$ | $v=0$ |
| second-family | $[l_j,r_j]$, grid $1/400$ on $[lo_2,hi_2]$ | $\lceil G_{\phi_2}(l_j)\rceil_S$ | $\lfloor w(r_j)\rfloor_S$ | 0 | 0 | $v$ at $r_j$, anchor $\min(\max(a,\min(\mathrm{source\_l2},l_j)),s)$ |

Here $\mathrm{den}\in\{200,400,500,800,2000\}$ (inside), $200$ (nodes, outside), $100$ (large
branch); $\phi=1/4$ for type rc and $1/3$ for complex in the hidden columns; $\phi_2=1/4$ iff
$n_2=1$. With a reserved family, the ordinary bins with $r_i\le\lambda_3^{lo}$ are **deleted**
(not only removed from the count row). The scalars are
$$F=\lceil(1+\eta)V\rceil_S-[\text{inside}]\,n\lfloor w(b)\rfloor_S-[\text{reserved, no columns}]\,n_2\lfloor w(hi_2)\rfloor_S,$$
$\mathrm{first}=\min(\lceil J_{old}\rceil_S,\lceil J_{new}\rceil_S)+J_2$ (inside) or $J_2$ (outside), with
$J_2=n_2\lceil G_{\phi_2}(lo_2)\rceil_S$ removed when the family is charged by columns, and
$\mathrm{final}=5\eta S=5\cdot10^{10}$. The near-row integers are (PROOF §6.4, builders'
normalization): radius $d=\lceil(1+\eta)(d_1/D_u+\eta)\rceil_S$, diagonal
$\lceil(1+\eta)D^+_j/D_u\rceil_S$, feature $\lfloor r_j/\sqrt{I_uD_u}-\eta\rfloor_S$ clamped at $0$.
These formulas were confirmed on regenerated leaves (§7) and agree with
`research/notes/leaf-data-semantics-2026-09-29.md` §§2–3.

**Every rounding is in the safe direction:** $G$, $F$, $\mathrm{first}$, $d$, $D$ up; $W$, $v$,
$N_{\rm tail}$ down; $C,E$, counts and $\mathrm{final}$ exact.

### 1.3 The configuration is a feasible point

**Proposition 7.3 (actual-zero realization).** Fix a leaf and its case (a cell of the case tree
of PROOF §8), and let $q\ge q_0$. Assume the inputs

* (I1, far; PROOF §4) for every choice of one zero $\rho_\chi$ per nonprincipal character with
  $|\mathrm{Im}\,\rho_\chi|\le1$ and $\lambda_{\rho_\chi}\le\frac13\log\log\ell$,
  $\sum_\chi w(\lambda_{\rho_\chi})\le(1+\eta)V$ (X Lemma 5.1, (5.19), p. 66);
* (I2, third family; PROOF §5) unreserved: at most two non-first characters have a
  $T^*$-representative with parameter $<\lambda_3$; reserved: every non-first, non-reserved
  character has $T^*$-representative $\ge\lambda_3$; in both cases $\lambda_3\ge\lambda_3^{lo}$;
* (I2′, ranges; PROOF §§3, 5, 8) every ordinary $T^*$-representative has parameter $\ge r_0$
  (`ordinary_lower` bounds the height-one representatives, and a $T^*$-representative lies to
  their right); the reserved family has $\nu_2\in[lo_2,hi_2]$; every $R_P$ zero of an outside
  first-family character has parameter $\ge p_h$;
* (I3, costs; PROOF §3) the occurrence sum $\sum_{\rho\in R_P}|H((1-\rho)\ell)|/H_0$ of each
  character is at most the objective of its column at its parameter (plus the errors E2–E4 of §4
  below), and the first family is charged $\mathrm{first}$;
* (I4, near rows; PROOF §6) for each row $k$ the entries (every character of the row, each with
  its representative and anchor) satisfy (T) in the builders' normalization, with every stored
  feature at most the entry's feature, every stored diagonal at least the entry's diagonal and
  $d_k/S$ at least the entry radius (Lean `GradedNear.Row.row_threshold`).

Assign the characters to columns as follows (bins half-open, so ties go upward):
$x_c$ = number of ordinary characters whose $T^*$-representative has parameter in $[\ell_c,r_c)$;
$x_{\rm tail}=\sum_{\lambda_\chi\ge R}w(\lambda_\chi)$; $y_h$ = number of first-family characters whose
rightmost $R_P$ zero has parameter in $[\ell_h,r_h)$; $y_{\rm tail}=\sum_{t_\chi\ge R_h}w(t_\chi)$;
$z_j=n_2\,\mathbf 1[\nu_2\in\text{column }j]$; $\tau_k$ = the threshold given by (T) for row $k$.
Then $(x,\tau)$ is feasible, and
$$W_{\rm occ}:=H_0^{-1}\sum_{\chi\ne\chi_0}\sum_{\rho\in R_P}|H((1-\rho)\ell)|\le\mathrm{Obj}(x)-\frac{\mathrm{final}}S+E_2+E_3+E_4 .$$

*Proof.* (P0) is clear.

(P1) Choose as far representative: the $T^*$-representative for ordinary characters, the
height-one representative (parameter $\nu_2$) for the reserved family, $\rho_1$ for an inside
first family ($|\gamma_1|\le C_B/\ell\le1$), and the rightmost $R_P$ zero ($|\gamma|\le C_P/\ell\le1$)
for an outside first-family character; characters with no $R_P$ zero are dropped (legitimate:
(I1) holds for any subfamily since all terms are positive). All these have
$|\mathrm{Im}\,\rho|\le1$ and $\lambda\le C_P\le\frac13\log\log\ell$. Since $w$ decreases, a character in a
bin $[\ell,r)$ has $w(\lambda)\ge w(r)\ge W_c/S$; a tail column receives exactly
$\sum w(\lambda_\chi)$ with $W_c=S$; a second-family column receives $z_j=n_2$ with
$z_jW_j/S=n_2\lfloor w(r_j)\rfloor_S/S\le n_2w(\nu_2)$; the inside first family has
$n\,w(\lambda_1)\ge n\lfloor w(b)\rfloor_S/S$; the reserved family, when charged at a fixed end,
$n_2w(\nu_2)\ge n_2\lfloor w(hi_2)\rfloor_S/S$. Hence
$\sum_cW_cx_c\le S\sum_{\chi\ \rm in\ columns}w(\lambda_\chi)\le S(1+\eta)V-S\sum_{\chi\ \rm fixed}w(\lambda_\chi)\le F$, the
last sum running over the first family (inside) and a reserved family charged at fixed ends.

(P2) Only ordinary bins with $r_c\le\lambda_3^{lo}$ have $C_c=S$. A character counted there has
$T^*$-representative $<r_c\le\lambda_3^{lo}\le\lambda_3$ (half-open bins), so by (I2) there are at most
two of them. With a reserved family those bins are deleted, and (I2) says no character is lost.

(P3) Each first-family character has at most one hidden column (its rightmost $R_P$ zero). A
hidden bin contributes $S$ per character; the hidden tail contributes
$\lfloor1/w(R_h)\rfloor_S\,w(t_\chi)\le S\,w(t_\chi)/w(R_h)\le S$ per character since $t_\chi\ge R_h$ and $w$
decreases. Hence $\sum N_cy_c\le S\cdot\#\{\text{first-family characters}\}\le n_gS$.

(P4) The $n_2$ characters of the reserved family share one height-one parameter $\nu_2$
(conjugate characters have the same representative parameter, every region used being
symmetric in the height), so $\sum_jE_jz_j=Sn_2$.

(P5$_k$) By (I4), (T) holds at $\tau_k\in[0,\sqrt{d^{\rm true}}]$ with the entries' true data. Each
column with a positive feature in row $k$ receives exactly the characters binned to it, all of
which are entries of row $k$; tails have $v=0$ and contribute nothing whatever $x_{\rm tail}$ is. The
conservative-binning lemma (Lean `GradedNear.Cert.near_row_of_bins`,
`Cert/Bins.lean`) turns (T) into (P5$_k$): each term $(v-\tau)_+^2/D$ is increasing in $v$ and
decreasing in $D$ at $\tau\ge0$, each family term has at least $n$ entries, and $d_k/S$ dominates
the true radius, so $\tau_k^2\le d_k/S$ and $\tau^2/(d_k/S)\le\tau^2/d^{\rm true}$.

Objective: by (I3), a character in a bin costs at most $e^{-A\lambda}B(\ldots)\le G_c/S$ (all objectives
decrease in $\lambda$, and $G_c$ is taken at the left end); a character in a tail costs at most
$G(\lambda)=w(\lambda)\cdot G(\lambda)/w(\lambda)\le w(\lambda)G(R)/w(R)\le w(\lambda)G_c/S$ because
$G(\lambda)/w(\lambda)=B_{1/3}(\lambda)\int_u^x w_0(t)^2e^{-(A-2t)\lambda}dt$ is a product of positive decreasing
functions when $A>2x$ (here $2x=2.347$ or $2.261<A=3.156$); the same for the hidden tail with
$e^{-At}B_\phi(p_h)$. The first family and a reserved family charged at fixed ends are in
$\mathrm{first}$. Summing, $W_{\rm occ}\le(\mathrm{first}+\sum G_cx_c)/S+E_2+E_3+E_4$. $\square$

Lean: `GradedNear.Cert.leaf_relaxation` (`Cert/Relaxation.lean`) and `leaf_interpretation`
(`Cert/Semantics.lean`) prove the implication "(P1)–(P5) at the masses and per-character cost
bounds $\Rightarrow$ total cost $<1$" for an abstract configuration; `Row/Masses.lean`
(`row_at_masses`) supplies (P5$_k$) for every checked row (not for the inherited two-test row).

### 1.4 Certificates

**Definition 7.4 (root box).** For row $k$ put $e_k=\lceil\sqrt{\lfloor d_kT_S^2/S\rfloor+1}\,\rceil$
(computed with the exact integer square root). The root box is $\prod_k[0,e_k]$ in ticks of
$10^{-6}$. The end is not stored; a verifier recomputes it.

**Definition 7.5 (integer costs and budgets).** Let $0\le a<b$ be integers (ticks), $k$ a row, and
$\epsilon\in\{0,1,2\}$ a *case*. Write $\mathrm{fam}_k$ as a list of $(n,v,D)$.

* **First order ($\epsilon=2$):** with $s_b=b\,S/T_S$,
  $$\kappa_{kc}=\Bigl\lfloor\frac{(v_{kc}-s_b)_+^2}{D_{kc}}\Bigr\rfloor,\qquad
  \beta_k=S-\Bigl\lfloor\frac{S^2a^2}{T_S^2d_k}\Bigr\rfloor-\sum_{(n,v,D)}\Bigl\lfloor\frac{n(v-s_b)_+^2}{D}\Bigr\rfloor .$$
* **Tangent cases ($\epsilon\in\{0,1\}$):** put $\sigma_0=+1$, $\sigma_1=-1$,
  $\xi_{kc}=v_{kc}-(a+b)H_S$, $\vartheta=(b-a)H_S$,
  $$t_{kc}=\begin{cases}0,&\xi_{kc}\le0,\\ \lfloor\xi_{kc}(\xi_{kc}+2\sigma_\epsilon\vartheta)/S\rfloor,&\xi_{kc}>0,\end{cases}\qquad
  \kappa_{kc}=\Bigl\lfloor\frac{t_{kc}S}{D_{kc}}\Bigr\rfloor .$$
  With $m=\frac{a+b}{2T_S}$, $h=\frac{b-a}{2T_S}$ and, for $w\in\mathbb Q$,
  $\Theta_\epsilon(w)=(w-m)_+^2+2\sigma_\epsilon h\,(w-m)_+$,
  $$\beta_k=\Bigl\lceil S\Bigl(1-\frac{m^2-2\sigma_\epsilon hm}{d_k/S}-\sum_{(n,v,D)}n\frac{\Theta_\epsilon(v/S)}{D/S}\Bigr)\Bigr\rceil .$$
  (Note $m^2-2hm=(a/T_S)^2-h^2$ and $m^2+2hm=(b/T_S)^2-h^2$;
  $\Theta_0(w)=((w-m)_++h)^2-h^2$, $\Theta_1(w)=((w-m)_+-h)^2-h^2$ when $(w-m)_+>0$, and $0$
  otherwise.)

**Definition 7.6 (certificate).** A certificate is a finite binary tree. An internal node
$(k,\mathrm{mid})$ on a box with $k$-th side $[a,b]$ requires $a<\mathrm{mid}<b$ and has children on
$[a,\mathrm{mid}]$ and $[\mathrm{mid},b]$. A leaf node on a box $\prod_k[a_k,b_k]$ carries *orders*
$o\in\{1,2\}^K$ and, for every *case vector* $\epsilon\in\prod_k E(o_k)$, $E(1)=\{0,1\}$,
$E(2)=\{2\}$ (listed lexicographically, first coordinate slowest), either the word
`excluded` or integer duals $(Y,V,U,P,M,Z_1,\dots,Z_K)\in\mathbb Z_{\ge0}^{5+K}$. The node is
*accepted* if for every case vector:

* **exclusion:** some row $k$ has $\beta_k<0$ and $\kappa_{kc}\ge0$ for **every** column $c$; or
* **duals:** for every column $c$,
  $$D_S\,G_c\ \le\ YW_c+VC_c+UN_c+(P-M)E_c+\sum_kZ_k\kappa_{kc},\tag{7.1}$$
  and then the case value is
  $$\mathrm{val}_\epsilon=\Bigl\lceil\frac{YF+2SV+n_gSU+(P-M)n_2S+\sum_kZ_k\beta_k}{D_S}\Bigr\rceil+\mathrm{first}+\mathrm{final}.$$

The node value is the maximum of the case values ($-1$ if all cases are excluded) and must be
$<S$. The certificate is accepted with value $v^*$ = the maximum node value.

This is `graded_cert.verify_tree/check_box/check_case/excludable/_row_case/tangent_cost`
and, identically, `GradedNear.Cert.checkLeaf` (`Defs.lean` lines 372–510). Python's
`graded_cert` additionally asserts $W_c>0$, $v\ge0$, $C_c\in\{0,S\}$, integer types, and $U=0$
(resp. $P=M=0$) without hidden (resp. second-family) columns; so it accepts a subset of what
`checkLeaf` accepts.

### 1.5 Soundness

**Theorem 7.7 (soundness of the checker).** If a certificate for $\mathcal L$ is accepted with value
$v^*$, then every feasible $(x,\tau)$ satisfies $S\,\mathrm{Obj}(x)\le v^*<S$; in particular
$\mathrm{Obj}(x)<1$.

The proof uses five lemmas. Fix a feasible $(x,\tau)$.

**Lemma 7.8 (root box).** $0\le\tau_kT_S\le e_k$ for all $k$.

*Proof.* $(\tau_kT_S)^2\le d_kT_S^2/S<\lfloor d_kT_S^2/S\rfloor+1\le e_k^2$. $\square$
(Lean `SoundAux.le_rootEnd`.)

**Lemma 7.9 (first-order relaxation).** If $0\le a\le\tau_kT_S\le b$, then
$\sum_c\kappa^{(2)}_{kc}x_c\le\beta^{(2)}_k$.

*Proof.* For $t=\tau_k\le b/T_S$ and any $v$: $(v/S-t)_+\ge(v-s_b)_+/S\ge0$, so
$S\frac{(v/S-t)_+^2}{D/S}\ge\frac{(v-s_b)_+^2}{D}\ge\kappa$; for family terms also $n\ge0$. And
$t\ge a/T_S\ge0$ gives $St^2/(d_k/S)\ge S^2a^2/(T_S^2d_k)$. Multiply $\Phi_k(x;t)\le1$ by $S$, bound
each column term below (using $x\ge0$), each family term and the quadratic term below, move
the latter to the right, and use that $\lfloor\cdot\rfloor$ of a subtracted quantity only enlarges
$\beta_k$. $\square$ (Lean `relax_first`; it needs $n\ge0$ and $a\ge0$.)

**Lemma 7.10 (tangent relaxation).** If $a\le\tau_kT_S\le b$, then there is $\epsilon\in\{0,1\}$ with
$\sum_c\kappa^{(\epsilon)}_{kc}x_c\le\beta^{(\epsilon)}_k$.

*Proof.* For $w\in\mathbb R$ let $g_w(t)=(w-t)_+^2$ and $\ell_w(s)=(w-m)_+^2-2(w-m)_+s$, the
tangent line of $g_w$ at $m$ as a function of $s=t-m$. Then $g_w(m+s)\ge\ell_w(s)$ for all $s$:
if $w\le m$, $\ell_w=0\le g_w$; if $w>m$ and $s\le w-m$,
$g_w(m+s)-\ell_w(s)=s^2\ge0$; if $s>w-m>0$, $g_w=0$ and
$-\ell_w(s)=(w-m)(2s-(w-m))>0$. Likewise $(m+s)^2\ge m^2+2ms$. Hence, since $x\ge0$, $n\ge0$,
$D,d>0$, the affine function
$$\Lambda(s)=\sum_cx_c\frac{\ell_{v_{kc}/S}(s)}{D_{kc}/S}+\sum_{(n,v,D)}n\frac{\ell_{v/S}(s)}{D/S}+\frac{m^2+2ms}{d_k/S}$$
satisfies $\Lambda(\tau_k-m)\le\Phi_k(x;\tau_k)\le1$. As $|\tau_k-m|\le h$ and $\Lambda$ is affine,
$\Lambda(-h)\le1$ or $\Lambda(h)\le1$ (whichever endpoint lies on the non-increasing side). Now
$\ell_w(-\sigma_\epsilon h)=\Theta_\epsilon(w)$ and $m^2-2\sigma_\epsilon hm$ is the quadratic term, so
$\Lambda(-\sigma_\epsilon h)\le1$ is the exact case-$\epsilon$ constraint
$\sum_cx_c\Theta_\epsilon(v_{kc}/S)/(D_{kc}/S)\le1-\frac{m^2-2\sigma_\epsilon hm}{d_k/S}-\sum n\Theta_\epsilon(v/S)/(D/S)$.
Rounding: $\xi=S(v/S-m)$, $\vartheta=Sh$, so $\xi(\xi+2\sigma_\epsilon\vartheta)/S=S\,\Theta_\epsilon(v/S)$ when $\xi>0$;
both floors (Python `//` rounds toward $-\infty$, also for negative numbers) give
$\kappa_{kc}\le S\,\Theta_\epsilon(v_{kc}/S)/(D_{kc}/S)$, and the ceiling gives $\beta_k\ge S\cdot$(exact
budget). Multiplying by $x_c\ge0$ preserves the inequalities. $\square$ (Lean `relax_tangent`,
`RelaxAux.tangent_ineq`, `tline_le`, `endpoint`.)

Remark (PROOF §7 phrasing). "$\Phi_k(\tau^*)\le1$ forces $\Phi_k(m)\mp h\Phi_k'(m)\le1$ for one sign"
is the same statement: $\Phi_k(m)+s\Phi_k'(m)=\Lambda(s)$, the upper sign is case 0.

**Lemma 7.11 (exclusion).** If an accepted node excludes a case vector $\epsilon$ and $x\ge0$
satisfies the relaxed constraint of every row for $\epsilon$, contradiction.

*Proof.* The witnessing row has $\sum_c\kappa_{kc}x_c\ge0>\beta_k$. $\square$ (Lean `not_excludable`.)

*Why the rule needs all costs $\ge0$.* In case 1, $\Theta_1(w)=(w-m)_+((w-m)_+-2h)<0$ for
$m<w<m+2h$, so costs can be negative and a negative budget can be met by some $x\ge0$.
First-order and case-0 costs are always $\ge0$. The earlier rule "negative budget suffices" was
unsound exactly here (sieve-majorant-near §8, second review); the corpus contains 22 feasible
case-1 cases with a negative budget and a negative cost, correctly not excluded
(independent-checks §1).

**Lemma 7.12 (weak duality).** If $x\ge0$ satisfies (P1)–(P4) and the relaxed constraints
$\sum_c\kappa_{kc}x_c\le\beta_k$ of a case vector with accepted duals, then $S\,\mathrm{Obj}(x)\le\mathrm{val}_\epsilon$.

*Proof.* Multiply (7.1) by $x_c\ge0$ and sum:
$D_S\sum_cG_cx_c\le Y\sum W_cx_c+V\sum C_cx_c+U\sum N_cx_c+(P-M)\sum E_cx_c+\sum_kZ_k\sum_c\kappa_{kc}x_c$.
Use (P1)–(P3) with $Y,V,U\ge0$, the *equality* (P4) with the multiplier $P-M$ of arbitrary sign,
and the relaxed rows with $Z_k\ge0$: the right side is at most
$YF+2SV+n_gSU+(P-M)n_2S+\sum Z_k\beta_k=:\mathcal T$. Hence
$\sum G_cx_c\le\mathcal T/D_S\le\lceil\mathcal T/D_S\rceil$, and adding $\mathrm{first}+\mathrm{final}$ gives the
claim. Costs $\kappa_{kc}$ of either sign are allowed; only $Y,V,U,Z$ must be $\ge0$. $\square$
(Lean `SoundAux.weak_duality`, `caseValue_sound`.)

*Proof of Theorem 7.7.* By Lemma 7.8 the point $\tau T_S$ lies in the root box. Descending the
tree (at a split go left iff $\tau_kT_S\le\mathrm{mid}$) reaches a leaf node whose box contains $\tau T_S$
and has all lower ends $\ge0$. For each row with order 2, Lemma 7.9 gives the case-2 relaxed
constraint; for each row with order 1, Lemma 7.10 gives some $\epsilon_k\in\{0,1\}$. The resulting case
vector is one of those enumerated. By Lemma 7.11 it is not excluded; so it carries duals, and
by Lemma 7.12, $S\,\mathrm{Obj}(x)\le\mathrm{val}_\epsilon\le$ node value $\le v^*<S$. $\square$

(Lean: `GradedNear.Cert.checkLeaf_sound`, `checkLeaf_lt`, `certified`, `Cert/Sound.lean`, with
no `sorry`; `checkLeaf_ofCore`/`checkLeaf_toCore` (`Cert/FastEq.lean`) identify the compiled
Mathlib-free checker with `checkLeaf`.)

**Corollary 7.13.** If every leaf of the case tree has an accepted certificate, then for every
configuration of the middle range and $q\ge q_0$: $W_{\rm occ}\le v^*/S-5\eta+E_2+E_3+E_4$, where $v^*$ is
the leaf's value. At $L=3.99$ the largest leaf value in the corpus is
$9999998223456687/S=.99999982234566\ldots$ (inside and nodes) and
$9999942478462508/S$ (outside). (Proposition 7.3 + Theorem 7.7.)

### 1.6 Remarks for the paper

* The two relaxations are per dimension and may be mixed within one box; the number of cases of a
  box is $2^{\#\{k:o_k=1\}}$.
* A negative case value is a valid (infeasibility) certificate; the checker then records $-1$.
  (Observed on root 1416: three leaves whose every box is infeasible.)
* Integer overflow is impossible (Python and Lean integers are unbounded).
* The large-branch certificate of §9.4 is **not** of this format: it is an older first-order
  certificate (contiguous threshold intervals, one far and one near dual each), checked by
  `computations/core/code/verify_published_single.scenario`; it is the special case
  $K=1$, all orders 2, no count/hidden/second rows, with the near row multiplied by $D$.

---

## 2. PROOF §9: the exterior regimes

Throughout, $\lambda_1$ is the least parameter of a zero of a nonprincipal $L(s,\chi)$ in $R(l)$
(X §3.1.2 = H §6 numbering), and "$q\ge q_0$" hides finitely many thresholds fixed in §3.

### 2.1 No zero in $R(l)$

**Proposition 9.1.** Let $L=3.99$ and the 16-step kernel of PROOF §2 be fixed ($A=3.156342>3$).
There is $q_0$ such that for $q\ge q_0$: if no nonprincipal $L(s,\chi)$, $\chi\bmod q$, vanishes in
$R(l)$, then every reduced class $a\bmod q$ contains a prime $p$ with $q^{A}<p<q^{L}$.

*Proof.* The kernel is a positive combination of 31 triangles $h_{A+(k+2)\kappa,\kappa}$ with left
ends $A+k\kappa\ge A>3$, so X (3.57)–(3.58) (p. 34–35) applies with $\varepsilon=\eta H_0$: there are
$C_0,q_0$ with $\Sigma\ge\frac{\ell}{\varphi(q)}\bigl(H_0-\sum_{\chi\ne\chi_0}\sum'_\rho|H((1-\rho)\ell)|-\eta H_0\bigr)$, $\Sigma'$
over the rectangle (3.58). Take $C_P\ge C_0$; for $q$ large $C_P\le\frac13\log\log\ell$ and
$C_P/\ell\le1\le l$, so the rectangle lies in $R(l)$ and the zero sum is empty. Then
$\Sigma\ge(1-\eta)H_0\ell/\varphi(q)>0$, and X's $\Sigma$ is a sum over primes $p\equiv a$ with
$\log p/\ell\in\mathrm{supp}\,h\subset(A,L)$ (X p. 33). $\square$ (Xylouris states this case himself, X p. 36,
Bemerkung.)

### 2.2 The small first zero, $u_0\le\lambda_1\le.1$

**Fixed data.** $L=\frac{399}{100}$, $K=\frac{1821}{10000}$, $A=L-2K=\frac{18129}{5000}=3.6258$;
triangle kernel $h=h_{L,K}$ (X (3.51)), with transform $F(z)=e^{-Az}F_2(z)$,
$F_2(z)=\bigl(\frac{1-e^{-Kz}}{z}\bigr)^2$, $F(0)=K^2$. Density parameters $c_1=\frac{57}{1000}$,
$c_2=\frac{777}{5000}=.1554$, $\phi=\frac13$:
$$a_d=\tfrac43+6c_1+2c_2=\tfrac{3724}{1875},\quad b_d=\tfrac23+4c_1=\tfrac{671}{750},\quad
V_d=\frac{2/3+2c_1+c_2}{4c_1c_2}=\frac{184750}{6993}=26.4193\ldots$$
Envelope: $\mathcal B_\phi(m)=\phi\frac{1-e^{-2Km}}{2m}+\frac{2Km-1+e^{-2Km}}{2m^2}$ (decreasing in $m$, with
$\mathcal B_\phi(0^+)=K^2+\phi K$). $\alpha=\frac{109}{100}<\frac{12}{11}$, $B_1=K^2+K/4=.07868541$. Pieces:
$\mathcal P_1=[u_0,.08]$ with $m(u)=\alpha\log(1/u)$ and $m^*=m(.08)=\alpha\log12.5=2.7530442\ldots$;
$\mathcal P_2=[.08,.1]$ with fixed gaps $m_2=2.83-\epsilon_T$, $m_2'=4.96-\epsilon_T$, $\epsilon_T=\frac1{1000}$.
Always $u_0\le\min(.08,1/3)$.

**Proposition 9.2.** For each fixed $u_0\in(0,.08]$ there is $q_0(u_0)$ such that for $q\ge q_0$: if
$u_0\le\lambda_1\le.1$, every reduced class $a\bmod q$ contains a prime $p$ with $q^{3.6258}<p<q^{3.99}$.

*Proof.* Write $u=\lambda_1$.

*Step 0 (shape of the configuration).* If $\chi_1$ or $\rho_1$ were nonreal then $\lambda_1>.440$
(X Lemma 4.5 with Table 11, pp. 60–61). So $\chi_1$ and $\rho_1=1-u/\ell$ are real. $\rho_1$ is simple:
H's $\lambda_0$ counts a repeated $\rho_1$ as $\rho_0$ (H p. 28), and $\lambda_0\ge(2-\varepsilon)\log(1/u)>u$ on
$\mathcal P_1$ (H Lemma 8.4, p. 43) resp. $\lambda_0\ge4.96-\epsilon_T>u$ on $\mathcal P_2$ (H Table 2, p. 39).

*Step 1 (criterion).* $L>2K+3$ ($3.99>3.3642$). By H Lemma 13.2 (p. 81) (equivalently X (3.57)
with one triangle), for any $\varepsilon>0$ there are $R(\varepsilon)$ and $q_0$ with
$$\frac{\varphi(q)}{\ell}\Sigma\ \ge\ K^2-\sum_{\chi\ne\chi_0}\sum\nolimits'_{\rho}|F((1-\rho)\ell)|-\varepsilon ,$$
$\Sigma'$ over $1-R/\ell\le\beta\le1$, $|\gamma|\le R/\ell$ (we may take $R=R(\varepsilon)\ge3$: enlarging the
rectangle only adds nonnegative terms); for large $q$ this rectangle lies in $R(l)$ and in
$|\gamma|\le1$. The zero $\rho_1$ contributes $F(u)=:H(u)$.

*Step 2 (gaps).* Every zero $\rho\ne\rho_1$ of $L(s,\chi_1)$ in $R(l)$ has $\lambda_\rho\ge\lambda_0$, and every zero of
$\chi\ne\chi_0,\chi_1$ in $R(l)$ has $\lambda_\rho\ge\lambda_2$ (H §6 numbering, p. 26–28; $\chi_1=\bar\chi_1$). On $\mathcal P_1$:
$\lambda_0\ge(2-\varepsilon)\log(1/u)\ge m(u)$ (H Lemma 8.4, $u\le.2$) and $\lambda_2\ge(\frac{12}{11}-\varepsilon)\log(1/u)\ge m(u)$
(H Lemma 8.8, p. 48, with $\varepsilon=\frac{12}{11}-\alpha=\frac1{1100}$). On $\mathcal P_2$: $\lambda_2\ge2.83-\epsilon_T$ and
$\lambda_0\ge4.96-\epsilon_T$ for every $\lambda_1\le.10$ (H Tables 5 and 2, rows $.10$, pp. 46 and 39, with
H p. 38: "$\lambda_0\ge\lambda_{0b}-\varepsilon$ for $q\ge q(\varepsilon,b)$ whenever $0\le\lambda_1\le b$"; Table 5 is computed
"in the same way", p. 45, and the hypothesis $\lambda_2\le\lambda_0$ of Lemma 8.5 is redundant there because
$\lambda_0\ge4.96-\epsilon_T>2.83$). Put $m_1(u)=m(u)$ on $\mathcal P_1$, $m_1=m_2'$ on $\mathcal P_2$, and $m(u)=m_2$ on $\mathcal P_2$.

*Step 3 (the other zeros of $\chi_1$).* Apply H Lemma 13.3, (13.3) (p. 82) to $\chi_1$ with the fixed
$\lambda=u_0/2$ (legitimate: no zero of $\chi_1$ has $\beta>1-u_0/(2\ell)$, $|\gamma|\le1$) and $\phi(\chi_1)=\frac14$
($\chi_1$ real, order $2\le\ell$: H Lemma 2.5, p. 10; X p. 17):
$\sum'_\rho|F_2((1-\rho)\ell)|\le\mathcal B_{1/4}(u_0/2)+\eta_1\le B_1+\eta_1$ for $q\ge q(\eta_1)$. Hence
$$T_1:=\sum\nolimits'_{\rho\ne\rho_1}|F((1-\rho)\ell)|\le e^{-Am_1}\sum\nolimits'_{\rho}|F_2|\le e^{-Am_1}(B_1+\eta_1).$$

*Step 4 (the other characters).* For $\chi\ne\chi_0,\chi_1$ with a zero in the $\Sigma'$ rectangle, let
$\lambda(\chi)$ be the parameter of its rightmost zero with $|\gamma|\le1$; then $\lambda(\chi)\le R$ and every $\rho$ in
$\Sigma'$ has $\lambda_\rho\ge\lambda(\chi)\ge m(u)$. Apply (13.3) with the **fixed** $\lambda=m^*$ on $\mathcal P_1$
($m^*\le m(u)$ there) or $\lambda=m_2$ on $\mathcal P_2$, and $\phi(\chi)\le\frac13$ ($\mathcal B_\phi$ increases in $\phi$):
$\sum'_\rho|F((1-\rho)\ell)|\le e^{-A\lambda(\chi)}(\mathcal B_{1/3}(\bar m)+\eta_1)$, $\bar m\in\{m^*,m_2\}$. By X (5.18)
(p. 66; = H Lemma 11.1, (11.3), p. 68) with $\phi=\frac13\ge\max_\chi\phi(\chi)$, choosing the zero of
$\chi$ at $\lambda(\chi)$ and dropping the (nonnegative) term of $\chi_1$:
$\sum_\chi\lambda(\chi)/(e^{a_d\lambda(\chi)}-e^{b_d\lambda(\chi)})\le V_d+\varepsilon_2$. Since
$t\mapsto e^{-At}(e^{a_dt}-e^{b_dt})/t=\int_{b_d}^{a_d}e^{-(A-s)t}ds$ decreases ($A>a_d$),
$$T_2:=\sum_{\chi\ne\chi_0,\chi_1}\sum\nolimits'_{\rho}|F|\le(\mathcal B_{1/3}(\bar m)+\eta_1)(V_d+\varepsilon_2)\,Q(m(u)),\qquad
Q(m)=\frac{e^{-(A-a_d)m}-e^{-(A-b_d)m}}{m}.$$

*Step 5 (monotonicity).* $M(u):=(K^2-H(u))/u=\int h(t)\frac{1-e^{-ut}}u\,dt$ decreases in $u$ ($h\ge0$).
On $\mathcal P_1$, $u=e^{-m/\alpha}$, so $Q(m(u))/u=\int_{A-a_d-1/\alpha}^{A-b_d-1/\alpha}e^{-tm(u)}dt$ with
$A-a_d-1/\alpha=\frac{236171}{327000}>0$; it increases in $u$, and so does
$e^{-Am(u)}/u=e^{-(A-1/\alpha)m(u)}$. On $\mathcal P_2$ the zero terms are $u$-independent. Hence with
$$\mu_1=M(.08)-V_d\,\mathcal B_{1/3}(m^*)\frac{Q(m^*)}{.08}-B_1\frac{e^{-Am^*}}{.08},\qquad
\mu_2=M(.1)-V_d\,\mathcal B_{1/3}(m_2)\frac{Q(m_2)}{.08}-B_1\frac{e^{-Am_2'}}{.08},$$
we get $K^2-H(u)-T_1-T_2\ge\mu_iu-\mathcal E$ on $\mathcal P_i$, where
$\mathcal E=\eta_1(1+(V_d+\varepsilon_2)(a_d-b_d))+\varepsilon_2\mathcal B_{1/3}(0)(a_d-b_d)$ (use $Q(m)\le a_d-b_d$).

*Step 6 (numbers).* Interval arithmetic (`small_exception_tables.py`, and independently mpmath
at 40 digits, §7):

| piece | $M$ | other | first | margin $\mu_i$ | relative |
| --- | --- | --- | --- | --- | --- |
| $\mathcal P_1$ ($u=.08$, $m^*=2.7530442$) | .1088458429 | .0783116746 | .0000454655 | **.0304887029** | 28.0% |
| $\mathcal P_2$ ($m_2=2.829$, $m_2'=4.959$) | .1050056698 | .0668874692 | .0000000153 | **.0381181853** | 36.3% |

Choose $\eta_1,\varepsilon_2,\varepsilon$ (after $u_0$) with $\mathcal E+\varepsilon<.03u_0$. Then
$\frac{\varphi(q)}\ell\Sigma\ge(.0304-.03)u_0>0$. $\square$

**Remarks.** (i) With (13.3) applied at the fixed $\lambda=m^*$ rather than at $\lambda=m(u)$, every
analytic input has fixed parameters, so one $q_0(u_0)$ serves the whole piece; the checked
number is unchanged because at $u=.08$ the two coincide (hole H-1). (ii) The code checks
$\alpha(A-a_d)=1.787>1$, equivalent to the positivity of the lower limit. (iii) Recomputation of
H's rows from his printed parameters (Lemmas 7.1, 7.5): Table 2, $b=.10$, $\lambda=.965$, $k=\frac32$
gives $\lambda_{0b}=4.96355$; Table 5, $b=.10$, $\lambda=.89$, $k=2$ ($\theta=.98738$) gives
$\lambda_{2b}=2.84577$. Both exceed the printed values, so $\epsilon_T=.001$ is safe with room .0036 and
.0158. (iv) At lower exponents with the same $K,c_1,c_2$ the margins are .0204/.0292 (3.95),
.0062/.0167 (3.90) and .00007/.0112 (3.88), consistent with "positive down to about 3.90".

### 2.3 The tiny exceptional zero, $\lambda_1<u_0$

**Theorem (HB90, Corollary 1, p. 406).** Let $\psi$ be a real character mod $q$, not necessarily
primitive, and $\beta_0$ real with $L(\beta_0,\psi)=0$ and $\beta_0\ge1-\frac1{3\log q}$; put
$\eta_{HB}=((1-\beta_0)\log q)^{-1}$ ($\ge3$). For every $\delta>0$ there is an effectively computable
$\eta(\delta)$ such that $\eta_{HB}\ge\eta(\delta)$ implies $P(a,q)\le q^{3+\delta}$ for every $a$ coprime to $q$.

**Proposition 9.3.** Put $u_0=\min\bigl(1/\eta(\tfrac12),.08\bigr)$. For $q\ge q_0$, if $\lambda_1<u_0$ then
$P(a,q)\le q^{3.5}$ (or $\ll q^{3.5}$) for all $(a,q)=1$.

*Proof.* By Step 0 of 9.2, $\chi_1$ is real (nonprincipal) and $\beta_0:=\rho_1=1-\lambda_1/\ell$ is real, with
$(1-\beta_0)\log q=\lambda_1<u_0\le\frac13$. So $\eta_{HB}=1/\lambda_1>1/u_0\ge\eta(\frac12)$. Apply HB90 Cor. 1 with
$\delta=\frac12$. $\square$

Effectivity: $\eta(\delta)$ is effective, so $u_0$ is. The ineffective Corollary 2 ($q^{2+\delta}$) and X
Lemma 6.2(d) (p. 87–88: $P(q)\ll_\varepsilon q^{3.5+\varepsilon}$ for $\lambda_1\le\lambda(\varepsilon)$, effective $\lambda(\varepsilon)$ but
ineffective implied constant) are alternatives. H p. 48 explains why this separate input is
needed: "the estimates of this section have not been proved for extremely small values of
$\lambda_1$, since we are only concerned with zeros $\rho_0,\rho_2$ in the rectangle (6.1)". H p. 6 cites the same
result as "$P(a,q)\ll_\varepsilon q^{3+\varepsilon}$, providing that $\lambda\le\lambda(\varepsilon)$ … effective".

### 2.4 The large first zero, $\lambda_1\ge1.5$

**Proposition 9.4.** Let $L=3.99$ with the 16-step kernel and the inherited far weight
($c_1=.09035$, $c_2=.235968$, $\theta=1.28683$, $V=175.26640331\ldots$). For $q\ge q_0$: if
$\lambda_1\ge1.5$, then every reduced class contains a prime in $(q^{3.156342},q^{3.99})$.

*The LP.* All nonprincipal characters with an $R_P$ zero are ordinary, represented by their
rightmost zero with $|\gamma|\le1$ (parameter $\ge1.5$); bins $[1.5+\frac{j}{100},1.5+\frac{j+1}{100})$,
$j<150$, and the tail $[3,\infty)$; $F=\lceil(1+\eta)V\rceil_S=1752665785811216087$; $\mathrm{first}=0$;
$\mathrm{final}=5\cdot10^{10}$; no count, hidden or second-family rows; one near row.

*The near row* is the graded near lemma (PROOF §6.2) with $H=0$, $s=s_1=\frac32$, Gram test
$g_1=f_{3/2}$ and detector $f=f_1$ (parabolic autocorrelations), and no family entries. The safe
anchor hypothesis holds because every zero in $R(l)$ has $\lambda\ge\lambda_1\ge1.5$; for each entry no zero lies
right of the test point, so the response lemma holds with $S=\{\rho_\chi\}$ and no $T^*$ argument.
In the builders' normalization ($I_u\ge I_B$, $D_u=G_1(-s)$):
$d=\lceil(1+\eta)(d_0+\eta)\rceil_S=280760811507875$, $D=\lceil(1+\eta)(1-d_0)\rceil_S=9719259188502126$ with $d_0=g_1(0)/(6D_u)$,
features $\lfloor(F_Z(r_i-s)-f_Z(0)/6)/\sqrt{I_uD_u}-\eta\rfloor_S$. This is exactly what
`two_test_enclosures.constants/feat/norm` compute for $(\gamma_G,\gamma_Z,s)=(\frac32,1,\frac32)$: the
correction $C=\sup_{\mathrm{Re}\,z\ge0}(-\mathrm{Re}F_G(z))=0$ at $s-a=0$, hence $D=D_f$; the $N$ used is
$\sqrt{R_B^{up}R_G^{up}}$; all ratios are invariant under scaling $f$ or $g$.

*The certificate* (`results/large_branch_3.99.json`, checked by
`verify_published_single.scenario` after regenerating the input): 36 contiguous threshold
intervals covering $[0,e]$, $e=\lceil\sqrt{d\,T_S^2/S}\rceil$; on each, the first-order
relaxation (costs at $b$, budget $D(1-a^2/d)$ at $a$), duals $Y,Z\ge0$ satisfying
$YW_i+Z\lfloor(v_i-bS/T_S)_+^2/S\rfloor\ge D_SG_i$ for all 151 columns, and value
$\lceil(YF+ZB)/D_S\rceil+\mathrm{first}+\mathrm{final}<S$. Maximum
$9946508085154141/S=.9946508085154141$ at $[.1625,.165]$ ($Y=5139815868$, $Z=1622818786878$);
5,436 column checks; no exclusions. This is Theorem 7.7 in the special case $K=1$, orders 2.

*Proof.* Proposition 7.3 (with these inputs) and Theorem 7.7 give $W_{\rm occ}\le.9946508-5\eta+E_2+E_4$,
and the criterion (X (3.57)) with $\varepsilon=\eta H_0$ gives the prime. $\square$

---

## 3. PROOF §10: join and uniformity

**Theorem 10.1 (conditional on the premises of PROOF §11).** There is a constant $C$ such that
$P(a,q)\le C\,q^{3.99}$ for every $q\ge1$ and every $a$ with $(a,q)=1$.

*Proof.* Let $q\ge q_0$ ($q_0$ as in §3.2 below). Exactly one of the following holds.

1. No nonprincipal $L(s,\chi)$ vanishes in $R(l)$: Proposition 9.1.
2. Otherwise $\lambda_1$ is defined (a nonempty finite set of zeros in the compact $R(l)$; $\lambda_1>0$).
   * $\lambda_1<u_0$: Proposition 9.3 (exponent $3.5$).
   * $u_0\le\lambda_1\le.1$: Proposition 9.2 (exponent $3.99$).
   * $.1\le\lambda_1<1.5$: the configuration has a type (rr, rc, complex) and is *inside*
     ($|\mu_1|\le C_B$; always for rr since $\mu_1=0$) or *outside* ($|\mu_1|>C_B$, which since
     $\lambda_1<1.5<C_B$ is the only way to leave $R_B$). The source cover and the case tree
     (PROOF §§5, 8; other components) place it in a leaf or an exclusion node. By Corollary 7.13,
     $W_{\rm occ}\le v^*/S-5\eta+E_2+E_3+E_4<1-2\eta$ (§4), and X (3.57) with $\varepsilon=\eta H_0$ gives a
     prime in $(q^{A},q^{3.99})$.
   * $\lambda_1\ge1.5$: Proposition 9.4.

The overlap at $\lambda_1=.1$ is harmless. A prime below $q^{L'}$ with $L'\le3.99$ is below $q^{3.99}$. For
$q<q_0$ there are finitely many pairs $(a,q)$; put
$C=\max\bigl(1,\max_{q<q_0}\max_{(a,q)=1}P(a,q)q^{-3.99}\bigr)$. $\square$

### 3.1 Uniformity

* **Finiteness.** The case tree has finitely many leaves (3,146 inside incl. 233 identities
  nodes, 1,642 outside at 3.99), each with fixed rational data, fixed tests and anchors, and
  finitely many offsets (grid $1/200$). The exterior regimes use finitely many fixed inputs. So
  finitely many source thresholds occur, and $q_0$ is their maximum.
* **Unboundedly many characters.** Three kinds of error are summed over characters:
  (a) the per-character envelope errors (E2) and (b) the smoothing errors (E4), both carrying the
  factor $e^{-A\lambda_\chi}$ and summed through the far resource; (c) the near-lemma errors, which
  are uniform per entry ($\eta'$ inside every feature and radius) or a uniform $o(1)$ multiple of
  $(\sum a_j)^2$ in the Gram form (PROOF §6.3). No error is multiplied by the number of
  characters.
* **Heights.** Every test point has physical height $\le2l\le\ell/5$, inside the uniform ranges of X
  Lemmas 3.1–3.4 (PROOF §6.3); this is §6's responsibility.

### 3.2 The order of the constants

| Stage | Fixed | Depends on |
| --- | --- | --- |
| S0 | $L=3.99$; the 16-step kernel; both far profiles and $V$; all tests, anchors ($s_{\max}$ = largest anchor), grids ($\mathrm{den}$, $1/400$, offsets $1/200$); the case tree, leaves and certificates; $\eta=\eta'=10^{-6}$; the small-branch data $K,c_1,c_2,\alpha,\epsilon_T=10^{-3}$; $u_0=\min(1/\eta_{HB}(\frac12),.08)$ | nothing |
| S1 | $\varepsilon_c=\eta H_0$; $C_P\ge\max(C_0(\varepsilon_c),3)$ ($C_0$ of X (3.57) for the step kernel) | S0 |
| S2 | the auxiliary smoothing $\psi_\delta$ of the envelope tests, with $E_4\le\eta$ | S0, S1 ($N(C_P)$, $K_{\rm far}$) |
| S3 | $K_0$ = uniform bound (log-free density) for the number of zeros of all $L(s,\chi)$, $\chi\bmod q$, with $\lambda\le s_{\max}$ and $\lvert\gamma\rvert\le2$; then $M$ with $\lvert F(x+iY)\rvert\le\eta'/(2K_0)$ and $\lvert G_1(-\sigma+iY)\rvert\le\eta'/4$ for $\lvert Y\rvert\ge M$ (all fixed tests, $x,\sigma$ in fixed compact ranges); then $C_B>\max(C_P+M,1.5)$ with $4c_{\rm out}/(H_0C_B^2)\le\eta$ | S0, S1 |
| S4 | tolerances of X Lemmas 3.1, 3.2 (and its disc radius $\delta\le\frac16$), 3.10 ($\varepsilon_1=\eta H_0/19$), 5.1 ($\le\eta V$), Graham, Burgess, PNT; every table $\varepsilon$ below its margin (e.g. $\epsilon_T$ for H Tables 2, 5; $\frac1{1100}$ for H Lemma 8.8); the small branch's $\varepsilon,\eta_1,\varepsilon_2$ with $\mathcal E+\varepsilon<.03u_0$ and its $R(\varepsilon)$ | S0–S3 |
| S5 | $q_0$ = max of all thresholds of S1–S4, of X Lemma 3.3, of the rectangle inclusions ($C_P\le\frac13\log\log\ell$, $C_B/\ell\le1$, $R_B$ inside the local discs), and $\ell>4M(K_0+1)$ | all |

**No circularity.** The dependency graph is S0 → S1 → S2, S0/S1 → S3 → S4 → S5; it is acyclic:

* The certificates (S0) depend only on $L,\eta,\eta'$ and fixed data, not on $C_P,M,C_B,\delta,T^*$ or $q$.
* $K_0$ counts zeros to height $2$, not $1+\delta$: $\delta$ is fixed in S4 and $M$ (S3) depends on $K_0$;
  since $\delta<1$ always, height 2 dominates (interface closure §5).
* $T^*\in[\frac12,1]$ is chosen for each $q$ by pigeonhole: split $[\frac12,1]$ into $K_0+1$ intervals;
  one contains no $|\gamma|$ of the $\le K_0$ zeros; its midpoint is at distance
  $\ge\frac1{4(K_0+1)}\ge M/\ell$ from every such $|\gamma|$ when $\ell\ge4M(K_0+1)$. The localized envelope
  needs $\delta<\frac12\le T^*$, true for every $T^*$ because $\delta\le\frac16$ (H p. 14 proof of Lemma 3.1;
  H p. 24 allows $\delta=1/\log\ell$).
* $u_0$ is fixed in S0 from an effective constant of HB90 that does not depend on anything else;
  the small-branch errors are chosen after it.

**Effectivity.** Every input is claimed effective (Burgess, Graham, H's tables, the log-free
density for $K_0$, HB90 Cor. 1); hence $q_0$ and $C$ are effective but not computed. This was
not audited input by input (hole H-11); it is not needed for the statement $L\le3.99$.

---

## 4. The error allowance $\mathrm{final}=5\eta$ (PROOF §2)

Every leaf value contains $\mathrm{final}/S=5\eta$. The true occurrence sum differs from the LP
objective by at most the following.

| Term | Content | Bound (normalized by $H_0$) |
| --- | --- | --- |
| E1 | the criterion's $\varepsilon=\eta H_0$ (X (3.57)) | $\eta$ |
| E2 | per-character envelope errors, $\varepsilon_1e^{-A\lambda_\chi}$ each, $\varepsilon_1=\eta H_0/19$ | $\le\eta K_{\rm far}/19<\eta$ |
| E3 | $\le4$ distinguished outside first-family terms, each $\le c_{\rm out}/C_B^2$ | $\le4c_{\rm out}/(H_0C_B^2)\le\eta$ |
| E4 | smoothing: $K_{\rm far}\bigl[N(C_P)\cdot2\|\psi-\psi_\delta\|_1/\|\psi\|_1+\sup_{\lambda\ge0}\lvert B_\delta(\lambda)-B(\lambda)\rvert\bigr]$ | $\le\eta$ |

**Lemma 4.1 (E2).** Let $w$ be the leaf's far profile, $A>2x$. For every choice of one zero per
character as in (I1), $\sum_\chi e^{-A\lambda_\chi}\le K_{\rm far}:=(1+\eta)V/w(0)$. For the inherited
profile $K_{\rm far}=16.3717$, for the retuned one $18.4712$.

*Proof.* $e^{-A\lambda}/w(\lambda)=\int_u^xw_0(t)^2e^{-(A-2t)\lambda}dt$ is decreasing on $\lambda\ge0$ because
$A-2t\ge A-2x>0$. Hence $e^{-A\lambda_\chi}\le w(\lambda_\chi)/w(0)$; sum and use (I1). Numerically
$w(0)^{-1}=\int_u^x e^{-\theta t}\sqrt{\min(t-u+\epsilon_0,c_2+\epsilon_0)}\,dt=.0934101463$ (inherited, $u=.5140333$,
$x=1.1736847$) and $.0759127165$ (retuned, $u=.4977177$, $x=1.1303336$). $\square$

Hence the per-character envelope errors total $\le(\varepsilon_1/H_0)K_{\rm far}<\eta$. The error form
$\varepsilon_1e^{-A\lambda}$ comes from X Lemma 3.10 (p. 35) applied with $H_2(z)=e^{A\lambda}H(z)$ and
$f_1^\lambda=f_\lambda$ (so $|H_2(\lambda+it)|=|\Psi(\lambda+it)|^2=\mathrm{Re}\,F_\lambda(it)$), whose threshold is uniform in
$\lambda\in(\lambda_{11},C_0]$ (X p. 35–36), after smoothing (E4). It applies to ordinary characters (bins
and tail, anchor = representative), the reserved family (anchor $\nu_2$), hidden columns
($e^{-At}\times$ the envelope at $p_h$, $t$ = the far representative) and to $J_{new}$ ($e^{-Ap}$ with
$p\ge b\ge\lambda_1$). For $J_{old}$ with $p<b$ the factor is $e^{-Ap}$ with possibly $p<\lambda_1$ (hole H-7).

**Lemma 4.2 (E4).** If $\psi_\delta\ge0$ with $\|\psi_\delta\|_1\le\|\psi\|_1$, then for $\mathrm{Re}\,z\ge0$,
$|\Psi(z)^2-\Psi_\delta(z)^2|\le2\|\psi\|_1\|\psi-\psi_\delta\|_1$, so each zero changes by at most
$2e^{-A\lambda_\rho}\|\psi-\psi_\delta\|_1/\|\psi\|_1$ after normalization by $H_0=\|\psi\|_1^2$. With at most $N(C_P)$
zeros per character in $R_P$ and $\lambda_\rho\ge\lambda_\chi$, and $|B_\delta-B|$ for the envelope itself, the sum is at
most the E4 entry. It is $\le\eta$ once $\delta$ is small (S2), since $B_\delta\to B$ uniformly on $\lambda\ge0$ as
$\psi_\delta\to\psi$ in $L^1\cap L^2$. $\square$

**Proposition 4.3.** In every leaf, $W_{\rm occ}\le v^*/S-5\eta+E_2+E_3+E_4\le v^*/S-2\eta$, and the
criterion's bracket is $\ge H_0(1-W_{\rm occ}-\eta)\ge H_0\eta>0$.

Not charged to final (already inside other bounds): prime powers (X's $\Sigma$ is over primes,
X p. 33, the correction $O(q^{-(L-2K)/2})$ is inside (3.57)); the far lemma's $\varepsilon$ (inside
$(1+\eta)V$); the near-lemma errors (inside $\eta'$); enclosure errors (outward rounding). The
interface-closure note §6 lists only E1–E3 ($3\eta$) and makes E4 optional; PROOF §2 lists
E1–E4 ($4\eta$). Both are $<5\eta$; the spare $\eta$ is available (hole H-7).

The small branch (§2.2) and the tiny branch (§2.3) do not use final: the small branch has its
own margin $\ge.0304u$, against errors chosen below $.03u_0$.

---

## 5. Literature inputs: printed statement, hypotheses, page, and how they are used

Pages: X printed = PDF; H = retained ORA preprint pagination (see H-3); HB90 journal pages.

| # | Source, statement, page | Printed content and hypotheses (checked in the retained text) | Use here and match |
| --- | --- | --- | --- |
| L1 | X (3.51), (3.56)–(3.58), pp. 33–35 | $\Sigma=\sum_{p\equiv a}\frac{\log p}p h(\log p/\ell)$ over primes; for $h=\sum_i\alpha_ih_{L_i,K_i}$, $\alpha_i$ real, $L_i>2K_i+3$, fixed $\varepsilon>0$: $\exists C_0(\varepsilon),q_0(\varepsilon)$ with $\Sigma\ge\frac\ell{\varphi(q)}(H(0)-\sum_\rho\sum'_{\chi\ne\chi_0}|H((1-\rho)\ell)|-\varepsilon)$, $\Sigma'$ over $1-C_0/\ell\le\beta\le1$, $|\gamma|\le C_0/\ell$ (3.58) | Step kernel = 31 triangles with $L_k-2K_k=A+k\kappa\ge3.156>3$; single triangle ($K=.1821$) in §2.2; E1; Props 9.1, 9.4 |
| L2 | H §13, p. 79; Lemma 13.2, p. 81 | Same criterion for one triangle $f$ with $0<2K<L$, hypothesis $L>2K+3$, $\Sigma$ over primes, zeros counted in $1-R/\ell\le\beta\le1$, $|\gamma|\le R/\ell$, $R=R(\varepsilon)$, $q$ large | §2.2 Step 1 ($3.99>3.3642$) |
| L3 | H Lemma 13.3, (13.3), pp. 81–82 | For $\chi\ne\chi_0$ with no zeros in $1-\lambda/\ell<\beta\le1$, $|\gamma|\le1$, $0<\lambda\le R$, and $\eta>0$: $\sum'_\rho|F_2((1-\rho)\ell)|\le\frac\phi2\frac{1-e^{-2K\lambda}}\lambda+\frac{2K\lambda-1+e^{-2K\lambda}}{2\lambda^2}+\eta$ for $q\ge q(\eta)$; $\lambda\to0$ gives $\phi K+K^2+\eta$ | $\mathcal B_\phi(m)$ with $\phi=\frac13$ (other characters, $\lambda=m^*$ or $m_2$, fixed) and $\phi=\frac14$ ($\chi_1$, $\lambda=u_0/2$). Matches H's own use in §14 (p. 83: "$\lambda=0$ and $\phi=\frac14$ for $\chi=\chi_1$") |
| L4 | X (5.18), p. 66 = H Lemma 11.1, (11.3), p. 68 | $\lambda_0=\frac13\log\log\ell$, $\varepsilon,c_1,c_2>0$, $\phi=\max_\chi\phi(\chi)$, $q\ge q_0(\varepsilon,c_1,c_2)$: $\sum_{k\le N(\lambda_0)}\lambda^{(k)}/(e^{(4\phi+6c_1+2c_2)\lambda^{(k)}}-e^{(2\phi+4c_1)\lambda^{(k)}})\le\frac{2\phi+2c_1+c_2}{4c_1c_2}+\varepsilon$; $N(\lambda)$ counts characters with a zero in $\sigma\ge1-\lambda/\ell$, $|t|\le1$, and $\rho^{(k)}$ is *any* chosen such zero (H p. 68) | §2.2 Step 4 with $\phi=\frac13$ (monotone: LHS decreases, RHS increases in $\phi$), $c_1=.057$, $c_2=.1554$; exponents $a_d,b_d$ and $V_d$ exactly as stored |
| L5 | X Lemma 5.1, (5.19), p. 66 | Far density with profile $w_0$ (continuous, piecewise $C^1$, $1\ll w_0\ll1$, $w_0'\ll1$), $M$ pieces, $\alpha_i\ge0$, $\sum\alpha_i=1$ | (I1), E2 (Lemma 4.1). Other component (§4) |
| L6 | H Lemma 2.5, p. 10; X p. 17 | $\phi(\chi)=\frac14$ if $q$ cube-free or $\mathrm{ord}\,\chi\le\ell$; $\frac13$ otherwise | $\phi(\chi_1)=\frac14$ for the real $\chi_1$ (order 2); $\phi\le\frac13$ always. So $B_{1/4}$ for real characters is *printed* (see H-12) |
| L7 | H §6, pp. 26–28 | Numbering: $\rho_1$ rightmost in $R$ (6.1), families removed whole; $\rho_0\ne\rho_1$ rightmost other zero of $L(s,\chi_1)$ in $R$, "or a repeated zero $\rho_0=\rho_1$", excluding $\bar\rho_1$ when $\chi_1$ real and $\rho_1$ complex | $\lambda_0$ bounds every other zero of $\chi_1$ and excludes a multiple $\rho_1$; $\lambda_2$ bounds every zero of every $\chi\ne\chi_1,\bar\chi_1$ |
| L8 | H Lemma 6.3, p. 30; p. 38; Table 2, p. 39 | $\chi_1,\rho_1$ real; $\lambda_0\ge\lambda_{0b}-\varepsilon$ for $q\ge q(\varepsilon,b)$ whenever $0\le\lambda_1\le b$; printed values "a little below $\lambda_{0b}$"; row $b=.10$: $\lambda=.965$, $\lambda_0=4.96$ | $\lambda_0\ge4.959$ on $\mathcal P_2$. Recomputed: $\lambda_{0b}=4.96355$ ($k=\frac32$) |
| L9 | H Lemma 8.4, p. 43 | $\chi_1,\rho_1$ real, $\varepsilon>0$: $\lambda_0\ge(2-\varepsilon)\log(1/\lambda_1)$ if $\lambda_1\le.2$ and $q$ large | other zeros of $\chi_1$ on $\mathcal P_1$ (code uses the weaker $1.09\log(1/u)$) |
| L10 | H Lemma 8.5, p. 45; Table 5, p. 46 | Lemma 8.5 ($\lambda_2\le\lambda_0$; $\psi\le\frac{11}{24}$); Table 5 computed with the $k=2$ function "in the same way as … Tables 1 and 2"; "the condition $\lambda_2\le\lambda_0$ is redundant"; row $.10$: $\lambda=.89$, $\lambda_2=2.83$ | $\lambda_2\ge2.829$ on $\mathcal P_2$. Recomputed: $\lambda_{2b}=2.84577$ |
| L11 | H Lemma 8.8, p. 48 | $\chi_1,\rho_1$ real, $\varepsilon>0$: $\lambda_2\ge(\frac{12}{11}-\varepsilon)\log(1/\lambda_1)$ if $q\ge q(\varepsilon)$; "not proved for extremely small values of $\lambda_1$" | $\mathcal P_1$ with $\varepsilon=\frac1{1100}$, $u\ge u_0$ fixed |
| L12 | H Lemmas 7.1, 7.5, pp. 34, 36 | the extremal functions; $\sin^2\theta=k(1-\theta\cot\theta)$ | only for the recomputation of L8, L10 |
| L13 | X Lemma 4.5, Table 11, pp. 60–61 | $\chi_1$ or $\rho_1$ complex $\Rightarrow\lambda_1>.440$ ($q\ge q_0$) | §2.2 Step 0; §2.3 |
| L14 | X Lemma 3.3 (= H Lemma 6.1), p. 19 | $l=l(q)\le\ell/10$ with no zeros in $R(10l)\setminus R(l)$, $q\ge q_0$ | definition of $R(l)$, $\lambda_1$ |
| L15 | X Lemma 3.10, pp. 35–36 | uniform in $\lambda\in(\lambda_{11},C_0]$, $q_0$ depending on $\varepsilon,M,\lambda_{11},C_0$ only; bound $F_1^\lambda(-\lambda)+f_1^\lambda(0)/6+\varepsilon$; Condition 1 needed | E2, E4, uniformity remark in §2.2 |
| L16 | HB90, Corollary 1, p. 406 (hypotheses p. 406) | real $\psi$ mod $q$, *not necessarily primitive*; $L(\beta_0,\psi)=0$, $\eta_{HB}=((1-\beta_0)\log q)^{-1}\ge3$; for any $\delta>0$ an *effectively computable* $\eta(\delta)$ with $\eta_{HB}\ge\eta(\delta)\Rightarrow$ [display illegible in the retained OCR; per PROOF.md and H p. 6: $P(a,q)\le q^{3+\delta}$] for all $a$ coprime to $q$ | §2.3 with $\delta=\frac12$ |
| L17 | H p. 6 | cites HB90: "$P(a,q)\ll_\varepsilon q^{3+\varepsilon}$, providing that $\lambda\le\lambda(\varepsilon)$ … effective" | corroborates L16 |
| L18 | X Lemma 6.2(d), pp. 87–88 | effective $\lambda(\varepsilon)$, $\lambda_1\le\lambda(\varepsilon)\Rightarrow P(q)\ll_\varepsilon q^{3.5+\varepsilon}$ with ineffective implied constant | alternative to L16 |
| L19 | H p. 14 (proof of Lemma 3.1), p. 24 (after Lemma 5.2) | $\delta=\min(\frac1{2k},\frac{\varepsilon_0}{3c_0k^2})$, $k\ge3$, so $\delta\le\frac16$; "one may take $\delta=1/\log\ell$" | $\delta<\frac12\le T^*$ (§3.2) |

---

## 6. HOLES AND CONCERNS

No blocking or major defect was found in these components. The soundness proof of the
certificate checker (PROOF §7; §1 here) is complete and matches the Lean proof; the exterior
numbers reproduce exactly; the constant order is acyclic. The items below are ordered by
severity; H-1 to H-7 need text changes in the paper, the rest are documentation or
observations.

**H-1 (minor; §9 small branch, uniformity).** PROOF §9 and 4.33 §6 reduce the piece
$u_0\le u\le.08$ to $u=.08$ by monotonicity in $u$, with the gap $m(u)=1.09\log(1/u)$ fed into
H (13.3). Read literally, (13.3) is then applied with a $u$-dependent $\lambda=m(u)$, and the text
does not say why one $q_0$ serves all $u\in[u_0,.08]$ (H's Lemma 13.3 does not state uniformity in
$\lambda$). *Fix* (no numbers change): apply (13.3) with the fixed $\lambda=m^*=1.09\log12.5$ (valid
since $m(u)\ge m^*$) and use $m(u)$ only inside the elementary factor
$Q(m(u))/u=\int_{A-a_d-1/\alpha}^{A-b_d-1/\alpha}e^{-tm(u)}dt$; for $\chi_1$ use $\lambda=u_0/2$ (§2.2). Alternatively
cite X Lemma 3.10's uniformity in $\lambda\in(\lambda_{11},C_0]$ (X p. 35–36). Also state explicitly
that the analytic errors are chosen after $u_0$ below $.03u_0$.

**H-2 (minor; §9 tiny zero, source verification).** The retained OCR of HB90 p. 406 drops the
displayed formulas of the hypothesis on $\beta_0$ and of Corollary 1. What is legible: $\psi$ real,
"not necessarily primitive", $\eta=\{(1-\beta_0)\log q\}^{-1}$ "so that $\eta\ge3$", "effectively
computable constant $\eta(\delta)$", "for any $a$ coprime to $q$". The exponent $3+\delta$ is
corroborated by H p. 6 ($\ll_\varepsilon q^{3+\varepsilon}$, effective) and X p. 88. *Fix*: check the display
against a clean scan and quote it (including whether it is "$\le$" or "$\ll$" and any "$q$
sufficiently large"); either form suffices. The proof must also take $u_0\le\min(.08,\frac13)$ (so
that $\eta_{HB}\ge3$ and the pieces fit); PROOF §9 says only $u_0=1/\eta(1/2)$. Rename HB90's $\eta$
to avoid the clash with $\eta=10^{-6}$.

**H-3 (minor; citations).** Every "H p. n" in PROOF.md, 4.33.md and the code refers to the
retained ORA preprint's own pagination (e.g. Table 2 on p. 39, Table 5 on p. 46, (13.3) on
p. 82), not to Proc. London Math. Soc. (3) 64 (1992) 265–338. The paper must cite statement
numbers with journal pages, or state the preprint explicitly. X pages are fine (printed = PDF).

**H-4 (minor; PROOF §7 text vs code).** (a) The hidden count is stated as $\sum y_h\le n$; in the code
the hidden *tail* column has variable = far mass $\sum w(t)$ and coefficient $N=\lfloor S/w(R_h)\rfloor$
(verified on outside roots 1990 and 1107: $N_{\rm tail}=242486230730708033$). The ordinary tail's
variable is also a far mass, not a count (stated in §4 but not in §7, where "$x_i$ counts
characters"). (b) With a reserved family, bins with $hi\le\lambda_3^{lo}$ are *deleted*, not just
left out of the count row. (c) Ties at a bin end must go to the upper bin (half-open bins);
otherwise a third-family character with $\lambda=\lambda_3=\lambda_3^{lo}=hi_i$ could be counted in a count
bin. (d) The displayed column inequality omits $UN_c$ and the scale $D_S$. (e) The rounding list
should include features (down, clamped), diagonals and radii (up), $N_{\rm tail}$ (down), $F$ and
first (up). *Fix*: adopt Definitions 7.1–7.6 above (they match `graded_cert` and `Cert.Feasible`).

**H-5 (minor; E3 and E4 undefined constants).** $c_{\rm out}$ (E3) is never defined in PROOF.md
or the notes. It should be: for the finitely many outside leaves' first-family auxiliary tests
$f_p$ and anchors, a constant with $|\mathrm{Re}\,F_p(x+iY)|\le c_{\rm out}Y^{-2}$ for the relevant
$x$ and $|Y|\ge1$ (two integrations by parts; 4.33 §2 "Disc, height, and regularity details"),
together with the count "at most four" (two characters, at most two distinguished occurrences
each). $N(C_P)$ (E4) needs a cited uniform bound for the number of zeros of one $L(s,\chi)$ in
$R_P$ (standard, $\ll C_P+1$ uniformly in $\chi\bmod q$).

**H-6 (minor; large branch, premise tag and checker).** 4.33 §7 calls the large-branch row "the
inherited two-test inequality" ([R]); PROOF §9 calls it "§6.5 with $s=s_1=1.5$, $H=0$" ([N],
formalized). I checked that `two_test_enclosures.constants/feat/norm` with
$(\gamma_G,\gamma_Z,s,a)=(\frac32,1,\frac32,\frac32)$ compute exactly the builders' normalization of the
graded near lemma with $H=0$ (the correction $C$ vanishes, $D=D_f$), so the §6 reading is valid
and the [R] premise is not needed. PROOF §11's premise row "Exterior branches … P/R" should say so.
Note also that this certificate is checked by `verify_published_single.scenario` (first-order
intervals), not by `graded_cert`/Lean; it is covered by Theorem 7.7's proof but not by the Lean
run.

**H-7 (minor; E2 bookkeeping).** E2 bounds errors of the form $\varepsilon_1e^{-A\lambda_\chi}$ with $\lambda_\chi$ the far
representative. The first family's $J_{old}$ (used when $p<b$) carries its error with the factor
$e^{-Ap}$, and $p$ may be below $\lambda_1$; the excess is at most $e^{A(b-a)}$ for at most two characters.
Also the "+$\varepsilon$" of $J_{new}$ is not in the code's `first` (semantics note §4.1) and is charged
to E2. *Fix*: say so, and charge the first family's errors to the spare $\eta$ of final (E1–E4
use $4\eta$), or take $\varepsilon_1=\eta H_0/21$.

**H-8 (minor; documentation of the maximum).** PROOF.md says "maximum $.99999982<1$"; the
recorded maximum is $.9999998223456688$ (nodes corpus). State $<.99999983$ or the exact value.

**H-9 (minor; status text).** PROOF §11 says the Lean-compiled checker was run on the outside
corpus; `computations/graded/lean_runs/leafcheck_full_inside_3.99.json` records the native
`leafcheck` passing the full inside corpus as well (3,949 leaves including node leaves,
4,109,455 boxes, maximum $9999998223456687$), plus the numeric and row checks. Update.

**H-10 (minor; A > 2x assertion).** The tail columns require $A>2x$. It is asserted in
`replace_far` and in `verify_published_single` (large branch), but not for inherited-weight
leaves built by `make_endgame` (semantics note §4.5). It holds ($2.347<3.156$), but the paper
should state it as a checked condition at $L=3.99$.

**H-11 (minor; effectivity).** "All inputs are effective" is asserted, not audited per input
(Burgess, Graham, the log-free density behind $K_0$, H's tables, the repository rows). Not
needed for $L\le3.99$ with some $C$; state as a remark with references or drop.

**H-12 (observation; premise tag).** $B_{1/4}$ for real characters is tagged [PD] in PROOF §3,
§11, but $\phi(\chi)=\frac14$ for $\mathrm{ord}\,\chi\le\ell$ is printed (H Lemma 2.5, p. 10; X p. 17), and H
itself uses $\phi=\frac14$ for the real $\chi_1$ in (13.3) (H p. 83). It can be tagged [P].

**H-13 (observation; Table 5 convention).** H states the "a little below" convention for
Table 2 (p. 38) and only "in the same way" for Table 5 (p. 45). My recomputation from H's
printed parameters (λ = .89, k = 2) gives $\lambda_{2b}=2.84577>2.83$, so the row is valid with
$\epsilon_T=.001$ (room .0158). Record the recomputation in the paper.

**H-14 (observation; code-level redundancies that are safe).** The small-branch code charges
$\chi_1$'s other zeros on $\mathcal P_1$ with the gap $1.09\log(1/u)$ instead of Lemma 8.4's
$(2-\varepsilon)\log(1/u)$, and uses $B_{1/4}(0)=K^2+K/4$; both are conservative. With $\phi=\frac13$
instead the "first" term would rise from .0000455 to .0000542 on $\mathcal P_1$ — irrelevant.

**Checked and found correct (no hole):** the root-box end formula and its containment; both
relaxations and every rounding direction; the strict exclusion rule and why case 1 needs it;
weak duality with signed costs and the free dual $P-M$; the Python checker equals the Lean
checker on accepted inputs (Python adds only restrictive assertions); tail and hidden-tail
semantics (feature 0 in every row, far cost $S$, count 0); the small-branch arithmetic
(margins .0304887 and .0381182, 28.0% and 36.3%); the large-branch certificate (.9946508085154141,
36 intervals, 5,436 column checks); $K_{\rm far}=16.3717,18.4712<19$; $2x=2.347,2.261<A$; the order of
constants.

---

## 7. Verification log (this session)

All commands were run with `.venv/bin/python` in the repository (read-only use).

1. `small_exception_tables.check()` and `small_exception_399.check()`: pass; piece margins
   `304887028609599`, `381181853361608` (scale $10^{16}$); old single check `8039784319735`.
2. Independent mpmath (40 digits) recomputation of the three quantities per piece: margins
   $.030488702860959985$ ($\mathcal P_1$), $.038118185336160880$ ($\mathcal P_2$); relative 28.01%, 36.30%;
   $\alpha(A-a_d)=1.78724$; $A-a_d-1/\alpha=236171/327000$. Margins at 3.95, 3.90, 3.88 as in §2.2.
3. Recomputation of H Table 2 row .10 ($\lambda=.965$, $k=\frac32$) and Table 5 row .10 ($\lambda=.89$, $k=2$)
   from Lemmas 7.1, 7.5, 6.3, 8.5 by quadrature (script `scratchpad/deepdive/hb_tables.py`):
   roots $4.963551$ and $2.845770$; closed forms of Lemma 7.1 agree with quadrature.
4. `verify_published_single.scenario(large_branch_3.99.json, None, '3.99', regen=True)`:
   maximum $9946508085154141$, 36 branches, 0 excluded, 5,436 checks; $d=280760811507875$,
   $D=D_f=9719259188502126$, $F=1752665785811216087$.
5. $K_{\rm far}$ by quadrature: $16.371676739790978$ (inherited), $18.471175129831978$ (retuned);
   $x=1.1736847$, $1.1303336$; $A=3.156342$.
6. An exact-rational checker written from Definitions 7.1–7.6 (`scratchpad/deepdive/indep_leaf.py`,
   `indep_inside.py`; it recomputes costs and budgets without rounding and re-checks every
   exclusion and dual) on leaves regenerated by the repository replay: outside roots 1990 (41
   boxes; exact max $.9999942478462505$ vs stored $.9999942478462508$) and 1107 (309 boxes, count dual
   used); inside roots 1220 (19 second-family columns, 665 boxes), 10 (257), 1146 (rc height
   split, 44+110), 567 (44 second-family columns, 1,540), 1416 (six leaves incl. three fully
   infeasible ones; hardest $.9999998132810006$). In every case the exact value is $\le$ the integer
   value, as Theorem 7.7's rounding analysis predicts; tail features are 0 in every row.
7. Read, not re-run: Lean `Cert/Relax.lean`, `Cert/Sound.lean`, `Cert/Bins.lean`, `Defs.lean`
   (Cert section), `Cert/FastEq.lean` header; no `sorry` in these files; the recorded Lean runs
   in `computations/graded/lean_runs/`.

---

## 8. References

* [X] T. Xylouris, *Über die Nullstellen der Dirichletschen L-Funktionen und die kleinste
  Primzahl in einer arithmetischen Progression*, Bonner Mathematische Schriften 404, 2011
  (dissertation). Used: pp. 17–21 (φ(χ), Lemmas 3.1–3.4), 33–36 ((3.51)–(3.60), Lemma 3.10), 60–61
  (Table 11, Lemma 4.5), 66 ((5.18), Lemma 5.1), 87–88 (Lemma 6.2).
* [H] D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in an
  arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338. Page numbers here are
  those of the retained preprint: pp. 6, 10, 14, 24, 26–30, 34–39, 43–48, 68, 79–85.
* [HB90] D. R. Heath-Brown, *Siegel zeros and the least prime in an arithmetic progression*,
  Quart. J. Math. Oxford (2) 41 (1990) 405–418; Corollary 1, p. 406.
* Repository: `research/PROOF.md` §§2, 7, 9, 10, 11; `research/arguments/4.33.md` §§2, 6–8;
  `research/arguments/sieve-majorant-near.md` §§6a, 6e, 8; `research/notes/interface-closure-2026-09-29.md`
  §§3, 5, 6; `research/notes/independent-checks-2026-09-29.md`;
  `research/notes/leaf-data-semantics-2026-09-29.md`.
* Code: `computations/graded/graded_cert.py`, `graded_leaves.py`, `graded_driver.py`,
  `graded_verify.py`; `computations/core/code/small_exception_tables.py`,
  `small_exception_399.py`, `verify_published_single.py`, `published_single_inputs.py`,
  `two_test_enclosures.py`, `triple_inputs.py`; `computations/near/code/first_outside_blocks.py`;
  `computations/frontier/verify_existing_components.py`, `existing_components_verified.json`.
* Lean: `lean-graded/GradedNear/Defs.lean` (namespace `GradedNear.Cert`),
  `Cert/Relax.lean` (`relax_first`, `relax_tangent`), `Cert/Sound.lean` (`checkLeaf_sound`,
  `certified`), `Cert/Bins.lean` (`near_row_of_bins`), `Cert/Relaxation.lean`
  (`leaf_relaxation`), `Cert/Semantics.lean` (`leaf_interpretation`), `Cert/FastEq.lean`
  (`checkLeaf_toCore`, `checkLeaf_ofCore`).
