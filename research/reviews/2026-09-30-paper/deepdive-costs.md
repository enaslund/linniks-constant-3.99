# Notation, prime detection, zero costs and the error allowance

*Component write-up and verification for PROOF.md §§1–3, the error allowance
of §2 and its use in §10. Written 2026-09-30 from the repository at commit
`3e63657`. The component was checked against the printed texts (X = Xylouris,
dissertation; H = Heath-Brown 1992), the code (`config_v4.py`,
`enclosures.py`, `triple_inputs.py`, `published_single_inputs.py`,
`first_outside_blocks.py`, `graded_leaves.py`) and the Lean definitions
(`lean-graded/GradedNear/{Kernel,Functions,KernelFacts,Prime,Envelope,Adapters}.lean`).*

**Page conventions.** X is cited by its printed page numbers. In the PDF these
equal the PDF page numbers (checked on pp. 17–37 and 77–83). H is cited by
lemma or equation number and by the page of the 99-page author copy (Oxford
repository) held in the repository. That copy's pagination is **not** the
journal's (Proc. LMS 64 (1992) 265–338). Where X gives a journal page for an
H statement, it is added as "journal p.".

**Verdict in one paragraph.** The component is sound. Every step can be derived
from printed statements of X and H together with elementary facts about the
kernel. Four steps are derivations from printed *proofs* [PD], not printed
*statements*:
* the localized (disc) form of X Lemma 3.10;
* the radius bound $\delta\le1/6$;
* the conductor coefficient $1/4$ for real characters;
* the smoothing of the step kernel.

All four check out. The repository only sketches the per-character zero count
that the smoothing needs, for $\lambda_1\ge.1$ only. It asserts the old
first-family bound in the case $p<b$ without proof. Complete proofs are given
below (Lemma 3.8, Proposition 3.13).
No blocking or major hole was found in this component. The minor items are
listed in §6.

---

## 1. Notation

Throughout, $q$ is the modulus and $\ell:=\log q$ (H and X write
$\mathcal L$). All characters are Dirichlet characters mod $q$, and $\chi_0$
is the principal character. Every inequality below holds for $q\ge q_0$,
where $q_0$ depends only on finitely many fixed choices (§4.2). Put
$\eta:=10^{-6}$.

**Definition 1.1 (normalized coordinates).** Let $\chi\neq\chi_0$. Write
$Z(\chi)$ for the multiset of nontrivial zeros of $L(s,\chi)$, and
$m_\chi(\rho)\ge1$ for multiplicities. For a zero $\rho$ put
$$
\lambda_\rho:=(1-\operatorname{Re}\rho)\,\ell,\qquad
\mu_\rho:=(\operatorname{Im}\rho)\,\ell,\qquad
\rho=1-\frac{\lambda_\rho}{\ell}+i\,\frac{\mu_\rho}{\ell},\qquad
\hat\rho:=(1-\rho)\ell=\lambda_\rho-i\mu_\rho .
$$
$\operatorname{Im}\rho$ is the *physical* height and $\mu_\rho$ the
*normalized* height. Since $L(s,\chi)\ne0$ for $\operatorname{Re}s\ge1$, every
zero has $\lambda_\rho>0$.

**Definition 1.2 (regions).**
* **Enlarged rectangle** (X (3.7), p. 18):
  $$R(x):=\Bigl\{\sigma+it:\ 1-\tfrac{\log\log\ell}{3\ell}\le\sigma\le1,\ |t|\le x\Bigr\}.$$
* **The height $l$.** $l=l(q)\in\mathbb N$ with $l\le\ell/10$ is given by
  X Lemma 3.3 (= H Lemma 6.1): for $q\ge q_0$, the product
  $\prod_{\chi\bmod q}L(s,\chi)$ has no zero in $R(10l)\setminus R(l)$. Put
  $\mathcal R:=R(l)$.
* **Prime window** $R_P:=\{\rho:\ 0\le\lambda_\rho\le C_P,\ |\mu_\rho|\le C_P\}$.
  This is X's square (3.58) with $C_0$ replaced by $C_P$.
* **Buffer** $R_B:=\{\rho:\ \lambda_\rho\le C_B,\ |\mu_\rho|\le C_B\}$, with
  $C_B>C_P+M$.

$C_P$, $M$ and $C_B$ are fixed constants, chosen in the order of §4.2. For
$q\ge q_0$ we have $R_P\subset R_B\subset\mathcal R$ and
$R_B\subset\{|1-\rho|\le\sqrt2\,C_B/\ell\}$.

**Definition 1.3 (global families; X §3.1.2, pp. 21–22).** Let
$P(s):=\prod_{\chi\bmod q}L(s,\chi)$ (X (3.11)).
* Let $\rho_1$ be a zero of $P$ in $\mathcal R$ with maximal real part, and
  $\chi_1$ a character with $L(\rho_1,\chi_1)=0$.
* Inductively, $\rho_k$ is a zero in $\mathcal R$ of
  $P(s)/\prod_{i<k}L(s,\chi_i)L(s,\bar\chi_i)$ with maximal real part, and
  $\chi_k$ is a corresponding character.
* Put $\lambda_k:=\lambda_{\rho_k}$ and $\mu_k:=\mu_{\rho_k}$. Then
  $\lambda_1\le\lambda_2\le\lambda_3\le\cdots$.

The following facts hold.
* $\chi_i\ne\chi_j,\bar\chi_j$ for $i\ne j$.
* By X Lemma 3.3, for $q\ge q_0$: if $\chi\ne\chi_i,\bar\chi_i$ ($i<k$) and
  $L(\rho,\chi)=0$, then $\operatorname{Re}\rho\le\operatorname{Re}\rho_k$ or
  $|\operatorname{Im}\rho|\ge10l$ (X (3.12)).
* For $q\ge q_0$, $L(s,\chi_0)$ has no zero in $\mathcal R$ (X p. 21,
  footnote 4), so $\chi_1\ne\chi_0$.

A **family** is $\{\chi,\bar\chi\}$.

**Definition 1.4 (type, $n$, $\alpha$, distinguished occurrences, $\lambda'$).**
The **type** is
* $\mathrm{rr}$ if $\chi_1$ and $\rho_1$ are both real;
* $\mathrm{rc}$ if $\chi_1$ is real and $\rho_1$ is nonreal;
* $\mathrm{complex}$ if $\chi_1$ is nonreal.

Put $n:=2$ if $\chi_1$ is nonreal and $n:=1$ otherwise (X (6.24)). Put
$\alpha:=2$ for type rc and $\alpha:=1$ otherwise (X (6.23)). The **first
family** is $\mathcal F_1:=\{\chi_1,\bar\chi_1\}$, which has $n$ elements.

The **distinguished occurrences** $D_\chi$ of $\chi\in\mathcal F_1$ are:
* for $\chi_1$: one occurrence of $\rho_1$, and for type rc also one
  occurrence of $\bar\rho_1$ (a zero of the real $\chi_1$);
* for $\bar\chi_1$ (complex type): one occurrence of $\bar\rho_1$.

So $\#D_\chi=\alpha$. Every distinguished occurrence has parameter $\lambda_1$.
$\lambda'$ is the least parameter of a non-distinguished occurrence of a zero
of $\chi_1$ in $\mathcal R$, and $+\infty$ if there is none. This is X's
$\lambda'$ (Cases 1–3, pp. 21–22, and X p. 80: "$\lambda'=\infty$ if $\rho'$
does not exist"). In particular $\lambda'=\lambda_1$ if $\rho_1$ is multiple.
Conjugation preserves multiplicities, since
$L(\bar s,\bar\chi)=\overline{L(s,\chi)}$. Hence the non-distinguished
occurrences of $\bar\chi_1$ also have parameters $\ge\lambda'$.

**Definition 1.5 (representatives).** For $\chi\ne\chi_0$ and
$0<T'\le1$ put
$\lambda_\chi(T'):=\min\{\lambda_\rho:\rho\in Z(\chi),\ |\operatorname{Im}\rho|\le T'\}$,
with the minimum of an empty set equal to $+\infty$.
* The **height-one representative** is $\nu_\chi:=\lambda_\chi(1)$.
* The **$T^*$-representative** is $\lambda^*_\chi:=\lambda_\chi(T^*)$. Here
  $T^*=T^*(q)\in[\tfrac12,1]$ is fixed by the pigeonhole of PROOF.md §4.

Then $\lambda^*_\chi\ge\nu_\chi$, and conjugate characters have equal
representatives.

**Definition 1.6 (occurrence cost).** For $\Phi:\mathbb C\to\mathbb C$ and
$\chi\ne\chi_0$ put
$$
S_\chi(\Phi):=\sum_{\rho\in Z(\chi)\cap R_P} m_\chi(\rho)\,|\Phi(\hat\rho)|,\qquad
W_{\rm occ}:=H_0^{-1}\sum_{\chi\ne\chi_0}S_\chi(H),
$$
with $H$ and $H_0$ as in Definition 2.1.

| PROOF.md | here | X | code / Lean |
|---|---|---|---|
| `ℓ` | $\ell$ | $\mathcal L$ | `log q` |
| `h(a)=Ψ(a)²/H₀` | $\tilde h(a)$ | $H_2(\lambda_1)/H(0)$ in $A(\chi_1)$, p. 80 | `w.h`, `hRatio` |
| `B_φ` | $B_\phi$ | $B$ of (6.22) (only $\phi=1/3$) | `w.B(l,real)`, `Benv` |
| `G`, `G_φ` | $G=G_{1/3}$, $G_\phi$ | $e^{-(L-2K-2K_2)\lambda}B(\lambda)$ | `w.G`, `Gphi` |
| `C(p,a)` | $C(p,a)$ | — | `cross_envelope`, `Cpa` |

The letter $h$ is used by PROOF.md both for the prime weight and for
$\Psi(a)^2/H_0$. Here the latter is written $\tilde h$.

---

## 2. Prime detection

### 2.1 The kernel

**Definition 2.1 (the 16-step kernel).** Put
$T:=\tfrac{416829}{10^6}$ and
$\kappa:=T/16=\tfrac{416829}{16\,000\,000}=0.0260518125$. The heights
$\beta_0,\dots,\beta_{15}$ are exact decimals (`config_v4.py`, `Kernel.beta`):

| $i$ | $\beta_i$ | $i$ | $\beta_i$ | $i$ | $\beta_i$ | $i$ | $\beta_i$ |
|---|---|---|---|---|---|---|---|
| 0 | 0.02318741 | 4 | 0.23237155 | 8 | 0.47877833 | 12 | 0.75172165 |
| 1 | 0.07159337 | 5 | 0.29081583 | 9 | 0.54505502 | 13 | 0.82236428 |
| 2 | 0.12265085 | 6 | 0.35147264 | 10 | 0.61279917 | 14 | 0.89340300 |
| 3 | 0.17627704 | 7 | 0.41418551 | 11 | 0.68177389 | 15 | 0.96451862 |

They are strictly increasing in $(0,1)$, with
$\sum_i\beta_i=7.43296816$. Define:
* $\psi:=\sum_{i=0}^{15}\beta_i\mathbf 1_{[i\kappa,(i+1)\kappa)}$;
* $\Psi(z):=\int_0^T\psi(t)e^{-zt}\,dt=\frac{1-e^{-\kappa z}}{z}\sum_i\beta_ie^{-i\kappa z}$
  for $z\ne0$;
* $\Psi(0)=\kappa\sum_i\beta_i=0.19364229282279$;
* $H_0:=\Psi(0)^2=0.0374973375696671475463433841$ (exact);
* $L:=3.99$ and $A:=L-2T=3.156342$;
* $h(t):=(\psi*\psi)(t-A)$ and $H(z):=\int_0^\infty h(t)e^{-zt}dt$.

**Lemma 2.2 (triangle decomposition).** Let $h_{L',K'}$ be X's triangle (3.51):
it is $0$ for $t\le L'-2K'$, equals $t-(L'-2K')$ on $[L'-2K',L'-K']$, equals
$L'-t$ on $[L'-K',L']$, and is $0$ for $t\ge L'$. Then
$$
h=\sum_{k=0}^{30}c_k\,h_{A+(k+2)\kappa,\ \kappa},\qquad c_k:=\sum_{\substack{i+j=k\\0\le i,j\le15}}\beta_i\beta_j>0 .
$$
Every component has left endpoint $A+k\kappa\ge A$ and right endpoint at most
$A+32\kappa=L$. Every component satisfies
$L_k-2K_k-3=A-3+k\kappa\ge0.156342>0$. Moreover
$$H(z)=e^{-Az}\Psi(z)^2,\qquad H(0)=H_0,$$
$h\ge0$, and $h>0$ exactly on $(A,L)$. The coefficients are exact 16-digit
decimals:

| $k$ | $c_k$ | $k$ | $c_k$ | $k$ | $c_k$ |
|---|---|---|---|---|---|
| 0 | 0.0005376559825081 | 11 | 0.8187775064533394 | 22 | 3.9370552674055367 |
| 1 | 0.0033201296469434 | 12 | 1.0619093339149814 | 23 | 3.9303854918198614 |
| 2 | 0.0108135217195539 | 13 | 1.3519916535612598 | 24 | 3.8328030926039857 |
| 3 | 0.0257367913698618 | 14 | 1.6938638748377861 | 25 | 3.6366881637917548 |
| 4 | 0.0510599545045431 | 15 | 2.0924257879571598 | 26 | 3.3346309866394820 |
| 5 | 0.0900001140656156 | 16 | 2.5045869193464605 | 27 | 2.9195044866539260 |
| 6 | 0.1460151821308156 | 17 | 2.8797800418440268 | 28 | 2.3845402413747872 |
| 7 | 0.2227951555079868 | 18 | 3.2106167755005268 | 29 | 1.7234076573277200 |
| 8 | 0.3242508125457649 | 19 | 3.4895220191429576 | 30 | 0.9302961683267044 |
| 9 | 0.4544997100199518 | 20 | 3.7087781831497483 | | |
| 10 | 0.6178493635962489 | 21 | 3.8605736248319870 | | |

Their sum is $(\sum\beta_i)^2=55.2490156675737856$ exactly.

*Proof.*
1. For every $t$,
   $(\mathbf 1_{[0,\kappa)}*\mathbf 1_{[0,\kappa)})(t)=|[0,\kappa)\cap(t-\kappa,t]|$.
   This is $t$ on $[0,\kappa]$, $2\kappa-t$ on $[\kappa,2\kappa]$ and $0$
   otherwise, that is, $h_{2\kappa,\kappa}(t)$.
2. Translating, $\mathbf 1_{[i\kappa,(i+1)\kappa)}*\mathbf 1_{[j\kappa,(j+1)\kappa)}=h_{2\kappa,\kappa}(\cdot-(i+j)\kappa)$.
   Hence
   $h(t)=\sum_{i,j}\beta_i\beta_jh_{2\kappa,\kappa}(t-A-(i+j)\kappa)=\sum_{i,j}\beta_i\beta_jh_{A+(i+j+2)\kappa,\kappa}(t)$.
   Grouping by $k=i+j$ gives the decomposition.
3. By X (3.54), $H_{L',K'}(z)=e^{-(L'-2K')z}\bigl(\frac{1-e^{-K'z}}{z}\bigr)^2$. So
   $$H(z)=\Bigl(\tfrac{1-e^{-\kappa z}}{z}\Bigr)^2e^{-Az}\sum_kc_ke^{-k\kappa z}=e^{-Az}\Bigl(\tfrac{1-e^{-\kappa z}}{z}\sum_i\beta_ie^{-i\kappa z}\Bigr)^2=e^{-Az}\Psi(z)^2 .$$
4. Since every $\beta_i>0$, $\psi>0$ on $[0,T)$, so $\psi*\psi>0$ exactly on
   $(0,2T)$.

The decimals were computed in exact rational arithmetic (§7). ∎

### 2.2 The criterion

**Theorem 2.3 [X (3.56)–(3.58), pp. 33–35; cf. H Lemmas 13.1–13.2].**
Translation of X p. 34, with (3.51) and (3.54) as above.

> Let $a,q\in\mathbb N$ with $(a,q)=1$, and
> $\Sigma=\sum_{p\equiv a\,(q)}\frac{\log p}{p}h(\mathcal L^{-1}\log p)$.
> "From now on we use, instead of $h=h_{L,K}$, the linear combination
> $h(t)=\sum_{i=1}^M\alpha_ih_{L_i,K_i}(t)$ with corresponding Laplace
> transform $H(z)$ — here $M\in\mathbb N$, $L_i,K_i,\alpha_i\in\mathbb R$ and
> $L_i>2K_i+2$. Obviously (3.56) also holds for this new $h$ and $H$. […]
> More precisely, for fixed $\varepsilon>0$ and $L_i>2K_i+3$ $(i=1,\dots,M)$
> there are positive constants $C_0=C_0(\varepsilon)$ and $q_0=q_0(\varepsilon)$
> such that for $q\ge q_0$ (compare [H, Lemma 13.2])
> $$\Sigma\ \ge\ \frac{\mathcal L}{\varphi(q)}\Bigl(H(0)-\sum_\rho\sum\nolimits'_{\chi\ne\chi_0}|H((1-\rho)\mathcal L)|-\varepsilon\Bigr).\tag{3.57}$$
> The sum $\sum'$ runs over the zeros $\rho=\beta+i\gamma$ of $L(s,\chi)$ in the
> rectangle
> $1-\mathcal L^{-1}C_0\le\beta\le1$, $|\gamma|\le\mathcal L^{-1}C_0$ (3.58)."

(3.56) is quoted by X from H journal p. 325: for $L>2K+2$,
$\Sigma=\frac{\mathcal L}{\varphi(q)}\bigl(H(0)-\sum_{\chi\ne\chi_0}\bar\chi(a)\sum_\rho H((1-\rho)\mathcal L)+O(\mathcal L^{-1})\bigr)$.
Zeros are counted with multiplicity, as in the explicit formula; X Lemma 3.2
states this convention explicitly. $C_0$ and $q_0$ also depend on the fixed
kernel.

**Corollary 2.4 (prime detection).** Let $L>3+2T=3.833658$. Put
$\varepsilon_c:=\eta H_0$ and choose $C_P\ge C_0(\varepsilon_c)$. If, for some
$q\ge q_0$, $W_{\rm occ}<1-\eta$, then every class $a$ with $(a,q)=1$ contains
a prime $p$ with $q^A<p<q^L$.

*Proof.*
1. By Lemma 2.2 the kernel is a combination as in Theorem 2.3, with every
   $L_i>2K_i+3$, since $A>3$.
2. Enlarging the square (3.58) from $C_0$ to $C_P$ only adds nonnegative terms.
   So (3.57) holds with $R_P$, giving
   $\Sigma\ge\frac{\ell}{\varphi(q)}H_0(1-W_{\rm occ}-\eta)>0$.
3. Hence some prime $p\equiv a$ has $h(\log p/\ell)>0$, that is,
   $A<\log p/\ell<L$ (Lemma 2.2). ∎

The Lean theorem `Kernel.exists_prime` is this corollary, from
`XylourisCriterion357` stated as printed.

**Remark 2.5 (occurrence form).** In (3.57) every zero occurrence is charged
$|H(\hat\rho)|$ separately. The modulus is that of the *combined* transform
$H=\sum_kc_kH_{L_k,K_k}$, not $\sum_kc_k|H_{L_k,K_k}|$. Each cost bound of §3
bounds the full occurrence sum $S_\chi(H)$ of one character, over all its
zeros in $R_P$ with multiplicity. Summing over $\chi$ therefore bounds
$W_{\rm occ}$ exactly as (3.57) requires.

A bound on the grouped quantity $|\sum_\rho H(\hat\rho)|$ would not suffice,
since $|\sum_\rho H|\le\sum_\rho|H|$. It is never used. PROOF.md's phrase "all
the costs bound individual occurrences" means this (§6, H13).

**Remark 2.6 (where Condition 1 matters).** The triangle combination $h$ is
not $C^2$, but (3.57) is stated for triangle combinations, so the prime weight
needs no regularity. Regularity matters only for the *auxiliary* test
functions of §3:
* $f_\lambda$ is the autocorrelation of $\psi e^{-\lambda\cdot}$;
* it is Lipschitz, but $f_\lambda'$ jumps at the points $j\kappa\in(0,T)$;
* hence it violates X Condition 1 (twice continuously differentiable on
  $(0,x_0)$).

§3.2 handles this.

---

## 3. Zero costs

### 3.1 Kernel functions

**Definition 3.1.** For real $\lambda,a,p$ and $\phi\ge0$ put
$$
f_\lambda(t):=2\int_0^{T-t}\psi(u)\psi(u+t)e^{-\lambda(2u+t)}\,du\ \ (0\le t<T),\qquad f_\lambda(t):=0\ \ (t\ge T),
$$
$$
F_\lambda(z):=\int_0^Tf_\lambda(t)e^{-zt}dt,\qquad
B_\phi(\lambda):=H_0^{-1}\bigl[F_\lambda(-\lambda)+\tfrac\phi2f_\lambda(0)\bigr],\qquad
G_\phi(\lambda):=e^{-A\lambda}B_\phi(\lambda),
$$
$$
G:=G_{1/3},\qquad \tilde h(\lambda):=\Psi(\lambda)^2/H_0,\qquad
C(p,a):=\frac2{H_0}\int_0^T\psi(u)e^{-2pu}\int_u^T\psi(v)e^{-a(v-u)}dv\,du .
$$

**Lemma 3.2 (identities).**
1. $F_\lambda(-\lambda)=2\int_0^T\psi(u)e^{-2\lambda u}\int_u^T\psi(v)\,dv\,du$
   and $f_\lambda(0)=2\int_0^T\psi^2e^{-2\lambda u}du$. Hence
   $$B_\phi(\lambda)=H_0^{-1}\Bigl[2\int_0^T\psi(u)e^{-2\lambda u}\int_u^T\psi\,dv\,du+\phi\int_0^T\psi(u)^2e^{-2\lambda u}du\Bigr],$$
   the formula of 4.33 §2 and two-test foundation §5.
2. **Closed form.** For $\lambda\ne0$ put $E=e^{-2\kappa\lambda}$,
   $U=(1-E)/\lambda$, $Q_0=\kappa/\lambda-U/(2\lambda)$ and
   $S_i=\sum_{j>i}\beta_j$. Then
   $$H_0B_\phi(\lambda)=\sum_{i=0}^{15}E^i\bigl[\beta_i^2(Q_0+\tfrac\phi2U)+\kappa U\beta_iS_i\bigr].$$
   At $\lambda=0$, take $U=2\kappa$ and $Q_0=\kappa^2$. This is
   `enclosures.RigorousWeights.B`, where `den=6` gives $\phi=1/3$ and `den=8`
   gives $\phi=1/4$; it is also Lean `Benv_eq`.
3. $F_\lambda(0)=\int f_\lambda=\Psi(\lambda)^2$,
   $C(p,a)=F_p(a-p)/H_0$ and $C(a,a)=\tilde h(a)$.
4. **Cells of $C$.** Put $X(r,j):=\int_{j\kappa}^{(j+1)\kappa}e^{-ru}du$ and
   $\tau_j:=\sum_{i>j}\beta_i\frac{e^{-ai\kappa}-e^{-a(i+1)\kappa}}{a}$ for
   $a\ne0$. Then
   $$\tfrac{H_0}2C(p,a)=\sum_j\beta_j\Bigl[\tfrac{\beta_j}{a}X(2p,j)+\bigl(\tau_j-\tfrac{\beta_j}{a}e^{-a(j+1)\kappa}\bigr)X(2p-a,j)\Bigr].$$
   This is `triple_inputs.cross_envelope` and Lean `Cpa_closed`.

*Proof.*
* (1): Fubini, with $v=u+t$.
* (2): On $[i\kappa,(i+1)\kappa)$, $\int_u^T\psi=\beta_i((i+1)\kappa-u)+\kappa S_i$.
  Also $2\int_0^\kappa(\kappa-s)e^{-2\lambda s}ds=Q_0$ and
  $\int_0^\kappa e^{-2\lambda s}ds=U/2$.
* (3): $\int_0^Tf_\lambda=\bigl(\int\psi e^{-\lambda u}\bigr)^2$, and
  $e^{-p(2u+t)}e^{-(a-p)t}=e^{-2pu-at}$.
* (4): For $u\in[j\kappa,(j+1)\kappa)$,
  $\int_u^T\psi(v)e^{-av}dv=\beta_j\frac{e^{-au}-e^{-a(j+1)\kappa}}a+\tau_j$. ∎

**Lemma 3.3 (positivity and monotonicity).** For $\phi\ge0$ and $\lambda\ge0$:
1. $B_\phi(\lambda)\ge\tilde h(\lambda)+\frac{\phi}{2H_0}f_\lambda(0)>\tilde h(\lambda)>0$;
2. $B_\phi$, $\tilde h$, $G_\phi$ and $e^{-A\lambda}\tilde h$ are nonincreasing
   on $[0,\infty)$;
3. $B_\phi$ is increasing in $\phi$, so $B_{1/4}\le B_{1/3}$.

*Proof.* For $u<v$ and $\lambda\ge0$, $e^{-2\lambda u}\ge e^{-\lambda(u+v)}$. So
$F_\lambda(-\lambda)=2\iint_{u<v}\psi(u)\psi(v)e^{-2\lambda u}\ge2\iint_{u<v}\psi(u)\psi(v)e^{-\lambda(u+v)}=\Psi(\lambda)^2$.
All integrands in Lemma 3.2(1), and $\Psi(\lambda)=\int\psi e^{-\lambda t}$,
are nonnegative and nonincreasing in $\lambda$. Finally $A>0$. ∎

Numerically $B_{1/4}(\lambda)<2\tilde h(\lambda)$ exactly for
$\lambda<1.89505\ldots$ (§7). This matters for type rc (Remark 3.13′).

**Lemma 3.4 (autocorrelation identity and comparison).** Let
$\psi^\flat\ge0$ be bounded, supported in $[0,T]$, with transform
$\Psi^\flat$, and form $f^\flat_\lambda$ and $F^\flat_\lambda$ as in
Definition 3.1. Then for real $\lambda$:
1. $f^\flat_\lambda\ge0$ and $f^\flat_\lambda$ is Lipschitz;
2. $\operatorname{Re}F^\flat_\lambda(iy)=|\Psi^\flat(\lambda+iy)|^2$ for
   $y\in\mathbb R$;
3. $\operatorname{Re}F^\flat_\lambda(z)\ge|\Psi^\flat(\lambda+z)|^2\ge0$ for
   $\operatorname{Re}z\ge0$;
4. $|\Psi^\flat(\lambda+iy)|\le\Psi^\flat(\lambda)$.

*Proof.*
1. Put $g(u):=\psi^\flat(u)e^{-\lambda u}$. For $t\ge0$,
   $f^\flat_\lambda(t)=2\gamma_g(t)$ with $\gamma_g(t)=\int g(u)g(u+t)du$ even,
   and $|\gamma_g(t)-\gamma_g(t')|\le\|g\|_\infty\mathrm{TV}(g)|t-t'|$.
2. $\operatorname{Re}F^\flat_\lambda(iy)=\int_0^\infty2\gamma_g\cos(yt)\,dt=\int_{\mathbb R}\gamma_ge^{-iyt}dt=|\hat g(y)|^2$,
   and $\hat g(y)=\Psi^\flat(\lambda+iy)$.
3. Apply X Lemma 3.5 (= H Lemma 4.1) to $F_1:=F^\flat_\lambda$ and
   $F_2(z):=\Psi^\flat(\lambda+z)^2$.
   * Both are entire.
   * On $\operatorname{Re}z=0$, $\operatorname{Re}F_1=|F_2|$ by (2).
   * Both tend to $0$ uniformly on $\operatorname{Re}z\ge0$. Indeed
     $|F^\flat_\lambda(z)|\le(f^\flat_\lambda(0)+\|(f^\flat_\lambda)'\|_1)/|z|$,
     by one integration by parts ($f^\flat_\lambda(T)=0$). And
     $\Psi^\flat(\lambda+z)=O_\lambda(|z|^{-1})$ for the step kernel by its
     closed form, and for smooth $\psi^\flat$ by integration by parts.
4. Since $\psi^\flat\ge0$. ∎

**Lemma 3.5 (coupled comparison; 4.33 §2).** In the setting of Lemma 3.4, let
$0\le\lambda\le p$ and $\mu\in\mathbb R$. Put
$C^\flat(p,a):=F^\flat_p(a-p)/H_0^\flat$ with $H^\flat_0:=\Psi^\flat(0)^2$, and
$$V^\flat_p(\lambda):=e^{-A\lambda}\Psi^\flat(\lambda)^2-e^{-Ap}F^\flat_p(\lambda-p)=H^\flat_0\bigl[e^{-A\lambda}\tilde h^\flat(\lambda)-e^{-Ap}C^\flat(p,\lambda)\bigr].$$
Then
$$
e^{-A\lambda}|\Psi^\flat(\lambda-i\mu)|^2-e^{-Ap}\operatorname{Re}F^\flat_p\bigl((\lambda-p)-i\mu\bigr)\ \le\ V^\flat_p(\lambda),
$$
and $\lambda\mapsto V^\flat_p(\lambda)$ is nonnegative and nonincreasing on
$[0,p]$, with $V^\flat_p(p)=0$.

*Proof.* Put
$$D_\lambda(t):=e^{-A\lambda}f^\flat_\lambda(t)-e^{-Ap}e^{(p-\lambda)t}f^\flat_p(t)=2\int_0^{T-t}\psi^\flat(u)\psi^\flat(u+t)e^{-\lambda t}\bigl[e^{-\lambda(A+2u)}-e^{-p(A+2u)}\bigr]du .$$
1. For $0\le\lambda\le p$ and $A+2u>0$ the bracket is $\ge0$, so $D_\lambda\ge0$.
2. By Lemma 3.4(2) with $y=-\mu$, the left side equals $\int_0^TD_\lambda(t)\cos(\mu t)dt$.
3. Since $D_\lambda\ge0$, this is at most $\int_0^TD_\lambda=V^\flat_p(\lambda)$,
   by Lemma 3.2(3).
4. For fixed $u,t$, the map $\lambda\mapsto e^{-\lambda t}[e^{-\lambda(A+2u)}-e^{-p(A+2u)}]$
   is a product of two nonnegative nonincreasing functions on $[0,p]$.
5. $D_p\equiv0$, so $V^\flat_p(p)=0$. ∎

This is the step that 4.33 §2 calls "keeping the distinguished zero and its
correction together". The two terms are *not* bounded separately.

### 3.2 Analytic tools

The printed inputs (X Conditions 1–2, $\phi(\chi)$, and Lemmas 3.1, 3.2, 3.3,
3.5, 3.10, 5.1) are quoted in full in §5.

**Lemma 3.6 (disc radius; [PD] from H's proofs of Lemmas 3.1 and 5.2).** Let
$\varepsilon>0$. Let $\mathcal T$ be a family of functions satisfying X
Condition 1 with $f(0)\ge0$ and with common upper bounds for $x_0$,
$x_0^{-1}$, $\sup|f|$ and $\sup(|f'|+|f''|)$. Then there are
$\delta\in(0,\tfrac16]$ and $q_0$ such that X Lemma 3.2 holds for every
$f\in\mathcal T$ with this radius $\delta$ and this $q_0$.

*Proof.*
1. H Lemma 5.2's radius is the $\delta$ of H Lemma 3.1, used in (5.8)
   (copy pp. 23–24).
2. H's proof of Lemma 3.1 (copy p. 14) ends by choosing
   $k=3+[3\phi/2\varepsilon_0]$, $R=1/k$, $\varepsilon=\pi\varepsilon_0/18k$ and
   $\delta=\min(\frac1{2k},\frac{\varepsilon_0}{3c_0k^2})$. It uses only
   $0<R\le1/k$, $\delta<R$ and
   $\frac\phi{2k}+\frac{6\varepsilon}{\pi R}+\frac{c_0\delta}{R^2}\le\varepsilon_0$.
   These persist when $\delta$ decreases, so every
   $\delta'\in(0,\delta]$ works. Since $k\ge3$, $\delta\le\frac16$.
3. In the proof of Lemma 5.2, $\delta$ enters otherwise only through the
   discarding of zeros with $|1+it-\rho|\ge\delta$. The cost is
   $O_\delta(A(f)\log(2+|s|))=O_\delta(\ell^{1/2}\log\ell)=o(\ell)$.
4. H also remarks after Lemma 5.2 (copy p. 24): "one may take
   $\delta=1/\log\mathcal L$, independent of $f$".
5. Uniformity over $\mathcal T$ is X's dependence paragraph after Lemma 3.10
   (p. 36): "$\delta$ and $q_0$ of Lemma 3.2 and the implied constant of
   Lemma 3.1 depend only on $\varepsilon$ and an upper bound for $x_0$,
   $x_0^{-1}$, $\sup|f|$ and $\sup(|f'|+|f''|)$". ∎

**Lemma 3.7 (smoothing).** For every $\theta\in(0,1]$ there is
$\psi_\theta\in C_c^\infty((0,T))$ with $0\le\psi_\theta\le\beta_{15}$ and
$\|\psi-\psi_\theta\|_1\le\theta$. Let $\Psi_\theta$, $H_{0,\theta}$,
$f^\theta_\lambda$, $F^\theta_\lambda$, $B^\theta_\phi$, $\tilde h^\theta$ and
$C^\theta$ be defined from $\psi_\theta$ as in Definitions 2.1 and 3.1. Put
$$c_1:=4\Psi(0)+3\ (\approx3.775),\qquad \omega(\theta):=2\Psi(0)\theta+3\theta^2 .$$
1. For $\operatorname{Re}z\ge0$: $|\Psi(z)-\Psi_\theta(z)|\le\theta$ and
   $|\Psi(z)|^2\le|\Psi_\theta(z)|^2+\omega(\theta)$.
2. For $\lambda,a,p\ge0$ and $\phi\le\frac13$, each of
   $|H_{0,\theta}B^\theta_\phi(\lambda)-H_0B_\phi(\lambda)|$,
   $|H_{0,\theta}\tilde h^\theta(\lambda)-H_0\tilde h(\lambda)|$ and
   $|H_{0,\theta}C^\theta(p,a)-H_0C(p,a)|$ is at most $c_1\theta$.
3. $f^\theta_\lambda\ge0$, $f^\theta_\lambda(0)\ge0$ and
   $f^\theta_\lambda\in C^\infty(\mathbb R)$ vanishes for $t\ge T$. So
   $f^\theta_\lambda$ satisfies X Condition 1 with $x_0=T$. Its bounds on
   $\sup|f|$ and $\sup(|f'|+|f''|)$ are uniform in $\lambda$ on compact sets.
   Also $(f^\theta_\lambda)'(0)=0$.
4. Lemmas 3.2(1),(3), 3.3, 3.4 and 3.5 hold for $\psi_\theta$.

*Proof.*
* **Construction.** Put $\tau=\theta/3$ and
  $g:=\psi\mathbf 1_{[\tau,T-\tau]}$. Take $\psi_\theta:=g*\varrho$ with a
  mollifier $\varrho\ge0$, $\int\varrho=1$, $\operatorname{supp}\varrho\subset(-\tau/2,\tau/2)$.
  Then $\operatorname{supp}\psi_\theta\subset(0,T)$ and
  $0\le\psi_\theta\le\beta_{15}$. Moreover
  $\|\psi-\psi_\theta\|_1\le\|\psi-g\|_1+\|g-g*\varrho\|_1\le2\tau+\frac\tau2\mathrm{TV}(g)\le3\tau$,
  since $\mathrm{TV}(g)\le2\beta_{15}<2$.
* **(1).** $|e^{-zt}|\le1$. Then
  $|\Psi|^2\le(|\Psi_\theta|+\theta)^2$ and $|\Psi_\theta|\le\Psi(0)+\theta$.
* **(2).** $H_0B_\phi(\lambda)$ is a bilinear form in $\psi$ with kernel
  bounded by $1$, plus $\phi\int\psi^2e^{-2\lambda u}$. Hence
  $$|\Delta|\le2\theta(2\Psi(0)+\theta)+2\phi\beta_{15}\theta\le c_1\theta,$$
  using $|\psi^2-\psi_\theta^2|\le2\beta_{15}|\psi-\psi_\theta|$. The same
  bound holds for $\Psi(\lambda)^2$ and for $H_0C(p,a)$, whose kernel
  $e^{-2pu-a(v-u)}\le1$ for $u\le v$.
* **(3).** $f^\theta_\lambda=2\gamma_g$ with $g=\psi_\theta e^{-\lambda\cdot}\in C^\infty_c((0,T))$.
  An autocorrelation of a smooth compactly supported function is smooth and
  even, so $\gamma_g'(0)=0$.
* **(4).** Those proofs used only $\psi\ge0$, bounded, supported in $[0,T]$. ∎

The two-test foundation (§5) says "converge in $L^1$". $L^1$ convergence alone
does not control $\int\psi_\theta^2$. The bound $0\le\psi_\theta\le\beta_{15}$
is what makes (2) hold (§6, H1).

**Lemma 3.8 (uniform zero count).** Let $C>0$. There is $q_0$ such that for
$q\ge q_0$ and every $\chi\ne\chi_0$,
$$\sum_{\rho\in Z(\chi),\ \lambda_\rho\le C,\ |\mu_\rho|\le C}m_\chi(\rho)\ \le\ N_0(C):=\frac{2e}{\cos1}\Bigl(1+\frac C6\Bigr).$$

*Proof.*
1. **The test.** Let $x_0:=1/C$ and $f_0(t):=(x_0-t)_+$.
   * It satisfies Condition 1 ($f_0''=0$ on $(0,x_0)$) and $f_0(0)=x_0\ge0$.
   * $F_0(z)=\frac{x_0}z-\frac{1-e^{-x_0z}}{z^2}$ tends to $0$ uniformly on
     $\operatorname{Re}z\ge0$.
   * $\operatorname{Re}F_0(iy)=(1-\cos x_0y)/y^2\ge0$. By X Lemma 3.5 with
     $F_2=0$, $\operatorname{Re}F_0\ge0$ on $\operatorname{Re}z\ge0$ (Condition 2).
2. **A lower bound on the square.** For $0\le x\le C$, $|y|\le C$ and
   $t\le x_0$ we have $xt\le1$ and $|y|t\le1$. So
   $$\operatorname{Re}F_0(x+iy)\ge e^{-1}\cos(1)\,x_0^2/2=:m_0>0 .$$
3. **Explicit formula at $s=1$.** Apply X Lemma 3.2 at $s=1$ ($t=0$) with
   tolerance $\varepsilon'=x_0^2/4$, and radius $\delta_0$.
   * Every zero has $\lambda_\rho>0$, so every term
     $\operatorname{Re}F_0(\hat\rho)$ in the disc is $\ge0$.
   * $-\ell^{-1}\sum\Lambda(n)\operatorname{Re}(\chi(n)/n)f_0\le\ell^{-1}\sum\Lambda(n)\chi_0(n)n^{-1}f_0=F_0(0)+o(1)$,
     by X Lemma 3.1 at $s=1$ and $f_0\ge0$.
   * For large $q$ the square $\{\lambda\le C,|\mu|\le C\}$ lies in the disc
     $|1-\rho|\le\delta_0$.
4. **Count.** Hence
   $$m_0\cdot\#\le F_0(0)+\tfrac13\tfrac{f_0(0)}2+2\varepsilon'\le x_0^2+x_0/6,$$
   and dividing by $m_0$ gives the bound. ∎

The two-test foundation's version (§5) uses an anchor $.05$ and needs
$\lambda_1\ge.1$. The anchor $0$ above needs nothing (§6, H2).

### 3.3 The local envelope

**Proposition 3.9 (local envelope, smoothed kernel; localized X Lemma 3.10).**
Fix $\theta\in(0,1]$, $C>0$, $\Lambda\ge0$, a finite set
$\mathcal P\subset[0,\Lambda]$ and $\varepsilon>0$. There are
$\delta\in(0,\frac16]$ and $q_0$ such that for $q\ge q_0$ and every
$\chi\ne\chi_0$ the following hold.

* **(a) Anchored explicit formula.** For every $\sigma_0\in[0,\Lambda]$,
  $$\sum_{\rho\in Z(\chi),\,|1-\rho|\le\delta}m_\chi(\rho)\operatorname{Re}F^\theta_{\sigma_0}(\hat\rho-\sigma_0)\ \le\ H_{0,\theta}B^\theta_{\phi(\chi)}(\sigma_0)+\varepsilon .$$
* **(b) Disc.** Every $\rho$ with $\lambda_\rho\le C$ and $|\mu_\rho|\le C$
  has $|1-\rho|\le\delta$.
* **(c) Envelope.** Let $\lambda\in[0,\Lambda]$, and suppose every
  $\rho\in Z(\chi)$ with $|1-\rho|\le\delta$ has $\lambda_\rho\ge\lambda$.
  Then
  $$\sum_{\rho\in Z(\chi),\,\lambda_\rho\le C,\,|\mu_\rho|\le C}m_\chi(\rho)|\Psi_\theta(\hat\rho)|^2\ \le\ H_{0,\theta}B^\theta_{\phi(\chi)}(\lambda)+\varepsilon .$$

*Proof.*
* **(a).** Let $s=1-\sigma_0/\ell$, so $t=0$ and
  $|\sigma-1|=\sigma_0/\ell\le(\log\ell)^{1/2}/\ell$ for large $q$, and
  $(s-\rho)\ell=\hat\rho-\sigma_0$.
  1. By Lemma 3.7(3), X Lemma 3.2 applies to $f^\theta_{\sigma_0}$ with
     tolerance $\varepsilon/2$. By Lemma 3.6 one radius $\delta\le\frac16$
     and one $q_0$ serve all $\sigma_0\in[0,\Lambda]$.
  2. This gives
     $\sum_{\rm disc}\operatorname{Re}F^\theta_{\sigma_0}(\hat\rho-\sigma_0)\le-\ell^{-1}K+\frac{\phi(\chi)}2f^\theta_{\sigma_0}(0)+\frac\varepsilon2$,
     with $K=\sum\Lambda(n)\operatorname{Re}(\chi(n)n^{-s})f^\theta_{\sigma_0}(\ell^{-1}\log n)$.
  3. $s$ is real and $f^\theta\ge0$, so
     $-K\le\sum\Lambda(n)\chi_0(n)n^{-s}f^\theta_{\sigma_0}$. By X Lemma 3.1
     this is $\ell F^\theta_{\sigma_0}(-\sigma_0)+O(\ell/\log\ell)$, uniformly by
     the dependence paragraph.
* **(b).** $|1-\rho|=|\hat\rho|/\ell\le\sqrt2C/\ell\le\delta$ for large $q$.
* **(c).** For a disc zero, $\operatorname{Re}(\hat\rho-\lambda)=\lambda_\rho-\lambda\ge0$.
  By Lemma 3.4(3) for $\psi_\theta$ with $z=\hat\rho-\lambda$:
  $\operatorname{Re}F^\theta_\lambda(\hat\rho-\lambda)\ge|\Psi_\theta(\hat\rho)|^2\ge0$.
  Sum over the square, which lies in the disc by (b). Add the remaining disc
  zeros, whose terms are $\ge0$. Then apply (a) with $\sigma_0=\lambda$. ∎

Part (c) is X Lemma 3.10 with $M=1$, $f^\lambda_1:=f^\theta_\lambda$,
$H_2:=\Psi_\theta^2$ (so (3.59) holds with equality) and $C_0:=C$. There is
one change: the hypothesis "no zero in $1-\lambda/\ell<\beta\le1$,
$|\gamma|\le1$" is replaced by "no zero with $\lambda_\rho<\lambda$ in the
disc". X's proof uses the rectangle hypothesis only in two places:
* to make $\operatorname{Re}(s-\rho)\ge0$ for zeros of the square;
* to drop the disc zeros outside the square.

Both are covered by the disc hypothesis. Hence the "localized form" is a
[PD] reading of the printed proof.

**Theorem 3.10 (local envelope for the step kernel).** Let $C_P$ be fixed,
$N_0:=N_0(C_P)$ as in Lemma 3.8, $\theta\in(0,1]$ and $\varepsilon>0$. Put
$$\varepsilon':=\bigl(\varepsilon+c_1\theta+N_0\,\omega(\theta)\bigr)/H_0 .$$
Take $\delta\le\frac16$ and $q_0$ as in Proposition 3.9, with $C=\Lambda=C_P$,
and $q_0$ also as in Lemma 3.8. Let $q\ge q_0$, $\chi\ne\chi_0$ and
$\lambda\ge0$, and suppose every $\rho\in Z(\chi)$ with $|1-\rho|\le\delta$ has
$\lambda_\rho\ge\lambda$. Then
$$
H_0^{-1}S_\chi(H)\ \le\ G_{\phi(\chi)}(\lambda)+\varepsilon'e^{-A\lambda},
$$
and $S_\chi(H)=0$ if $\lambda>C_P$.

*Proof.*
* **$\lambda>C_P$.** An $R_P$ zero lies in the disc (Proposition 3.9(b)),
  so it would have $C_P\ge\lambda_\rho\ge\lambda>C_P$. Hence $R_P$ contains
  no zero of $\chi$.
* **$\lambda\le C_P$.** Every $\rho\in R_P$ lies in the disc, so
  $\lambda_\rho\ge\lambda$. By Lemma 3.7(1),
  $$|H(\hat\rho)|=e^{-A\lambda_\rho}|\Psi(\hat\rho)|^2\le e^{-A\lambda}\bigl(|\Psi_\theta(\hat\rho)|^2+\omega(\theta)\bigr).$$
  Sum with multiplicities; there are at most $N_0$ occurrences (Lemma 3.8).
  Proposition 3.9(c) then gives
  $S_\chi(H)\le e^{-A\lambda}\bigl(H_{0,\theta}B^\theta_{\phi(\chi)}(\lambda)+\varepsilon+N_0\omega(\theta)\bigr)$.
  Finally use Lemma 3.7(2). ∎

The anchors used below are $\lambda\ge0$, so PROOF.md's restriction
$\lambda\ge\lambda_{\min}>0$ is not needed. X needs $\lambda>\lambda_{11}>0$
only because its own $f_1^\lambda$ degenerate as $\lambda\to0$.

**Corollary 3.11 (ordinary characters).** Let $\chi$ be an ordinary character,
that is, neither in $\mathcal F_1$ nor reserved, with $T^*$-representative
$\lambda^*_\chi$. Then
$$H_0^{-1}S_\chi(H)\le G(\lambda^*_\chi)+\varepsilon'e^{-A\lambda^*_\chi},$$
and the left side is $0$ if $\lambda^*_\chi>C_P$.

*Proof.* A disc zero has $|\operatorname{Im}\rho|\le\delta\le\frac16<\frac12\le T^*$,
so $\lambda_\rho\ge\lambda^*_\chi$. Apply Theorem 3.10 with
$\lambda=\lambda^*_\chi$, then $\phi(\chi)\le\frac13$ and Lemma 3.3(3). ∎

**Remark 3.12 (the coefficient $1/4$ for real characters; [PD]).** In
Proposition 3.9 and Theorem 3.10 the conductor coefficient is $\phi(\chi)$ of
X Lemma 3.2. X p. 17 defines $\phi(\chi)=\frac14$ if $q$ is cube-free or
$\operatorname{ord}\chi\le\mathcal L$ (the same definition as H Lemma 2.5,
copy p. 10). A real nonprincipal character has order $2\le\ell$ ($q\ge8$), so
$\phi(\chi)=\frac14$.

X prints (3.60) with $f(0)/6$, that is, after bounding $\phi\le\frac13$, and
uses the same $1/6$ in (6.22) even for a real $\chi_1$. The $\phi(\chi)$
version is obtained by running X's proof of Lemma 3.10 with Lemma 3.2's
$\phi(\chi)$ kept.
* This is exactly H Lemma 13.3 (copy p. 82), which is printed with a general
  $\phi$.
* H applies it with "$\lambda=0$ and $\phi=\frac14$ for $\chi=\chi_1$", the
  real exceptional character (H §14, copy p. 83).

So $B_{1/4}$ is used, correctly:
* for a real $\chi_1$ (types rr and rc) in $J_{\rm old}$ and $J_{\rm new}$;
* for a reserved family with $n_2=1$;
* for the hidden columns of type rc.

### 3.4 The first family, inside

**Hypotheses (Z).** These are supplied by the case tree (PROOF.md §5), not
proved here.
* (Z1) $a\le\lambda_1\le b$ with $0<a\le b$.
* (Z2) $p\ge0$, and every non-distinguished occurrence in $\mathcal R$ of a
  zero of $\chi_1$ (equivalently $\bar\chi_1$) has parameter $\ge p$, that
  is, $\lambda'\ge p$.

Put $\phi_1:=\phi(\chi_1)$, which is $\frac14$ for real $\chi_1$ and at most
$\frac13$ otherwise, and $B_t:=B_{\phi_1}$.

**Statement (F).** Let $\chi\in\mathcal F_1$. Every zero with
$|1-\rho|\le\delta$ has $|\operatorname{Im}\rho|\le\delta<10l$. So by X
Lemma 3.3 it lies in $\mathcal R$ or has $\lambda_\rho>\frac13\log\log\ell$.
Hence:
* it has $\lambda_\rho\ge\lambda_1$ (minimality of $\lambda_1$);
* if it is non-distinguished, it has $\lambda_\rho\ge p$.

**Proposition 3.13 ($J_{\rm old}$; 4.33 §2, two-test foundation §6; refines
X (6.22)–(6.24)).** Under (Z1) and (Z2), with no restriction on $p$,
$$
H_0^{-1}\sum_{\chi\in\mathcal F_1}S_\chi(H)\ \le\ J_{\rm old}+n\,\varepsilon'e^{-A\lambda_1},\qquad
J_{\rm old}:=n\Bigl[e^{-Ap}\bigl(B_t(a)-\alpha\tilde h(a)\bigr)_++\alpha e^{-Aa}\tilde h(a)\Bigr].
$$

*Proof.* Fix $\chi\in\mathcal F_1$.
1. **Envelope.** By (F), Theorem 3.10 applies with anchor $\lambda_1$. Its
   proof, before the factor $e^{-A\lambda}$ is taken out, gives
   $$H_0^{-1}\sum_{\rho\in R_P}m|\Psi(\hat\rho)|^2\le B_t(\lambda_1)+\varepsilon' .$$
2. **The two parts.** Let $X$ be the part of this sum over the distinguished
   occurrences lying in $R_P$, and $Y$ the rest.
   * By Lemma 3.4(4), $|\Psi(\lambda_1-i\mu)|^2\le\Psi(\lambda_1)^2$, so
     $X\le\alpha\tilde h(\lambda_1)$.
   * The other occurrences have $\lambda_\rho\ge p^*:=\max(p,\lambda_1)$.
3. **Linear program.** Hence $H_0^{-1}S_\chi(H)\le e^{-A\lambda_1}X+e^{-Ap^*}Y$,
   which is at most
   $$\Phi(\lambda_1):=\max\bigl\{e^{-A\lambda_1}X+e^{-Ap^*}Y:\ 0\le X\le\alpha\tilde h(\lambda_1),\ Y\ge0,\ X+Y\le B_t(\lambda_1)\bigr\}$$
   plus $e^{-A\lambda_1}\varepsilon'$. Raising the budget by $\varepsilon'$
   raises the maximum by at most $e^{-A\lambda_1}\varepsilon'$. Explicitly,
   $\Phi(\lambda_1)=e^{-A\lambda_1}\min(B_t,\alpha\tilde h)(\lambda_1)+e^{-Ap^*}(B_t-\alpha\tilde h)_+(\lambda_1)$.
4. **An auxiliary function.** For $x\in[0,p]$ put
   $\Phi_p(x):=(e^{-Ax}-e^{-Ap})\alpha\tilde h(x)+e^{-Ap}B_t(x)$. It is
   nonincreasing on $[0,p]$ by Lemma 3.3.
5. **Cases.** We show $\Phi(\lambda_1)\le J_{\rm old}/n$ in each case.
   * (i) $a\le\lambda_1\le p$ and $B_t(\lambda_1)\ge\alpha\tilde h(\lambda_1)$:
     $\Phi(\lambda_1)=\Phi_p(\lambda_1)\le\Phi_p(a)=\alpha e^{-Aa}\tilde h(a)+e^{-Ap}(B_t(a)-\alpha\tilde h(a))\le J_{\rm old}/n$.
   * (ii) $a\le\lambda_1\le p$ and $B_t(\lambda_1)<\alpha\tilde h(\lambda_1)$:
     $\Phi(\lambda_1)=e^{-A\lambda_1}B_t(\lambda_1)<\alpha e^{-A\lambda_1}\tilde h(\lambda_1)\le\alpha e^{-Aa}\tilde h(a)\le J_{\rm old}/n$.
   * (iii) $\lambda_1>p$: then $p^*=\lambda_1$ and
     $\Phi(\lambda_1)=e^{-A\lambda_1}B_t(\lambda_1)$.
     * If $p\ge a$: this is $\le e^{-Ap}B_t(p)=\Phi_p(p)\le\Phi_p(a)\le J_{\rm old}/n$.
     * If $p<a$: this is $\le e^{-Aa}B_t(a)=\alpha e^{-Aa}\tilde h(a)+e^{-Aa}(B_t(a)-\alpha\tilde h(a))\le J_{\rm old}/n$,
       since $e^{-Aa}\le e^{-Ap}$.
6. **Sum.** Summing over the $n$ characters of $\mathcal F_1$, which satisfy
   identical hypotheses, gives the claim. ∎

**Remark 3.13′ (a free improvement for type rc).** Step 3 shows
$\Phi(\lambda_1)\le e^{-A\lambda_1}B_t(\lambda_1)\le e^{-Aa}B_t(a)$. So
$\min\bigl(J_{\rm old},\,nG_{\phi_1}(a)\bigr)$ is also valid. It equals $n$
times X's own first-family charge $e^{-A\lambda_1}B(\lambda_1)-A(\chi_1)$,
with $A(\chi_1)=\max\{0,\cdot\}$ (X p. 80), evaluated at $\lambda_1=a$,
$\lambda'=p$.
* For $\alpha=2$, $B_{1/4}<2\tilde h$ on the whole middle range (Lemma 3.3,
  remark). There $J_{\rm old}=2e^{-Aa}\tilde h(a)$, which exceeds
  $G_{1/4}(a)$; for example by about 6% at $a=.75$.
* This affects optimality only, not validity (§6, H7).

**Proposition 3.14 ($J_{\rm new}$, the shifted bound; 4.33 §2).** Assume (Z1)
and (Z2) with $p\ge b$. Then
$$
H_0^{-1}\sum_{\chi\in\mathcal F_1}S_\chi(H)\ \le\ J_{\rm new}+n\,\varepsilon''e^{-Aa},\qquad
J_{\rm new}:=n\Bigl\{\alpha e^{-Aa}\tilde h(a)+e^{-Ap}\bigl[B_t(p)-\alpha C(p,a)\bigr]\Bigr\},
$$
where $\varepsilon'':=\bigl(\varepsilon+(2\alpha+1)c_1\theta+(N_0+\alpha)\omega(\theta)\bigr)/H_0$.
No positivity of $B_t(p)-\alpha C(p,a)$ is needed.

*Proof.* Fix $\chi\in\mathcal F_1$ and let $D:=D_\chi$. Its $\alpha$
occurrences have $\lambda=\lambda_1\le b\le p$. By (F), every other disc zero
has $\lambda_\rho\ge p$.
1. **Non-distinguished zeros of $R_P$.** For $\rho\in R_P\setminus D$,
   $\lambda_\rho\ge p$. By Lemma 3.7(1) and Lemma 3.4(3) for $\psi_\theta$ at
   $z=\hat\rho-p$:
   $$|H(\hat\rho)|\le e^{-Ap}\bigl(\operatorname{Re}F^\theta_p(\hat\rho-p)+\omega(\theta)\bigr).$$
2. **Explicit formula at $1-p/\ell$.** $R_P$ lies in the disc, and the terms
   of $\text{disc}\setminus D$ are $\ge0$. So, by Proposition 3.9(a) with
   $\sigma_0=p$,
   $$\sum_{R_P\setminus D}\operatorname{Re}F^\theta_p(\hat\rho-p)\le\sum_{{\rm disc}\setminus D}\operatorname{Re}F^\theta_p(\hat\rho-p)\le H_{0,\theta}B^\theta_{\phi_1}(p)+\varepsilon-\sum_{\rho\in D\cap{\rm disc}}\operatorname{Re}F^\theta_p(\hat\rho-p).$$
3. **Distinguished zeros of $R_P$.** For $\rho\in D\cap R_P$ (which lies in
   the disc):
   $|H(\hat\rho)|\le e^{-A\lambda_1}\bigl(|\Psi_\theta(\hat\rho)|^2+\omega(\theta)\bigr)$.
4. **Combine.** Adding 1–3,
   $$S_\chi(H)\le e^{-Ap}\bigl[H_{0,\theta}B^\theta_{\phi_1}(p)+\varepsilon+N_0\omega(\theta)\bigr]+\alpha e^{-A\lambda_1}\omega(\theta)+\sum_{\rho\in D\cap{\rm disc}}\Bigl[e^{-A\lambda_1}|\Psi_\theta(\hat\rho)|^2\mathbf 1_{R_P}(\rho)-e^{-Ap}\operatorname{Re}F^\theta_p(\hat\rho-p)\Bigr].$$
5. **The coupled term.** Each bracket is at most
   $e^{-A\lambda_1}|\Psi_\theta(\lambda_1-i\mu_\rho)|^2-e^{-Ap}\operatorname{Re}F^\theta_p((\lambda_1-p)-i\mu_\rho)$,
   which is $\le V^\theta_p(\lambda_1)\le V^\theta_p(a)$ by Lemma 3.5. There
   are at most $\alpha$ brackets and $V^\theta_p\ge0$, so their sum is
   $\le\alpha V^\theta_p(a)$. This also covers a distinguished zero lying in
   $R_B\setminus R_P$ (inside case), and one outside the disc, which is absent.
6. **Replace smoothed by exact quantities.** Use Lemma 3.7(2) and
   $e^{-Ap},e^{-A\lambda_1}\le e^{-Aa}$:
   * $H_{0,\theta}B^\theta(p)\le H_0B_t(p)+c_1\theta$;
   * $V^\theta_p(a)\le e^{-Aa}(H_0\tilde h(a)+c_1\theta)-e^{-Ap}(H_0C(p,a)-c_1\theta)$.
7. **Sum.** Summing over the $n$ characters gives the claim. ∎

The proof uses X Lemma 3.2 at $1-p/\ell$ (in Proposition 3.9(a)), X Lemma 3.1,
X Lemma 3.5 (in Lemma 3.4) and Lemma 3.5. It needs $p\ge b$ only for
$\lambda_1\le p$ in step 5. The leaf uses $\min(J_{\rm old},J_{\rm new})$,
both valid. PROOF.md's "$+\varepsilon$" in $J_{\rm new}$ is the error
$n\varepsilon''e^{-Aa}$, charged to E2/E4 (§4). The code computes $J_{\rm new}$
without it (`triple_inputs.shifted_first`), which is consistent.

### 3.5 The reserved second family

**Proposition 3.15.** Let $\chi$ have height-one representative $\nu_\chi$.
Then
$$H_0^{-1}S_\chi(H)\le G_{\phi(\chi)}(\nu_\chi)+\varepsilon'e^{-A\nu_\chi}.$$
Consider a reserved family of $n_2\in\{1,2\}$ characters whose common
parameter $\nu_2$ lies in $[{\rm lo}_2,{\rm hi}_2]$ (conjugates share
representatives). Its cost is at most $n_2G_{\phi_2}({\rm lo}_2)+n_2\varepsilon'e^{-A\nu_2}$,
with $\phi_2=\frac14$ exactly when $n_2=1$. A family with $n_2=1$ is
$\{\chi\}=\{\bar\chi\}$, a real character. For $n_2=2$, $\phi\le\frac13$.

*Proof.* Every zero with $|\operatorname{Im}\rho|\le1$ has
$\lambda_\rho\ge\nu_\chi$ by definition. The disc lies in
$|\operatorname{Im}\rho|\le\frac16$. Apply Theorem 3.10 (here the printed
rectangle hypothesis of X Lemma 3.10 even holds literally), then Remark 3.12
and Lemma 3.3. ∎

The code (`published_single_inputs`, `graded_leaves.second_columns`) charges
$n_2G_{\phi_2}({\rm lo}_2)$, or column objectives $G_{\phi_2}(l_j)$ on
sub-bins with real $=(n_2=1)$. This matches.

### 3.6 The first family, outside ($\rho_1\notin R_B$)

**Proposition 3.16 (hidden columns).** Assume (Z2) and $\rho_1\notin R_B$.
Since $\lambda_1<1.5<C_B$, this means $|\mu_1|>C_B$, and the type is rc or
complex. Let $\chi\in\mathcal F_1$ have a zero in $R_P$, and put
$t_\chi:=\min\{\lambda_\rho:\rho\in Z(\chi)\cap R_P\}$. Then $t_\chi\ge p$ and
$$
H_0^{-1}S_\chi(H)\le e^{-At_\chi}\Bigl[B_{\phi_1}(p)+\varepsilon'+\frac{d_\chi\,c_{\rm out}}{H_0C_B^2}\Bigr].
$$
Here $d_\chi:=\#(D_\chi\cap\text{disc})\le\alpha$, and $d_\chi:=0$ if
$\lambda_1\ge p$. The constant is
$$c_{\rm out}:=\max_{p\in\mathcal P}\ \sup_{-p\le x\le0}\Bigl[f^\theta_p(0)|x|+e^{|x|T}\|(f^\theta_p)''\|_{L^1(0,T)}\Bigr],$$
which depends only on $\theta$ and on the finite set $\mathcal P$ of anchors.

*Proof.*
1. **$t_\chi\ge p$.** Distinguished occurrences have $|\mu|=|\mu_1|>C_B>C_P$,
   so they are not in $R_P$. Hence every $R_P$ zero is non-distinguished and
   has $\lambda_\rho\ge p$ by (Z2).
2. **Each $R_P$ zero.** As in Proposition 3.14, step 1, but with the factor
   $e^{-A\lambda_\rho}\le e^{-At_\chi}$:
   $$|H(\hat\rho)|\le e^{-At_\chi}\bigl(\operatorname{Re}F^\theta_p(\hat\rho-p)+\omega(\theta)\bigr).$$
3. **Explicit formula.** As in step 2 there,
   $$\sum_{R_P}\le H_{0,\theta}B^\theta(p)+\varepsilon-\sum_{D\cap\rm disc}\operatorname{Re}F^\theta_p(\hat\rho-p).$$
4. **Distinguished terms.**
   * If $\lambda_1\ge p$, these terms are $\ge0$ and are dropped.
   * Otherwise, for $\rho\in D\cap$ disc, $z=\hat\rho-p=x-i\mu$ with
     $x=\lambda_1-p\in[-p,0)$ and $|\mu|>C_B$. Two integrations by parts
     (H (5.3), copy p. 20; here $(f^\theta_p)'(0)=0$ and $f^\theta_p$
     vanishes near $T$) give
     $F^\theta_p(z)=f^\theta_p(0)/z+z^{-2}\int_0^T(f^\theta_p)''e^{-zt}dt$.
     Since $|\operatorname{Re}(1/z)|=|x|/|z|^2$, we get
     $|\operatorname{Re}F^\theta_p(z)|\le c_{\rm out}/\mu^2\le c_{\rm out}/C_B^2$.
5. **Conclude.** Then apply Lemma 3.7(2). ∎

This covers every $|\mu_1|>C_B$.
* If $C_B/\ell<|\operatorname{Im}\rho_1|\le\delta$, the distinguished terms
  are adverse and cost $O(C_B^{-2})$.
* If $|\operatorname{Im}\rho_1|>\delta$, they are not in the disc at all.

So PROOF.md's "including physical heights $C_B/\ell<|\gamma_1|\le1$" is
correct. The code (`first_outside_blocks.first_out_input`) has two parts:
* hidden columns with objective $e^{-A\,{\rm lo}_h}B_{\phi_1}(p)$, where
  $p=\max(a,{\rm lp},\text{gap.lo})$ and real $=({\rm type}=\mathrm{rc})$;
* a hidden tail column $[R_h,\infty)$ with objective
  $e^{-AR_h}B_{\phi_1}(p)/w(R_h)$, far cost $1$ and count coefficient
  $\lfloor w(R_h)^{-1}\rfloor$.

The tail is valid because $e^{-At}/w(t)$ is nonincreasing (§4), and each
character counts $1=w(t)^{-1}w(t)\ge w(R_h)^{-1}w(t)$. Both match.
PROOF.md §3 does not state $\phi$ for the hidden columns, and §7 omits the
hidden tail (§6, H10).

### 3.7 The leaf objective

**Proposition 3.17.** Take a configuration in a middle-range leaf ($.1\le\lambda_1<1.5$) satisfying the leaf's zero-level hypotheses. Define its point by:
* $x_i:=\#\{\text{ordinary }\chi:\lambda^*_\chi\in[{\rm lo}_i,{\rm hi}_i]\}$
  (one bin per character);
* $x_{\rm tail}:=\sum_{\lambda^*_\chi\ge R}w(\lambda^*_\chi)$;
* $y_h$: the number of first-family characters with
  $t_\chi\in[{\rm lo}_h,{\rm hi}_h]$ (outside leaves);
* $z_j:=n_2\mathbf 1[\nu_2\in\text{column }j]$.

Then
$$
W_{\rm occ}\ \le\ {\rm first}+\sum_iG({\rm lo}_i)x_i+\frac{G(R)}{w(R)}x_{\rm tail}+\sum_hG_hy_h+\sum_jG_{\phi_2}(l_j)z_j+\mathrm{Err},
$$
where:
* ${\rm first}=\min(J_{\rm old},J_{\rm new})+J_2$ (inside; $J_{\rm new}$ only
  if $p\ge b$);
* ${\rm first}=J_2$ (outside);
* $J_2$ is omitted when the second family is given columns;
* $\mathrm{Err}$ is the sum of the error terms of Corollary 3.11 and
  Propositions 3.13–3.16.

*Proof.* Split the characters into $\mathcal F_1$, the reserved family and the
ordinary characters.
* **Ordinary.** Corollary 3.11 and $G$ nonincreasing. Characters with
  $\lambda^*_\chi>C_P$ cost $0$, and $G\ge0$ lets them be counted anyway.
* **Tail.** For $\lambda^*\ge R$,
  $G(\lambda^*)=\frac{G(\lambda^*)}{w(\lambda^*)}w(\lambda^*)\le\frac{G(R)}{w(R)}w(\lambda^*)$.
  Here $G/w=B\cdot(e^{-A\lambda}/w)$ is a product of positive nonincreasing
  functions when $A\ge2x$ (§4).
* **Reserved family.** Proposition 3.15.
* **$\mathcal F_1$ inside.** Propositions 3.13 and 3.14.
* **$\mathcal F_1$ outside.** Proposition 3.16, with
  $e^{-At_\chi}\le e^{-A{\rm lo}_h}$; the hidden tail is handled as above. ∎

The configuration's point satisfies the far row, the count rows and the near
rows by the other components (PROOF.md §§4–7). So
$W_{\rm occ}-\mathrm{Err}$ is at most the LP maximum plus ${\rm first}$.

---

## 4. The error allowance ${\rm final}=5\eta$

### 4.1 Summation over characters

**Lemma 4.0 (the far resource bounds the error sum).** Let $(c_1,c_2,\theta_w)$
be a far profile of the repository (Lean `inherited` or `retuned`). Put
$u=\frac13+2c_1$ and $x=\frac23+3c_1+c_2$. Define
$w_0(t)^2=e^{-\theta_wt}\sqrt{\min(t-u,c_2)+10^{-7}}$ on $[u,x]$, and
$w(\lambda)^{-1}=\int_u^xw_0^2e^{2\lambda t}dt$. If $A\ge2x$, then for
$\lambda\ge0$,
$$e^{-A\lambda}\le\frac{w(\lambda)}{w(0)}.$$
Consequently, for distinct $\chi\ne\chi_0$, each with a chosen zero satisfying
$|\operatorname{Im}\rho|\le1$ and $\lambda_\rho\le\frac13\log\log\ell$, and
for $q\ge q_0$,
$$\sum_\chi e^{-A\lambda_\chi}\le\frac{(1+\eta)V}{w(0)}=:K_{\rm far}.$$
Numerically:
* inherited: $K_{\rm far}=16.3717$, with $2x=2.34737<A=3.156342$;
* retuned: $K_{\rm far}=18.4712$, with $2x=2.26067$.

*Proof.* $e^{-A\lambda}w(\lambda)^{-1}=\int_u^xw_0^2e^{(2t-A)\lambda}dt$, and
$2t-A\le2x-A\le0$, so this is nonincreasing in $\lambda$. Then apply X
Lemma 5.1 (5.19), with its $\varepsilon=M^2\eta$. The lemma allows an
arbitrary choice of one zero per character (X §3.2.2, p. 26), and a sub-sum
of its positive left side is bounded by the whole. ∎

The E2 summation may use the inherited profile on every leaf, even one whose
far row uses the retuned profile. It is an independent application of the
lemma.

### 4.2 The split and the order of constants

**Proposition 4.1 (error allowance).** Choose, in this order, the constants
below. The dependencies and the resulting term are listed.

| Step | Choice | Depends on | Term |
|---|---|---|---|
| S0 | $L$, kernel, far profiles, tests, anchors (finite $\mathcal P\subset[0,2]$), leaves; $\eta=10^{-6}$ | — | — |
| S1 | $\varepsilon_c:=\eta H_0$; $C_P\ge\max(C_0(\varepsilon_c),3)$; $N_0:=N_0(C_P)$ | S0 | **E1** $=\varepsilon_c/H_0=\eta$ |
| S2 | $\theta$ with $\bigl((c_1\theta+N_0\omega(\theta))(K_{\rm far}+2)+2(4c_1\theta+2\omega(\theta))\bigr)/H_0\le\eta$ | S0, S1 | **E4** (smoothing) $\le\eta$ |
| S3 | $M$ (near lemma, PROOF.md §4); then $C_B>\max(C_P+M,1.5)$ with $4c_{\rm out}(\theta)/(H_0C_B^2)\le\eta$ | S0–S2 | **E3** $\le\eta$ |
| S4 | $\varepsilon\le\eta H_0/19$ (Lemma 3.2/3.1 tolerance); the radius $\delta\le\frac16$ of Lemma 3.6 | S0–S3 | **E2** $\le\frac{\eta}{19}(K_{\rm far}+2)<\eta$ with the inherited profile |
| S5 | $q_0$: the maximum of the thresholds of Theorem 2.3, Lemmas 3.6 and 3.8, Propositions 3.9–3.16 (including $\sqrt2C_B/\ell\le\delta$), X Lemma 5.1 and the other components | all | — |

Then $\mathrm{Err}\le$ E2 + E3 + E4 $\le3\eta$. Consider a certified leaf, with
value ${\rm first}+{\rm final}+(\text{LP bound})=:V_{\rm cert}<1$ and
${\rm final}=5\eta$. We get
$$W_{\rm occ}+\eta\le{\rm first}+\text{LP bound}+4\eta=V_{\rm cert}-\eta<1,$$
so Corollary 2.4 gives the prime.

*Proof and comments.*
* **Where each error comes from.**
  * Ordinary and reserved characters contribute $\varepsilon'e^{-A\lambda_\chi}$,
    where $\lambda_\chi$ is the parameter of a zero of height $\le T^*\le1$ or
    $\le1$.
  * First-family characters contribute $\varepsilon'e^{-A\lambda_1}$
    ($J_{\rm old}$), $\varepsilon''e^{-Aa}$ ($J_{\rm new}$), or
    $e^{-At_\chi}(\varepsilon'+\ldots)$ (hidden).
  * All characters are distinct, and each carries one chosen zero of height
    $\le1$: $\rho_1$ inside, the $R_P$ zero at $t_\chi$ outside, $\nu$, or
    $\lambda^*$. So Lemma 4.0 applies to the $e^{-A\lambda_\chi}$-weighted
    terms.
  * The $e^{-Aa}$-weighted $J_{\rm new}$ terms belong to at most two
    characters. They are bounded by $\le1$ times their constants: the "$+2$"
    and the second summand in S2.
  * The $\varepsilon$-parts sum to E2 and the $\theta$-parts to E4.
* **E3.** There are at most $\alpha\le2$ adverse distinguished terms, in
  total: one per character for the complex type, two for type rc. Each is
  weighted by $e^{-At}\le1$. PROOF.md's "four" is a safe overcount.
* **No circularity.** $c_{\rm out}$ depends on $\theta$ (S2), which precedes
  $C_B$ (S3). $\delta$ depends on $\varepsilon$ and on the smoothed tests; it
  is chosen after S2 and needs only $\delta\le\frac16<\frac12\le T^*$. $N_0$
  depends on $C_P$ only.
* **Items inside other bounds.** Prime powers and the $O(\ell^{-1})$ of
  (3.56) are inside (3.57). The far lemma's $\varepsilon$ is inside
  $(1+\eta)V$. The near-lemma errors are inside $\eta'$ (other component).
  Enclosure errors are rounded outward in the code.
* **Consistency with PROOF.md.** This is the table of PROOF.md §2
  (E1–E4, total $\le4\eta<5\eta$) and the order of §10 (steps 2–6). It
  corrects three details:
  * E2's summation should either use the inherited profile or keep a margin
    for the two $e^{-Aa}$-weighted characters; $18.47+2>19$ for the retuned
    profile.
  * E3 has at most two terms.
  * The smoothing stage, and $c_{\rm out}$'s dependence on it, are missing
    from interface-closure §5, whose §6 lists only E1–E3. ∎

---

## 5. Literature inputs

Each entry gives the printed statement (translated from German for X), its
hypotheses and page, and the check of our use.

**[X-C1] Condition 1** (X p. 17; from H journal p. 280 = copy p. 20).
> Let $x_0>0$ and $f:[0,\infty)\to\mathbb R$ continuous with $f(t)=0$ for
> $t\ge x_0$. Further let $B>0$ be a constant such that for all
> $t\in(0,x_0)$ the function $f$ is twice continuously differentiable and
> $|f''(t)|\le B$.

*Use:* $f^\theta_\lambda$ (Lemma 3.7(3)) and $f_0$ (Lemma 3.8). The step
autocorrelation $f_\lambda$ does **not** satisfy it (Remark 2.6), which is why
it is never inserted into Lemma 3.2.

**[X-C2] Condition 2** (X p. 18; H journal p. 286 = copy p. 27).
> $f(t)\ge0$ for $t\in[0,\infty)$, and the Laplace transform
> $F(z)=\int_0^\infty e^{-zt}f(t)dt$ satisfies $\operatorname{Re}F(z)\ge0$ for
> $\operatorname{Re}z\ge0$.

*Use:* derived for $f^\theta_\lambda$ and $f_0$ from Lemma 3.5 (Lemmas 3.4,
3.8). It is used only to discard disc zeros with $\lambda_\rho\ge$ anchor.

**[X-φ] The conductor coefficient** (X p. 17; H Lemma 2.5, copy p. 10).
> Let $\chi\ne\chi_0$ be a character mod $q$ and
> $\phi=\phi(\chi)=\frac14$ if $q$ is cube-free [i.e. $p^3\nmid q$ for all
> primes $p$] or $\operatorname{ord}\chi\le\mathcal L$; $\phi=\frac13$
> otherwise.

*Use:* $\phi\le\frac13$ always, and $\phi=\frac14$ for real $\chi$
($\operatorname{ord}=2\le\ell$). Remark 3.12.

**[X-L3.1] = H Lemma 5.3** (X p. 18; H copy p. 25).
> Let $s=\sigma+it$ with $|\sigma-1|\le(\log\mathcal L)^{1/2}/\mathcal L$,
> $|t|\le\mathcal L$, and let $f$ satisfy Condition 1. Then
> $\sum_{n\ge1}\Lambda(n)\chi_0(n)n^{-s}f(\mathcal L^{-1}\log n)=\mathcal L\,F((s-1)\mathcal L)+O(\mathcal L/\log\mathcal L)$,
> where the implied constant depends only on $f$.

*Use:* at real $s=1-\sigma_0/\ell$, $\sigma_0\in[0,C_P]$, for the smoothed
tests (Proposition 3.9(a)), and at $s=1$ for $f_0$ (Lemma 3.8). The range
holds for large $q$. Uniformity is from [X-dep].

**[X-L3.2] = H Lemma 5.2** (X p. 18; H copy p. 24).
> Let $\chi\ne\chi_0$ be a character mod $q$, $\phi=\phi(\chi)$ as above,
> $s=\sigma+it$ with $|\sigma-1|\le(\log\mathcal L)^{1/2}/\mathcal L$,
> $|t|\le\mathcal L$ (3.6), and $f$ satisfying Condition 1 with $f(0)\ge0$.
> Then for every $\varepsilon>0$ there is a $\delta\in(0,1)$, depending on $f$
> but not on $\chi$, $q$ or $s$, and a $q_0=q_0(f,\varepsilon)$, such that for
> all $q\ge q_0$
> $$\sum_{n\ge1}\Lambda(n)\operatorname{Re}\Bigl(\frac{\chi(n)}{n^s}\Bigr)f(\mathcal L^{-1}\log n)\le-\mathcal L\sum_{|1+it-\rho|\le\delta}\operatorname{Re}F((s-\rho)\mathcal L)+\frac{f(0)}2\phi\mathcal L+\varepsilon\mathcal L .$$
> The sum is over the nontrivial zeros $\rho$ of $L(s,\chi)$ with
> $|1+it-\rho|\le\delta$, each according to its multiplicity.

H's version has $f(0)(\frac\phi2+\varepsilon)\mathcal L$, which is equivalent.
*Use:* $t=0$ and $\sigma=1-\sigma_0/\ell$, for $f^\theta_{\sigma_0}$ and $f_0$.
All hypotheses are met; $\chi$ may be imprimitive. The radius is $\le\frac16$
by Lemma 3.6 [PD]. The zero sum includes zeros to the right of $s$ (needed
for the distinguished zeros in Propositions 3.14 and 3.16).

**[X-L3.3] = H Lemma 6.1** (X p. 19; H copy p. 26).
> There are $q_0$ and a number $l=l(q)\in\mathbb N$ depending on $q$, with
> $l\le\frac1{10}\mathcal L$, such that for $q\ge q_0$ the function
> $\prod_{\chi}L(s,\chi)$ has no zeros in the two rectangles
> $R(10l)\setminus R(l)$.

*Use:* disc zeros ($|\operatorname{Im}\rho|\le\delta<10l$) lie in $\mathcal R$
or far to the left (statement (F), §3.4). This is exactly X's own use in the
proof of Lemma 3.4 (p. 20).

**[X-sel] Selection of $\rho_k$, $\chi_k$, $\rho'$** (X (3.11)–(3.12),
pp. 21–22). Paraphrased in Definitions 1.3 and 1.4. The type-dependent
exclusions (Cases 1–3) match PROOF.md's $\lambda'$.

**[X-L3.5] = H Lemma 4.1** (X p. 22; H copy p. 18).
> Let $F_1$ and $F_2$ be holomorphic in $\mathbb H=\{\operatorname{Re}z\ge0\}$
> with $\operatorname{Re}F_1(z)\ge|F_2(z)|$ on $\operatorname{Re}z=0$. Let
> $F_1$ and $F_2$ tend to $0$ uniformly in $\mathbb H$ as $|z|\to\infty$.
> Then $\operatorname{Re}F_1(z)\ge|F_2(z)|$ on all of $\mathbb H$.

*Use:* Lemma 3.4(3) (entire functions, decay verified there) and
Lemma 3.8(1).

**[X-(3.51),(3.54)]** (X pp. 33–34). The triangle $h_{L,K}$, "with positive
constants $L$, $K$ and $L-2K>0$", and its transform
$H_{L,K}(z)=e^{-(L-2K)z}\bigl(\frac{1-e^{-Kz}}z\bigr)^2$. *Use:* Lemma 2.2.

**[X-(3.56)–(3.58)]** (X pp. 34–35). See Theorem 2.3. *Hypotheses:* a finite
real combination with $L_i>2K_i+3$, and fixed $\varepsilon$. *Use:*
$c_k>0$ and $L_k-2K_k=A+k\kappa>3$; $\varepsilon=\eta H_0$; the square is
enlarged to $C_P\ge C_0$. X's own kernel (6.2) is a six-triangle combination
used the same way (X p. 77: condition (6.3) "in order to be able to apply
(3.57) to this $h$").

**[X-L3.10] and its proof** (X pp. 35–36).
> Lemma 3.10 (compare Lemma 13.3 of [H]). We use the $C_0$ from (3.58). Let
> $\varepsilon,\lambda_{11}>0$, $\lambda\in(\lambda_{11},C_0]$, $M\in\mathbb N$
> and $f^\lambda_{1i}$ ($i=1,\dots,M$) functions each satisfying Condition 1
> for some $x_{0i}>0$. For all $i$ let $x_{0i}$, $x_{0i}^{-1}$,
> $\sup_{t\ge0}|f_{1i}(t)|$ and
> $\sup_{t\in(0,x_{0i})}\{|(f^\lambda_{1i})'(t)|+|(f^\lambda_{1i})''(t)|\}$
> be bounded above by a positive constant $C_1$ depending only on
> $\lambda_{11}$ and $C_0$. Let $f^\lambda_1=\sum_if^\lambda_{1i}$ be
> nonnegative. Let $H_2$ be holomorphic in $\operatorname{Re}z\ge0$, and let
> the Laplace transform $F^\lambda_1$ of $f^\lambda_1$ satisfy
> $|H_2(\lambda+it)|\le\operatorname{Re}F^\lambda_1(it)$ for $t\in\mathbb R$
> (3.59). Let $H_2$ and $F^\lambda_1$ tend to $0$ uniformly for
> $\operatorname{Re}z\ge0$, $|z|\to\infty$. Finally let $\chi\ne\chi_0$, and
> let $L(s,\chi)$ have no zeros in the rectangle
> $1-\mathcal L^{-1}\lambda<\beta\le1$, $|\gamma|\le1$. Then there is an
> effectively computable $q_0$, depending on $\varepsilon$, $M$,
> $\lambda_{11}$ and $C_0$ but not on $\lambda$, such that for $q\ge q_0$
> $$\sum\nolimits'_\rho|H_2((1-\rho)\mathcal L)|\le F^\lambda_1(-\lambda)+\frac{f^\lambda_1(0)}6+\varepsilon,\tag{3.60}$$
> the sum running over the zeros of $L(s,\chi)$ in (3.58).

The proof (pp. 35–36) chains Lemma 3.5, Lemma 3.2 (for each $f_{1i}$),
$f_1\ge0$ and Lemma 3.1. [X-dep] is the paragraph after it: "The $\delta$ and
$q_0$ of Lemma 3.2 and the implied constant of Lemma 3.1 depend only on
$\varepsilon$ and an upper bound for $x_0$, $x_0^{-1}$, $\sup|f|$ and
$\sup\{|f'|+|f''|\}$ […] because this lemma will later be used for arbitrary
$\lambda\in(0.348,C_0]$."

*Use.* We use the argument, not the statement (Proposition 3.9(c)), with
four departures:
* $M=1$ and $f_1=f^\theta_\lambda$ with $f_1(0)\ge0$. X's statement omits the
  hypothesis $f_{1i}(0)\ge0$ that Lemma 3.2 needs, and for $M>1$ its chain
  applies Lemma 3.2 to each $f_{1i}$ after restricting to the square, which
  requires summing first on a common disc. Neither issue arises for $M=1$.
* $C_0$ replaced by $C_P$, which the proof permits.
* The disc hypothesis in place of the rectangle hypothesis, which is all the
  proof uses.
* $\phi(\chi)$ kept (Remark 3.12).

**[X-L5.1] Lemma 5.1, (5.19)** (X p. 66).
> Let $\varepsilon,c_1,c_2>0$, $\lambda_0=\frac13\log\log\mathcal L$,
> $M\in\mathbb N$, $\alpha_i\ge0$ with $\sum\alpha_i=1$,
> $x=\frac23+3c_1+c_2$ and $u_i=\frac13+2c_1+ic_2/M$. Let
> $w_0:[u_0,x]\to\mathbb R$ be continuous, continuously differentiable except
> at finitely many points, with $1\ll w_0\ll1$ and $w_0'\ll1$. Then there is
> $q_0$, depending on all chosen parameters, such that for $q\ge q_0$
> $$\sum_{1\le k\le N(\lambda_0)}\Bigl(\int_{u_0}^xw_0(t)^2e^{2\lambda^{(k)}t}dt\Bigr)^{-1}\le\frac{M^2+\varepsilon}{c_1c_2^2}\sum_{i=1}^M\alpha_i^2\int_{u_{i-1}}^xw_0(t)^{-2}\min\{t-u_{i-1},u_i-u_{i-1}\}dt .$$

Here (X §3.2.2, p. 26) $N(\lambda)$ counts the characters with a zero in
$\sigma\ge1-\mathcal L^{-1}\lambda$, $|t|\le1$, and for each "we choose an
associated zero $\rho^{(k)}$". *Use:* Lemma 4.0, with one chosen zero of
height $\le1$ and $\lambda\le C_P\le\lambda_0$ per character. The profile
conditions are proved in Lean (`far_bound_corpus`).

**[X-6] X §6.1–6.2** (pp. 77–82): (6.22) $B$, (6.23) $\alpha$, (6.24) $n$,
$A(\chi_1)$ (p. 80), (6.32) and (6.33) $L-2K-2K_2\ge2x$. These are the
templates for §§3.3–3.4 and Lemma 4.0. They are not used as inputs.
Differences:
* X's $B$ has $1/6$ throughout;
* X's $A(\chi_1)$ uses $\max\{0,\cdot\}$ (compare Remark 3.13′);
* X sums the per-character errors of (6.32) implicitly into one $\varepsilon$.
  The explicit justification is Lemma 4.0, as in H §15 (H's $w$ and
  "$e^{-(L-2K)\lambda}B(\lambda)/w(\lambda)$ is decreasing", copy p. 87).

**[H-L3.1] H Lemma 3.1 and proof** (copy pp. 12–14).
> For any $\varepsilon>0$ there is $\delta=\delta(\varepsilon)>0$ such that
> $-\operatorname{Re}\frac{L'}L(s,\chi)\le-\sum_{|1+it-\rho|\le\delta}\operatorname{Re}\frac1{s-\rho}+(\frac\phi2+\varepsilon)\mathcal L$,
> uniformly for $1+\frac1{\mathcal L\log\mathcal L}\le\sigma\le1+\frac{\log\mathcal L}{\mathcal L}$,
> $|t|\le\mathcal L$, for $q$ sufficiently large.

The proof fixes $\delta=\min(\frac1{2k},\frac{\varepsilon_0}{3c_0k^2})$ with
$k\ge3$. *Use:* Lemma 3.6 only.

**[H-L13.3] H Lemma 13.3** (copy p. 82) and its use in §14 (copy p. 83).
> $\sum'_\rho|F_2((1-\rho)\mathcal L)|\le\frac\phi2\frac{1-e^{-2K\lambda}}\lambda+\frac{2K\lambda-1+e^{-2K\lambda}}{2\lambda^2}+\eta$
> for $q\ge q(\eta)$, under "$L(s,\chi)$ has no zeros in the rectangle
> $1-\mathcal L^{-1}\lambda<\beta\le1$, $|\gamma|\le1$".

§14: "we may take $\lambda=1.42$ and $\phi=\frac13$ for $\chi\ne\chi_1$, and
$\lambda=0$ and $\phi=\frac14$ for $\chi=\chi_1$". *Use:* precedent for
Remark 3.12.

**[H-15] H §15, (15.1)** (copy p. 86). The first-family comparison
$(e^{-(L-2K)\lambda_1}-e^{-(L-2K)\lambda'})(B(\lambda_1)-\alpha K^{-2}F_2(\lambda_1))$
is the ancestor of $J_{\rm old}$. It is not used as an input.

**[4.33 §2] Repository** (4.33.md §2, two-test foundation §§5–6, near-blocks
§5). These are the sources of $J_{\rm old}$, $J_{\rm new}$, $C(p,a)$, the
hidden-column bound and the smoothing. Here they are re-derived in full
(Propositions 3.13–3.16, Lemmas 3.5, 3.7 and 3.8).

---

## 6. HOLES AND CONCERNS

None is blocking. None invalidates a certificate number.

| # | Severity | Issue | Suggested fix |
|---|---|---|---|
| H1 | minor | The smoothing is described as "in $L^1$" (PROOF.md §3; two-test foundation §5, "converge in $L^1$"). $L^1$ convergence alone does not give convergence of the conductor term $\frac\phi2 f_\lambda(0)=\phi\int\psi^2e^{-2\lambda u}$, which needs $L^2$ | Require $0\le\psi_\theta\le\max\beta_i$, with support in $(0,T)$ (mollification), as in Lemma 3.7; then all errors are $\le c_1\theta$ |
| H2 | minor (closed here) | The per-character count $N_0$ of $R_P$ zeros, which the smoothing needs, is asserted in PROOF.md without proof. Two-test foundation §5 sketches it only for $\lambda_1\ge.1$ (anchor $.05$) | Include Lemma 3.8 (anchor $0$, all regimes, $N_0(C)=\frac{2e}{\cos1}(1+\frac C6)$) |
| H3 | minor [PD] | X Lemma 3.10 as printed: (a) omits $f_{1i}(0)\ge0$, needed by Lemma 3.2; (b) for $M>1$ applies Lemma 3.2 to each piece after restricting to the square, which is valid only after summing on a common disc; (c) is stated with the criterion's $C_0$ and the rectangle hypothesis. The "localized form" is a reading of the proof | Use it as in Proposition 3.9: $M=1$, $f(0)\ge0$, $C_0:=C_P$, disc hypothesis. State in the paper that this is derived from the printed proof |
| H4 | minor [PD] | $\delta<\frac12$ is not in X's statement ($\delta\in(0,1)$). It comes from H's proofs (H Lemma 3.1, copy p. 14: $\delta\le\frac16$; the proof works for every smaller $\delta$; remark after Lemma 5.2) | Lemma 3.6 as written. An alternative avoids it: disc zeros above height $T^*$ with $\lambda_\rho<\lambda$ are $O(1)$ in number, and each has $\lvert F\rvert\ll1/\ell$ |
| H5 | minor [PD] | $B_{1/4}$ for real characters: X prints $f(0)/6$ in (3.60) and (6.22). The $\phi(\chi)$ version is a proof-derived variant, sound and parallel to H Lemma 13.3 and H §14. The Lean hypothesis `XylourisLemma32` is stated only with $\phi\le1/3$, so the $\phi=\frac14$ uses ($J$ for rr/rc, $n_2=1$, rc hidden columns) lie outside the formal hypotheses. They are in the unformalized family bounds anyway (lean-graded README) | Cite as in Remark 3.12. If formalized, add $\phi(\chi)=\frac14$ for real $\chi$ to the Lemma 3.2 hypothesis |
| H6 | minor (closed here) | The validity of $J_{\rm old}$ when $p<b$ (and $p<a$) is asserted ("old safe bound retained", 4.33 §2) but nowhere proved | Proposition 3.13, case (iii) |
| H7 | minor (optimality, not soundness) | For type rc, $B_{1/4}<2\tilde h$ for $\lambda<1.895$, so $J_{\rm old}=2e^{-Aa}\tilde h(a)$ throughout. This is weaker than X's own $\max\{0,\cdot\}$ form and than $nG_{\phi_1}(a)$, by about 6% at $a=.75$ | Optionally use $\min(J_{\rm old},nG_{\phi_1}(a),J_{\rm new})$ (Remark 3.13′). No certificate needs it |
| H8 | minor | E2 wording: PROOF.md sums "$\varepsilon_1$ per character through $\sum_\chi e^{-A\lambda_\chi}<19$". The $J_{\rm new}$ errors are $e^{-Aa}$-weighted, not $e^{-A\lambda_1}$-weighted, and with the retuned profile $K_{\rm far}=18.47$ leaves margin $0.53<2$ | Use the inherited profile for the E2 summation ($K_{\rm far}=16.37$) and add $2$ for the first family, as in Proposition 4.1 |
| H9 | minor (docs) | E3 says "at most four" terms; there are at most two. $c_{\rm out}$ depends on the smoothing, so $C_B$ must follow $\theta$. PROOF.md §10 respects this, but interface-closure §5's table has no smoothing stage, and its §6 lists only E1–E3 | Harmonize with Proposition 4.1 |
| H10 | minor (docs) | PROOF.md §3 gives the hidden-column cost as "$e^{-At}B(p)$" without $\phi$; the code uses $B_{1/4}$ for rc, which is correct. The hidden tail column (count coefficient $\lfloor w(R_h)^{-1}\rfloor$, objective $e^{-AR_h}B(p)/w(R_h)$) is absent from PROOF.md §7 (also noted in leaf-data-semantics §4) | State both in the paper (Proposition 3.16 and the paragraph after it) |
| H11 | minor (code) | $A>2x$, needed for the tail columns and E2, is asserted only in `replace_far`. Inherited-weight leaves rely on the unasserted fact $2.347<3.156$ | Add an assertion, or state it once in the paper (Lemma 4.0) |
| H12 | minor (citations) | PROOF.md's H page numbers ("p. 14", "p. 24", "p. 38", …) are those of the 99-page Oxford copy, not of Proc. LMS 64 (1992) 265–338. X's page numbers are correct | In the paper cite H by lemma or equation number, or convert to journal pages (X's cross-references give Condition 1 = p. 280, Condition 2 = p. 286, (3.56) = p. 325). **Uncertain:** other journal pages are not determinable from the available text |
| H13 | minor (wording) | "All the costs in §3 bound individual occurrences" is imprecise. Each cost bounds the occurrence *sum* $S_\chi(H)$ of one character, with multiplicity, which is what (3.57) needs | Use the wording of Remark 2.5 |
| H14 | informational | PROOF.md's $\lambda\ge\lambda_{\min}>0$ in the ordinary envelope is unnecessary with smoothed tests | None needed |
| H15 | informational (scope) | The zero-level hypotheses fed into these costs are outside this component and were not verified here: (Z1), (Z2), $\lambda'$ gaps, the $T^*$ pigeonhole, the reserved ranges and the inside/outside split (PROOF.md §§4–5, 8) | Covered by other deep dives |
| H16 | informational | The alternative "exact step kernel" route (interface closure 7d) is also valid and would remove E4 and Lemma 3.7. Write $f_\lambda$ as a sum of 17 Condition-1 pieces: rebalanced kink-cancelling terms $s_j(j\kappa-t)_++c_j(j\kappa-t)_+^2-(\ldots)\varphi_j(t)$, each vanishing at $0$, plus a $C^2$ remainder with $r(0)=f_\lambda(0)\ge0$ | Optional; the smoothing route is complete as written |

---

## 7. Numerical checks performed

These were run with `.venv/bin/python`; scripts are in
`scratchpad/costs/check{1,2,3b,4}.py`.

* **Kernel.** The values of $\kappa$, $A=3.156342$, $\Psi(0)$, $H_0$ and all
  $c_k$ are exact rationals. $\sum c_k=(\sum\beta_i)^2$ holds exactly, and
  $3+2T=3.833658$.
* **$B_\phi$.** The closed form of Lemma 3.2(2) was compared with direct
  30-digit quadrature of the definition at $\lambda\in\{.1,.75,1.5,3\}$ and
  $\phi\in\{\frac13,\frac14\}$. The difference is below $2\cdot10^{-28}$.
* **$C(p,a)$.**
  * $C(1.54,.74)=0.46838341468$ by a Riemann sum with 32,000 cells, against
    the repository's certified $0.4683834147609186$.
  * $C(.7,.7)=\tilde h(.7)=0.67510098908$.
* **$D_\lambda$ and $V_p$.** $D_\lambda(t)\ge0$ was sampled for
  $\lambda\in\{.3,.5,.74,1.2,1.54\}$ with $p=1.54$. $V_p$ decreases from
  $0.3236$ to $1\cdot10^{-13}\approx V_p(p)=0$.
* **Sample $J$ values ($L=3.99$).**

  | cell | $p$ | $J_{\rm old}$ | $J_{\rm new}$ |
  |---|---|---|---|
  | complex $[.74,.7425]$ | $1.54$ | $.13950$ | $.13510$ |
  | rr $[.70,.7025]$ | $1.2$ | $.08756$ | $.08413$ |
  | rc $[.63,.64]$ | $1.0$ | $.19217$ | $.18775$ |

  Both are valid; the leaf takes the minimum.
* **$B_{1/4}$ against $2\tilde h$.** $B_{1/4}-2\tilde h$ has its root at
  $\lambda=1.89505$ and is negative below it.
* **Reference values.**

  | $\lambda$ | $B_{1/3}$ | $B_{1/4}$ | $\tilde h$ | $G$ |
  |---|---|---|---|---|
  | 0 | 2.11670 | 1.83752 | 1 | 2.11670 |
  | 0.44 | 1.66425 | 1.45307 | 0.78033 | 0.41503 |
  | 0.75 | 1.41104 | 1.23706 | 0.65665 | 0.13227 |
  | 1 | 1.23855 | 1.08946 | 0.57211 | 0.05274 |
  | 1.5 | 0.96139 | 0.85136 | 0.43589 | 0.0084475 |
  | 3 | 0.47839 | 0.43213 | 0.19874 | $3.693\cdot10^{-5}$ |

* **$K_{\rm far}$.** Quadrature gives $V=175.26640$ (repository
  $175.2664033\ldots$) and $w(0)^{-1}=0.0934101$, so $K_{\rm far}=16.3717$ for
  the inherited profile. For the retuned profile: $V=243.32102$,
  $w(0)^{-1}=0.0759127$, $K_{\rm far}=18.4712$. $e^{-A\lambda}/w(\lambda)$ is
  decreasing on the samples $0,\dots,5$.

---

## 8. References

* **[H]** D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and
  the least prime in an arithmetic progression*, Proc. London Math. Soc. (3)
  **64** (1992), no. 2, 265–338. doi:10.1112/plms/s3-64.2.265. *Page numbers
  above refer to the 99-page author copy (Oxford University Research Archive)
  in `literature/`. Journal page numbers are uncertain except those X quotes:
  pp. 280, 286, 325.*
* **[X]** T. Xylouris, *Über die Nullstellen der Dirichletschen L-Funktionen
  und die kleinste Primzahl in einer arithmetischen Progression*, Dissertation,
  Rheinische Friedrich-Wilhelms-Universität Bonn, 2011 (defended 16 November
  2011). Also Bonner Mathematische Schriften **404** (2011). 110 pp.
* **[X-AA]** T. Xylouris, *On the least prime in an arithmetic progression and
  estimates for the zeros of Dirichlet L-functions*, Acta Arith. **150**
  (2011), no. 1, 65–91. doi:10.4064/aa150-1-4. (The article counterpart; its
  Lemma 2.1 is a variant of H Lemma 5.2. Not needed above.)
* **[X-18]** T. Xylouris, *Linniks Konstante ist kleiner als 5*, Chebyshevskii
  Sb. **19** (2018), no. 3, 80–94. doi:10.22405/2226-8383-2018-19-3-80-94.
  (Context only.)
* **[HB90]** D. R. Heath-Brown, *Siegel zeros and the least prime in an
  arithmetic progression*, Quart. J. Math. Oxford (2) **41** (1990), 405–418.
  doi:10.1093/qmath/41.4.405. (Used by PROOF.md §9, not by this component.)
* **Repository sources:**
  * `research/PROOF.md` §§1–3, 10–11;
  * `research/arguments/4.33.md` §§1–3;
  * `research/arguments/two-test-foundation.md` §§5–6, 8;
  * `research/arguments/near-blocks.md` §§5–7;
  * `research/notes/interface-closure-2026-09-29.md`;
  * `research/notes/occurrence-accounting.md`;
  * `research/notes/leaf-data-semantics-2026-09-29.md`;
  * `computations/core/code/{config_v4,enclosures,base_enclosures,triple_inputs,published_single_inputs,endgame}.py`;
  * `computations/near/code/first_outside_blocks.py`;
  * `computations/graded/graded_leaves.py`;
  * `lean-graded/GradedNear/{Kernel,Functions,KernelFacts,Prime,Envelope,Adapters}.lean`.
