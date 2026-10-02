# Real-first zero-location rows from conductor interpolation

Updated 2026-09-10. This is a new analytic deduction under the retained
explicit-formula and finite-zero-selection premises, with independently checked
numerical consequences. It is not a global Linnik bound.

For a real first character with a real first zero, the degree-two rows include

| First-zero interval | Global second-family lower bound |
| --- | --- |
| `[.700,.7025]` | `.7765` |
| `[.7025,.705]` | `.7754` |
| `[.710,.7125]` | `.7721` |
| `[.7375,.740]` | `.7603` |
| `[.750,.7525]` | `.7551` |

All 21 cells of width `.0025` across `[.700,.7525]` have outward elementary
certificates. Both real and nonreal second characters are covered, including the
order-four principal alias. The prior special row on `[.700,.7025]` gave `.762`;
reevaluating its original conductor bound with optimized parameters gives `.7624`.
The larger gain to `.7765` comes from the conductor interpolation below.

The degree-five refinement in §5 further raises the first row to **`.7793`**
and supplies 22 cells through `.755`. Both stages and their separate numerical
evidence are retained.

## 1. A weighted version of Heath–Brown's final-section refinement

Let

\[
 v=\prod_{p^e\parallel q,\ e\ge3}p^e,
 \qquad \theta=\frac{\log v}{\log q}\in[0,1].
\]

Heath–Brown Lemmas 2.3–2.5 and §16(4)
(the retained PDF's printed pp.8–10 and 93–94) give the character-sum bounds and
their passage to L-functions. Section 16 explicitly uses `rad(q)` for a real
character and `min(q^(1/3),(v^3 q)^(1/4))` for a general character. A primitive
quadratic conductor is at most `8 rad(q)`, and

\[
 \operatorname{rad}(q)\le qv^{-2/3}.
\]

Consequently, after normalizing by `log q`, admissible growth coefficients are

\[
 \phi_1\le\frac14-\frac\theta6+o(1),
 \qquad
 \phi_{\mathrm{gen}}\le
 \min\left(\frac13,\frac14+\frac{3\theta}4\right)+o(1).
\]

The factor `8` disappears into the small error. For an inducing conductor
`f | q`, one has `f <= q` and `v(f) <= v(q)`; the imprimitive passage is explicit
on Heath–Brown's printed p.10. The contour argument of §3 is linear in the growth
coefficient, so the corresponding pointwise conductor charge is `phi f(0)/2`.
This is the same interface used in Xylouris's
Lemmas 3.1–3.4.

Fix a positive polynomial parameter `t` and write

\[
 c_1=\frac{2t}{t^2+1/2},\qquad
 c_2=\frac{1/2}{t^2+1/2},\qquad \Sigma=c_1+c_2.
\]

If `Sigma >= 1/9`, the piecewise linear function

\[
 \frac18-\frac\theta{12}
 +\Sigma\min\left(\frac13,\frac14+\frac{3\theta}4\right)
\]

increases up to `theta=1/9` and decreases thereafter. Its maximum is

\[
 \boxed{\frac18+\frac\Sigma3-\frac1{108}}.
\]

For `Sigma=1`, this is `97/216`, exactly Heath–Brown's §16(4) refinement of
`11/24`. Our application permits the different positive weights arising from
the degree-two polynomial. The checker enforces `Sigma >= 1/9`.

The Burgess parameter and all positive error tolerances are fixed before
letting `q` grow. A finite list of strictly positive numerical margins then
permits one sufficiently large uniform modulus threshold. No error parameter
depending on `q` is used.

## 2. Positive polynomial and the generic character pattern

Use the same argument as the retained real-first row, now
with variable `t>0`:

\[
 (1+\chi_1(n))\frac{(t+\cos\vartheta)^2}{t^2+1/2}\ge0,
 \qquad e^{i\vartheta}=\chi_2(n)n^{-i\gamma_2}.
\]

The nonconstant Fourier coefficients are `c1,c2>0`. If the second character is
nonreal and `chi2^2 != chi1`, the sole principal character is the constant term.
The total conductor charge is at most
`phi1/2 + (c1+c2) phi_gen`. Retaining the centered selected zeros gives

\[
 F(\lambda_1-a)+c_1F(\lambda_2-a)
 \le F(-a)+
 \left(\frac18+\frac{c_1+c_2}3-\frac1{108}\right)f(0)+o(1).
\]

Here `a` is the left first-zero endpoint, so all discarded eligible zero terms
have nonnegative real transform under the source conventions. Coincidences
among nonprincipal characters do not change the conductor upper bound: terms
are counted with their original coefficients, and extra nonnegative zero
contributions may be discarded.

For each certified first-zero cell `[a,b]` and proposed second-family bound `h`,
monotonicity of the real Laplace transform makes the endpoint expression
`F(b-a)+c1 F(h-a)` a lower bound when `lambda2 <= h`. Every retained row has a
strictly positive outward margin after subtracting the displayed right side.

## 3. Principal alias and real second characters

If `chi2^2=chi1`, then `chi2` has order four. Retain the earlier conservative
conductor bound and explicitly bound the full correlation

\[
 R(\Delta)=c_2\{\Re F(-a+i\Delta)
               -\Re F(\lambda_1-a+i\Delta)\}
               -c_1\Re F(\lambda_2-a+i\Delta).
\]

The necessary inequality has conductor coefficient `(1+c2)/8+c1/3` and the
additional term `R(Delta)`. The checker covers all four real-part corners,
second-derivative interpolation errors, and the complete height tail. This is
exactly the retained order-four treatment with the new positive coefficients;
the generic conductor saving is not applied to a principal alias.

If the second character is real, retain the separate necessary inequality

\[
 F(\lambda_1-a)+F(\lambda_2-a)
 \le F(-a)+\tfrac38 f(0)+o(1).
\]

It is checked independently with test parameter `.82`. A real character with a
nonreal selected zero is included. Thus the new second-family lower bound covers
every character type.

## 4. Evidence, integration, and limitations

The numeric code and full rows retain
rational parameters, all three positive margins, the correlation mesh and errors,
and the infinite-height bound. The inside verifier regenerates these quantities
before a `real_location` node raises a source bound or excludes a reserved-second
interval. Independent quadrature and rejection checks cover the new rows and their
application. Two agents independently checked the conductor interpolation and
principal-alias bookkeeping against the primary sources; this is not a formal
verification of the analytic number theory.

The row `.7765` excludes source 174's entire second-family interval, whose upper
endpoint is `4939/6400 = .77171875`. It also removes the saved exactly feasible
`L=4.30` profile of value `1.0140024028519812`: that profile belongs to the older
relaxation with only the weaker `.7624` location input. Source 176 retains a
nonempty interval above `.7765`; this row does not exclude that remaining scope.

## 5. A small fifth harmonic strengthens the location input

The generic conductor charge depends on the sum of the positive Fourier
coefficients, while retaining the second zero earns a term proportional to the
first coefficient. This ratio motivated the nonnegative trigonometric
polynomial search recorded here. A floating linear program with sampled
positivity constraints suggested that a small fifth harmonic improves the
degree-two family. That search supplied a proposal; the following rational
polynomial has a separate continuous positivity certificate:

\[
 P(e^{i\vartheta})=1+c_1\cos\vartheta+c_2\cos2\vartheta+c_5\cos5\vartheta,
 \quad
 (c_1,c_2,c_5)=
 \frac{(1.41866466,\ .43287503,\ .01421037)}{1.000001}.
\]

All displayed decimals are exact rationals. Put `x=cos(theta)`. Then

\[
 P(x)=1+c_1x+c_2(2x^2-1)+c_5(16x^5-20x^3+5x).
\]

The checker evaluates this polynomial exactly at all 4,001 rational points
`x=j/2000`, `-2000<=j<=2000`. Since
`|P''(x)| <= 4*c2+440*c5` on `[-1,1]`, linear interpolation has error at most
`(4*c2+440*c5)/(8*2000^2)`. Subtracting that error from the least sampled value
gives a strictly positive lower bound, approximately `6.90953e-7`.
This proves nonnegativity at every phase, including between samples.

An independent exact check
converts `P(2*t-1)` to the Bernstein basis and bisects intervals until every
coefficient is positive. Nine intervals, with maximum subdivision depth eight,
give the global lower bound `770541633/13421786221772800 > 0`.
The check report also
records all 22 row regenerations, 2,450 finite character-alias checks,
independent high-precision integral comparisons, and nine rejected corruptions.

Apply `(1+chi1(n))*P(chi2(n)n^(-i*gamma2))>=0`, as before. There are only four
types requiring separate treatment:

| Second character | Conductor coefficient and additional principal term |
| --- | --- |
| Nonreal; no principal alias | `1/8+(c1+c2+c5)/3-1/108` |
| `chi2^2=chi1` (order four) | `(1+c2)/8+(c1+c5)/3`, plus the same `R(Delta)` from §3 with the new `c1,c2` |
| `chi2^5=1` or `chi2^5=chi1` (orders five or ten) | `(1+c5)/8+(c1+c2)/4`, plus at most `c5*F(-a)` |
| Real second character | The separate degree-one inequality with coefficient `3/8` |

These exhaust the principal aliases: the only nonzero positive frequencies are
1, 2 and 5, and the second character is distinct from the real first character.
For orders five and ten, every nonprincipal character in the expansion has
order at most ten, so the quarter coefficient applies. The sole extra principal
term is bounded by `Re F(-a+i*y)<=F(-a)`, using `f>=0`. Dropping all remaining
eligible zero terms is safe. In the order-four branch the fifth-frequency terms
are nonprincipal; their zeros can be discarded and their conductor charge is
bounded by `c5/3`. Coincidences at different heights are counted term by term.

The fifth frequency remains within the source height conventions. In Xylouris
Lemmas 3.3–3.4 the selected heights have size at most `l`, the enlarged zero-free
band reaches `10*l`, and the evaluation rectangle permits heights up to `9*l`.
The required heights have size at most `5*l`. Thus this extension does not
assume a new arbitrary-height explicit formula. Factors polynomial in these
heights contribute `O(log log q)=o(log q)` to the growth argument. As in §1,
all witnesses, the Burgess parameter and positive tolerances are fixed before
increasing `q`.

The [degree-five generator and verifier](../../computations/frontier/polynomial5_rows.py)
enclose all four inequalities for every retained cell, including the complete
order-four height correlation and its tail. The first row gives

\[
 .700\le\lambda_1\le .7025,\quad \chi_1,\rho_1\text{ real}
 \quad\Longrightarrow\quad \lambda_2>.7793.
\]

Its normalized margins are at least `.0001019769354330` (generic),
`.0803635944474492` (order four), `.1279981453863842` (orders five/ten),
and `.0289072324918931` (real second). The last cell `[.7525,.755]` gives
`lambda2>.7579`. The full 22-row table is
retained here.

The sampled generic optimization gave second-zero endpoints approximately
`.7766123` at degree two, `.7794505` at degree five, `.7796272` at degree twelve,
and `.7796604` at degree twenty on the first cell. Those are exploratory
values, with no certified optimality or alias claim. The increments decreased
across these sampled degrees in this model; they do not bound the gains from
other polynomials or searches. The recorded certificates use the displayed
rational degree-five polynomial and its fully checked implications.

```bash
python3 computations/frontier/polynomial5_rows.py
python3 computations/frontier/polynomial5_rows.py --verify
```
