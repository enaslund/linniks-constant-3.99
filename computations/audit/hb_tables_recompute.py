#!/usr/bin/env python3
r"""Recompute Heath-Brown's Tables 4 and 7, and rows .10 of his Tables 2 and 5.

Source
------
D. R. Heath-Brown, "Zero-free regions for Dirichlet L-functions, and the least prime in
an arithmetic progression", Proc. London Math. Soc. (3) 64 (1992) 265--338 ("HB").
Page numbers "p. n" below are those of the repository copy
`literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf` (99 pages; in that
copy the printed page number equals the PDF page number).  Only HB's printed statements
and printed parameters are used; nothing is imported from the repository's proof code
except in the final cross-check section, which reads the values the repository uses.

Run
---
    .venv/bin/python computations/audit/hb_tables_recompute.py [--dps 30] [--check-dps 45]

It prints a summary and writes `hb_tables_recompute.json` next to this file (about one
minute; `--no-sensitivity` skips the Table 7 k-perturbation runs and roughly halves it).
All computations are in mpmath floating point (default 30 digits), with a second run of
the key roots at a higher precision as a convergence check.  These are floating-point
recomputations, not interval proofs.

What is implemented
-------------------
(0) Conventions.  F(z) = int_0^oo e^{-zt} f(t) dt is the Laplace transform of the test
    function f (§5, p. 20).  P3(X) = X + X^2 + (2/3) X^3 is the third polynomial of
    (4.12) (p. 19); HB's formula for Re P3(alpha/(beta+it)) on p. 42 reduces to it at t=0.
    Every inequality is used with epsilon = 0, i.e. we compute the root of the epsilon=0
    left-hand side.  HB's statements hold for q >= q(epsilon); a printed value c strictly
    below the root is therefore an exact consequence for large q (take epsilon below the
    margin), with no "c - epsilon" loss.

(1) The test function of Lemma 7.1 (p. 34).  For 0 < theta < pi/2 and lambda > 0:
    zeta = lambda tan theta, gamma = theta/zeta,
    g(t) = lambda (1 + tan^2 theta)(cos zeta t - cos theta) on |t| <= gamma, f = g * g, with
      f(x) = c [ c (gamma - x/2) cos(zeta x) + lambda (2 gamma - x)
                 + sin(2 theta - zeta x)/sin(2 theta) - 2 (1 + sin(theta - zeta x)/sin(theta)) ]
    for 0 <= x <= 2 gamma (c = lambda (1 + tan^2 theta)), f = 0 beyond.  F(z) (z real) is
    computed by tanh-sinh quadrature of this closed form over [0, 2 gamma].  Self-checks:
    the closed form of f against the convolution g * g computed directly; the printed
    closed forms f(0), F(0) and F(-lambda) of Lemma 7.1; and the identity of Lemma 7.5
    (p. 36), F(-lambda) - k F(0) = -lambda^{-1} f(0) cos^2 theta.

(2) Lemma 7.5 (p. 36): for 0 < k < 3, theta in (0, pi/2) solves
    sin^2 theta = k (1 - theta cot theta).  HB uses k = 3/2 for Tables 2 and 3 ("the
    function of Lemmas 7.1 and 7.5 corresponding to k = 3/2", p. 38) and k = 2 for
    Table 5 (p. 45) and Lemma 8.2 (p. 38; HB: theta = 0.9873...).

(3) Table 4 (p. 44) = Lemma 8.3, inequality (8.7) (p. 43), with epsilon = 0:
      G(l1, l') = (K^2 + 1/2)(P3((a+l1)/a) - P3(1)) - 2K P3((a+l1)/(a+l'))
                  + (K+1)^2 (a+l1)/8  >= 0,
    valid for rho' complex, a > 0, K >= 1/4, under (8.6).  G is increasing in l'
    (p. 43).  HB's reading of a row (p. 43): "choose a, K optimally at l1 = B"; the entry
    (B, l', a, K) asserts l' >= printed value whenever l1 <= B.  We compute the root r_B
    of G(B, .) = 0 (closed form: solve the cubic P3(X) = T, l' = (a+B)/X - a).
    Side conditions, exactly as HB prescribes on p. 43, with A = the previous row's l1:
      (8.8) at l1 = A:
            (K^2+1/2)/a {1 + 2u + 2u^2} + (K+1)^2/8 - 10K/(a+l1) >= 0,  u = (a+l1)/a;
            its left side increases with l1, so we also report the threshold l1* where
            (8.8) becomes an equality ((8.8) holds exactly for l1 >= l1*);
      (8.6) at l1 = B "together with the value of l' corresponding to l1 = A", i.e. the
            previous row's printed l':  (a+l')^{-3} + (a+l1)^{-3} - a^{-3} >= 0.
    The slack of (8.6) is reported as the left side minus a^{-3} (HB's form), and also as
    a margin in l': l'_max(B) - l'_used, where l'_max(B) = (a^{-3} - (a+B)^{-3})^{-1/3} - a
    is the largest l' for which (8.6) holds at l1 = B.  We also report the weaker check
    that the logic of the lemma actually needs, (8.6) at (B, printed l'_B): if l' < l'_B
    and l1 <= B then (8.6) holds at the true point, because its left side decreases in
    both variables.  Finally we check r_B > B, which disposes of the case l' < B not
    covered by HB's derivative bound (8.8) (that bound uses l' >= l1; if l' < B then
    G(l1, l') <= G(l', l') < G(B, B) < 0 since d/dx G(x, x) > 0).

(4) Table 7 (p. 48) = Lemma 8.7, (8.10)-(8.11) (p. 47), with epsilon = 0:
      H(l1, l2) = (k^2 + 1/2){F(-l2) - F(l1 - l2)} - 2k F(0) + f(0) psi >= 0,
      psi = (k^2 + 1/2)/8 + (4k + 1)/6,
    with, as printed on p. 47, k = 0.98 - 0.15 l1 and theta = 1 in Lemma 7.1, and the
    row's printed lambda.  "Optimal at l1 = B" (p. 47): k is evaluated at l1 = B, and the
    root r_B of H(B, .) = 0 is the bound for all l1 <= B (H increases in l1 and l2).

(5) Table 2 row .10 (p. 39): Lemma 6.3 (p. 30) as used on p. 38:
      2F(-l') - 2F(b - l') - F(0) + f(0)/4 = 0,  b = 0.10,
    f from Lemmas 7.1/7.5 with k = 3/2 and the printed lambda = 0.965.  HB states that
    the printed l' values are "a little below" these roots (p. 38).
    Table 5 row .10 (p. 46): Lemma 8.5 (p. 45),
      F(-l2) - F(b - l2) - F(0) + (11/24) f(0) = 0,  b = 0.10,
    f from Lemmas 7.1/7.5 with k = 2 (p. 45) and the printed lambda = 0.89.

Supplementary rows (same code, not asked for, reported separately):
    all rows of Tables 2 and 3 (Table 3 row 0.30 is the fallback the paper cites for
    Table 4's first row), all rows of Table 5, Table 6 (p. 46: Lemma 8.5 with psi <= 3/8;
    HB does not name the function; we assume the k = 2 function of Table 5, which his
    last row lambda1 = lambda = lambda2 = 0.809 matches: by Lemma 7.5 the diagonal root is
    (8/3) cos^2 theta = 0.80926), and Lemma 8.2
    (lambda' >= 8 cos^2 theta for the k = 2 theta; HB prints 2.427...).

Reading and interpretation choices
----------------------------------
* epsilon = 0 everywhere; roots are compared with the printed values.
* Table 4: a row's side conditions use A = the previous row's l1 and the previous row's
  printed l' (HB p. 43).  Table 4's first row (0.3) has no previous row; for it we
  report (8.6) at (0.3, 2.293), at (0.3, 2.43) and at (0.3, 2.84) (Table 3 rows 0.30
  and 0.25) and the (8.8) threshold, and we recompute Table 3 row 0.30.
* Table 7: k = 0.98 - 0.15 B exactly (not rounded), theta = 1 exactly.  As a
  sensitivity check we also give the roots with k shifted by +-0.01.
* HB's printed tables were transcribed by hand into this file from the local copy
  (pp. 39, 44, 46, 48); if `pdftotext` is available, the script re-extracts those pages
  and checks every transcribed row against the extracted text.
"""
from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp

HERE = Path(__file__).resolve().parent
REPO = HERE.parent.parent
PDF = REPO / "literature" / "heath-brown-1992-zero-free-regions-and-least-prime.pdf"
OUT = HERE / "hb_tables_recompute.json"

# ---------------------------------------------------------------------------------------
# HB's printed tables (transcribed from the local copy; see the docstring).
# ---------------------------------------------------------------------------------------
# Table 4, p. 44: (lambda_1 = B, printed lambda', a, K)
TABLE4 = [
    ("0.3", "2.293", "3.9", "0.89"), ("0.35", "2.195", "4.0", "0.88"),
    ("0.4", "2.108", "4.1", "0.88"), ("0.45", "2.030", "4.2", "0.87"),
    ("0.5", "1.958", "4.3", "0.87"), ("0.55", "1.893", "4.4", "0.86"),
    ("0.6", "1.832", "4.4", "0.86"), ("0.65", "1.776", "4.5", "0.85"),
    ("0.7", "1.724", "4.5", "0.85"), ("0.75", "1.676", "4.6", "0.84"),
    ("0.8", "1.630", "4.6", "0.84"), ("0.85", "1.587", "4.7", "0.84"),
    ("0.9", "1.547", "4.7", "0.84"), ("0.95", "1.509", "4.8", "0.83"),
    ("1.0", "1.473", "4.8", "0.83"), ("1.05", "1.439", "4.8", "0.83"),
    ("1.1", "1.406", "4.9", "0.83"), ("1.15", "1.375", "4.9", "0.83"),
    ("1.175", "1.360", "4.9", "0.83"), ("1.2", "1.346", "4.95", "0.83"),
    ("1.225", "1.331", "5.0", "0.83"), ("1.25", "1.318", "5.0", "0.83"),
    ("1.275", "1.304", "5.0", "0.83"), ("1.294", "1.294", "5.0", "0.83"),
]
# Table 7, p. 48: (lambda_1 = B, lambda, printed lambda_2)
TABLE7 = [
    ("0.10", "0.79", "2.76"), ("0.12", "0.79", "2.56"), ("0.14", "0.77", "2.39"),
    ("0.16", "0.77", "2.25"), ("0.18", "0.75", "2.12"), ("0.20", "0.75", "2.01"),
    ("0.25", "0.73", "1.77"), ("0.30", "0.71", "1.58"), ("0.35", "0.69", "1.42"),
    ("0.40", "0.68", "1.29"), ("0.45", "0.66", "1.18"), ("0.50", "0.65", "1.08"),
    ("0.55", "0.64", "1.00"), ("0.60", "0.63", "0.92"), ("0.65", "0.61", "0.85"),
    ("0.70", "0.61", "0.79"), ("0.745", "0.59", "0.745"),
]
# Table 2, p. 39: (lambda_1 = b, lambda, printed lambda')
TABLE2 = [
    ("0.006", "1.10", "11.34"), ("0.008", "1.09", "10.71"), ("0.010", "1.08", "10.21"),
    ("0.015", "1.07", "9.31"), ("0.020", "1.06", "8.66"), ("0.025", "1.05", "8.15"),
    ("0.030", "1.04", "7.73"), ("0.035", "1.03", "7.37"), ("0.040", "1.025", "7.06"),
    ("0.045", "1.015", "6.79"), ("0.05", "1.010", "6.54"), ("0.06", "1.000", "6.11"),
    ("0.07", "0.895", "5.75"), ("0.08", "0.975", "5.43"), ("0.09", "0.970", "5.16"),
    ("0.10", "0.965", "4.96"), ("0.11", "0.960", "4.74"), ("0.12", "0.952", "4.53"),
    ("0.13", "0.945", "4.35"), ("0.14", "0.939", "4.18"), ("0.15", "0.932", "4.02"),
    ("0.16", "0.952", "3.87"), ("0.17", "0.919", "3.73"), ("0.18", "0.912", "3.59"),
    ("0.19", "0.905", "3.47"), ("0.20", "0.899", "3.35"),
]
# Table 3, p. 39
TABLE3 = [
    ("0.20", "0.899", "3.35"), ("0.25", "0.873", "2.84"), ("0.30", "0.847", "2.43"),
    ("0.35", "0.824", "2.09"), ("0.40", "0.807", "1.80"),
]
# Table 5, p. 46
TABLE5 = [
    ("0.010", "1.00", "5.68"), ("0.015", "0.98", "5.18"), ("0.020", "0.97", "4.83"),
    ("0.03", "0.96", "4.33"), ("0.04", "0.94", "3.96"), ("0.05", "0.93", "3.67"),
    ("0.06", "0.92", "3.44"), ("0.08", "0.90", "3.08"), ("0.10", "0.89", "2.83"),
    ("0.12", "0.88", "2.612"), ("0.14", "0.86", "2.421"), ("0.16", "0.85", "2.257"),
    ("0.18", "0.84", "2.111"), ("0.20", "0.83", "1.985"),
]
# Table 6, p. 46
TABLE6 = [
    ("0.2", "1.04", "2.73"), ("0.3", "1.00", "2.13"), ("0.4", "0.95", "1.72"),
    ("0.5", "0.91", "1.41"), ("0.6", "0.88", "1.17"), ("0.7", "0.84", "0.98"),
    ("0.8", "0.81", "0.82"), ("0.809", "0.809", "0.809"),
]

# The paper's quoted numbers (paper/sections/07-location.tex, "Printed tables";
# paper/sections/12-exteriors.tex, paragraph before "Fixed data").
PAPER_CLAIM_A = {"table4": {"1.05": "1.43904"}, "table7": {"0.20": "2.01015", "0.55": "1.00036"}}
PAPER_CLAIM_B_SLACKS = {"1.05": 3.8e-6, "1.15": 3.8e-6, "1.294": 2.3e-6}
PAPER_CLAIM_C = {"table2_row_0.10": "4.96355", "table5_row_0.10": "2.84577"}


def M(s) -> mp.mpf:
    return mp.mpf(s)


def sig(x, n=20) -> str:
    return mp.nstr(x, n, strip_zeros=False)


def fl(x) -> float:
    return float(x)


def truncates_to(root, printed: str) -> bool:
    """Is the printed value the root truncated (rounded down) to the printed decimals?"""
    d = len(printed.split(".")[1]) if "." in printed else 0
    return bool(int(mp.floor(root * 10 ** d)) == int(printed.replace(".", "")))


# ---------------------------------------------------------------------------------------
# Root finding: bracket + Anderson-Bjorck, then confirm the sign change.
# ---------------------------------------------------------------------------------------
def increasing_root(func, lo, hi, what=""):
    """Root of an increasing function; expands [lo, hi] until func(lo) < 0 < func(hi)."""
    lo, hi = M(lo), M(hi)
    flo, fhi = func(lo), func(hi)
    n = 0
    while flo > 0:
        lo = lo - (hi - lo)
        flo = func(lo)
        n += 1
        if n > 60:
            raise RuntimeError(f"no lower bracket for {what}")
    n = 0
    while fhi < 0:
        hi = hi + (hi - lo)
        fhi = func(hi)
        n += 1
        if n > 60:
            raise RuntimeError(f"no upper bracket for {what}")
    r = mp.findroot(func, (lo, hi), solver="anderson")
    h = mp.mpf(10) ** (-(mp.mp.dps - 10))
    if not (func(r - h) < 0 < func(r + h)):
        # fall back to bisection if the secant-type solver stopped early
        a, b = lo, hi
        for _ in range(4 * mp.mp.prec):
            m = (a + b) / 2
            if func(m) < 0:
                a = m
            else:
                b = m
            if b - a < h:
                break
        r = (a + b) / 2
        if not (func(r - 2 * h) < 0 < func(r + 2 * h)):
            raise RuntimeError(f"root not bracketed for {what}")
    return r


# ---------------------------------------------------------------------------------------
# Lemma 7.1 test function and Lemma 7.5.
# ---------------------------------------------------------------------------------------
class Lemma71:
    """f = g*g, g(t) = lam (1 + tan^2 theta)(cos zeta t - cos theta) on |t| <= gamma."""

    def __init__(self, lam, theta):
        self.lam = M(lam)
        self.theta = M(theta)
        th = self.theta
        self.zeta = self.lam * mp.tan(th)
        self.gamma = th / self.zeta
        self.c = self.lam * (1 + mp.tan(th) ** 2)
        self._F = {}

    def g(self, t):
        t = abs(M(t))
        if t >= self.gamma:
            return mp.mpf(0)
        return self.c * (mp.cos(self.zeta * t) - mp.cos(self.theta))

    def f(self, x):
        """Closed form printed in Lemma 7.1 (0 <= x <= 2 gamma), f = 0 beyond, even."""
        x = abs(M(x))
        if x >= 2 * self.gamma:
            return mp.mpf(0)
        th, z, c, lam, gam = self.theta, self.zeta, self.c, self.lam, self.gamma
        return c * (c * (gam - x / 2) * mp.cos(z * x) + lam * (2 * gam - x)
                    + mp.sin(2 * th - z * x) / mp.sin(2 * th)
                    - 2 * (1 + mp.sin(th - z * x) / mp.sin(th)))

    def f_conv(self, x):
        """Direct convolution (g*g)(x) for 0 <= x <= 2 gamma, as a check of the closed form."""
        x = M(x)
        return mp.quad(lambda t: self.g(t) * self.g(x - t), [x - self.gamma, self.gamma])

    def F(self, z):
        """Laplace transform F(z) = int_0^{2 gamma} e^{-zx} f(x) dx (z real)."""
        z = M(z)
        key = mp.nstr(z, mp.mp.dps)
        if key not in self._F:
            self._F[key] = mp.quad(lambda x: self.f(x) * mp.exp(-z * x),
                                   [0, self.gamma, 2 * self.gamma])
        return self._F[key]

    # Printed closed forms of Lemma 7.1.
    def f0_printed(self):
        th = self.theta
        return self.lam * (1 + mp.tan(th) ** 2) * (th * mp.tan(th) + 3 * th * mp.cot(th) - 3)

    def F0_printed(self):
        th = self.theta
        return 2 * (1 + mp.tan(th) ** 2) * (1 - th * mp.cot(th)) ** 2

    def Fmlam_printed(self):
        th = self.theta
        return 2 * mp.tan(th) ** 2 + 3 - 3 * th * mp.tan(th) - 3 * th * mp.cot(th)


def lemma75_theta(k):
    """theta in (0, pi/2) with sin^2 theta = k (1 - theta cot theta), 0 < k < 3 (Lemma 7.5)."""
    k = M(k)
    h = lambda th: mp.sin(th) ** 2 - k * (1 - th * mp.cot(th))
    # h > 0 near 0 (h ~ (1 - k/3) theta^2) and h -> 1 - k < 0 at pi/2 for 1 < k < 3.
    return increasing_root(lambda th: -h(th), M("0.05"), mp.pi / 2 - M("1e-12"), f"theta(k={k})")


def self_checks(fn: Lemma71, k=None):
    """Closed form vs convolution; printed f(0), F(0), F(-lambda); Lemma 7.5 identity."""
    out = {}
    xs = [fn.gamma * M(j) / 4 for j in range(0, 8)]
    out["max_abs_closed_form_minus_convolution"] = fl(max(abs(fn.f(x) - fn.f_conv(x)) for x in xs))
    out["f0_quadrature_minus_printed"] = fl(fn.f(0) - fn.f0_printed())
    out["F0_quadrature_minus_printed"] = fl(fn.F(0) - fn.F0_printed())
    out["Fmlam_quadrature_minus_printed"] = fl(fn.F(-fn.lam) - fn.Fmlam_printed())
    if k is not None:
        lhs = fn.F(-fn.lam) - M(k) * fn.F(0)
        rhs = -fn.f(0) * mp.cos(fn.theta) ** 2 / fn.lam
        out["lemma75_identity_residual"] = fl(lhs - rhs)
    return out


# ---------------------------------------------------------------------------------------
# Table 4: Lemma 8.3, (8.6)-(8.8).
# ---------------------------------------------------------------------------------------
def P3(X):
    return X + X ** 2 + M(2) / 3 * X ** 3


def G87(l1, lp, a, K):
    """Left side of (8.7) with epsilon = 0."""
    return ((K ** 2 + M(1) / 2) * (P3((a + l1) / a) - P3(M(1))) - 2 * K * P3((a + l1) / (a + lp))
            + (K + 1) ** 2 * (a + l1) / 8)


def table4_root(B, a, K):
    T = ((K ** 2 + M(1) / 2) * (P3((a + B) / a) - P3(M(1))) + (K + 1) ** 2 * (a + B) / 8) / (2 * K)
    if T <= 0:
        return None
    X = increasing_root(lambda X: P3(X) - T, M(0), T, "P3(X)=T")  # P3(X) >= X, so X <= T
    return (a + B) / X - a


def E86(l1, lp, a):
    """(8.6): (a+l')^-3 + (a+l1)^-3 - a^-3 (must be >= 0)."""
    return (a + lp) ** -3 + (a + l1) ** -3 - a ** -3


def lp_max86(l1, a):
    """Largest l' for which (8.6) holds at this l1 (None if (8.6) fails for every l')."""
    d = a ** -3 - (a + l1) ** -3
    return d ** (-M(1) / 3) - a if d > 0 else None


def D88(l1, a, K):
    """(8.8): left side minus right side (must be >= 0); increasing in l1."""
    u = (a + l1) / a
    return (K ** 2 + M(1) / 2) / a * (1 + 2 * u + 2 * u ** 2) + (K + 1) ** 2 / 8 - 10 * K / (a + l1)


def d88_threshold(a, K):
    """l1* with D88(l1*) = 0; (8.8) holds exactly for l1 >= l1*."""
    return increasing_root(lambda x: D88(x, a, K), -a + M("1e-6"), M(10), "(8.8) threshold")


def run_table4():
    rows = []
    for i, (B, lp, a, K) in enumerate(TABLE4):
        B_, lp_, a_, K_ = M(B), M(lp), M(a), M(K)
        r = table4_root(B_, a_, K_)
        row = {
            "lambda1": B, "printed": lp, "a": a, "K": K,
            "root": fl(r), "root_str": sig(r), "root_minus_printed": fl(r - lp_),
            "G87_at_root": fl(G87(B_, r, a_, K_)),
            "root_below_printed": bool(r < lp_),
            "printed_is_root_truncated": truncates_to(r, lp),
            "K_ge_quarter": bool(K_ >= M(1) / 4),
            "diag_root_gt_lambda1": bool(r > B_),
        }
        thr = d88_threshold(a_, K_)
        row["d88_threshold_lambda1"] = fl(thr)
        lpm = lp_max86(B_, a_)
        row["lambda_prime_max_for_86_at_B"] = fl(lpm) if lpm is not None else None
        # Minimal requirement: (8.6) at (B, printed lambda'_B).
        row["s86_at_B_printedB"] = fl(E86(B_, lp_, a_))
        row["s86_at_B_root"] = fl(E86(B_, r, a_))
        if i > 0:
            A, lpA = TABLE4[i - 1][0], TABLE4[i - 1][1]
            A_, lpA_ = M(A), M(lpA)
            row["A"] = A
            row["lambda_prime_at_A"] = lpA
            row["s88_at_A"] = fl(D88(A_, a_, K_))
            row["s88_at_A_relative"] = fl(D88(A_, a_, K_) / (10 * K_ / (a_ + A_)))  # LHS/RHS - 1
            row["s86_HB"] = fl(E86(B_, lpA_, a_))                       # HB's prescription
            row["s86_HB_relative"] = fl(E86(B_, lpA_, a_) * a_ ** 3)     # LHS/RHS - 1
            row["s86_HB_margin_in_lambda_prime"] = fl(lpm - lpA_) if lpm is not None else None
            row["side_conditions_HB_hold"] = bool(row["s88_at_A"] >= 0 and row["s86_HB"] >= 0)
        else:
            # First row: no previous row of Table 4.
            row["A"] = None
            row["first_row_checks"] = {
                "s86_at_(0.3,2.293)": fl(E86(B_, M("2.293"), a_)),
                "s86_at_(0.3,2.43)_Table3_row_0.30": fl(E86(B_, M("2.43"), a_)),
                "s86_at_(0.3,2.84)_Table3_row_0.25": fl(E86(B_, M("2.84"), a_)),
                "s88_at_0.25": fl(D88(M("0.25"), a_, K_)),
                "s88_at_0": fl(D88(M(0), a_, K_)),
                "note": "(8.8) holds only for lambda1 >= d88_threshold_lambda1; row 0.3 has no "
                        "previous Table 4 row, so HB's interval argument has no left end.",
            }
            row["side_conditions_HB_hold"] = None
        rows.append(row)
    return rows


# ---------------------------------------------------------------------------------------
# Table 7 (Lemma 8.7) and the f-based tables (Lemmas 6.3, 8.5).
# ---------------------------------------------------------------------------------------
def table7_root(B, lam, k=None):
    B_ = M(B)
    k_ = M("0.98") - M("0.15") * B_ if k is None else M(k)
    fn = Lemma71(lam, 1)
    psi = (k_ ** 2 + M(1) / 2) / 8 + (4 * k_ + 1) / 6
    F0, f0 = fn.F(0), fn.f(0)
    H = lambda l2: (k_ ** 2 + M(1) / 2) * (fn.F(-l2) - fn.F(B_ - l2)) - 2 * k_ * F0 + f0 * psi
    r = increasing_root(H, B_, B_ + 3, f"Table 7 row {B}")
    return r, k_, psi, fn, H


def run_table7(sensitivity=True):
    rows = []
    for B, lam, pr in TABLE7:
        r, k_, psi, fn, H = table7_root(B, lam)
        row = {
            "lambda1": B, "lambda": lam, "printed": pr, "k": fl(k_), "theta": 1, "psi": fl(psi),
            "root": fl(r), "root_str": sig(r), "root_minus_printed": fl(r - M(pr)),
            "lhs_at_printed": fl(H(M(pr))),
            "root_below_printed": bool(r < M(pr)),
            "printed_is_root_truncated": truncates_to(r, pr),
        }
        if sensitivity:
            row["root_k_minus_0.01"] = fl(table7_root(B, lam, k_ - M("0.01"))[0])
            row["root_k_plus_0.01"] = fl(table7_root(B, lam, k_ + M("0.01"))[0])
        rows.append(row)
    return rows


def f_table_root(kind, b, lam, theta):
    """Root in l of: Lemma 6.3 (Tables 2, 3), Lemma 8.5 (Table 5) or Lemma 8.5 with psi = 3/8 (Table 6)."""
    fn = Lemma71(lam, theta)
    b_ = M(b)
    F0, f0 = fn.F(0), fn.f(0)
    if kind == "lemma6.3":
        H = lambda l: 2 * fn.F(-l) - 2 * fn.F(b_ - l) - F0 + f0 / 4
    elif kind == "lemma8.5":
        H = lambda l: fn.F(-l) - fn.F(b_ - l) - F0 + M(11) / 24 * f0
    elif kind == "table6":
        H = lambda l: fn.F(-l) - fn.F(b_ - l) - F0 + M(3) / 8 * f0
    else:
        raise ValueError(kind)
    r = increasing_root(H, b_, b_ + 4, f"{kind} b={b}")
    return r, fn, H


def run_f_table(kind, table, theta):
    rows = []
    for b, lam, pr in table:
        r, fn, H = f_table_root(kind, b, lam, theta)
        rows.append({
            "lambda1": b, "lambda": lam, "printed": pr, "root": fl(r), "root_str": sig(r),
            "root_minus_printed": fl(r - M(pr)), "lhs_at_printed": fl(H(M(pr))),
            "root_below_printed": bool(r < M(pr)),
            "printed_is_root_truncated": truncates_to(r, pr),
        })
    return rows


# ---------------------------------------------------------------------------------------
# Transcription check against pdftotext.
# ---------------------------------------------------------------------------------------
def transcription_check():
    if not PDF.exists() or shutil.which("pdftotext") is None:
        return {"status": "skipped (pdftotext or PDF unavailable)"}

    def page_rows(page):
        txt = subprocess.run(["pdftotext", "-layout", "-f", str(page), "-l", str(page), str(PDF), "-"],
                             capture_output=True, text=True, check=True).stdout
        rows = []
        for line in txt.splitlines():
            toks = line.split()
            if toks and all(re.fullmatch(r"\d+\.\d+|\d+", t) for t in toks):
                rows.append(toks)
        return rows

    def check(table, page, ncols):
        rows = page_rows(page)
        missing = []
        for tr in table:
            if not any(r[:ncols] == list(tr[:ncols]) for r in rows):
                missing.append(tr)
        return missing

    res = {
        "Table 4 (p. 44)": check(TABLE4, 44, 4),
        "Table 7 (p. 48)": check(TABLE7, 48, 3),
        "Table 2 (p. 39)": check(TABLE2, 39, 3),
        "Table 3 (p. 39)": check(TABLE3, 39, 3),
        "Table 5 (p. 46)": check(TABLE5, 46, 3),
        "Table 6 (p. 46)": check(TABLE6, 46, 3),
    }
    res = {k: ("all rows found" if not v else {"not found": v}) for k, v in res.items()}
    res["status"] = "ok" if all(v == "all rows found" for v in res.values()) else "MISMATCH"
    return res


# ---------------------------------------------------------------------------------------
# Cross-check of the values the repository uses.
# ---------------------------------------------------------------------------------------
def parse_paper_parents():
    tex = (REPO / "paper" / "sections" / "07-location.tex").read_text()
    start = tex.index(r"\begin{tabular}", tex.index(r"\begin{proof}", tex.index("prop:parentrows")))
    end = tex.index(r"\label{tab:parents}")
    pat = re.compile(r"\$\\mathrm\{(rr|rc|complex)\}\$\s*&\s*\$\[([0-9.]+),\s*([0-9.]+)\]\$\s*&\s*"
                     r"\$([0-9.]+)\$\s*&\s*\$([0-9.]+)\$")
    return [m.groups() for m in pat.finditer(tex[start:end])]


def justify_rr(A, B, p, r, t4, t7, t3):
    """Source row for p (lambda') and r (lambda_2) on [A, B], type rr.

    Sources, as in the proof of the paper's Proposition "Parent rows": the trivial bounds
    lambda', lambda_2 >= lambda1 >= A; Table 4 rows t >= B (the one with the smallest such t
    has the largest printed value); Table 7 rows t >= B with t >= 0.12; and the bounds valid
    for every lambda1, Lemma 8.4 (lambda' >= 1.294: Table 4 row 1.294 for lambda1 <= 1.294,
    trivial beyond) and Lemma 8.8 (lambda_2 >= 0.745: Table 7 row 0.745, trivial beyond).
    """
    A, B, p, r = map(Fraction, (A, B, p, r))
    out = {"interval": [str(A), str(B)], "p": str(p), "r": str(r)}
    last4 = [row for row in t4 if row["lambda1"] == "1.294"][0]
    last7 = [row for row in t7 if row["lambda1"] == "0.745"][0]
    # lambda' sources.
    if p <= A:
        out["p_source"] = "trivial (lambda' >= lambda1 >= A)"
        out["p_ok"] = True
    else:
        cands = [row for row in t4 if Fraction(row["lambda1"]) >= B]
        best = max(cands, key=lambda row: Fraction(row["printed"])) if cands else None
        if best is None and p <= Fraction("1.294"):
            out["p_source"] = "HB Lemma 8.4, lambda' >= 1.294 (Table 4 row 1.294, trivial beyond)"
            out["p_source_root"] = last4["root"]
            out["p_ok"] = bool(last4["root"] >= 1.294)
            out["p_root_margin"] = last4["root"] - float(p)
        elif best is None:
            out["p_source"], out["p_ok"] = "none", False
        else:
            out["p_source"] = f"HB Table 4 row {best['lambda1']} (printed {best['printed']})"
            out["p_source_root"] = best["root"]
            out["p_le_printed"] = p <= Fraction(best["printed"])
            out["p_ok"] = bool(p <= Fraction(best["printed"]) and float(p) <= best["root"])
            out["p_root_margin"] = best["root"] - float(p)
            if best["lambda1"] == "0.3":
                t3row = [row for row in t3 if row["lambda1"] == "0.30"][0]
                out["p_row_0.3_fallback"] = (f"Table 3 row 0.30: printed {t3row['printed']}, "
                                             f"root {t3row['root']:.6f}")
    # lambda_2 sources: trivial; Table 7 rows t >= B with t >= 0.12 (row .10 not used).
    if r <= A:
        out["r_source"] = "trivial (lambda_2 >= lambda1 >= A)"
        out["r_ok"] = True
    else:
        cands = [row for row in t7 if Fraction(row["lambda1"]) >= B and Fraction(row["lambda1"]) >= Fraction("0.12")]
        best = max(cands, key=lambda row: Fraction(row["printed"])) if cands else None
        if best is None and r <= Fraction("0.745"):
            out["r_source"] = "HB Lemma 8.8, lambda_2 >= 0.745 (Table 7 row 0.745, trivial beyond)"
            out["r_source_root"] = last7["root"]
            out["r_ok"] = bool(last7["root"] >= 0.745)
            out["r_root_margin"] = last7["root"] - float(r)
        elif best is None:
            out["r_source"], out["r_ok"] = "none", False
        else:
            out["r_source"] = f"HB Table 7 row {best['lambda1']} (printed {best['printed']})"
            out["r_source_root"] = best["root"]
            out["r_le_printed"] = r <= Fraction(best["printed"])
            out["r_ok"] = bool(r <= Fraction(best["printed"]) and float(r) <= best["root"])
            out["r_root_margin"] = best["root"] - float(r)
    return out


def cross_check(t4, t7, t3, t2, t5):
    res = {}
    sys.path.insert(0, str(REPO / "computations" / "core" / "code"))
    try:
        import cover_v5  # noqa: E402  (read-only use of the data lists)
        import case_cover  # noqa: E402
    finally:
        sys.path.pop(0)
    # H_PRIME / H_SECOND: transcription and root check.
    t4map = {Fraction(r["lambda1"]): r for r in t4}
    t7map = {Fraction(r["lambda1"]): r for r in t7}
    hp = []
    for t, v in cover_v5.H_PRIME:
        row = t4map.get(Fraction(t))
        hp.append({"t": t, "v": v, "HB_printed": row["printed"] if row else None,
                   "equals_printed": bool(row and Fraction(v) == Fraction(row["printed"])),
                   "root": row["root"] if row else None,
                   "v_le_root": bool(row and float(Fraction(v)) <= row["root"])})
    hs = []
    for t, v in cover_v5.H_SECOND:
        row = t7map.get(Fraction(t))
        hs.append({"t": t, "v": v, "HB_printed": row["printed"] if row else None,
                   "equals_printed": bool(row and Fraction(v) == Fraction(row["printed"])),
                   "root": row["root"] if row else None,
                   "v_le_root": bool(row and float(Fraction(v)) <= row["root"])})
    res["cover_v5.H_PRIME"] = {"rows": hp, "all_ok": all(x["equals_printed"] and x["v_le_root"] for x in hp),
                               "n": len(hp)}
    res["cover_v5.H_SECOND"] = {"rows": hs, "all_ok": all(x["equals_printed"] and x["v_le_root"] for x in hs),
                                "n": len(hs)}
    # case_cover.PARENTS (rr rows).
    cc = [justify_rr(a, b, p, r, t4, t7, t3) for kind, a, b, p, r in case_cover.PARENTS if kind == "rr"]
    res["case_cover.PARENTS_rr"] = {"rows": cc, "all_ok": all(x["p_ok"] and x["r_ok"] for x in cc)}
    # cover_v5.PARENTS (rr rows, refined).
    v5 = [justify_rr(a, b, p, r, t4, t7, t3) for kind, a, b, p, r in cover_v5.PARENTS if kind == "rr"]
    res["cover_v5.PARENTS_rr"] = {"rows": v5, "all_ok": all(x["p_ok"] and x["r_ok"] for x in v5),
                                  "n": len(v5)}
    # The paper's Table "Parent implications" (rr rows).
    paper = parse_paper_parents()
    prr = [justify_rr(a, b, p, r, t4, t7, t3) for kind, a, b, p, r in paper if kind == "rr"]
    same = sorted((Fraction(a), Fraction(b), Fraction(p), Fraction(r)) for kind, a, b, p, r in paper if kind == "rr") == \
        sorted((Fraction(a), Fraction(b), Fraction(p), Fraction(r)) for kind, a, b, p, r in cover_v5.PARENTS if kind == "rr")
    res["paper_tab_parents_rr"] = {"rows": prr, "all_ok": all(x["p_ok"] and x["r_ok"] for x in prr),
                                   "n": len(prr), "n_all_types": len(paper),
                                   "rr_rows_equal_cover_v5_PARENTS_rr": same}
    # Section 12: lambda' >= 4.96 - 0.001 and lambda_2 >= 2.83 - 0.001 for lambda1 <= 0.10.
    r2 = [x for x in t2 if x["lambda1"] == "0.10"][0]["root"]
    r5 = [x for x in t5 if x["lambda1"] == "0.10"][0]["root"]
    res["section12"] = {"m2_prime": "4.959", "root_table2_row_0.10": r2, "ok_m2_prime": 4.959 <= r2,
                        "m2": "2.829", "root_table5_row_0.10": r5, "ok_m2": 2.829 <= r5}
    return res


# ---------------------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--dps", type=int, default=30, help="working precision (decimal digits)")
    ap.add_argument("--check-dps", type=int, default=45, help="precision of the convergence re-run")
    ap.add_argument("--no-sensitivity", action="store_true", help="skip the k +- 0.01 runs for Table 7")
    args = ap.parse_args()
    mp.mp.dps = args.dps
    t0 = time.time()
    report = {"source": "Heath-Brown, Proc. LMS 64 (1992); pages of the repository copy",
              "precision_dps": args.dps}

    report["transcription_check"] = transcription_check()

    # Lemma 7.5 thetas and self-checks of the Lemma 7.1 function.
    th32, th2 = lemma75_theta(M(3) / 2), lemma75_theta(2)
    report["lemma7.5_theta"] = {"k=3/2": sig(th32, 15), "k=2": sig(th2, 15)}
    report["lemma8.2"] = {"8cos^2(theta_k=2)": sig(8 * mp.cos(th2) ** 2, 10), "printed": "2.427..."}
    report["self_checks"] = {
        "Table7 row 0.20 (lambda=0.75, theta=1)": self_checks(Lemma71("0.75", 1)),
        "Table2 row 0.10 (lambda=0.965, k=3/2)": self_checks(Lemma71("0.965", th32), M(3) / 2),
        "Table5 row 0.10 (lambda=0.89, k=2)": self_checks(Lemma71("0.89", th2), 2),
    }

    t4 = run_table4()
    t7 = run_table7(sensitivity=not args.no_sensitivity)
    t2 = run_f_table("lemma6.3", TABLE2, th32)
    t3 = run_f_table("lemma6.3", TABLE3, th32)
    t5 = run_f_table("lemma8.5", TABLE5, th2)
    t6 = run_f_table("table6", TABLE6, th2)
    report["table4"] = t4
    report["table7"] = t7
    report["table2_row_0.10"] = [x for x in t2 if x["lambda1"] == "0.10"][0]
    report["table5_row_0.10"] = [x for x in t5 if x["lambda1"] == "0.10"][0]
    report["supplementary"] = {"table2_all_rows": t2, "table3_all_rows": t3, "table5_all_rows": t5,
                               "table6_all_rows_k2_assumed": t6}
    # Table 2 rows whose printed lambda looks like a digit transposition (0.895 in a column
    # running 1.000, ?, 0.975; 0.952 in a column running 0.932, ?, 0.919).
    report["supplementary"]["table2_lambda_transposition_probe"] = [
        {"lambda1": b, "printed_lambda": lp, "transposed_lambda": lt, "printed": pr,
         "root_with_printed_lambda": fl(f_table_root("lemma6.3", b, lp, th32)[0]),
         "root_with_transposed_lambda": fl(f_table_root("lemma6.3", b, lt, th32)[0])}
        for b, lp, lt, pr in [("0.07", "0.895", "0.985", "5.75"), ("0.16", "0.952", "0.925", "3.87")]]

    # Convergence re-run of the key roots at higher precision.
    with mp.workdps(args.check_dps):
        th32h, th2h = lemma75_theta(M(3) / 2), lemma75_theta(2)
        hi = {
            "table4_row_1.05": table4_root(M("1.05"), M("4.8"), M("0.83")),
            "table7_row_0.20": table7_root("0.20", "0.75")[0],
            "table7_row_0.55": table7_root("0.55", "0.64")[0],
            "table2_row_0.10": f_table_root("lemma6.3", "0.10", "0.965", th32h)[0],
            "table5_row_0.10": f_table_root("lemma8.5", "0.10", "0.89", th2h)[0],
            "table3_row_0.30": f_table_root("lemma6.3", "0.30", "0.847", th32h)[0],
        }
        lo = {
            "table4_row_1.05": [x for x in t4 if x["lambda1"] == "1.05"][0]["root_str"],
            "table7_row_0.20": [x for x in t7 if x["lambda1"] == "0.20"][0]["root_str"],
            "table7_row_0.55": [x for x in t7 if x["lambda1"] == "0.55"][0]["root_str"],
            "table2_row_0.10": report["table2_row_0.10"]["root_str"],
            "table5_row_0.10": report["table5_row_0.10"]["root_str"],
            "table3_row_0.30": [x for x in t3 if x["lambda1"] == "0.30"][0]["root_str"],
        }
        report["precision_check"] = {k: {"dps_hi": sig(v, 20), f"dps_{args.dps}": lo[k],
                                         "abs_diff": fl(abs(v - M(lo[k])))} for k, v in hi.items()}

    # Summaries.
    def closest(rows, n=3):
        return [(r["lambda1"], r["printed"], r["root"], r["root_minus_printed"])
                for r in sorted(rows, key=lambda r: r["root_minus_printed"])[:n]]

    t7_used = [r for r in t7 if Fraction(r["lambda1"]) >= Fraction("0.12")]
    sc_rows = [r for r in t4 if r["A"] is not None]
    s86_sorted = sorted(sc_rows, key=lambda r: r["s86_HB"])
    s88_sorted = sorted(sc_rows, key=lambda r: r["s88_at_A"])
    both = sorted([("T4", r["lambda1"], r["printed"], r["root"], r["root_minus_printed"],
                    r["root_minus_printed"] / float(r["printed"])) for r in t4] +
                  [("T7", r["lambda1"], r["printed"], r["root"], r["root_minus_printed"],
                    r["root_minus_printed"] / float(r["printed"])) for r in t7], key=lambda x: x[4])
    report["summary"] = {
        "table4_all_roots_ge_printed": all(not r["root_below_printed"] for r in t4),
        "table4_closest": closest(t4),
        "table4_root_minus_printed_range": [min(r["root_minus_printed"] for r in t4),
                                            max(r["root_minus_printed"] for r in t4)],
        "table7_all_roots_ge_printed": all(not r["root_below_printed"] for r in t7),
        "table7_closest": closest(t7),
        "table7_root_minus_printed_range": [min(r["root_minus_printed"] for r in t7),
                                            max(r["root_minus_printed"] for r in t7)],
        "table7_used_rows_all_ge_printed": all(not r["root_below_printed"] for r in t7_used),
        # Convention inferred (HB states none for Tables 4 and 7): printed = root rounded down.
        "table4_printed_is_root_truncated_all_rows": all(r["printed_is_root_truncated"] for r in t4),
        "table7_printed_is_root_truncated_all_rows": all(r["printed_is_root_truncated"] for r in t7),
        "tables_2356_rows_where_printed_is_root_truncated": {
            name: [r["lambda1"] for r in rows if r["printed_is_root_truncated"]]
            for name, rows in [("T2", t2), ("T3", t3), ("T5", t5), ("T6", t6)]},
        "table4_side_conditions_rows_0.35_on_hold": all(r["side_conditions_HB_hold"] for r in sc_rows),
        "table4_side_conditions_minimal_(8.6)_at_(B,printed_B)_all_rows": all(r["s86_at_B_printedB"] >= 0 for r in t4),
        "table4_s86_tightest": [(r["lambda1"], r["s86_HB"], r["s86_HB_relative"]) for r in s86_sorted[:4]],
        "table4_s88_tightest": [(r["lambda1"], r["s88_at_A"], r["s88_at_A_relative"]) for r in s88_sorted[:3]],
        "tables4and7_combined_ranking_by_root_minus_printed": both[:8],
        "table3_row_0.30_root": [x for x in t3 if x["lambda1"] == "0.30"][0]["root"],
        "table2_row_0.10_root": report["table2_row_0.10"]["root"],
        "table5_row_0.10_root": report["table5_row_0.10"]["root"],
    }

    # The paper's claims, checked mechanically (rounded to the quoted number of digits).
    def rnd(x, s):
        d = len(s.split(".")[1])
        return f"{x:.{d}f}"

    t4m = {r["lambda1"]: r for r in t4}
    t7m = {r["lambda1"]: r for r in t7}
    ca = {"every_root_exceeds_printed_T4": report["summary"]["table4_all_roots_ge_printed"],
          "every_root_exceeds_printed_T7": report["summary"]["table7_all_roots_ge_printed"],
          "quoted": {}}
    for tab, d in PAPER_CLAIM_A.items():
        m_ = t4m if tab == "table4" else t7m
        for row, q in d.items():
            ca["quoted"][f"{tab} row {row}"] = {"paper": q, "recomputed": rnd(m_[row]["root"], q),
                                                 "match": rnd(m_[row]["root"], q) == q}
    ca["closest_T4"] = report["summary"]["table4_closest"][0][0]
    ca["closest_two_T7"] = [x[0] for x in report["summary"]["table7_closest"][:2]]
    cb = {"rows_0.35_on_hold": report["summary"]["table4_side_conditions_rows_0.35_on_hold"],
          "three_smallest_86_slacks": [(r["lambda1"], r["s86_HB"]) for r in s86_sorted[:3]],
          "quoted": {row: {"paper": v, "recomputed": t4m[row]["s86_HB"],
                           "match_2sf": f"{t4m[row]['s86_HB']:.1e}" == f"{v:.1e}"}
                     for row, v in PAPER_CLAIM_B_SLACKS.items()},
          # compare relative slacks (LHS/RHS - 1), since (8.6) and (8.8) have different scales
          "min_relative_slack_86": min(r["s86_HB_relative"] for r in sc_rows),
          "min_relative_slack_88": min(r["s88_at_A_relative"] for r in sc_rows),
          "tightest_is_86": min(r["s86_HB_relative"] for r in sc_rows) < min(r["s88_at_A_relative"] for r in sc_rows),
          "table3_row_0.30_root_ge_2.43": report["summary"]["table3_row_0.30_root"] >= 2.43}
    cc = {k: {"paper": v, "recomputed": rnd(report[k]["root"], v), "match": rnd(report[k]["root"], v) == v}
          for k, v in PAPER_CLAIM_C.items()}
    report["paper_claims"] = {"a": ca, "b": cb, "c": cc}

    report["cross_check"] = cross_check(t4, t7, t3, t2, t5)
    report["runtime_seconds"] = round(time.time() - t0, 1)
    OUT.write_text(json.dumps(report, indent=1, default=str) + "\n")
    print_summary(report)


def print_summary(rep):
    print(f"Heath-Brown 1992, §8 tables recomputed (mpmath, {rep['precision_dps']} digits); "
          f"runtime {rep['runtime_seconds']} s")
    print(f"transcription check: {rep['transcription_check']['status']}")
    print(f"Lemma 7.5 theta: k=3/2 -> {rep['lemma7.5_theta']['k=3/2'][:12]}, k=2 -> "
          f"{rep['lemma7.5_theta']['k=2'][:12]};  Lemma 8.2: 8cos^2 theta = {rep['lemma8.2']['8cos^2(theta_k=2)']}")
    mx = max(abs(v) for d in rep["self_checks"].values() for v in d.values())
    print(f"Lemma 7.1 self-checks (closed form vs convolution, printed f(0),F(0),F(-lam), Lemma 7.5): "
          f"max |residual| = {mx:.1e}")
    print("\nTable 4 (Lemma 8.3, (8.7)); side conditions per HB p. 43: (8.8) at l1=A, (8.6) at (B, l'_A)")
    print(f"{'B':>6} {'printed':>8} {'a':>5} {'K':>5} {'root':>10} {'root-pr':>10} "
          f"{'(8.8)@A':>9} {'(8.6)HB':>10} {'dl_86':>9} {'(8.6)@B':>9} {'l1*(8.8)':>9}")
    for r in rep["table4"]:
        s88 = f"{r['s88_at_A']:.4f}" if r["A"] else "-"
        s86 = f"{r['s86_HB']:.2e}" if r["A"] else "-"
        dl = f"{r['s86_HB_margin_in_lambda_prime']:.5f}" if r["A"] else "-"
        flag = "  <-- ROOT BELOW PRINTED" if r["root_below_printed"] else ""
        print(f"{r['lambda1']:>6} {r['printed']:>8} {r['a']:>5} {r['K']:>5} {r['root']:10.6f} "
              f"{r['root_minus_printed']:10.2e} {s88:>9} {s86:>10} {dl:>9} {r['s86_at_B_printedB']:9.2e} "
              f"{r['d88_threshold_lambda1']:9.4f}{flag}")
    fr = rep["table4"][0]["first_row_checks"]
    print("  row 0.3: (8.6) at (0.3,2.293) = {:.2e}, at (0.3,2.43) = {:.2e}, at (0.3,2.84) = {:.2e}; "
          "(8.8) at 0.25 = {:.4f}, at 0 = {:.4f}".format(
              fr["s86_at_(0.3,2.293)"], fr["s86_at_(0.3,2.43)_Table3_row_0.30"],
              fr["s86_at_(0.3,2.84)_Table3_row_0.25"], fr["s88_at_0.25"], fr["s88_at_0"]))
    print("\nTable 7 (Lemma 8.7, (8.11)), k = 0.98 - 0.15*B, theta = 1")
    print(f"{'B':>6} {'lambda':>6} {'printed':>8} {'k':>7} {'root':>10} {'root-pr':>10}  "
          f"{'root(k-.01)':>11} {'root(k+.01)':>11}")
    for r in rep["table7"]:
        flag = "  <-- ROOT BELOW PRINTED" if r["root_below_printed"] else ""
        s1 = f"{r['root_k_minus_0.01']:11.6f}" if "root_k_minus_0.01" in r else ""
        s2 = f"{r['root_k_plus_0.01']:11.6f}" if "root_k_plus_0.01" in r else ""
        print(f"{r['lambda1']:>6} {r['lambda']:>6} {r['printed']:>8} {r['k']:7.4f} {r['root']:10.6f} "
              f"{r['root_minus_printed']:10.2e}  {s1} {s2}{flag}")
    sm = rep["summary"]
    print(f"\nPrinted value = recomputed root rounded down to the printed decimals: Table 4 all rows "
          f"{sm['table4_printed_is_root_truncated_all_rows']}, Table 7 all rows "
          f"{sm['table7_printed_is_root_truncated_all_rows']}")
    print("\nTables 2 and 5, rows .10:")
    for key, lem in [("table2_row_0.10", "Lemma 6.3, k=3/2"), ("table5_row_0.10", "Lemma 8.5, k=2")]:
        r = rep[key]
        print(f"  {key}: lambda={r['lambda']} printed={r['printed']} root={r['root']:.8f} "
              f"(root-printed={r['root_minus_printed']:.2e}) [{lem}]")
    print("\nSupplementary (not asked for): root - printed")
    for name, rows in rep["supplementary"].items():
        if "root_with_transposed_lambda" in rows[0]:
            for r in rows:
                print(f"    Table 2 row {r['lambda1']}: lambda {r['printed_lambda']} -> root "
                      f"{r['root_with_printed_lambda']:.5f}; lambda {r['transposed_lambda']} -> root "
                      f"{r['root_with_transposed_lambda']:.5f} (printed {r['printed']})")
            continue
        bad = [r["lambda1"] for r in rows if r["root_below_printed"]]
        rng = (min(r["root_minus_printed"] for r in rows), max(r["root_minus_printed"] for r in rows))
        print(f"  {name}: range [{rng[0]:.2e}, {rng[1]:.2e}]; rows with root < printed: {bad or 'none'}")
    t3 = {r["lambda1"]: r for r in rep["supplementary"]["table3_all_rows"]}
    print(f"  Table 3 row 0.30: printed {t3['0.30']['printed']}, root {t3['0.30']['root']:.6f}")
    print("\nPrecision check (key roots, higher precision):")
    for k, v in rep["precision_check"].items():
        print(f"  {k}: {v['dps_hi'][:16]}  |diff| = {v['abs_diff']:.1e}")
    print("\nPaper claims:")
    ca, cb, cc = rep["paper_claims"]["a"], rep["paper_claims"]["b"], rep["paper_claims"]["c"]
    print(f"  (a) all roots exceed printed: T4 {ca['every_root_exceeds_printed_T4']}, "
          f"T7 {ca['every_root_exceeds_printed_T7']}; closest T4 row {ca['closest_T4']}, "
          f"closest two T7 rows {ca['closest_two_T7']}")
    for k, v in ca["quoted"].items():
        print(f"      {k}: paper {v['paper']}, recomputed {v['recomputed']}  match={v['match']}")
    print("      Tables 4 and 7 combined, smallest root - printed: "
          + ", ".join(f"{t} {b} (+{d:.2e})" for t, b, _, _, d, _ in
                      rep["summary"]["tables4and7_combined_ranking_by_root_minus_printed"][:6]))
    print(f"  (b) side conditions hold for rows 0.35 on: {cb['rows_0.35_on_hold']}; tightest is (8.6): "
          f"{cb['tightest_is_86']}; three smallest (8.6) slacks: "
          + ", ".join(f"{a} {b:.2e}" for a, b in cb["three_smallest_86_slacks"]))
    for k, v in cb["quoted"].items():
        print(f"      row {k}: paper {v['paper']:.1e}, recomputed {v['recomputed']:.3e}  match={v['match_2sf']}")
    print(f"      smallest relative slacks (LHS/RHS - 1): (8.6) {cb['min_relative_slack_86']:.2e}, "
          f"(8.8) {cb['min_relative_slack_88']:.3f}")
    print(f"      Table 3 row 0.30 root >= 2.43: {cb['table3_row_0.30_root_ge_2.43']}")
    for k, v in cc.items():
        print(f"  (c) {k}: paper {v['paper']}, recomputed {v['recomputed']}  match={v['match']}")
    print("\nCross-check of repository values (used value <= recomputed root of its source row):")
    for k, v in rep["cross_check"].items():
        if isinstance(v, dict) and "all_ok" in v:
            extra = ""
            if k == "paper_tab_parents_rr":
                extra = f" (rr rows = cover_v5 rr rows: {v['rr_rows_equal_cover_v5_PARENTS_rr']})"
            print(f"  {k}: all ok = {v['all_ok']}{extra}")
    s12 = rep["cross_check"]["section12"]
    print(f"  section 12: 4.959 <= {s12['root_table2_row_0.10']:.6f}: {s12['ok_m2_prime']}; "
          f"2.829 <= {s12['root_table5_row_0.10']:.6f}: {s12['ok_m2']}")
    print(f"\nwrote {OUT.relative_to(REPO)}")


if __name__ == "__main__":
    main()
