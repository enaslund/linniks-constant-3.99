#!/usr/bin/env python3
"""Check every printed zero-location number used by the proof against the printed pages.

Sources (local copies; in both the printed page number equals the PDF page number, which the
script checks on every page it reads):
  H  D. R. Heath-Brown, Zero-free regions for Dirichlet L-functions, and the least prime in an
     arithmetic progression (1992), literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf
     (its own 99-page pagination).
  X  T. Xylouris, Ueber die Nullstellen der Dirichletschen L-Funktionen und die kleinste Primzahl in
     einer arithmetischen Progression, Dissertation, Bonn 2011,
     literature/xylouris-2011-dissertation.pdf.

What is checked.
 1. Tables. Each page is extracted with `pdftotext -layout`. Each table is parsed from the lines
    between its column header and its caption by a table-specific rule (side-by-side tables are
    split at the column of the second header). The parsed rows must equal the transcription stored
    in this file, and each transcribed row must also occur as a token sequence in the page text.
    Captions, and the sentences that fix the meaning and scope of each table, are matched as
    strings in the whitespace-normalized page text.
 2. Statements. The printed lemmas and inequalities used (H Lemmas 8.2, 8.4, 8.8, 9.4, 10.3, 11.1,
    13.2, 13.3; X (4.28), (4.29), (4.31), (4.34), (5.18)) are matched as strings. The fraction 6/7
    of H Lemma 10.3, which the text layer writes '67', is checked to be stacked from the word boxes
    of `pdftotext -bbox`. Three misprints in the sources, not used by the proof, are recorded.
 3. Uses. The numbers used are collected from
      computations/core/code/case_cover.py, cover_v4.py, cover_v5.py (imported; they use only
        fractions): the parent rows and the tables H_PRIME, H_SECOND, COMPLEX_PRIME,
        REAL_COMPLEX_PRIME;
      computations/core/results/source_cover.json.gz: lp and source_l2 of all 818 records;
      computations/core/results/polynomial_table.json: the parent bound of the 69 lambda' rows;
      computations/core/code/triple_inputs.py, small_exception_tables.py, poly_rows.py,
        alias_check.py, x434_check.py, computations/sieve_near/third_refine.py (read as source,
        not imported; the literal rows and the guards of third_bound are read with ast);
      paper/sections/07-location.tex (Table tab:parents and the statements of inp:rrtables,
        inp:complextables, inp:lambda3, prop:firstlower) and 12-exteriors.tex.
    Each use is compared with the printed value: 'equal'; 'safe' (the used bound is weaker than
    the printed one, for example an explicit -eps, or a used interval inside the printed one);
    'trivial' (not a printed number: lambda', lambda_2 >= lambda_1 >= A); or 'mismatch'.
 4. Scope, as far as it is mechanical: the type of chi_1, rho_1 (rr, rc, complex), the order of
    chi_1 where a table needs it, and the lambda_1 range. A row 'lambda_1 <= t => lambda >= c' is
    used on [A,B] only if B <= t, or if c <= t (then lambda >= lambda_1 > t >= c beyond t); an
    interval row only on subintervals. Every parent row and every source-cover record must lie
    below an in-scope printed bound or the trivial bound.
 5. Cross-checks between tables that remove printed hypotheses (H Table 7 against H Tables 2-4
    and 6; H Table 5 against H Table 2) or that tie two transcriptions together (X Table 7
    against X Tables 4, 5 and H Table 10; X Table 8's column 'alle Faelle'; X Table 11 against
    X Lemma 4.5).

Not checked: the analytic content of the printed results, the recomputation of printed roots
(H Tables 2, 4, 5, 7) and the side conditions (8.6), (8.8), and H 1990 (Corollary 1), whose
displayed formulas are missing from the OCR text layer of the local copy.

Run:   .venv/bin/python computations/audit/printed_tables_check.py [--out PATH]
Needs pdftotext (poppler) and the Python standard library. Writes
computations/audit/printed_tables_check.json, prints a summary, and exits 1 on any failure.
"""
import argparse
import ast
import gzip
import hashlib
import json
import platform
import re
import subprocess
import sys
import unicodedata
from fractions import Fraction as Q
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CODE = ROOT/'computations/core/code'
RESULTS = ROOT/'computations/core/results'
SIEVE = ROOT/'computations/sieve_near'
SECTIONS = ROOT/'paper/sections'
PDF = {'H': ROOT/'literature/heath-brown-1992-zero-free-regions-and-least-prime.pdf',
       'X': ROOT/'literature/xylouris-2011-dissertation.pdf'}
OUT = Path(__file__).with_suffix('.json')
TYPES = ('rr', 'rc', 'complex')
FAILURES = []


def fail(msg):
    FAILURES.append(msg)


def rel(path):
    path = Path(path)
    return str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)


def fmt(x):
    """A Fraction as a short decimal string when it is one, else p/q."""
    if x is None:
        return None
    x = Q(x)
    for k in range(13):
        y = x*10**k
        if y.denominator == 1:
            sign, digits = ('-' if y < 0 else ''), str(abs(y.numerator))
            if k == 0:
                return sign + digits
            digits = digits.rjust(k+1, '0')
            return f'{sign}{digits[:-k]}.{digits[-k:]}'
    return f'{x.numerator}/{x.denominator}'


# ---------------------------------------------------------------------------------------------
# Page text
# ---------------------------------------------------------------------------------------------

@lru_cache(None)
def page(src, p):
    raw = subprocess.run(['pdftotext', '-layout', '-f', str(p), '-l', str(p), str(PDF[src]), '-'],
                         check=True, capture_output=True).stdout.decode('utf-8')
    txt = unicodedata.normalize('NFC', raw)
    nonblank = [line for line in txt.splitlines() if line.strip()]
    if not nonblank or nonblank[-1].strip() != str(p):
        raise SystemExit(f'{src} p. {p}: the last line of the page is not its number')
    return txt


def flat(s):
    return re.sub(r'\s+', ' ', unicodedata.normalize('NFC', s)).strip()


def on_page(src, p, snippet):
    return flat(snippet) in flat(page(src, p))


def snippet_record(src, p, snippet, note=None):
    ok = on_page(src, p, snippet)
    if not ok:
        fail(f'{src} p. {p}: text not found: {snippet!r}')
    out = {'source': src, 'page': p, 'text': snippet, 'found': ok}
    if note:
        out['note'] = note
    return out


# ---------------------------------------------------------------------------------------------
# Transcriptions. One row per line; '_' marks an empty cell, '-' a printed dash.
# The text extraction writes the prime of lambda' as 0 (lambda0 = lambda'), see the captions.
# ---------------------------------------------------------------------------------------------

def rows(s):
    return [tuple('' if t == '_' else t for t in line.split()) for line in s.strip().splitlines()]


H2 = rows("""
0.006 1.10 11.34 10.23
0.008 1.09 10.71 9.65
0.010 1.08 10.21 9.21
0.015 1.07 9.31 8.39
0.020 1.06 8.66 7.82
0.025 1.05 8.15 7.37
0.030 1.04 7.73 7.01
0.035 1.03 7.37 6.70
0.040 1.025 7.06 6.43
0.045 1.015 6.79 6.20
0.05 1.010 6.54 5.99
0.06 1.000 6.11 5.62
0.07 0.895 5.75 5.31
0.08 0.975 5.43 5.05
0.09 0.970 5.16 4.81
0.10 0.965 4.96 4.60
0.11 0.960 4.74 4.41
0.12 0.952 4.53 4.24
0.13 0.945 4.35 4.08
0.14 0.939 4.18 3.93
0.15 0.932 4.02 3.79
0.16 0.952 3.87 3.66
0.17 0.919 3.73 3.54
0.18 0.912 3.59 3.42
0.19 0.905 3.47 3.32
0.20 0.899 3.35 3.21
""")
H3 = rows("""
0.20 0.899 3.35 2.41
0.25 0.873 2.84 2.77
0.30 0.847 2.43 1.80
0.35 0.824 2.09 1.57
0.40 0.807 1.80 1.37
""")
H4 = rows("""
0.3 2.293 3.9 0.89 1.80
0.35 2.195 4.0 0.88 1.57
0.4 2.108 4.1 0.88 1.37
0.45 2.030 4.2 0.87 1.19
0.5 1.958 4.3 0.87 1.03
0.55 1.893 4.4 0.86 0.89
0.6 1.832 4.4 0.86 0.76
0.65 1.776 4.5 0.85 0.64
0.7 1.724 4.5 0.85 _
0.75 1.676 4.6 0.84 _
0.8 1.630 4.6 0.84 _
0.85 1.587 4.7 0.84 _
0.9 1.547 4.7 0.84 _
0.95 1.509 4.8 0.83 _
1.0 1.473 4.8 0.83 _
1.05 1.439 4.8 0.83 _
1.1 1.406 4.9 0.83 _
1.15 1.375 4.9 0.83 _
1.175 1.360 4.9 0.83 _
1.2 1.346 4.95 0.83 _
1.225 1.331 5.0 0.83 _
1.25 1.318 5.0 0.83 _
1.275 1.304 5.0 0.83 _
1.294 1.294 5.0 0.83 _
""")
H5 = rows("""
0.010 1.00 5.68 5.023
0.015 0.98 5.18 4.581
0.020 0.97 4.83 4.267
0.03 0.96 4.33 3.825
0.04 0.94 3.96 3.511
0.05 0.93 3.67 3.268
0.06 0.92 3.44 3.069
0.08 0.90 3.08 2.755
0.10 0.89 2.83 2.511
0.12 0.88 2.612 2.313
0.14 0.86 2.421 2.144
0.16 0.85 2.257 1.999
0.18 0.84 2.111 1.870
0.20 0.83 1.985 1.755
""")
H6 = rows("""
0.2 1.04 2.73
0.3 1.00 2.13
0.4 0.95 1.72
0.5 0.91 1.41
0.6 0.88 1.17
0.7 0.84 0.98
0.8 0.81 0.82
0.809 0.809 0.809
""")
H7 = rows("""
0.10 0.79 2.76 2.511
0.12 0.79 2.56 2.313
0.14 0.77 2.39 2.144
0.16 0.77 2.25 1.999
0.18 0.75 2.12 1.870
0.20 0.75 2.01 1.755
0.25 0.73 1.77 1.512
0.30 0.71 1.58 1.313
0.35 0.69 1.42 1.145
0.40 0.68 1.29 0.999
0.45 0.66 1.18 0.871
0.50 0.65 1.08 0.756
0.55 0.64 1.00 0.652
0.60 0.63 0.92 0.557
0.65 0.61 0.85 _
0.70 0.61 0.79 _
0.745 0.59 0.745 _
""")
H10 = rows("""
0.34 0.929 0.47
0.36 0.903 0.48
0.38 0.887 0.48
0.40 0.871 0.49
0.42 0.856 0.50
0.44 0.842 0.50
0.46 0.829 0.50
0.48 0.816 0.51
0.50 0.803 0.52
0.52 0.791 0.52
0.54 0.780 0.53
0.56 0.769 0.53
0.58 0.759 0.54
0.60 0.749 0.55
0.62 0.739 0.55
0.64 0.730 0.55
0.66 0.721 0.55
0.68 0.712 0.55
0.70 0.704 0.56
0.702 0.702 0.56
""")
X2 = rows("""
0.36 2.06 0.903 0.0172
0.38 1.96 0.887 0.0134
0.40 1.86 0.871 0.0102
0.42 1.77 0.856 0.0074
0.44 1.69 0.842 0.0049
0.46 1.61 0.829 0.0032
0.48 1.53 0.816 0.0028
0.50 1.47 0.803 0.0025
0.52 1.40 0.791 0.0021
0.54 1.34 0.780 0.0018
0.56 1.28 0.769 0.0015
0.58 1.23 0.759 0.0012
0.60 1.18 0.749 0.0009
0.62 1.13 0.739 0.0008
0.64 1.09 0.730 0.0008
0.66 1.04 0.714 0.0007
0.68 1.00 0.712 0.0007
0.70 0.96 _ 0.0012
0.72 0.93 _ 0.0011
0.74 0.91 _ 0.0010
0.76 0.89 _ 0.0009
0.78 0.86 _ 0.0008
0.80 0.84 _ 0.0007
0.82 0.83 _ 0.0006
0.827 0.827 _ 0.0005
""")
X3 = rows("""
0.38 2.53 0.0060 0.0027
0.42 2.35 0.0051 0.0024
0.46 2.20 0.0043 0.0020
0.50 2.06 0.0035 0.0017
0.54 1.94 0.0028 0.0015
0.58 1.84 0.0021 0.0012
0.62 1.75 0.0015 0.0010
0.66 1.67 0.0010 0.0008
0.70 1.59 0.0006 0.0006
0.74 1.52 0.0006 0.0004
0.78 1.46 0.0006 0.0003
0.82 1.40 0.0006 0.0002
0.86 1.35 0.0006 0.0002
0.90 1.30 0.0006 0.0002
0.94 1.25 0.0006 0.0002
0.98 1.21 0.0006 0.0002
1.02 1.17 0.0006 0.0002
1.06 1.13 0.0006 0.0002
1.099 1.099 0.0006 0.0002
""")
X4 = rows("""
0.36 1.69 0.903 0.0223 0.0152
0.38 1.69 0.887 0.0263 0.0181
0.40 1.69 0.871 0.0310 0.0214
0.42 1.69 0.856 0.0362 0.0252
0.44 1.67 0.842 0.0408 0.0287
0.46 1.59 0.829 0.0414 0.0297
0.48 1.52 0.816 0.0420 0.0307
0.50 1.45 0.803 0.0420 0.0315
0.52 1.39 0.791 0.0423 0.0324
0.54 1.31 0.780 0.0401 0.0317
0.56 1.23 0.769 0.0373 0.0305
0.58 1.13 0.759 0.0320 0.0274
0.60 1.04 0.749 0.0271 0.0245
0.62 0.96 0.739 0.0226 0.0216
0.64 0.88 0.730 0.0176 0.0182
0.66 0.82 0.721 0.0144 0.0156
0.68 0.76 0.712 0.0139 0.0126
""")
X5 = rows("""
0.36 1.69 0.903 0.0664
0.38 1.69 0.887 0.0702
0.40 1.69 0.871 0.0742
0.42 1.69 0.856 0.0783
0.44 1.67 0.842 0.0799
0.46 1.56 0.829 0.0700
0.48 1.45 0.816 0.0606
0.50 1.36 0.803 0.0535
0.52 1.27 0.791 0.0465
0.54 1.19 0.780 0.0406
0.56 1.11 0.769 0.0348
0.58 1.04 0.759 0.0299
0.60 0.97 0.749 0.0249
0.62 0.91 0.739 0.0208
0.64 0.85 0.730 0.0167
0.66 0.79 0.721 0.0126
0.68 0.74 0.712 0.0092
""")
X6 = rows("""
0.54 1.43 0.780 0.0301
0.58 1.36 0.759 0.0276
0.62 1.28 0.739 0.0242
0.66 1.20 0.721 0.0206
0.70 1.11 0.704 0.0167
0.74 1.02 0.70 0.0128
0.78 0.93 0.74 0.0090
0.82 0.82 0.78 0.0070
""")
X7 = rows("""
0.36 1.69 0.903
0.38 1.69 0.887
0.40 1.69 0.871
0.42 1.69 0.856
0.44 1.67 0.842
0.46 1.56 0.829
0.48 1.45 0.816
0.50 1.36 0.803
0.52 1.27 0.791
0.54 1.19 0.780
0.56 1.11 0.769
0.58 1.04 0.759
0.60 0.97 0.749
0.62 0.91 0.739
0.64 0.85 0.730
0.66 0.79 0.721
0.68 0.74 0.712
0.70 - 0.704
0.702 - 0.702
""")
X8 = rows("""
0.52 1.320 1.352 1.320 1.39 1.27
0.54 1.243 1.253 1.243 1.31 1.19
0.56 1.160 1.160 1.167 1.23 1.11
0.58 1.079 1.079 1.103 1.13 1.04
0.60 1.001 1.001 1.038 1.04 0.97
0.62 0.933 0.933 0.979 0.96 0.91
""")
X9 = rows("""
0.62 0.64 - 0.902
0.64 0.66 - 0.898
0.66 0.68 - 0.893
0.68 0.70 - 0.888
0.68 0.70 0.745 1.054
0.70 0.71 - 0.886
0.70 0.71 0.745 1.048
0.71 0.72 - 0.883
0.71 0.72 0.75 1.036
0.72 0.74 - 0.878
0.72 0.74 0.76 1.012
0.74 0.78 - 0.868
0.74 0.78 0.78 0.996
""")
X10 = rows("""
0.44 0.60 1.176
0.60 0.70 1.055
0.70 0.80 0.952
""")
X11 = rows("""
≥6 0.440 0.364 0.44 1.67 1.00 -
=5 0.493 0.397 0.50 1.36 0.90 120
=4 0.478 0.348 0.48 1.45 0.82 235
=3 0.498 0.389 0.50 1.36 0.82 290
=2 0.628 0.518 0.66 1.20 0.70 58
""")
X45 = rows("""
≥6 0.440
=5 0.493
=4 0.478
=3 0.498
=2 0.628
""")
X2P = rows("""
0.46 1.85 1.56 0.0797
0.48 1.76 1.45 0.0598
0.50 1.67 1.36 0.0455
0.52 1.59 1.27 0.0332
0.54 1.51 1.19 0.0235
0.56 1.44 1.11 0.0150
0.58 1.36 1.04 0.0084
0.60 1.29 0.97 0.0026
0.62 1.22 0.91 0.0016
0.64 1.15 0.85 0.0010
0.66 1.08 0.79 0.0008
0.68 1.02 0.74 0.0007
0.70 0.96 _ -
0.72 0.93 _ -
0.74 0.91 _ -
0.76 0.89 _ -
0.78 0.86 _ -
0.80 0.84 _ -
0.82 0.83 _ -
0.827 0.827 _ -
""")

# ---------------------------------------------------------------------------------------------
# Table specifications. key/value: column indices of t (or interval) and of the bound c.
# form 'le': lambda_1 <= t => bound; 'interval': lambda_1 in [a,b] => bound.
# eps: printed as 'c - eps' (H p. 38; H Table 5 is computed 'in the same way', H p. 45).
# strict: X prints 'lambda > c'.  cond: hypothesis beyond the type, so not usable type-wide.
# ---------------------------------------------------------------------------------------------

TABLES = {
    'H Table 2': dict(
        src='H', page=39, transcription=H2, ncols=4,
        start=r'^\s*λ1\s+λ\s+λ0\s+2 log 1/λ1\s*$', end=r'Table 2: λ0 for real χ1 and ρ1',
        columns=['λ1 ≤ t', 'λ (test parameter)', "λ′ ≥ c − ε", '2 log 1/λ1'],
        captions=['Table 2: λ0 for real χ1 and ρ1'],
        meaning=[('H', 38, 'it then follows that λ0 ≥ λ0b − ε for q ≥ q(ε, b), whenever 0 ≤ λ1 ≤ b.'),
                 ('H', 38, 'and calculated values a little below λ0b'),
                 ('H', 30, 'Lemma 6.3 Let χ1 and ρ1 be real.')],
        rule=dict(q='lp', form='le', key=0, value=2, types=('rr',), eps=True),
        scope="χ1, ρ1 real (rr); λ1 ≤ t ⇒ λ′ ≥ c − ε; printed c a little below the root (H p. 38)"),
    'H Table 3': dict(
        src='H', page=39, transcription=H3, ncols=4,
        after=r'Table 2: λ0 for real χ1 and ρ1',
        start=r'^\s*λ1\s+λ\s+λ0\s+2 log 1/λ1\s*$', end=r'Table 3: λ0 for real χ1 and ρ1',
        columns=['λ1 ≤ t', 'λ (test parameter)', "λ′ ≥ c − ε", '(3/2) log 1/λ1'],
        captions=['Table 3: λ0 for real χ1 and ρ1'],
        meaning=[('H', 38, 'Similarly for Table 3.')],
        rule=dict(q='lp', form='le', key=0, value=2, types=('rr',), eps=True),
        scope='as H Table 2'),
    'H Table 4': dict(
        src='H', page=44, transcription=H4, ncols=5, pad=4,
        start=r'^\s*λ1\s+λ0\s+a\s+K\s+2 log 1/λ1\s*$', end=r'Table 4: λ0 for real χ1 and ρ1',
        columns=['λ1 ≤ t', "λ′ ≥ c", 'a', 'K', '(3/2) log 1/λ1'],
        captions=['Table 4: λ0 for real χ1 and ρ1'],
        meaning=[('H', 43, 'Thus the entry 0.7, 1.724, 4.5, 0.85 indicates that λ0 ≥ 1.724 whenever λ1 ≤ 0.7.'),
                 ('X', 24, 'gilt die Abschätzung λ0 ≥ 1.724 immer wenn λ1 ≤ 0.70.'),
                 ('X', 23, 'Ist jedoch ρ0 reell, so liefert [23, Lemma 8.2] bessere Werte, so dass diese '
                           'Tabelle für beide Fälle gilt.')],
        rule=dict(q='lp', form='le', key=0, value=1, types=('rr',)),
        scope="χ1, ρ1 real (rr); λ1 ≤ t ⇒ λ′ ≥ c (H p. 43); a real ρ′ is covered by Lemma 8.2 (X p. 23)"),
    'H Table 5': dict(
        src='H', page=46, transcription=H5, ncols=4,
        start=r'^\s*λ1\s+λ\s+λ2\s+11 log 1/λ1\s*$', end=r'Table 5: λ2 for real χ1 and ρ1',
        columns=['λ1 ≤ t', 'λ (test parameter)', 'λ2 ≥ c − ε', '(12/11) log 1/λ1'],
        captions=['Table 5: λ2 for real χ1 and ρ1'],
        meaning=[('H', 45, 'We then compute the values in Table 5 in the same way as we did for Tables 1 and 2.'),
                 ('H', 45, 'We may observe in Table 5 that the condition λ2 ≤ λ0 is redundant, as a '
                           'comparison with Table 2 shows.'),
                 ('H', 45, 'Lemma 8.5 Let χ1 and ρ1 be real, and suppose that λ2 ≤ λ0 .')],
        rule=dict(q='l2', form='le', key=0, value=2, types=('rr',), eps=True),
        scope='rr; λ1 ≤ t ⇒ λ2 ≥ c − ε; printed under λ2 ≤ λ′, redundant by H Table 2 (cross-check)'),
    'H Table 6': dict(
        src='H', page=46, transcription=H6, ncols=3,
        after=r'Table 5: λ2 for real χ1 and ρ1',
        start=r'^\s*λ1\s+λ\s+λ2\s*$', end=r'Table 6: λ2 for real χ1 and ρ1',
        columns=['λ1 ≤ t', 'λ (test parameter)', 'λ2 ≥ c'],
        captions=['Table 6: λ2 for real χ1 and ρ1'],
        meaning=[('H', 45, 'For those χ2 for which χ42 = χ0 we shall merely use Lemma 8.5, but with (6.10) '
                           'replaced by ψ ≤ 38 . This gives us Table 6.')],
        rule=dict(q='l2', form='le', key=0, value=2, types=('rr',), cond='χ2^4 = χ0'),
        scope='rr with χ2^4 = χ0 only (not used directly; it removes the hypothesis χ2^4 ≠ χ0 of Table 7)'),
    'H Table 7': dict(
        src='H', page=48, transcription=H7, ncols=4, pad=3,
        start=r'^\s*λ1\s+λ\s+λ2\s+11 log 1/λ1\s*$', end=r'Table 7: λ2 for real χ1 and ρ1',
        columns=['λ1 ≤ t', 'λ (test parameter)', 'λ2 ≥ c', '(12/11) log 1/λ1'],
        captions=['Table 7: λ2 for real χ1 and ρ1'],
        meaning=[('H', 47, 'Since the left hand side of (8.11) is increasing with respect to both λ1 and λ2 '
                           'we may tabulate bounds for λ2 in the usual way.'),
                 ('H', 47, 'The condition λ2 ≤ λ0 , required for Table 7, is in fact redundant, as one sees '
                           'on comparing with Tables 2,3 and 4.'),
                 ('H', 47, 'Thus the values in Table 7 apply whether χ42 6= χ0 or not.'),
                 ('X', 24, 'Insgesamt folgt wieder, dass diese Tabelle in allen Fällen gültig ist '
                           '(ausgenommen wenn λ1 ≤ 0.10).')],
        rule=dict(q='l2', form='le', key=0, value=2, types=('rr',)),
        scope='rr; λ1 ≤ t ⇒ λ2 ≥ c, for all χ2 except in row 0.10 (X p. 24; cross-check with Table 6)'),
    'H Table 10': dict(
        src='H', page=57, transcription=H10, ncols=3,
        start=r'^\s*λ1\s+λ2\s+λ\s*$', end=r'Table 10: λ2 in the complex case',
        columns=['λ1 ≤ t', 'λ2 ≥ c', 'λ (test parameter)'],
        captions=['Table 10: λ2 in the complex case'],
        meaning=[('H', 49, 'in the case in which either χ1 or ρ1 is complex.'),
                 ('H', 56, 'Thus for example, the line λ1 = 0.4, λ2 = 0.871, λ = 0.49, means that λ2 ≥ 0.871 '
                           'whenever λ1 ≤ 0.4.'),
                 ('H', 56, 'Lemma 9.4 The bounds given in Table 10 apply in all cases.')],
        rule=dict(q='l2', form='le', key=0, value=1, types=('rc', 'complex')),
        scope='χ1 or ρ1 complex (rc, complex), all cases (Lemma 9.4); λ1 ≤ t ⇒ λ2 ≥ c'),
    'X Table 2': dict(
        src='X', page=45, transcription=X2, ncols=4, side='left', pad=2,
        start=r'^\s*λ1 ≤ λ0 >\s+λ\?\s+C≤\s+λ1 ≤ λ0 >\s+C1 ≤\s+C2 ≤\s*$',
        end=r'Tabelle 3 liefert bessere Werte',
        columns=['λ1 ≤ t', "λ′ > c", 'λ⋆', 'C ≤'],
        captions=['Tabelle 2. λ0 -Abschätzungen', '(χ1 oder ρ1 komplex)'],
        meaning=[('X', 44, 'Die folgenden Tabellen liefern Aussagen der Form λ1 ≤ λ12 ⇒ λ0 > c2 .'),
                 ('X', 45, 'Tabelle 3 liefert bessere Werte als Tabelle 2. Damit gilt Tabelle 2 für beide Fälle')],
        rule=dict(q='lp', form='le', key=0, value=1, types=('rc', 'complex'), strict=True),
        scope='χ1 or ρ1 complex; λ1 ≤ t ⇒ λ′ > c (X p. 44); superseded by Table 2′ (not used directly)'),
    'X Table 3': dict(
        src='X', page=45, transcription=X3, ncols=4, side='right',
        start=r'^\s*λ1 ≤ λ0 >\s+λ\?\s+C≤\s+λ1 ≤ λ0 >\s+C1 ≤\s+C2 ≤\s*$',
        end=r'Tabelle 3 liefert bessere Werte',
        columns=['λ1 ≤ t', "λ′ > c", 'C1 ≤', 'C2 ≤'],
        captions=['Tabelle 3. λ0 -Abschätzungen', '(χ1 oder ρ1 komplex, ord χ1 ∈ {2, 3, 4})'],
        meaning=[('X', 44, 'Die folgenden Tabellen liefern Aussagen der Form λ1 ≤ λ12 ⇒ λ0 > c2 .')],
        rule=dict(q='lp', form='le', key=0, value=1, types=('rc',), strict=True,
                  extra=dict(types=('complex',), cond='ord χ1 ∈ {3, 4}')),
        scope='χ1 or ρ1 complex and ord χ1 ∈ {2,3,4}: type rc, and type complex of order 3 or 4'),
    'X Table 4': dict(
        src='X', page=52, transcription=X4, ncols=5,
        start=r'^\s*λ1 ≤ λ2 > λ2,neu = λ2,alt = C1 ≤\s+C2 ≤\s*$', end=r'Beachte: Wir werden gleich zeigen',
        columns=['λ1 ≤ t', 'λ2 > c', 'λ2,alt', 'C1 ≤', 'C2 ≤'],
        captions=['Tabelle 4. λ2 -Abschätzungen (χ1 oder ρ1 komplex, Fall 1, 2, 3, 4, 6, 8)'],
        meaning=[],
        rule=dict(q='l2', form='le', key=0, value=1, types=('rc', 'complex'), strict=True,
                  cond='Fall 1, 2, 3, 4, 6, 8'),
        scope='Fälle 1-4, 6, 8 only (not used directly; enters X Table 7)'),
    'X Table 5': dict(
        src='X', page=53, transcription=X5, ncols=4, side='left',
        start=r'^\s*λ1 ≤ λ2 > λ2,neu = λ2,alt =\s+C2 ≤\s+λ1 ≤ λ2 > λ2,neu = λ2,alt = C1 ≤\s*$',
        end=r'Insgesamt erhalten wir die folgenden Abschätzungen',
        columns=['λ1 ≤ t', 'λ2 > c', 'λ2,alt', 'C2 ≤'],
        captions=['Tabelle 5. λ2 -Abschätzungen', '(χ1 oder ρ1 komplex, Fall 5)'],
        meaning=[],
        rule=dict(q='l2', form='le', key=0, value=1, types=('rc', 'complex'), strict=True, cond='Fall 5'),
        scope='Fall 5 only (not used directly; enters X Table 7)'),
    'X Table 6': dict(
        src='X', page=53, transcription=X6, ncols=4, side='right',
        start=r'^\s*λ1 ≤ λ2 > λ2,neu = λ2,alt =\s+C2 ≤\s+λ1 ≤ λ2 > λ2,neu = λ2,alt = C1 ≤\s*$',
        end=r'Insgesamt erhalten wir die folgenden Abschätzungen',
        columns=['λ1 ≤ t', 'λ2 > c', 'λ2,alt', 'C1 ≤'],
        captions=['Tabelle 6. λ2 -Abschätzungen', '(χ1 reell und ρ1 komplex, Fall 7)'],
        meaning=[('X', 52, 'In Fall 7 ist χ1 reell und ρ1 komplex.')],
        rule=dict(q='l2', form='le', key=0, value=1, types=('rc',), strict=True),
        scope='χ1 real, ρ1 complex (Fall 7 = type rc); λ1 ≤ t ⇒ λ2 > c'),
    'X Table 7': dict(
        src='X', page=53, transcription=X7, ncols=3,
        start=r'^\s*λ1 ≤\s+λ2 >\s+λ2 >\s*$', end=r'^\s*53\s*$',
        columns=['λ1 ≤ t', 'λ2 > c (neue Werte)', 'λ2 > (alte Werte = H Table 10)'],
        captions=['Tabelle 7. λ2 -Abschätzungen (χ1 oder ρ1 komplex, alle Fälle)'],
        meaning=[('X', 53, 'Wähle dazu das Minimum der Einträge von Tabelle 4, 5 und 6. Dies ist letztendlich '
                           'immer der Eintrag aus Tabelle 5.')],
        rule=dict(q='l2', form='le', key=0, value=1, types=('rc', 'complex'), strict=True),
        scope='χ1 or ρ1 complex, all cases; λ1 ≤ t ⇒ λ2 > c'),
    'X Table 8': dict(
        src='X', page=55, transcription=X8, ncols=6,
        start=r'^\s*λ1 ≤\s+λ3 >\s+λ3 >\s+λ3 >\s+λ3 >\s+λ\?\s*$', end=r'4\.3\.2',
        columns=['λ1 ≤ t', 'λ3 > c (alle Fälle)', 'λ3 > (Fall 1)', 'λ3 > (Fall 2-4)', 'λ3 > (Fall 5-8)', 'λ⋆'],
        captions=['Tabelle 8. λ3 -Abschätzungen (χ1 oder ρ1 komplex) (alle Fälle) (Fall 1) (Fall 2-4) (Fall 5-8)'],
        meaning=[('X', 54, 'denn im Fall λ1 ≤ 0.50 liefert Tabelle 7, dass λ3 ≥ λ2 ≥ 1.36 ≥ 1.320.')],
        rule=dict(q='l3', form='le', key=0, value=1, types=('rc', 'complex'), strict=True),
        scope='χ1 or ρ1 complex; column "alle Fälle"; λ1 ≤ t ⇒ λ3 > c'),
    'X Table 9': dict(
        src='X', page=55, transcription=X9, ncols=4, parser='x9',
        columns=['a', 'b', 'Zusatzbedingung λ2 ≤', 'λ3 > c'],
        captions=['Tabelle 9. λ3 -Abschätzungen', '(χ1 komplex)'],
        meaning=[('X', 55, 'Die vierte Zeile in Tabelle 9 besagt λ1 ∈ [0.68, 0.70] ⇒ λ3 > 0.888,')],
        rule=None,
        scope='χ1 complex; not used by the proof'),
    'X Table 10': dict(
        src='X', page=55, transcription=X10, ncols=3, parser='x10',
        columns=['a', 'b', 'λ3 > c'],
        captions=['Tabelle 10. λ3 -Abschätzungen', '(χ1 und ρ1 reell)'],
        meaning=[('X', 55, 'Lemma 4.4. Es gibt eine Konstante q0 , so dass für q ≥ q0 in den Fällen χ1 komplex '
                           'bzw. χ1 und ρ1 beide reell die folgenden zwei Tabellen gelten.'),
                 ('X', 59, 'damit die Behauptung λ3 > λ32 = 1.176. Analog für die restlichen Einträge aus Tabelle 10.')],
        rule=dict(q='l3', form='interval', key=(0, 1), value=2, types=('rr',), strict=True),
        scope='χ1, ρ1 real (rr); λ1 ∈ [a,b] ⇒ λ3 > c'),
    'X Table 11': dict(
        src='X', page=60, transcription=X11, ncols=7,
        start=r'^\s*ord χ1\s+λ1 > λ1,neu =\s+λ1,alt\s+λ1,Ann\s+λ\?\s+γ\s+C≤\s*$', end=r'^\s*60\s*$',
        columns=['ord χ1', 'λ1 > λ1,neu', 'λ1,alt', 'λ1,Ann', 'λ⋆', 'γ', 'C ≤'],
        captions=['Tabelle 11. λ1 -Abschätzungen (χ1 oder ρ1 komplex)'],
        meaning=[],
        rule=None,
        scope='χ1 or ρ1 complex; the values are those of X Lemma 4.5 (cross-check)'),
    'X Lemma 4.5': dict(
        src='X', page=61, transcription=X45, ncols=2, parser='x45',
        columns=['ord χ1', 'λ1 > c'],
        captions=['Lemma 4.5. Sei χ1 oder ρ1 komplex. Dann gibt es eine Konstante q0 , so dass für q ≥ q0 gilt'],
        meaning=[],
        rule=None,
        scope='χ1 or ρ1 complex: type complex (orders ≥ 3, minimum 0.440) and type rc (order 2, 0.628)'),
    "X Table 2'": dict(
        src='X', page=62, transcription=X2P, ncols=4, pad=2,
        start=r'^\s*λ1 ≤ λ0 >\s+λ\?\s+C≤\s*$', end=r'^\s*62\s*$',
        columns=['λ1 ≤ t', "λ′ > c", 'λ⋆', 'C ≤'],
        captions=['Tabelle 2’. Verbesserte λ0 -Abschätzungen. (χ1 oder ρ1 komplex)'],
        meaning=[('X', 61, 'Außerdem benutzen wir auch, dass λ1 ≥ 0.44 gemäß Lemma 4.5.'),
                 ('X', 44, 'Die folgenden Tabellen liefern Aussagen der Form λ1 ≤ λ12 ⇒ λ0 > c2 .')],
        rule=dict(q='lp', form='le', key=0, value=1, types=('rc', 'complex'), strict=True),
        scope="χ1 or ρ1 complex; λ1 ≤ t ⇒ λ′ > c"),
}

# Printed statements (lemmas and inequalities); the text is matched in the normalized page.
# Built-up fractions are extracted with numerator and denominator side by side or on separate
# lines: '67' is 6/7, '13' is 1/3, and '12 ... 11', '7 ... 6' etc. are on the lines around.
STATEMENTS = {
    'H Lemma 8.2': [('H', 38, 'Lemma 8.2 Let χ1 , ρ1 and ρ0 be real. Then λ0 ≥ 2.427 . . . .')],
    'H Lemma 8.4': [('H', 43, 'Lemma 8.4 Let χ1 and ρ1 be real, and let ε > 0. Then λ0 ≥ (2 − ε) log(λ−1 1 ) '
                              'providing that λ1 ≤ 0.2, and q is sufficiently large. Moreover 3 λ0 ≥ max( '
                              'log(λ−1 1 ), 1.294) 2 for all sufficiently large q and any λ1 .',
                     "λ′ ≥ (2−ε) log(1/λ1) for λ1 ≤ 0.2; λ′ ≥ max((3/2) log(1/λ1), 1.294) (3 over 2 built up)"),
                    ('H', 43, 'Lemma 8.3 is effective up to λ1 = 1.294, so that λ0 ≥ 1.294 in all cases.')],
    'H Lemma 8.8': [('H', 48, 'Lemma 8.8 Let χ1 and ρ1 be real, and let ε > 0. Then 12 λ2 ≥ ( − ε) log(λ−1 1 ), 11 '
                              'if q ≥ q(ε). Moreover λ2 ≥ 0.745 for all sufficiently large q.',
                     'λ2 ≥ (12/11 − ε) log(1/λ1); λ2 ≥ 0.745 (12 over 11 built up)'),
                    ('H', 48, 'Lastly, we point out that the estimates of this section have not been proved for '
                              'extremely small values of λ1 , since we are only concerned with zeros ρ0 , ρ2 in the '
                              'rectangle (6.1).',
                     'applies to all of H §8 (Lemmas 8.1-8.8, Tables 2-7)'),
                    ('H', 47, 'Finally we always have λ2 ≥ 0.745.')],
    'H Lemma 9.4': [('H', 56, 'Lemma 9.4 The bounds given in Table 10 apply in all cases. In particular we have '
                              'λ2 ≥ 0.702 for all sufficiently large q.'),
                    ('X', 45, 'Es wurde aber λ2 > 0.702 bewiesen. In der Regel gilt für jegliche Abschätzungen aus '
                              '[23], in denen als bewiesene Abschätzung λ ≥ c präsentiert wird, dass in Wirklichkeit '
                              'λ > c gezeigt wurde.', 'X footnote 2 on p. 45')],
    'H Lemma 10.3': [('H', 67, 'Lemma 10.3 Let ε > 0. Then if q is sufficiently large we have λ3 ≥ 67 − ε.',
                      'λ3 ≥ 6/7 − ε; the fraction is set as 6 over 7 (checked from the word box below)'),
                     ('H', 67, '3+δ 8 3+δ 9 P3 ( ) − − 2P3 ( ) + (3 + δ)( + ε) ≥ 0. 3 3 4 14',
                      'with λ = 6/7 and a = 3λ the coefficient (3/4)λ is 9/14, which fixes the reading 6/7'),
                     ('X', 86, 'dem Wert aus unserer Tabelle 10 und 0.857 (siehe [23, Lemma 10.3])',
                      'Xylouris uses 0.857 for H Lemma 10.3')],
    'H Lemma 11.1': [('H', 68, 'Then if λ0 = 13 log log L, we have X λ(k) /{exp((4φ + 6c1 + 2c2 )λ(k) ) − '
                               'exp((2φ + 4c1 )λ(k) )} k≤N (λ0 ) 2φ + 2c1 + c2 ≤ + ε, (11.3) 4c1 c2',
                      'λ0 = (1/3) log log L; sum ≤ (2φ+2c1+c2)/(4c1c2) + ε')],
    'X (5.18)': [('X', 66, 'X λ(k) 2φ + 2c1 + c2 ≤ + ε. (5.18) 1≤k≤N (λ0 ) e(4φ+6c1 +2c2 )λ(k) − e(2φ+4c1 )λ(k) 4c1 c2')],
    'H Lemma 13.2': [('H', 81, 'Lemma 13.2 Let ε > 0 be given, and suppose that L > 2K + 3.')],
    'H Lemma 13.3': [('H', 82, 'Lemma 13.3 Let η > 0 be given. Then X φ 1 − e−2Kλ 2Kλ − 1 + e−2Kλ 0 '
                               '|F2 ((1 − ρ)L)| ≤ ( )+ +η (13.3) ρ 2 λ 2λ2',
                      'Σ′|F2| ≤ (φ/2)(1 − e^{−2Kλ})/λ + (2Kλ − 1 + e^{−2Kλ})/(2λ²) + η'),
                     ('H', 82, 'In particular, taking λ → 0, we obtain a bound φK + K 2 + η.')],
    'X (4.28)': [('X', 56, '7 0 ≤ F (−λ1 ) − F (λ3 − λ1 ) − F (λ2 − λ1 ) − F (0) + f (0) + ε. (4.28) 6',
                  'coefficient 7/6'),
                 ('X', 56, 'Wir möchten beweisen, dass (4.28) auch dann gilt, vorausgesetzt λ1 ∈ [0.44, 0.85].'),
                 ('X', 55, 'Den Fall χ1 reell und ρ1 komplex haben wir nicht behandelt')],
    'X (4.29)': [('X', 57, '1 sup <{F (−λ1 + it) − 2F (it)} ≤ f (0). (4.29) t∈R 6', 'bound f(0)/6'),
                 ('X', 57, 'Also beweisen wir (4.29) und zwar für die Funktion f (t) mit γ = 1.25.'),
                 ('X', 57, 's1 = λ1 , s11 = 0.44, s12 = 0.85,'),
                 ('X', 57, 'f (0) sup <{F (−λ1 + it) − 2F (it)} < 0.18 < 0.54 . . . = . t∈R 6')],
    'X (4.31)': [('X', 58, '9 0 ≤ F (−λ2 ) − F (λ3 − λ2 ) − F (0) − F (λ1 − λ2 ) + f (0) + ε. (4.31) 8',
                  'coefficient 9/8'),
                 ('X', 58, 'Wir können außerdem annehmen, dass λ2 ≤ 1.294.')],
    'X (4.34)': [('X', 58, '5 sup < F (−λ2 + it) − F (λ1 − λ2 + it) − F (it) − f (0) (4.34) t∈R 48',
                  'bound (5/48) f(0)'),
                 ('X', 58, 'Wenn wir also zeigen, dass der Term aus (4.34) für λ1 ∈ [0.44, 0.80] und '
                           'λ2 ∈ [0.44, 1.176] kleiner oder gleich 0 ist, dann gilt die Ungleichung (4.31) auch für Fall 2.'),
                 ('X', 58, 'Mit γ = 1.04 und den'),
                 ('X', 59, '< 0.10 < 0.13 . . . = f (0). t∈R 48'),
                 ('X', 59, 'Damit gilt (4.31) immer im Fall χ1 und ρ1 beide reell (für γ = 1.04 wohlgemerkt).')],
    'X conventions': [('X', 43, 'Für hinreichend kleines ε > 0 ist dies ein Widerspruch.'),
                      ('X', 44, 'Jedoch haben wir eigentlich nur Aussagen der Form λ1 ∈ [λ11 , λ12 ] ⇒ λ0 > c2 '
                                'bewiesen. Da aber die Abschätzungen für kleinere λ1 besser sind')],
}

# Misprints in the sources that the proof does not use (recorded so that later work avoids them).
ERRATA = [
    dict(item='H Lemma 8.3: "providing that ρ1 is complex" should read ρ′ (Xylouris: "dass ρ0 komplex ist")',
         evidence=[('H', 43, 'for any constants a > 0, K ≥ 14 for which (8.6) holds, providing that ρ1 is complex '
                             'and q ≥ q(a, K, ε).'),
                   ('X', 23, 'Diese Tabelle ist ein Korollar von [23, Lemma 8.3], welches unter der Voraussetzung '
                             'gilt, dass ρ0 komplex ist.')],
         used='no (Table 4 holds for real ρ′ by Lemma 8.2, see the cross-checks)'),
    dict(item='H Table 8, row 0.66: λ′ ≥ 0.783 should read 0.738 (Xylouris)',
         evidence=[('H', 54, '0.66 0.783 2.66'),
                   ('X', 43, 'dass in [23, Table 8 (§9)] in der Zeile mit λ1 ≤ 0.66 ein Zahlendreher vorliegt. Die '
                             'Abschätzung λ0 ≥ 0.783 müsste dort λ0 ≥ 0.738 lauten.')],
         used='no (H Table 8 is not used)'),
    dict(item='H Table 7, row 0.10: not valid when χ2^4 = χ0 (H Table 6 gives only 2.73 < 2.76)',
         evidence=[('X', 24, '(ausgenommen wenn λ1 ≤ 0.10)')],
         used='no (cover_v5.H_SECOND starts at row 0.12; see the cross-checks)'),
]


# ---------------------------------------------------------------------------------------------
# Parsing
# ---------------------------------------------------------------------------------------------

def block(lines, start, end, after=None):
    i0 = 0
    if after:
        i0 = next(k for k, line in enumerate(lines) if re.search(after, line)) + 1
    i = next(k for k in range(i0, len(lines)) if re.search(start, lines[k]))
    j = next(k for k in range(i+1, len(lines)) if re.search(end, lines[k]))
    return i, lines[i+1:j]


TOKEN = re.compile(r'^(\d+\.\d+|\d+|-|[≥=]\d)$')


def parse_table(spec):
    lines = page(spec['src'], spec['page']).splitlines()
    parser = spec.get('parser')
    if parser == 'x9' or parser == 'x10':
        _, body = block(lines, r'^\s*λ1 ∈\s+Zusatzbedingung λ3 >\s+λ1 ∈\s+λ3 >\s*$',
                        r'Die vierte Zeile in Tabelle 9 besagt')
        rx = re.compile(r'^\s*\[(\d\.\d+), (\d\.\d+)\] (?:-|λ2 ≤ (\d\.\d+))\s+(\d\.\d+)'
                        r'(?:\s+\[(\d\.\d+), (\d\.\d+)\] (\d\.\d+))?\s*$')
        out9, out10, bad = [], [], []
        for line in body:
            if not line.strip():
                continue
            m = rx.match(line)
            if not m:
                bad.append(line)
                continue
            g = m.groups()
            out9.append((g[0], g[1], g[2] or '-', g[3]))
            if g[4]:
                out10.append((g[4], g[5], g[6]))
        return (out9 if parser == 'x9' else out10), bad
    if parser == 'x45':
        text = page('X', 61)
        seg = text[text.index('Lemma 4.5.'):text.index('Bemerkung. Liu und Wang')]
        found = re.findall(r'(\d\.\d+) falls ord χ1 ([≥=]) (\d)', seg)
        return [(f'{rel_}{o}', v) for v, rel_, o in found], []
    header, body = block(lines, spec['start'], spec['end'], spec.get('after'))
    side = spec.get('side')
    boundary = None
    if side:
        hl = lines[header]
        second = [m.start() for m in re.finditer('λ1', hl)][1]
        boundary = second - 2
    out, bad = [], []
    for line in body:
        if not line.strip():
            continue
        toks = [(m.start(), m.end(), m.group()) for m in re.finditer(r'\S+', line)]
        if side:
            if any(s < boundary < e for s, e, _ in toks):
                bad.append(line)
                continue
            toks = [x for x in toks if (x[0] < boundary) == (side == 'left')]
            if not toks:
                continue
        words = [w for _, _, w in toks]
        if not all(TOKEN.match(w) for w in words):
            bad.append(line)
            continue
        if len(words) == spec['ncols'] - 1 and 'pad' in spec:
            words.insert(spec['pad'], '')
        if len(words) != spec['ncols']:
            bad.append(line)
            continue
        out.append(tuple(words))
    return out, bad


def row_regex(row):
    toks = [t for t in row if t != '']
    return re.compile(r'(?<![\d.])' + r'\s+'.join(re.escape(t) for t in toks) + r'(?![\d.])')


def check_tables():
    report = {}
    for name, spec in TABLES.items():
        src, p = spec['src'], spec['page']
        parsed, bad = parse_table(spec)
        trans = spec['transcription']
        equal = parsed == trans
        if bad:
            fail(f'{name}: unparsed lines {bad}')
        if not equal:
            fail(f'{name}: parsed rows differ from the transcription: '
                 f'{[r for r in parsed if r not in trans]} / {[r for r in trans if r not in parsed]}')
        text = page(src, p)
        unmatched = []
        for r in trans:
            rx = row_regex(r)
            if spec.get('parser') == 'x45':
                rx = re.compile(re.escape(r[1]) + r' falls ord χ1 ' + re.escape(r[0][0]) + ' ' + re.escape(r[0][1:]))
            elif spec.get('parser') in ('x9', 'x10'):
                cond = '-' if r[-2] == '-' else f'λ2 ≤ {r[2]}' if spec['parser'] == 'x9' else None
                parts = [re.escape(f'[{r[0]}, {r[1]}]')] + ([re.escape(cond)] if cond else []) + [re.escape(r[-1])]
                rx = re.compile(r'\s+'.join(parts) + r'(?![\d.])')
            if not rx.search(text):
                unmatched.append(r)
        if unmatched:
            fail(f'{name}: transcribed rows not found in the page text: {unmatched}')
        caps = [snippet_record(src, p, c) for c in spec['captions']]
        meaning = [snippet_record(s, q, t) for s, q, t in spec['meaning']]
        report[name] = dict(
            source=src, page=p, columns=spec['columns'], scope=spec['scope'],
            rows_parsed=len(parsed), rows_transcribed=len(trans), parse_equals_transcription=equal,
            rows_matched_in_text=len(trans)-len(unmatched), unparsed_lines=bad,
            captions=caps, meaning=meaning,
            rows=[[c if c != '' else None for c in r] for r in parsed],
            uses=[])
    return report


def check_statements():
    out = {}
    for name, items in STATEMENTS.items():
        out[name] = [snippet_record(*it) for it in items]
    return out


def check_errata():
    return [dict(item=e['item'], used_by_the_proof=e['used'],
                 evidence=[snippet_record(*ev) for ev in e['evidence']]) for e in ERRATA]


def lemma_103_fraction():
    """H Lemma 10.3: the word '67' after the inequality sign is one glyph wide and two lines high."""
    xml = subprocess.run(['pdftotext', '-bbox', '-f', '67', '-l', '67', str(PDF['H']), '-'],
                         check=True, capture_output=True).stdout.decode('utf-8')
    words = re.findall(r'<word xMin="([\d.]+)" yMin="([\d.]+)" xMax="([\d.]+)" yMax="([\d.]+)">([^<]*)</word>', xml)
    i = next(k for k, w in enumerate(words) if w[4] == '10.3')
    seq = [w[4] for w in words[i:i+30]]
    j = i + seq.index('67')
    x0, y0, x1, y1 = map(float, words[j][:4])
    lam = next(w for w in words[i:j] if w[4] == 'λ')
    line_h = float(lam[3]) - float(lam[1])
    digit_w = max(float(w[2]) - float(w[0]) for w in words[i:j] if w[4] == '3')
    stacked = (x1 - x0) <= 1.05*digit_w and (y1 - y0) > 1.3*line_h
    if not stacked:
        fail('H Lemma 10.3: the fraction 6/7 is not stacked in the word boxes')
    return dict(word='67', width=round(x1-x0, 3), height=round(y1-y0, 3), digit_width=round(digit_w, 3),
                text_line_height=round(line_h, 3), stacked_fraction=stacked,
                reading='6 over 7: one digit wide and taller than the text line')


# ---------------------------------------------------------------------------------------------
# Rules: the printed implications in a common form
# ---------------------------------------------------------------------------------------------

def build_rules(tables, crosscheck_flags):
    rules = []

    def add(**kw):
        kw.setdefault('eps', False)
        kw.setdefault('strict', False)
        kw.setdefault('cond', None)
        kw['types'] = set(kw['types'])
        rules.append(kw)

    for name, spec in TABLES.items():
        r = spec.get('rule')
        if not r:
            continue
        for row in tables[name]['rows']:
            if r['form'] == 'le':
                t, c = Q(row[r['key']]), row[r['value']]
                if c in (None, '-'):
                    continue
                label = row[r['key']]
                base = dict(table=name, row=label, q=r['q'], form='le', t=t, c=Q(c), eps=r.get('eps', False),
                            strict=r.get('strict', False))
                cond = r.get('cond')
                if name == 'H Table 7' and Q(label) == Q('0.10') and not crosscheck_flags['H7 row 0.10 covers χ2^4=χ0']:
                    cond = 'χ2^4 ≠ χ0 (X p. 24)'
                if name == 'H Table 7' and not crosscheck_flags['H7 λ2≤λ′ redundant']:
                    cond = 'λ2 ≤ λ′'
                if name == 'H Table 5' and not crosscheck_flags['H5 λ2≤λ′ redundant']:
                    cond = 'λ2 ≤ λ′'
                add(types=r['types'], cond=cond, **base)
                if 'extra' in r:
                    add(types=r['extra']['types'], cond=r['extra']['cond'], **base)
            else:
                a, b = Q(row[0]), Q(row[1])
                add(table=name, row=f'[{row[0]}, {row[1]}]', q=r['q'], form='interval', a=a, b=b,
                    c=Q(row[r['value']]), types=r['types'], strict=r.get('strict', False), cond=r.get('cond'))
    add(table='H Lemma 8.2', row='2.427', q='lp', form='all', c=Q('2.427'), types=('rr',), cond="ρ′ real")
    add(table='H Lemma 8.4', row='1.294', q='lp', form='all', c=Q('1.294'), types=('rr',))
    add(table='H Lemma 8.8', row='0.745', q='l2', form='all', c=Q('0.745'), types=('rr',))
    add(table='H Lemma 9.4', row='0.702', q='l2', form='all', c=Q('0.702'), types=('rc', 'complex'))
    add(table='H Lemma 10.3', row='6/7', q='l3', form='all', c=Q(6, 7), types=TYPES, eps=True)
    lemma45 = {o: Q(v) for o, v in tables['X Lemma 4.5']['rows']}
    add(table='X Lemma 4.5', row='ord ≥ 3 (minimum)', q='l1', form='all', strict=True, types=('complex',),
        c=min(v for o, v in lemma45.items() if o != '=2'))
    add(table='X Lemma 4.5', row='ord = 2', q='l1', form='all', strict=True, types=('rc',), c=lemma45['=2'])
    return rules


def applicable(rules, q, kind, A, B, conds=()):
    out = []
    for r in rules:
        if r['q'] != q or kind not in r['types'] or (r['cond'] and r['cond'] not in conds):
            continue
        if r['form'] == 'le':
            ok = B <= r['t'] or r['c'] <= r['t']
        elif r['form'] == 'interval':
            ok = r['a'] <= A and B <= r['b']
        else:
            ok = True
        if ok:
            out.append(r)
    return out


def rid(r):
    return f"{r['table']} row {r['row']}" if not r['table'].startswith(('H Lemma', 'X Lemma')) else f"{r['table']} ({r['row']})"


def classify(rules, q, kind, A, B, v, conds=()):
    """Status of the lower bound v for q on [A,B]: equal / trivial / safe / mismatch."""
    A, B, v = Q(A), Q(B), Q(v)
    cands = applicable(rules, q, kind, A, B, conds)
    equal = [r for r in cands if r['c'] == v and not r['eps']]
    above = [r for r in cands if r['c'] > v]
    best = max(cands, key=lambda r: r['c']) if cands else None
    if equal:
        status = 'equal'
    elif v <= A and q != 'l1':
        status = 'trivial'
    elif above:
        status = 'safe'
    else:
        status = 'mismatch'
    return dict(status=status, value=fmt(v), printed=[rid(r) for r in equal],
                best=(fmt(best['c']), rid(best)) if best else None)


# When a value equals several printed values in scope, the use is booked under the first table
# in this order (the source the paper cites for that type); all equal sources are kept in the
# parent records.
PREFERENCE = ['H Table 4', 'H Table 7', "X Table 2'", 'X Table 3', 'X Table 6', 'X Table 7', 'H Table 10',
              'X Table 8', 'X Table 10', 'H Lemma 8.4', 'H Lemma 8.8', 'H Lemma 9.4', 'H Lemma 10.3',
              'X Table 2', 'H Table 2', 'H Table 3', 'H Table 5']


def preferred(printed):
    def key(pr):
        table = pr.split(' row ')[0].split(' (')[0]
        return PREFERENCE.index(table) if table in PREFERENCE else len(PREFERENCE)
    return min(printed, key=key) if printed else None


STATEMENT_USES = {}


def add_use(tables, table, row, printed, used, status, where, note=None):
    """Book a use under its table (or, for a printed lemma, under STATEMENT_USES)."""
    use = dict(row=row, printed=printed, used=used, status=status, where=where)
    if note:
        use['note'] = note
    if table in tables:
        tables[table]['uses'].append(use)
    else:
        STATEMENT_USES.setdefault(table, []).append(use)
    if status == 'mismatch':
        fail(f'{table} row {row}: used {used} at {where}, printed {printed}')


def book(tables, pr, value, where):
    """Book an 'equal' use of the printed rule with identifier pr."""
    if ' row ' in pr:
        table, _, row = pr.partition(' row ')
    else:
        table, _, row = pr.partition(' (')
        row = row.rstrip(')')
    add_use(tables, table, row, value if table in tables else row, value, 'equal', where)


def printed_value(tables, table, key, col):
    for row in tables[table]['rows']:
        if Q(row[0]) == Q(key):
            return row[col]
    return None


def compare_lower(used, printed, eps=False):
    """A used lower bound against a printed one."""
    used, printed = Q(used), Q(printed)
    if used == printed and not eps:
        return 'equal'
    if used < printed or (used == printed and eps):
        return 'safe'
    return 'mismatch'


# ---------------------------------------------------------------------------------------------
# Cross-checks between printed tables
# ---------------------------------------------------------------------------------------------

def cross_checks(tables):
    T = {k: v['rows'] for k, v in tables.items()}
    out, flags = [], {}

    def best_le(table_rows, t, col):
        """Best printed value among rows with t' >= t, or c' <= t' (valid for all lambda_1)."""
        vals = [Q(r[col]) for r in table_rows if Q(r[0]) >= t or Q(r[col]) <= Q(r[0])]
        return max(vals) if vals else None

    # H Table 7 against H Table 6 (the case chi_2^4 = chi_0)
    res = []
    for r in T['H Table 7']:
        t, c = Q(r[0]), Q(r[2])
        b6 = best_le(T['H Table 6'], t, 2)
        res.append(dict(row=r[0], table7=r[2], table6_best=fmt(b6), covered=b6 is not None and b6 >= c))
    flags['H7 row 0.10 covers χ2^4=χ0'] = res[0]['covered']
    ok = all(x['covered'] for x in res[1:])
    out.append(dict(check='H Table 7 rows hold when χ2^4 = χ0 (H Table 6, H p. 47)', passed=ok,
                    detail=res, note='row 0.10 is not covered (2.73 < 2.76), as X p. 24 says; the proof does not use it'))
    if not ok:
        fail('H Table 7 against H Table 6')
    # H Table 7 against H Tables 2, 3, 4 and Lemma 8.4 (the case lambda_2 > lambda')
    res = []
    for r in T['H Table 7']:
        t, c = Q(r[0]), Q(r[2])
        cands = [(Q(x[2]), 'H Table 2', True) for x in T['H Table 2'] if Q(x[0]) >= t]
        cands += [(Q(x[2]), 'H Table 3', True) for x in T['H Table 3'] if Q(x[0]) >= t]
        cands += [(Q(x[1]), 'H Table 4', False) for x in T['H Table 4'] if Q(x[0]) >= t or Q(x[1]) <= Q(x[0])]
        cands += [(Q('1.294'), 'H Lemma 8.4', False)]
        good = [x for x in cands if x[0] > c or (x[0] == c and not x[2])]
        b = max(cands)
        res.append(dict(row=r[0], table7=r[2], lambda_prime_best=f'{fmt(b[0])} ({b[1]})', covered=bool(good)))
    flags['H7 λ2≤λ′ redundant'] = all(x['covered'] for x in res)
    out.append(dict(check="H Table 7 hypothesis λ2 ≤ λ′ is redundant (H Tables 2-4, H p. 47)",
                    passed=flags['H7 λ2≤λ′ redundant'], detail=res))
    # H Table 5 against H Table 2
    res = []
    for r in T['H Table 5']:
        t, c = Q(r[0]), Q(r[2])
        b2 = max([Q(x[2]) for x in T['H Table 2'] if Q(x[0]) >= t] or [Q(0)])
        res.append(dict(row=r[0], table5=r[2], table2_best=fmt(b2), covered=b2 > c))
    flags['H5 λ2≤λ′ redundant'] = all(x['covered'] for x in res)
    out.append(dict(check="H Table 5 hypothesis λ2 ≤ λ′ is redundant (H Table 2, H p. 45)",
                    passed=flags['H5 λ2≤λ′ redundant'], detail=res))
    # H Table 4 row 0.3 against H Table 3 row 0.30; Lemma 8.2 against Table 4
    t3 = Q(printed_value(tables, 'H Table 3', '0.30', 2))
    t4 = Q(printed_value(tables, 'H Table 4', '0.3', 1))
    out.append(dict(check='H Table 4 row (0.3, 2.293) is implied by H Table 3 row (0.30, 2.43)',
                    passed=t3 > t4, detail=dict(table3=fmt(t3), table4=fmt(t4)),
                    note='the side conditions (8.6), (8.8) of Table 4 need not hold for row 0.3 (paper §7)'))
    mx4 = max(Q(x[1]) for x in T['H Table 4'])
    out.append(dict(check='H Lemma 8.2 (λ′ ≥ 2.427 for real ρ′) exceeds every H Table 4 value (X p. 23)',
                    passed=Q('2.427') >= mx4, detail=dict(max_table4=fmt(mx4))))
    for x in out[-2:]:
        if not x['passed']:
            fail(x['check'])
    # X Table 7 = minimum of X Tables 4, 5, 6; old values = H Table 10
    res = []
    for r in T['X Table 7']:
        t = Q(r[0])
        h10 = printed_value(tables, 'H Table 10', r[0], 1)
        item = dict(row=r[0], new=r[1], old=r[2], h_table10=h10, old_equals_h10=h10 is not None and Q(h10) == Q(r[2]))
        if r[1] != '-':
            vals = [Q(x[1]) for name in ('X Table 4', 'X Table 5', 'X Table 6') for x in T[name] if Q(x[0]) == t]
            item['minimum_of_4_5_6'] = fmt(min(vals))
            item['new_is_minimum'] = Q(r[1]) == min(vals)
        res.append(item)
    ok = all(x['old_equals_h10'] and x.get('new_is_minimum', True) for x in res)
    out.append(dict(check='X Table 7: new = min(X Tables 4, 5, 6) (X p. 53); old = H Table 10', passed=ok, detail=res))
    if not ok:
        fail('X Table 7 cross-check')
    # lambda_2,alt of X Tables 4, 5, 6 = H Table 10 (X pp. 51-52), or lambda_11 beyond 0.70
    res = []
    for name in ('X Table 4', 'X Table 5', 'X Table 6'):
        width = Q('0.04') if name == 'X Table 6' else Q('0.02')
        for r in T[name]:
            h10 = printed_value(tables, 'H Table 10', r[0], 1)
            alt = Q(r[2])
            ok_row = (h10 is not None and Q(h10) == alt) or (h10 is None and alt == Q(r[0]) - width)
            res.append(dict(table=name, row=r[0], alt=r[2], h_table10=h10, ok=ok_row))
    ok = all(x['ok'] for x in res)
    out.append(dict(check='λ2,alt of X Tables 4-6 = H Table 10, or λ11 when λ11 ≥ 0.70 (X pp. 51-52)',
                    passed=ok, detail=res))
    if not ok:
        fail('X Tables 4-6 lambda2,alt cross-check')
    # X Table 8, column 'alle Faelle' = minimum of the other three columns
    res = [dict(row=r[0], alle=r[1], minimum=fmt(min(Q(r[2]), Q(r[3]), Q(r[4]))),
                ok=Q(r[1]) == min(Q(r[2]), Q(r[3]), Q(r[4]))) for r in T['X Table 8']]
    ok = all(x['ok'] for x in res)
    out.append(dict(check="X Table 8: 'alle Fälle' = minimum of Fall 1, Fall 2-4, Fall 5-8", passed=ok, detail=res))
    if not ok:
        fail('X Table 8 cross-check')
    # X Table 11 = X Lemma 4.5
    l45 = dict(T['X Lemma 4.5'])
    ok = all(l45.get(r[0]) == r[1] for r in T['X Table 11']) and len(l45) == len(T['X Table 11'])
    out.append(dict(check='X Table 11, column λ1,neu = X Lemma 4.5', passed=ok,
                    detail=[[r[0], r[1], l45.get(r[0])] for r in T['X Table 11']]))
    if not ok:
        fail('X Table 11 against X Lemma 4.5')
    # X Table 2' against X Table 2
    t2 = {Q(r[0]): Q(r[1]) for r in T['X Table 2']}
    res = [dict(row=r[0], table2p=r[1], table2=fmt(t2.get(Q(r[0]))), ok=Q(r[1]) >= t2[Q(r[0])])
           for r in T["X Table 2'"] if Q(r[0]) in t2]
    ok = all(x['ok'] for x in res)
    out.append(dict(check="X Table 2' improves X Table 2 on every common row", passed=ok, detail=res))
    if not ok:
        fail("X Table 2' against X Table 2")
    return out, flags


# ---------------------------------------------------------------------------------------------
# Uses in the code
# ---------------------------------------------------------------------------------------------

def source(path):
    return Path(path).read_text()


def require(path, pattern, what):
    text = source(path)
    m = re.search(pattern, text)
    if not m:
        fail(f'{rel(path)}: {what}: pattern not found: {pattern}')
    return m


def code_tables(tables, rules):
    sys.path.insert(0, str(CODE))
    import case_cover
    import cover_v4
    import cover_v5
    out = {}
    # cover_v5: H_PRIME (H Table 4), H_SECOND (H Table 7); used for rr and only on cells with hi <= t
    require(CODE/'cover_v5.py', re.escape("table=H_PRIME+H_SECOND if kind=='rr' else []"), 'H rows only for rr')
    require(CODE/'cover_v5.py', re.escape("ps=[Q(v) for t,v in H_PRIME if hi<=Q(t)] if kind=='rr' else []"),
            'H Table 4 rows only when hi <= t')
    require(CODE/'cover_v5.py', re.escape("rs=[Q(v) for t,v in H_SECOND if hi<=Q(t)] if kind=='rr' else []"),
            'H Table 7 rows only when hi <= t')
    require(CODE/'cover_v4.py', re.escape("table=COMPLEX_PRIME if kind=='complex' else REAL_COMPLEX_PRIME if kind=='rc' else []"),
            "X Table 2' rows for complex, X Table 3 rows for rc")
    require(CODE/'cover_v4.py', re.escape("applicable=[Q(v) for t,v in table if hi<=Q(t)]"), 'X rows only when hi <= t')
    for name, rows_, table, col, kind in [
            ('cover_v5.H_PRIME', cover_v5.H_PRIME, 'H Table 4', 1, 'rr'),
            ('cover_v5.H_SECOND', cover_v5.H_SECOND, 'H Table 7', 2, 'rr'),
            ('cover_v4.COMPLEX_PRIME', cover_v4.COMPLEX_PRIME, "X Table 2'", 1, 'complex'),
            ('cover_v4.REAL_COMPLEX_PRIME', cover_v4.REAL_COMPLEX_PRIME, 'X Table 3', 1, 'rc')]:
        stats = dict(rows=len(rows_), equal=0, safe=0, mismatch=0)
        for t, v in rows_:
            pv = printed_value(tables, table, t, col)
            st = 'mismatch' if pv is None else compare_lower(v, pv)
            rule_types = next(r['types'] for r in rules if r['table'] == table and not r['cond'])
            if kind not in rule_types:
                st = 'mismatch'
                fail(f'{name}: {table} used for type {kind} outside its scope')
            stats[st] += 1
            add_use(tables, table, fmt(Q(t)), pv, v, st, f'computations/core/code/{name.split(".")[0]}.py {name.split(".")[1]}',
                    note=f'type {kind}, applied only on cells with hi ≤ t')
        out[name] = stats
    if [Q(t) for t, _ in cover_v5.H_SECOND][0] != Q('0.12'):
        fail('H_SECOND should start at row 0.12 (row 0.10 excluded)')
    out['H_SECOND excludes H Table 7 row 0.10'] = all(Q(t) != Q('0.10') for t, _ in cover_v5.H_SECOND)
    return out, case_cover, cover_v4, cover_v5


def parents_check(tables, rules, case_cover, cover_v5):
    res = []
    counts = {}
    for j, (kind, A, B, p, r) in enumerate(cover_v5.PARENTS):
        cp = classify(rules, 'lp', kind, A, B, p)
        cr = classify(rules, 'l2', kind, A, B, r)
        for qn, c in (("lambda'", cp), ('lambda_2', cr)):
            counts[c['status']] = counts.get(c['status'], 0) + 1
            if c['status'] == 'mismatch':
                fail(f'parent {j} {kind} [{fmt(A)},{fmt(B)}]: {qn} = {c["value"]} unsupported')
            pr = preferred(c['printed'])
            if pr:
                book(tables, pr, c['value'], f'parent row {j} ({kind}, [{fmt(A)},{fmt(B)}]), {qn}')
        res.append(dict(parent=j, kind=kind, interval=[fmt(A), fmt(B)], lambda_prime=cp, lambda_2=cr))
    base = []
    for j, (kind, a, b, p, r) in enumerate(case_cover.PARENTS):
        cp = classify(rules, 'lp', kind, a, b, p)
        cr = classify(rules, 'l2', kind, a, b, r)
        for c in (cp, cr):
            if c['status'] == 'mismatch':
                fail(f'case_cover row {j}: {c["value"]} unsupported')
        base.append(dict(row=j, kind=kind, interval=[a, b], lambda_prime=cp, lambda_2=cr))
    # tiling: the parents tile [start, 1.5] per type, starting at the printed lambda_1 bounds
    starts = {}
    for kind in TYPES:
        sub = [x for x in cover_v5.PARENTS if x[0] == kind]
        contiguous = all(sub[i][2] == sub[i+1][1] for i in range(len(sub)-1))
        starts[kind] = dict(rows=len(sub), start=fmt(sub[0][1]), end=fmt(sub[-1][2]), contiguous=contiguous)
        if not contiguous or sub[-1][2] != Q('1.5'):
            fail(f'parents of type {kind} do not tile up to 1.5')
    for kind, rowname in (('rc', 'ord = 2'), ('complex', 'ord ≥ 3 (minimum)')):
        lb = next(r['c'] for r in rules if r['table'] == 'X Lemma 4.5' and r['row'] == rowname)
        st = 'equal' if Q(starts[kind]['start']) == lb else 'safe' if Q(starts[kind]['start']) < lb else 'mismatch'
        starts[kind]['printed_lambda1_lower_bound'] = fmt(lb)
        starts[kind]['status'] = st
        add_use(tables, 'X Lemma 4.5', rowname, fmt(lb), starts[kind]['start'], st,
                f'start of the {kind} parent rows (cover_v5, check_first_cover)', note='λ1 > c, so the tiling starts at c')
    return dict(count=len(res), statuses=counts, tiling=starts, rows=res, case_cover_rows=base)


def source_cover_check(rules):
    with gzip.open(RESULTS/'source_cover.json.gz', 'rt') as f:
        cover = json.load(f)
    counts = {'lp': {}, 'source_l2': {}}
    n = 0
    for root in cover:
        recs = [root['root']] + [leaf['case'] for leaf in root['leaves']]
        for c in recs:
            n += 1
            for key, q in (('lp', 'lp'), ('source_l2', 'l2')):
                st = classify(rules, q, c['kind'], Q(c['lo']), Q(c['hi']), Q(c[key]))['status']
                counts[key][st] = counts[key].get(st, 0) + 1
                if st == 'mismatch':
                    fail(f'source_cover record {c}: {key} unsupported')
    return dict(records=n, roots=len(cover), cells=n-len(cover), statuses=counts)


def third_family(tables, rules):
    """triple_inputs.third_bound: literal rows and guards, read with ast; simulated on all cells."""
    path = CODE/'triple_inputs.py'
    tree = ast.parse(source(path))
    fn = next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == 'third_bound')
    parent = {}
    for n in ast.walk(fn):
        for ch in ast.iter_child_nodes(n):
            parent[ch] = n
    loops = []
    for n in ast.walk(fn):
        if isinstance(n, ast.For) and isinstance(n.iter, ast.List):
            outer = parent[n]
            loops.append(dict(target=[e.id for e in n.target.elts], rows=ast.literal_eval(n.iter),
                              guard=ast.unparse(n.body[0].test), outer=ast.unparse(outer.test),
                              brk=any(isinstance(s, ast.Break) for s in ast.walk(n))))
    # the universal bound: the first top-level assignment r=Q('...') of the function
    universal = None
    for st_ in fn.body:
        if (isinstance(st_, ast.Assign) and isinstance(st_.targets[0], ast.Name) and st_.targets[0].id == 'r'
                and isinstance(st_.value, ast.Call) and getattr(st_.value.func, 'id', None) == 'Q'):
            universal = ast.literal_eval(st_.value.args[0])
            break
    t10 = next(x for x in loops if x['target'] == ['aa', 'bb', 'z'])
    t8 = next(x for x in loops if x['target'] == ['bb', 'z'])
    expected = {'t10': ("kind == 'rr'", 'Q(aa) <= a <= b <= Q(bb) and Q(z) > r'),
                't8': ("kind != 'rr'", 'b <= Q(bb) and Q(z) > r')}
    for key, loop in (('t10', t10), ('t8', t8)):
        if (loop['outer'], loop['guard']) != expected[key]:
            fail(f'triple_inputs.third_bound guard changed: {loop["outer"]} / {loop["guard"]}')
    if not t8['brk']:
        fail('triple_inputs.third_bound: the Table 8 loop no longer stops at the first row')
    out = dict(guards={'X Table 10': [t10['outer'], t10['guard']], 'X Table 8': [t8['outer'], t8['guard']]})
    where = 'computations/core/code/triple_inputs.py third_bound'
    # values
    for aa, bb, z in t10['rows']:
        row = next((r for r in tables['X Table 10']['rows'] if Q(r[0]) == Q(aa) and Q(r[1]) == Q(bb)), None)
        st = 'mismatch' if row is None else compare_lower(z, row[2])
        add_use(tables, 'X Table 10', f'[{aa}, {bb}]', row[2] if row else None, z, st, where,
                note="type rr; only on cells [a,b] inside [aa,bb] (guard)")
    for bb, z in t8['rows']:
        pv = printed_value(tables, 'X Table 8', bb, 1)
        st = 'mismatch' if pv is None else compare_lower(z, pv)
        add_use(tables, 'X Table 8', fmt(Q(bb)), pv, z, st, where,
                note="types rc, complex; only on cells with b ≤ t (guard); the first applicable row is the largest")
    rows8 = [Q(z) for _, z in t8['rows']]
    if rows8 != sorted(rows8, reverse=True) or [Q(b) for b, _ in t8['rows']] != sorted(Q(b) for b, _ in t8['rows']):
        fail('X Table 8 rows in triple_inputs are not ordered so that the first applicable row is the best')
    if universal is None:
        fail('triple_inputs.third_bound: the universal lambda_3 bound r=Q(...) not found')
        universal = '1'
    st = 'safe' if Q(universal) < Q(6, 7) else 'mismatch'
    tables_statement_use = dict(row='constant', printed='6/7 − ε', used=universal, status=st, where=where,
                                note=f'{universal} < 6/7 = 0.857142…, so λ3 > {universal} for small ε; X p. 86 also '
                                     'uses 0.857')
    add_use(tables, 'H Lemma 10.3', 'constant', '6/7 − ε', universal, st, where, note=tables_statement_use['note'])
    # (4.28) block: the guard's lambda_1 range, the test parameter and the coefficient
    blk = next(n for n in ast.walk(fn) if isinstance(n, ast.If) and "kind == 'complex'" in ast.unparse(n.test))
    test_src = ast.unparse(blk.test)
    m = re.fullmatch(r"kind == 'complex' and Q\('([\d.]+)'\) <= a <= b <= Q\('([\d.]+)'\)", test_src)
    body = ast.unparse(blk)
    g = re.search(r"f = test\(Q\('([\d.]+)'\)\)", body)
    k = re.search(r"I\(Q\((\d+), (\d+)\)\) \* f\.f0", body)
    if not (m and g and k):
        fail(f'triple_inputs (4.28) block changed: {test_src}')
    lo, hi = (Q(m.group(1)), Q(m.group(2))) if m else (Q(0), Q(2))
    gam = Q(g.group(1)) if g else Q(0)
    coef = Q(int(k.group(1)), int(k.group(2))) if k else Q(0)
    x428 = dict(guard=test_src, gamma=fmt(gam), coefficient=fmt(coef),
                printed='X (4.28): χ1 complex; λ1 ∈ [0.44, 0.85]; coefficient 7/6; (4.29) verified by X with γ = 1.25')
    add_use(tables, 'X (4.28)', 'λ1 range', '[0.44, 0.85]', f'[{fmt(lo)}, {fmt(hi)}]',
            inside((lo, hi), (Q('0.44'), Q('0.85'))), where,
            note="type complex only (guard kind == 'complex'); the cell must lie in the range")
    add_use(tables, 'X (4.28)', 'coefficient', '7/6', fmt(coef), at_least(coef, Q(7, 6)), where,
            note='a larger coefficient would be weaker (safe)')
    add_use(tables, 'X (4.29)', 'γ', '1.25', fmt(gam), 'equal' if gam == Q('1.25') else 'mismatch', where,
            note='f = f_γ with the γ for which (4.29) is verified (X p. 57; alias_check.py)')
    # simulate the guards on all first-zero cells of the source cover
    with gzip.open(RESULTS/'source_cover.json.gz', 'rt') as f:
        cover = json.load(f)
    cells = [leaf['case'] for root in cover for leaf in root['leaves']]
    fired = {}
    scope_bad = []
    for c in cells:
        kind, a, b = c['kind'], Q(c['lo']), Q(c['hi'])
        r = Q(universal)
        env = {'Q': Q, 'kind': kind, 'a': a, 'b': b}
        if eval(t10['outer'], {'__builtins__': {}}, env):
            for aa, bb, z in t10['rows']:
                env.update(aa=aa, bb=bb, z=z, r=r)
                if eval(t10['guard'], {'__builtins__': {}}, env):
                    r = Q(z)
                    fired[f'X Table 10 [{aa},{bb}]'] = fired.get(f'X Table 10 [{aa},{bb}]', 0) + 1
                    if not (kind == 'rr' and Q(aa) <= a and b <= Q(bb)):
                        scope_bad.append((c, aa, bb))
        if eval(t8['outer'], {'__builtins__': {}}, env):
            for bb, z in t8['rows']:
                env.update(bb=bb, z=z, r=r)
                if eval(t8['guard'], {'__builtins__': {}}, env):
                    r = Q(z)
                    fired[f'X Table 8 row {bb}'] = fired.get(f'X Table 8 row {bb}', 0) + 1
                    if not (kind in ('rc', 'complex') and b <= Q(bb)):
                        scope_bad.append((c, bb))
                    break
        allowed = applicable(rules, 'l3', kind, a, b)
        best = max(x['c'] for x in allowed)
        if r > best:
            scope_bad.append((c, 'above best', fmt(r)))
    if scope_bad:
        fail(f'third_bound printed rows outside scope: {scope_bad[:5]}')
    out.update(x428=x428, universal=tables_statement_use, cells_simulated=len(cells), rows_fired=fired,
               out_of_scope=len(scope_bad))
    return out


def grab(path, pattern, what):
    """The groups of the first match of pattern in the source of path (records a failure if none)."""
    m = require(path, pattern, what)
    return m.groups() if m else None


def inside(used, printed):
    """A used interval must lie inside the printed one (a hypothesis range)."""
    if used == printed:
        return 'equal'
    return 'safe' if printed[0] <= used[0] and used[1] <= printed[1] else 'mismatch'


def covers(used, printed):
    """A checked box must contain the printed one (a verified side condition)."""
    if used == printed:
        return 'equal'
    return 'safe' if used[0] <= printed[0] and printed[1] <= used[1] else 'mismatch'


def at_least(used, printed):
    if used == printed:
        return 'equal'
    return 'safe' if used > printed else 'mismatch'


def at_most(used, printed):
    if used == printed:
        return 'equal'
    return 'safe' if used < printed else 'mismatch'


def other_code(tables):
    out = {}
    # third_refine.py: X (4.31) for rr with gamma = 1.04, lambda_1 in [0.44, 0.80], lambda_2 <= 1.176, 9/8
    p = SIEVE/'third_refine.py'
    w = 'computations/sieve_near/third_refine.py'
    g = grab(p, r'GAMMA = Q\((\d+), (\d+)\)', 'γ of (4.31)')
    t = grab(p, r'T_LO, T_HI = Q\((\d+), (\d+)\), Q\((\d+), (\d+)\)', 'range of t (λ3 > t, and λ2 ≤ min(t,h) ≤ t)')
    r1 = grab(p, r'if not \(Q\((\d+), (\d+)\) <= a <= b <= Q\((\d+), (\d+)\)\):\s*return None', 'λ1 range')
    c = grab(p, r'val = _F\(-c2\)-_F\(t-c2\)-_F\(0\)-_F\(b-c\)\+I\(Q\((\d+), (\d+)\)\)', 'coefficient of (4.31)')
    kind = require(p, r"if c\['kind'\] != 'rr':\s*return inp", 'type rr only')
    fr = lambda grp, i: Q(int(grp[i]), int(grp[i+1]))
    if g:
        add_use(tables, 'X (4.34)', 'γ', '1.04', fmt(fr(g, 0)), 'equal' if fr(g, 0) == Q('1.04') else 'mismatch', w)
    if r1:
        lam1 = (fr(r1, 0), fr(r1, 2))
        add_use(tables, 'X (4.34)', 'λ1 range', '[0.44, 0.80]', f'[{fmt(lam1[0])}, {fmt(lam1[1])}]',
                inside(lam1, (Q('0.44'), Q('0.80'))) if kind else 'mismatch', w, note='type rr only')
    if t and r1:
        # lambda_2 runs over [a, min(t,h)] with a >= lambda_1 range start and t <= T_HI
        lam2 = (fr(r1, 0), fr(t, 2))
        add_use(tables, 'X (4.34)', 'λ2 range', '[0.44, 1.176]', f'[a, min(t,h)] ⊆ [{fmt(lam2[0])}, {fmt(lam2[1])}]',
                inside(lam2, (Q('0.44'), Q('1.176'))), w)
    if c:
        add_use(tables, 'X (4.31)', 'coefficient', '9/8', fmt(fr(c, 0)), at_least(fr(c, 0), Q(9, 8)), w)
    out['third_refine.py'] = dict(gamma=fmt(fr(g, 0)) if g else None, t_range=[fmt(fr(t, 0)), fmt(fr(t, 2))] if t else None,
                                  lambda1=[fmt(fr(r1, 0)), fmt(fr(r1, 2))] if r1 else None,
                                  coefficient=fmt(fr(c, 0)) if c else None, rr_only=bool(kind))
    # x434_check.py: the (4.34) side condition is verified on a box containing the printed one
    p = CODE/'x434_check.py'
    w = 'computations/core/code/x434_check.py'
    g = grab(p, r'g=Q\((\d+),(\d+)\)', 'γ')
    l1 = grab(p, r'for j in range\((\d+),(\d+)\)\]\s+# lambda_1 grid', 'λ1 grid')
    l2 = grab(p, r'for j in range\((\d+),(\d+)\)\]\s+# lambda_2 grid', 'λ2 grid')
    b = grab(p, r'permitted=lower\(I\(Q\((\d+),(\d+)\)\)\*f\.f0\)', 'permitted bound')
    if g:
        add_use(tables, 'X (4.34)', 'γ', '1.04', fmt(fr(g, 0)), 'equal' if fr(g, 0) == Q('1.04') else 'mismatch', w)
    if l1 and l2:
        box1 = (Q(int(l1[0]), 100), Q(int(l1[1]) - 1, 100))
        box2 = (Q(int(l2[0]), 100), Q(int(l2[1]) - 1, 100))
        st1, st2 = covers(box1, (Q('0.44'), Q('0.80'))), covers(box2, (Q('0.44'), Q('1.176')))
        st = 'mismatch' if 'mismatch' in (st1, st2) else 'safe' if 'safe' in (st1, st2) else 'equal'
        add_use(tables, 'X (4.34)', 'box checked', 'λ1 ∈ [0.44, 0.80], λ2 ∈ [0.44, 1.176]',
                f'λ1 ∈ [{fmt(box1[0])}, {fmt(box1[1])}], λ2 ∈ [{fmt(box2[0])}, {fmt(box2[1])}]', st, w,
                note='grid with step 1/100 and interpolation errors between grid points')
    if b:
        add_use(tables, 'X (4.34)', 'bound', '5/48', fmt(fr(b, 0)), at_most(fr(b, 0), Q(5, 48)), w)
    out['x434_check.py'] = dict(gamma=fmt(fr(g, 0)) if g else None, lambda1_grid=l1, lambda2_grid=l2,
                                bound=fmt(fr(b, 0)) if b else None)
    # alias_check.py: the (4.29) side condition, gamma = 5/4, lambda_1 in [0.44, 0.85], f(0)/6
    p = CODE/'alias_check.py'
    w = 'computations/core/code/alias_check.py'
    g = grab(p, r'g=Q\((\d+),(\d+)\)', 'γ')
    l1 = grab(p, r'for j in range\((\d+),(\d+)\):', 'λ1 grid')
    b = grab(p, r'margin=lower\(f\.f0/(\d+)-I', 'permitted bound f(0)/n')
    if g:
        add_use(tables, 'X (4.29)', 'γ', '1.25', fmt(fr(g, 0)), 'equal' if fr(g, 0) == Q('1.25') else 'mismatch', w)
    if l1:
        box = (Q(int(l1[0]), 100), Q(int(l1[1]) - 1, 100))
        add_use(tables, 'X (4.29)', 'λ1 range', '[0.44, 0.85]', f'[{fmt(box[0])}, {fmt(box[1])}]',
                covers(box, (Q('0.44'), Q('0.85'))), w)
    if b:
        add_use(tables, 'X (4.29)', 'bound', '1/6', f'1/{b[0]}', at_most(Q(1, int(b[0])), Q(1, 6)), w)
    out['alias_check.py'] = dict(gamma=fmt(fr(g, 0)) if g else None, lambda1_grid=l1, bound=f'1/{b[0]}' if b else None)
    # poly_rows.py: orders 3 and 4 use X Table 3 row (0.86, 1.35)
    p = CODE/'poly_rows.py'
    w = 'computations/core/code/poly_rows.py additional_row'
    m = grab(p, r"assert a<=p and b<=Q\('([\d.]+)'\) and h<Q\('([\d.]+)'\)", 'X Table 3 row used for orders 3, 4')
    if m:
        t3, c3 = Q(m[0]), Q(m[1])
        pv = printed_value(tables, 'X Table 3', fmt(t3), 1)
        st = 'mismatch' if pv is None else compare_lower(c3, pv)
        add_use(tables, 'X Table 3', fmt(t3), pv, fmt(c3), st, w,
                note='complex χ1 of order 3 or 4 (⊂ {2,3,4}); cells with b ≤ t; needs λ′ > h with h < c')
        out['poly_rows.py'] = dict(row=[fmt(t3), fmt(c3)], used_for='ord χ1 ∈ {3,4}, b ≤ t, h < c')
    return out


def polynomial_rows(tables, rules):
    data = json.loads((RESULTS/'polynomial_table.json').read_text())
    res = {}
    for row in data['rows']:
        if row['type'] != 'additional':
            continue
        pr = row['proof']
        a, b, p = Q(pr['a']), Q(pr['b']), Q(pr['old_lower'])
        c = classify(rules, 'lp', 'complex', a, b, p)
        res[c['status']] = res.get(c['status'], 0) + 1
        if c['status'] == 'mismatch':
            fail(f'polynomial_table row {row["id"]}: old_lower {pr["old_lower"]} unsupported')
        pp = preferred(c['printed'])
        if pp:
            book(tables, pp, fmt(p),
                 f'computations/core/results/polynomial_table.json row {row["id"]} ([{fmt(a)},{fmt(b)}], old_lower)')
    return dict(additional_rows=sum(res.values()), statuses=res)


def module_constants(path, names):
    tree = ast.parse(source(path))
    ns = {}
    for node in tree.body:
        if isinstance(node, ast.Assign) and len(node.targets) == 1 and isinstance(node.targets[0], ast.Name):
            if node.targets[0].id in names:
                ns[node.targets[0].id] = eval(compile(ast.Expression(node.value), str(path), 'eval'),
                                              {'Q': Q, '__builtins__': {}}, dict(ns))
    return ns


def small_exception(tables):
    p = CODE/'small_exception_tables.py'
    ns = module_constants(p, ['L', 'K', 'C1', 'C2', 'ALPHA', 'EPS', 'TABLE_PIECE', 'ALPHA_END'])
    (a, b), m2, m2p, _ = ns['TABLE_PIECE']
    where = 'computations/core/code/small_exception_tables.py TABLE_PIECE'
    pv5 = printed_value(tables, 'H Table 5', '0.10', 2)
    pv2 = printed_value(tables, 'H Table 2', '0.10', 2)
    st5 = compare_lower(m2, pv5, eps=True)
    st2 = compare_lower(m2p, pv2, eps=True)
    scope_ok = b <= Q('0.10')
    add_use(tables, 'H Table 5', '0.10', pv5, fmt(m2), st5 if scope_ok else 'mismatch', where,
            note=f'2.83 − ε with ε = {fmt(ns["EPS"])}; piece [{fmt(a)}, {fmt(b)}] with b ≤ 0.10; type rr (λ1 ≤ 0.44)')
    add_use(tables, 'H Table 2', '0.10', pv2, fmt(m2p), st2 if scope_ok else 'mismatch', where,
            note=f'4.96 − ε with ε = {fmt(ns["EPS"])}; piece [{fmt(a)}, {fmt(b)}] with b ≤ 0.10; type rr')
    alpha = ns['ALPHA']
    out = dict(constants={k: fmt(v) if isinstance(v, Q) else None for k, v in ns.items() if k != 'TABLE_PIECE'},
               table_piece=[fmt(a), fmt(b), fmt(m2), fmt(m2p)])
    out['alpha'] = dict(used=fmt(alpha), printed=['(12/11 − ε) log(1/λ1) (H Lemma 8.8)', '(2 − ε) log(1/λ1) (H Lemma 8.4)'],
                        status='safe' if alpha < Q(12, 11) and alpha < 2 else 'mismatch',
                        scope=f'piece [u0, {fmt(ns["ALPHA_END"])}] ⊂ (0, 0.2] (Lemma 8.4 needs λ1 ≤ 0.2); fixed u0 > 0 '
                              '(H p. 48: not proved for extremely small λ1)')
    if out['alpha']['status'] != 'safe' or ns['ALPHA_END'] > Q('0.2'):
        fail('small_exception_tables: alpha or its range')
    w = 'computations/core/code/small_exception_tables.py ALPHA'
    add_use(tables, 'H Lemma 8.8', 'log coefficient', '12/11 − ε', fmt(alpha), out['alpha']['status'], w,
            note=out['alpha']['scope'])
    add_use(tables, 'H Lemma 8.4', 'log coefficient', '2 − ε', fmt(alpha), out['alpha']['status'], w,
            note=out['alpha']['scope'])
    # the density and per-character formulas against H Lemma 11.1 / X (5.18) and H Lemma 13.3
    text = source(p)
    formulas = [(r'aa = Q\(4, 3\)\+6\*C1\+2\*C2', '4φ + 6c1 + 2c2 with φ = 1/3 (H (11.3), X (5.18))'),
                (r'bb = Q\(2, 3\)\+4\*C1', '2φ + 4c1 with φ = 1/3'),
                (r'V = \(Q\(2, 3\)\+2\*C1\+C2\)/\(4\*C1\*C2\)', '(2φ + 2c1 + c2)/(4c1c2) with φ = 1/3'),
                (r'B = I\(Q\(1, 3\)\)\*\(1-e\)/\(2\*m\)\+\(2\*ki\*m-1\+e\)/\(2\*m\*m\)',
                 '(φ/2)(1 − e^{−2Kλ})/λ + (2Kλ − 1 + e^{−2Kλ})/(2λ²) with φ = 1/3 (H (13.3))'),
                (r'first = \(ki\*ki\+ki/4\)', 'K² + φK with φ = 1/4, the λ → 0 limit of H (13.3)')]
    out['formulas'] = [dict(pattern=pat, printed=m, found=bool(re.search(pat, text))) for pat, m in formulas]
    for f, statement in zip(out['formulas'], ['H Lemma 11.1']*3 + ['H Lemma 13.3']*2):
        add_use(tables, statement, 'formula', f['printed'], f['pattern'].replace('\\', ''),
                'equal' if f['found'] else 'mismatch', 'computations/core/code/small_exception_tables.py')
    c1, c2 = ns['C1'], ns['C2']
    phi = Q(1, 3)
    out['derived'] = dict(a_d=fmt(4*phi+6*c1+2*c2), b_d=fmt(2*phi+4*c1), V_d=fmt((2*phi+2*c1+c2)/(4*c1*c2)))
    return out, ns


# ---------------------------------------------------------------------------------------------
# The paper
# ---------------------------------------------------------------------------------------------

def paper_parents(cover_v5):
    tex = source(SECTIONS/'07-location.tex')
    end = tex.index(r'\label{tab:parents}')
    start = tex.rindex(r'\begin{table}', 0, end)
    body = tex[tex.index(r'\midrule', start, end):tex.index(r'\bottomrule', start, end)]
    rx = re.compile(r'\$\\mathrm\{(rr|rc|complex)\}\$ & \$\[([\d.]+),([\d.]+)\]\$ & \$([\d.]+)\$ & \$([\d.]+)\$')
    left, right = [], []
    for line in body.splitlines():
        found = rx.findall(line)
        if found:
            left.append(found[0])
            right.extend(found[1:])
    rows_ = [(k, Q(a), Q(b), Q(p), Q(r)) for k, a, b, p, r in left + right]
    code = [(k, Q(a), Q(b), Q(p), Q(r)) for k, a, b, p, r in cover_v5.PARENTS]
    diffs = [dict(index=i, paper=[x[0]] + [fmt(v) for v in x[1:]], code=[y[0]] + [fmt(v) for v in y[1:]])
             for i, (x, y) in enumerate(zip(rows_, code)) if x != y]
    equal = rows_ == code
    if not equal:
        fail(f'paper tab:parents differs from cover_v5.PARENTS: {diffs[:5]} (lengths {len(rows_)}, {len(code)})')
    counts = {k: sum(1 for x in rows_ if x[0] == k) for k in TYPES}
    caption = flat(tex[end-600:end])
    cap_ok = all(s in caption for s in ('the $33$ real-first-zero rows', 'the $13$ real-character/nonreal-zero rows',
                                        '$12$ nonreal-character rows'))
    if not cap_ok or counts != {'rr': 33, 'rc': 13, 'complex': 12}:
        fail('paper tab:parents caption counts')
    return dict(rows=len(rows_), equal_to_code=equal, counts=counts, caption_counts_ok=cap_ok, differences=diffs)


def judge(how, printed, used):
    """Compare a number in the paper (or code) with the printed one.

    lower: lower bounds, equal or safe (smaller); exact: must be equal (parameters, ranges);
    below: strictly below a printed 'c - eps' (safe); eps: c - eps restated (equal) or c minus an
    explicit eps (safe); trunc: the paper's and the printed decimals are truncations of the value.
    """
    if how == 'lower':
        return compare_lower(used, printed)
    if how == 'exact':
        same = printed.replace(' ', '') == used.replace(' ', '')
        try:
            same = same or Q(printed) == Q(used)
        except ValueError:
            pass
        return 'equal' if same else 'mismatch'
    if how == 'below':
        return 'safe' if Q(used) < Q(printed) else 'mismatch'
    if how == 'eps':
        return 'equal' if Q(used) == Q(printed) else compare_lower(used, printed, eps=True)
    if how == 'trunc':
        value, digits = printed
        ok = all(str(d).startswith(t) for d, t in ((value, used), (value, digits)))
        return 'equal' if ok else 'mismatch'
    raise ValueError(how)


def decimal(x, n=8):
    """x truncated to n decimals, as a string."""
    x = Q(x)
    digits = str(x.numerator*10**n//x.denominator).rjust(n+1, '0')
    return digits[:-n] + '.' + digits[-n:]


def paper_statements(tables):
    loc = flat(source(SECTIONS/'07-location.tex'))
    ext = flat(source(SECTIONS/'12-exteriors.tex'))
    T = {k: v['rows'] for k, v in tables.items()}
    h4, h7, x2p, x3, x8, x10 = T['H Table 4'], T['H Table 7'], T["X Table 2'"], T['X Table 3'], T['X Table 8'], T['X Table 10']
    pv = lambda table, key, col: printed_value(tables, table, key, col)
    f0 = lambda g: Q(16)*Q(g)**5/15  # f_gamma(0): paper (eq:ftest) and X (3.17), at t = 0
    c1, c2, phi = Q('0.057'), Q('0.1554'), Q(1, 3)
    # (where, text, tex substring, [(printed source, row, printed value, value in the paper, comparison)], refs)
    items = [
        ('inp:rrtables(a)', loc, r"the $24$ pairs $(t,c)$ from $(0.3,\,2.293)$ to $(1.294,\,1.294)$",
         [('H Table 4', 'number of rows', str(len(h4)), '24', 'exact'), ('H Table 4', h4[0][0], h4[0][1], '2.293', 'lower'),
          ('H Table 4', h4[-1][0], h4[-1][1], '1.294', 'lower')], []),
        ('inp:rrtables(a)', loc, r"For a real $\rho'$ this follows from $\lambda'\ge2.427$ (Lemma~8.2)",
         [('H Lemma 8.2', 'constant', '2.427', '2.427', 'lower')], ['H Lemma 8.2']),
        ('inp:rrtables(b)', loc, r"\lambda'\ge(2-\eps)\log\lambda_1^{-1}$ if $\lambda_1\le0.2$ and $q\ge q(\eps)$; and "
                                 r"$\lambda'\ge\max\bigl(\frac32\log\lambda_1^{-1},1.294\bigr)$ for every $\lambda_1$",
         [('H Lemma 8.4', 'λ1 ≤', '0.2', '0.2', 'exact'), ('H Lemma 8.4', 'log coefficient', '2', '2', 'exact'),
          ('H Lemma 8.4', 'second log coefficient', '3/2', '3/2', 'exact'),
          ('H Lemma 8.4', 'constant', '1.294', '1.294', 'lower')], ['H Lemma 8.4']),
        ('inp:rrtables(c)', loc, r"the $16$ pairs $(t,c)$ from $(0.12,\,2.56)$ to $(0.745,\,0.745)$ of the table; these "
                                 r"hold whether or not $\chi_2^4=\chi_0$ (the row $t=0.10$ is not used)",
         [('H Table 7', 'number of rows other than 0.10', str(len(h7)-1), '16', 'exact'),
          ('H Table 7', h7[1][0], h7[1][2], '2.56', 'lower'), ('H Table 7', h7[-1][0], h7[-1][2], '0.745', 'lower')], []),
        ('inp:rrtables(d)', loc, r"\lambda_2\ge\max\bigl((\frac{12}{11}-\eps)\log\lambda_1^{-1},0.745\bigr)$ for $q\ge q(\eps)$.",
         [('H Lemma 8.8', 'log coefficient', '12/11', '12/11', 'exact'),
          ('H Lemma 8.8', 'constant', '0.745', '0.745', 'lower')], ['H Lemma 8.8']),
        ('inp:complextables(a)', loc, r"Table~2$'$, p.~62]{Xylouris2011nullstellen}. If $\lambda_1\le t$ then $\lambda'>c$, "
                                      r"for the pairs $(0.46,1.85),\dots,(0.827,0.827)$",
         [("X Table 2'", x2p[0][0], x2p[0][1], '1.85', 'lower'), ("X Table 2'", x2p[-1][0], x2p[-1][1], '0.827', 'lower')], []),
        ('inp:complextables(b)', loc, r"Table~3, p.~45]{Xylouris2011nullstellen}. If $\ord\chi_1\in\{2,3,4\}$ and "
                                      r"$\lambda_1\le t$, then $\lambda'>c$, for the pairs $(0.38,2.53),\dots,(1.099,1.099)$; "
                                      r"in particular $\lambda_1\le0.86$ implies $\lambda'>1.35$",
         [('X Table 3', x3[0][0], x3[0][1], '2.53', 'lower'), ('X Table 3', x3[-1][0], x3[-1][1], '1.099', 'lower'),
          ('X Table 3', '0.86', pv('X Table 3', '0.86', 1), '1.35', 'lower')], []),
        ('inp:complextables(c)', loc, r"Tables~6 and~7, p.~53]{Xylouris2011nullstellen}. If $\lambda_1\le t$ then "
                                      r"$\lambda_2>c$; Table~6 concerns a real $\chi_1$ (Fall~7), Table~7 all cases",
         [], ['X Table 6 caption (χ1 reell und ρ1 komplex, Fall 7), p. 53', 'X Table 7 caption (alle Fälle), p. 53']),
        ('inp:complextables(d)', loc, r"$\lambda_2\ge0.702$ always, and $\lambda_1\le0.70$ implies $\lambda_2\ge0.704$",
         [('H Lemma 9.4', 'constant', '0.702', '0.702', 'lower'),
          ('H Table 10', '0.70', pv('H Table 10', '0.70', 1), '0.704', 'lower')], ['H Lemma 9.4']),
        ('inp:lambda3(a)', loc, r"$\lambda_3\ge\frac67-\eps$; we use $\lambda_3>0.857$",
         [('H Lemma 10.3', 'constant', '6/7', '6/7', 'exact'), ('H Lemma 10.3', 'constant used', '6/7', '0.857', 'below')],
         ['H Lemma 10.3']),
        ('inp:lambda3(b)', loc, r"column ``alle F\"alle'', p.~55]{Xylouris2011nullstellen}. If $\chi_1$ or $\rho_1$ is "
                                r"nonreal and $\lambda_1\le t$, then $\lambda_3>c$, for $(t,c)=(0.52,1.320)$, $(0.54,1.243)$, "
                                r"$(0.56,1.160)$, $(0.58,1.079)$, $(0.60,1.001)$, $(0.62,0.933)$",
         [('X Table 8', r[0], r[1], u, 'lower') for r, u in zip(x8, ['1.320', '1.243', '1.160', '1.079', '1.001', '0.933'])],
         []),
        ('inp:lambda3(c)', loc, r"Lemma~4.4 and Table~10, p.~55]{Xylouris2011nullstellen}. If $\chi_1$ and $\rho_1$ are "
                                r"real, then $\lambda_1\in[0.44,0.60]$, $[0.60,0.70]$, $[0.70,0.80]$ imply $\lambda_3>1.176$, "
                                r"$1.055$, $0.952$",
         [('X Table 10', f'[{r[0]}, {r[1]}]', r[2], u, 'lower') for r, u in zip(x10, ['1.176', '1.055', '0.952'])], []),
        ('inp:lambda3(d)', loc, r"(4.28)--(4.29), pp.~56--57]{Xylouris2011nullstellen}. Let $\chi_1$ be nonreal and "
                                r"$\lambda_1\in[0.44,0.85]$, and let $f$ be the test function \eqref{eq:ftest} with "
                                r"$\gamma=\frac54$. Then \[ 0\le F(-\lambda_1)-F(\lambda_3-\lambda_1)-F(\lambda_2-\lambda_1)"
                                r"-F(0)+\tfrac76f(0)+\eps, \] provided that $\sup_{y\in\RR}\Re\{F(-\lambda_1+iy)-2F(iy)\}"
                                r"\le\frac16f(0)$",
         [('X (4.28)', 'λ1 range', '[0.44, 0.85]', '[0.44, 0.85]', 'exact'), ('X (4.28)', 'coefficient', '7/6', '7/6', 'exact'),
          ('X (4.29)', 'γ', '1.25', '5/4', 'exact'), ('X (4.29)', 'bound', '1/6', '1/6', 'exact')],
         ['X (4.28)', 'X (4.29)']),
        ('inp:lambda3(e)', loc, r"(4.31) and (4.34), pp.~58--59]{Xylouris2011nullstellen}. Let $\chi_1$ and $\rho_1$ be real, "
                                r"$\lambda_1\in[0.44,0.80]$ and $\lambda_2\in[0.44,1.176]$, and let $f$ be \eqref{eq:ftest} with "
                                r"$\gamma=1.04$. Then \[ 0\le F(-\lambda_2)-F(\lambda_3-\lambda_2)-F(0)-F(\lambda_1-\lambda_2)"
                                r"+\tfrac98f(0)+\eps, \] provided that $\sup_{t\in\RR}\Re\{F(-\lambda_2+it)-F(\lambda_1-\lambda_2+it)"
                                r"-F(it)\}\le\frac5{48}f(0)$ on this box",
         [('X (4.34)', 'λ1 range', '[0.44, 0.80]', '[0.44, 0.80]', 'exact'),
          ('X (4.34)', 'λ2 range', '[0.44, 1.176]', '[0.44, 1.176]', 'exact'),
          ('X (4.34)', 'γ', '1.04', '1.04', 'exact'), ('X (4.31)', 'coefficient', '9/8', '9/8', 'exact'),
          ('X (4.34)', 'bound', '5/48', '5/48', 'exact')], ['X (4.31)', 'X (4.34)']),
        ('after inp:lambda3', loc, r"the supremum is at most $0.00335$, while $\frac16f(0)=0.5425\ldots$",
         [('X (4.29)', 'f(0)/6 at γ = 5/4 (printed "0.54 . . .")', (decimal(f0(Q(5, 4))/6), '0.54'), '0.5425', 'trunc')],
         ['X (4.29)']),
        ('after inp:lambda3', loc, r"he states that the supremum is below $0.10$, while $\frac5{48}f(0)=0.1351\ldots$",
         [('X (4.34)', 'supremum bound stated by X', '0.10', '0.10', 'exact'),
          ('X (4.34)', '(5/48) f(0) at γ = 1.04 (printed "0.13 . . .")', (decimal(f0(Q('1.04'))*5/48), '0.13'), '0.1351',
           'trunc')], ['X (4.34)']),
        ('prop:firstlower', loc, r"\lambda_1>0.440\quad\text{if }\chi_1\text{ is nonreal},\qquad \lambda_1>0.628\quad\text{if }"
                                 r"\chi_1\text{ is real and }\rho_1\text{ is nonreal}.",
         [('X Lemma 4.5', 'ord ≥ 3 (minimum)', min((v for o, v in T['X Lemma 4.5'] if o != '=2'), key=Q), '0.440', 'lower'),
          ('X Lemma 4.5', 'ord = 2', dict(T['X Lemma 4.5'])['=2'], '0.628', 'lower')], []),
        ('after prop:firstlower', loc, r"Xylouris's lemma gives $\lambda_1>0.440$, $0.493$, $0.478$, $0.498$ and $0.628$ "
                                       r"for characters of order $\ge6$, $=5$, $=4$, $=3$ and $=2$ respectively",
         [('X Lemma 4.5', o, v, u, 'exact') for (o, v), u in zip(T['X Lemma 4.5'], ['0.440', '0.493', '0.478', '0.498', '0.628'])],
         []),
        ('Printed tables (subsec:locconventions)', loc, (r"$1.43904$ against $1.439$", r"$2.01015$ against $2.01$",
                                                         r"$1.00036$ against $1.00$"),
         [('H Table 4', '1.05', pv('H Table 4', '1.05', 1), '1.439', 'exact'),
          ('H Table 7', '0.20', pv('H Table 7', '0.20', 2), '2.01', 'exact'),
          ('H Table 7', '0.55', pv('H Table 7', '0.55', 2), '1.00', 'exact')], []),
        ('Printed tables (subsec:locconventions)', loc, r"Heath-Brown's Table~3, which gives $\lambda'\ge2.43$ for "
                                                        r"$\lambda_1\le0.30$",
         [('H Table 3', '0.30', pv('H Table 3', '0.30', 2), '2.43', 'exact')], []),
        ('Printed tables (subsec:locconventions)', loc, r"footnote~2 on p.~45]{Xylouris2011nullstellen}", [],
         ['H Lemma 9.4 (X footnote 2, p. 45)', 'X conventions']),
        ('Printed tables (subsec:locconventions)', loc, (r"$0.857<\frac67$ in \cref{inp:lambda3}",
                                                         r"$1.09<\frac{12}{11}$ and $\eps=0.001$ in \cref{sec:exteriors}"),
         [('H Lemma 10.3', 'constant used', '6/7', '0.857', 'below'),
          ('H Lemma 8.8', 'log coefficient used', '12/11', '1.09', 'below')], []),
        ('after prop:polyrows', loc, r"$p=0.96$, $0.93$, $0.91$, $0.89$, $0.86$, $0.84$, $0.83$ on the cells in "
                                     r"$[0.68,0.70]$, $[0.70,0.72]$, \dots, $[0.80,0.82]$, $p=0.827$ on $[0.82,0.8275]$",
         [("X Table 2'", t, pv("X Table 2'", t, 1), u, 'lower')
          for t, u in zip(['0.70', '0.72', '0.74', '0.76', '0.78', '0.80', '0.82', '0.827'],
                          ['0.96', '0.93', '0.91', '0.89', '0.86', '0.84', '0.83', '0.827'])], []),
        ('after prop:polyrows', loc, r"For $\chi_1$ of order $3$ or $4$, \cref{inp:complextables}(b) gives $\lambda'>1.35$ "
                                     r"whenever $\lambda_1\le0.86$",
         [('X Table 3', '0.86', pv('X Table 3', '0.86', 1), '1.35', 'lower')], []),
        ('sec:exteriors', ext, r"tables, which hold for all $\lambda_1\le0.10$ bounded below by a fixed positive constant "
                               r"\cite[\S8, Table~2 and Table~5]{HeathBrown1992zero} (see the remark after \cref{inp:rrtables}; "
                               r"we use them for $\lambda_1\ge0.08$): "
                               r"if $\chi_1$ and $\rho_1$ are real and $\lambda_1\le0.10$, then $\lambda'\ge4.96-\eps$ and "
                               r"$\lambda_2\ge2.83-\eps$ for $q\ge q(\eps)$",
         [('H Table 2', '0.10', pv('H Table 2', '0.10', 2), '4.96', 'eps'),
          ('H Table 5', '0.10', pv('H Table 5', '0.10', 2), '2.83', 'eps')], []),
        ('sec:exteriors', ext, (r"$\eps=0.001$", r"Table~5 is stated under $\lambda_2\le\lambda'$",
                                r"$\lambda'\ge4.959>2.83$"), [],
         ['H Table 5 meaning (H p. 45: the condition λ2 ≤ λ′ is redundant by Table 2)', 'cross-check H Table 5 vs H Table 2']),
        ('sec:exteriors', ext, r"$\alpha=1.09<\frac{12}{11}$",
         [('H Lemma 8.8', 'log coefficient used', '12/11', '1.09', 'below')], ['H Lemma 8.8']),
        ('sec:exteriors', ext, r"$m_2=2.829$ and $m_2'=4.959$",
         [('H Table 5', '0.10', pv('H Table 5', '0.10', 2), '2.829', 'eps'),
          ('H Table 2', '0.10', pv('H Table 2', '0.10', 2), '4.959', 'eps')], []),
        ('inp:hb132', ext, r"Let $L'>2K+3$", [('H Lemma 13.2', 'hypothesis', 'L>2K+3', "L>2K+3", 'exact')],
         ['H Lemma 13.2']),
        ('inp:hb133', ext, r"\mathcal B_\phi(\lambda)=\frac\phi2\,\frac{1-e^{-2K\lambda}}\lambda+\frac{2K\lambda-1+e^{-2K\lambda}}"
                           r"{2\lambda^2}", [], ['H Lemma 13.3']),
        ('sec:exteriors', ext, r"with limit $\phi K+K^2$ as $\lambda\to0$", [], ['H Lemma 13.3']),
        ('inp:hb111', ext, r"\sum_\chi\frac{\lambda(\chi)}{e^{(4\phi+6c_1+2c_2)\lambda(\chi)}-e^{(2\phi+4c_1)\lambda(\chi)}}"
                           r"\le\frac{2\phi+2c_1+c_2}{4c_1c_2}+\eps", [], ['H Lemma 11.1', 'X (5.18)']),
        ('inp:hb111', ext, r"($\lambda_0=\frac13\log\log\LL$)", [], ['H Lemma 11.1']),
        ('Fixed data (sec:exteriors)', ext, r"a_d=\tfrac43+6c_1+2c_2=\tfrac{3724}{1875},\quad b_d=\tfrac23+4c_1=\tfrac{671}{750},"
                                            r"\quad V_d=\frac{2/3+2c_1+c_2}{4c_1c_2}=\frac{184750}{6993}",
         [('H Lemma 11.1', 'a_d = 4φ+6c1+2c2 (φ = 1/3, c1 = 0.057, c2 = 0.1554)', fmt(4*phi+6*c1+2*c2), '3724/1875', 'exact'),
          ('H Lemma 11.1', 'b_d = 2φ+4c1', fmt(2*phi+4*c1), '671/750', 'exact'),
          ('H Lemma 11.1', 'V_d = (2φ+2c1+c2)/(4c1c2)', fmt((2*phi+2*c1+c2)/(4*c1*c2)), '184750/6993', 'exact')],
         ['H Lemma 11.1', 'X (5.18)']),
    ]
    out = []
    for where, text, pattern, vals, refs in items:
        frags = pattern if isinstance(pattern, tuple) else (pattern,)
        missing = [f for f in frags if flat(f) not in text]
        found = not missing
        for f in missing:
            fail(f'paper {where}: text not found: {f[:90]}')
        checks = []
        for name, row, printed, used, how in vals:
            st = judge(how, printed, used)
            shown = printed[0] if how == 'trunc' else printed
            checks.append(dict(printed_in=name, row=row, printed=shown, paper=used, comparison=how, status=st))
            if row.startswith('number of rows'):
                if st == 'mismatch':
                    fail(f'paper {where}: {name} {row}: printed {printed}, paper {used}')
            else:
                add_use(tables, name, row, shown, used, st,
                        f'paper/sections/{"07-location" if text is loc else "12-exteriors"}.tex {where}')
        out.append(dict(where=where, tex=list(frags), found=found, values=checks, printed_statements=refs))
    return out


def observations(stmt_report):
    """Points where the paper's wording omits a printed qualification (none affects the proof)."""
    loc = flat(source(SECTIONS/'07-location.tex'))
    ext = flat(source(SECTIONS/'12-exteriors.tex'))
    caveat = any(x['found'] and 'extremely small' in x['text'] for x in stmt_report['H Lemma 8.8'])
    i = loc.find(flat(r"\cite[Lemma~8.4]{HeathBrown1992zero}. For every $\eps>0$"))
    b_text = loc[i:loc.find(r'\cite[Table~7 and Lemma~8.7]', i)] if i >= 0 else ''
    j = ext.find('which hold for all $\\lambda_1\\le0.10$')
    ext_text = ext[j:j+400] if j >= 0 else ''
    # the general remark after inp:rrtables (added 2026-10-01) states the caveat for (a)-(d)
    k = loc.find(r'\label{inp:rrtables}')
    general = k >= 0 and 'have not been proved for extremely small values' in loc[k:k+4000]
    ext_ok = 'bounded below by a fixed positive constant' in ext_text
    out = []
    if caveat and i >= 0 and 'extremely small' not in b_text and not (general and ext_ok):
        out.append(dict(
            where='paper/sections/07-location.tex, inp:rrtables(b) (also 12-exteriors.tex: the rows of H Tables 2 '
                  'and 5 "hold for all λ1 ≤ 0.10")' if j >= 0 and 'extremely small' not in ext_text else
                  'paper/sections/07-location.tex, inp:rrtables(b)',
            printed='H p. 48: "the estimates of this section have not been proved for extremely small values of λ1" '
                    '(all of H §8: Lemmas 8.1-8.8 and Tables 2-7)',
            paper='the caveat is attached to Lemma 8.8 in inp:rrtables(d) only; (b) states Lemma 8.4 without it',
            effect='none: the bounds are used for λ1 in fixed ranges away from 0 (λ1 ≥ 0.1 in the case tree, '
                   '[u_exc, 0.08] and [0.08, 0.1] in §12, with u_exc > 0 fixed)'))
    return out


def tool_info():
    v = subprocess.run(['pdftotext', '-v'], capture_output=True).stderr.decode().splitlines()[0]
    pdfs = {}
    for k, p in PDF.items():
        pdfs[k] = dict(path=rel(p), sha256=hashlib.sha256(p.read_bytes()).hexdigest())
    return dict(pdftotext=v, python=platform.python_version()), pdfs


def count(uses):
    c = {'uses': len(uses), 'equal': 0, 'safe': 0, 'trivial': 0, 'mismatch': 0}
    for u in uses:
        c[u['status']] += 1
    return c


def summarize(tables, statements):
    out = {}
    for name, t in tables.items():
        t['counts'] = count(t['uses'])
        out[name] = dict(kind='table', source=t['source'], page=t['page'], rows=t['rows_parsed'],
                         transcription_ok=t['parse_equals_transcription']
                         and t['rows_matched_in_text'] == t['rows_transcribed'], **t['counts'])
    def where(name):
        snips = statements.get(name, [])
        return (name[0], snips[0]['page'] if snips else 0, name)
    for name in sorted(STATEMENT_USES, key=where):
        snips = statements.get(name, [])
        pages = [x['page'] for x in snips if x['source'] == name[0]]
        out[name] = dict(kind='statement', source=name[0], page=pages[0] if pages else None, rows=None,
                         transcription_ok=all(x['found'] for x in snips) if snips else None,
                         **count(STATEMENT_USES[name]))
    return out


def main():
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--out', type=Path, default=OUT)
    args = ap.parse_args()
    tools, pdfs = tool_info()
    tables = check_tables()
    statements = check_statements()
    errata = check_errata()
    fraction = lemma_103_fraction()
    xchecks, flags = cross_checks(tables)
    rules = build_rules(tables, flags)
    code, case_cover, cover_v4, cover_v5 = code_tables(tables, rules)
    parents = parents_check(tables, rules, case_cover, cover_v5)
    cells = source_cover_check(rules)
    third = third_family(tables, rules)
    others = other_code(tables)
    poly = polynomial_rows(tables, rules)
    small, _ = small_exception(tables)
    tex_parents = paper_parents(cover_v5)
    tex = paper_statements(tables)
    obs = observations(statements)
    summary = summarize(tables, statements)
    every = [(k, u) for k, t in tables.items() for u in t['uses']] + \
            [(k, u) for k, v in STATEMENT_USES.items() for u in v]
    safe = [dict(table=k, **u) for k, u in every if u['status'] == 'safe']
    mism = [dict(table=k, **u) for k, u in every if u['status'] == 'mismatch']
    totals = count([u for _, u in every])
    report = dict(
        status='PASS' if not FAILURES else 'FAIL',
        failures=FAILURES,
        purpose='Transcription and scope check of the printed zero-location inputs (H 1992, X 2011) used by the proof',
        tools=tools, sources=pdfs,
        conventions=['pdftotext extracts the prime of λ′ as 0: λ0 in the page text is λ′ (the rendered pages read '
                     '"λ′", e.g. "Table 4: λ′ for real χ1 and ρ1")',
                     'built-up fractions are extracted with numerator and denominator adjacent ("67" = 6/7, "13" = 1/3) '
                     'or on neighbouring lines; the statements are matched in this extracted form',
                     "in a transcription, an empty cell is null; '-' is a printed dash",
                     "status: 'equal' = the printed value; 'safe' = weaker than the printed value (smaller lower bound, "
                     "explicit −ε, or a larger checked box); 'trivial' = not a printed number (λ′, λ2 ≥ λ1 ≥ A); "
                     "'mismatch' = neither"],
        summary=dict(per_source=summary, all_uses=totals, safe_direction=len(safe), mismatches=len(mism),
                     statements_matched=f"{sum(x['found'] for v in statements.values() for x in v)}"
                                        f"/{sum(len(v) for v in statements.values())}",
                     cross_checks=f"{sum(x['passed'] for x in xchecks)}/{len(xchecks)} passed",
                     parents=parents['statuses'], source_cover=cells['statuses'],
                     polynomial_rows=poly['statuses'], third_bound_cells_out_of_scope=third['out_of_scope'],
                     paper_tab_parents_equal_to_code=tex_parents['equal_to_code'],
                     paper_statements_found=f"{sum(x['found'] for x in tex)}/{len(tex)}"),
        tables=tables, statements=statements, statement_uses=STATEMENT_USES, lemma_10_3_fraction=fraction,
        cross_checks=xchecks, rule_flags=flags,
        code=dict(tables=code, third_family=third, other=others, small_exception=small, polynomial_rows=poly),
        parents=parents, source_cover=cells,
        paper=dict(tab_parents=tex_parents, statements=tex),
        safe_direction=safe, mismatches=mism, observations=obs, source_errata_not_used=errata,
        not_checked=['analytic content of the printed lemmas and tables',
                     'the recomputation of printed roots (H Tables 2, 4, 5, 7) and of the side conditions (8.6), (8.8) '
                     'claimed in paper §7 and §12 (a separate floating-point computation, not a transcription check)',
                     'H 1990 Corollary 1 (inp:siegel): the local copy is a scan whose text layer lacks the displayed formulas'])
    args.out.write_text(json.dumps(report, indent=1, ensure_ascii=False) + '\n')
    print(f"printed_tables_check: {report['status']}  ({tools['pdftotext']})")
    print(f"  {'source':<14} {'page':>4} {'rows':>4} {'text':>4} {'uses':>4} {'equal':>5} {'safe':>4} {'triv':>4} {'mism':>4}")
    for name, x in summary.items():
        ok = '-' if x['transcription_ok'] is None else 'ok' if x['transcription_ok'] else 'FAIL'
        print(f"  {name:<14} {x['page'] or '':>4} {x['rows'] if x['rows'] is not None else '':>4} {ok:>4} "
              f"{x['uses']:>4} {x['equal']:>5} {x['safe']:>4} {x['trivial']:>4} {x['mismatch']:>4}")
    print(f"  all uses: {totals}")
    print(f"  statements matched on the pages: {report['summary']['statements_matched']}; "
          f"H Lemma 10.3 fraction 6/7 stacked: {fraction['stacked_fraction']}")
    print(f"  cross-checks: {report['summary']['cross_checks']}")
    print(f"  parent rows (58 x lambda', lambda_2): {parents['statuses']}")
    print(f"  source cover ({cells['records']} records): lp {cells['statuses']['lp']}, "
          f"source_l2 {cells['statuses']['source_l2']}")
    print(f"  polynomial rows (parent bound of {poly['additional_rows']} lambda' rows): {poly['statuses']}")
    print(f"  third_bound guards simulated on {third['cells_simulated']} cells: rows fired {third['rows_fired']}, "
          f"out of scope {third['out_of_scope']}")
    print(f"  paper tab:parents equal to cover_v5.PARENTS: {tex_parents['equal_to_code']}; "
          f"paper statements found: {report['summary']['paper_statements_found']}")
    print(f"  safe-direction differences ({len(safe)}):")
    for x in safe:
        print(f"    {x['table']} {x['row']}: printed {x['printed']}, used {x['used']}  [{x['where']}]")
    print(f"  mismatches: {len(mism)}")
    for o in obs:
        print(f"  observation: {o['where']}: {o['paper']} ({o['effect']})")
    for f in FAILURES:
        print(f'  FAILURE: {f}')
    print(f'  report: {args.out}')
    return 0 if not FAILURES else 1


if __name__ == '__main__':
    sys.exit(main())
