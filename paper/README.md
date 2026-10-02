# Linnik's constant is at most 3.99 — the paper

* `linnik399.tex`, `sections/01-introduction.tex` … `sections/16-appendix.tex` and
  `references.bib` are the source. `linnik399.pdf` is built from it.
* `dist/linnik399.tex` is the same paper as one self-contained file, with the
  bibliography inlined and no `\input`. It is the version to upload. Its PDF,
  `dist/linnik399.pdf`, is built from that file alone.
* `tools/flatten.py` produces `dist/linnik399.tex` from the source. It also scans
  the result for constructs that execute code or write files (`\write18`,
  `\directlua`, `filecontents`, `\special`, `minted`, `pythontex`, `\openout`,
  embedded files and so on). There are none: the paper is typeset mathematics
  only, and it compiles with `-no-shell-escape`.

Build the source version:

```
pdflatex -no-shell-escape linnik399
bibtex linnik399
pdflatex -no-shell-escape linnik399
pdflatex -no-shell-escape linnik399
```

Then produce and build the single-file version:

```
python3 tools/flatten.py . dist/linnik399.tex
cd dist
pdflatex -no-shell-escape linnik399
pdflatex -no-shell-escape linnik399
pdflatex -no-shell-escape linnik399
```

The flattened file uses only standard LaTeX classes and packages: `amsart`, `geometry`, the
AMS packages, `mathtools`, `booktabs`, `longtable`, `array`, `enumitem`,
`microtype`, `xcolor`, `colortbl`, `tikz` (for the proof map, drawn in the source),
`hyperref`, `aliascnt` and `cleveref`.
The bibliography style command is retained because `amsart` also uses it to format
reference labels; the standalone build does not require BibTeX or a `.bib` file.

The certificates, the programs that generate and check them, and the reports of every
verification run are in [`computations/`](../computations/README.md). The reviews made while the
paper was written, and the verification notes, are in [`research/`](../research/README.md); the
editorial record of the paper is
[`research/notes/paper-2026-09-30.md`](../research/notes/paper-2026-09-30.md). The Lean
formalization of parts of the proof is at the root of this repository; see the
[repository README](../README.md).

## Adversarial reviews

* [First review, October 1–2, 2026](reviews/adversarial-review-2026-10-01.md):
  section-by-section review, full certificate replay, source-table checks, and
  the missing positivity assumption in Example 8.9(i).
* [Second review, October 2, 2026](reviews/adversarial-review-2026-10-02.md):
  further examination of the analytic arguments, independent numerical checks
  of all 37 fallback rows, and an exact check of the root cover against the paper.

Example 8.9(i) now explicitly assumes `v > 0` in both LaTeX versions and their
PDFs. The first report records the example before this correction. Neither
review identified an error invalidating the global bound; neither constitutes
a complete independent proof of it. The audit code and raw results the reports cite are in
[`computations/audit/`](../computations/audit/README.md), at the paths the reports give, and their
reproduction commands run from the repository root. The first report's remark that the paper
still called for a public archive of the certificates refers to the version it reviewed; the
certificates are in this repository and the paper's §14 now cites it.
