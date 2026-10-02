# Reviews made while writing the 3.99 paper (2026-09-30)

AI agents wrote all of these reviews during the writing of
[`paper/linnik399.tex`](../../../paper/linnik399.tex); none is a human referee
report. Line numbers refer to drafts of the paper, which changed while the
reviews ran. What each review found, and how it was resolved, is summarized in
[notes/paper-2026-09-30.md](../../notes/paper-2026-09-30.md).

**Component deep dives.** Each rederives one part of the proof from the printed
sources, the code and the Lean files, starting from commit `3e63657`.

| File | Scope |
| --- | --- |
| [deepdive-costs.md](deepdive-costs.md) | Notation, prime detection, the per-character costs and the error allowance (PROOF.md §§1–3) |
| [deepdive-near.md](deepdive-near.md) | The graded near lemma, its rows and the two-test row (PROOF.md §6) |
| [deepdive-location.md](deepdive-location.md) | Zero location, including the 1/108 conductor refinement (PROOF.md §4) |
| [deepdive-casetree.md](deepdive-casetree.md) | The case tree, the far budget and the exteriors |
| [deepdive-certs.md](deepdive-certs.md) | Leaf programs, certificates and the verification records |

**Referee reports on the draft.**

| File | Scope | Outcome |
| --- | --- | --- |
| [referee-A.md](referee-A.md) | §§1–5 and 8: analytic framework, costs, near lemma | No blocking error. The quantifier and order-of-constants items were fixed. |
| [referee-B.md](referee-B.md) | §§9–11: near rows, LP certificates, leaf model | No blocking error. Three major items, all fixed: the height range of the "no zero to the right" lemma, the separation `M` for `η''`, and the rounded data of the paired row. |
| [referee-C.md](referee-C.md) | §§6, 7, 11–13: far density, location, case tree, exteriors, assembly | No blocking error. Three major items, all fixed: the pointwise detection proposition, the domain of the λ′ rows, and the sub-case configuration sets. |
| [referee-D.md](referee-D.md) | Numbers, attributions and citations throughout | Numerical and attribution corrections, all applied. |
| [referee-E.md](referee-E.md) | Final consistency pass over the revised text and notation | No blocking error. One major item, fixed: the disc radius `δ₀` must be fixed for the tolerance `H₀ε₁/8` that Lemma `anchored` uses. The 26 minor items were applied, including HB Table 4's row 0.3 (which now rests on HB Table 3) and the fixed-term reservation count `n_E`. |

[references-log.md](references-log.md) records how each bibliography entry was
checked against an authoritative online record.
