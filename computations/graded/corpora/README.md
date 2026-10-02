# Certificate corpora of the graded-near proof

This directory holds the **stored certificates** of the finite part of the graded-near proof
([research/PROOF.md](../../../research/PROOF.md) §§7–8), one subdirectory per target exponent
`L`. At present there is only `3.99/`.

The certificates are the evidence for the finite part of the 3.99 claim. They are the only part
that cannot be rebuilt from the repository's code. The leaf LPs themselves are not stored:
`graded_verify.py` regenerates every leaf from the verified 4.30 source trees and checks the
stored certificate against it. Every check of the finite part verifies these exact files:
* the replay (`computations/graded/verification_3.99.json`);
* the independent checker and the mutation test
  ([independent checks](../../../research/notes/independent-checks-2026-09-29.md));
* the native Lean checkers (`computations/graded/lean_runs/`).

`computations/graded/candidate_3.99.json` records their SHA-256 hashes.

**Regenerating them is not a substitute.** Re-running the certification (`graded_batch.py`)
would produce a different, equally checkable certificate set. The LP solves and the search are
not bit-reproducible, and the hardest roots needed manual repairs. The recorded hashes and every
check refer to these files.

## Files of `3.99/`

| File | Content | Roots | Leaves | Boxes | Bytes | In git as |
| --- | --- | --- | --- | --- | --- | --- |
| `inside.jsonl.gz` | The LP leaves of the 2,768 inside source trees | 2,768 | 2,913 | 3,067,092 | 298,536,973 | 4 parts |
| `nodes.jsonl.gz` | The identities nodes of 199 of those roots, replaced by the regular model | 199 | 233 | 1,042,363 | 159,624,716 | 2 parts |
| `outside.jsonl.gz` | The outside-buffer leaves of the 1,685 outside source trees | 1,685 | 1,642 | 87,424 | 8,626,435 | whole |

In total there are 4,453 roots, 4,788 leaves and 4,196,879 boxes. The largest certified value is
.99999982. The hashes are those recorded in `candidate_3.99.json`, and `SHA256SUMS` holds them:

```
539362a03e7b330dad03b33d6b5037871cfcbbf7b0973e7976fccf12509fe63c  inside.jsonl.gz
b715ac735b6976da17a2671667ecfdf07c3f19b8ab74ae5f0533dbcf6b2a6cfc  nodes.jsonl.gz
a53d4d5793f71c92647a7f22022110bdc8135cbda1f2575d1dc0c1f487f5ac1d  outside.jsonl.gz
```

## How they are stored in git: parts

GitHub rejects files over 100 MB. The two large files are therefore committed as parts, made
with GNU coreutils on 2026-09-29:

```bash
split -b 90M -d -a 2 inside.jsonl.gz inside.jsonl.gz.part-   # parts 00-02 of 94,371,840 bytes, 03 the rest
split -b 90M -d -a 2 nodes.jsonl.gz  nodes.jsonl.gz.part-    # parts 00-01
```

The parts are consecutive byte ranges. Concatenating them in suffix order (`00`, `01`, …)
gives the original file byte for byte. `outside.jsonl.gz` is small and committed whole.
`SHA256SUMS.parts` hashes the parts.

The rebuilt `inside.jsonl.gz` and `nodes.jsonl.gz` are ignored by git (see the repository's
`.gitignore`), so they cannot be committed by accident.

## Rebuild and check

```bash
computations/graded/corpora/assemble.sh
```

The script checks the parts against `SHA256SUMS.parts`, rebuilds `inside.jsonl.gz` and
`nodes.jsonl.gz`, and checks all three files against `SHA256SUMS`. By hand, in `3.99/`:

```bash
cat inside.jsonl.gz.part-?? > inside.jsonl.gz
cat nodes.jsonl.gz.part-??  > nodes.jsonl.gz
sha256sum -c SHA256SUMS
```

Then replay, or run the Lean checkers (see [the graded README](../README.md) and
[lean-graded](../../../README.md)):

```bash
python3 computations/graded/graded_verify.py --L 3.99 \
    --inside computations/graded/corpora/3.99/inside.jsonl.gz \
    --nodes computations/graded/corpora/3.99/nodes.jsonl.gz \
    --outside computations/graded/corpora/3.99/outside.jsonl.gz --workers 4
```

## Format

The files are gzip-compressed JSON lines, one line per root, in root order. `graded_pack.py`
produced them from the per-root result files of the certification runs. It removed the solver
logs, and a later directory overrides an earlier one for a re-certified root. The per-root files
are not in the repository.

**Root record.**

```json
{"L": "3.99", "id": 1083, "kind": "outside", "method": "graded-near", "status": "ok", "leaves": [...]}
```

* `id` is the root:
  * for `inside` and `nodes`, the index of the inside source spec (`endgame.specs()`, 0–2767);
  * for `outside`, the id of the outside source record (`certificate_io.load_outside('4.30')`).
* `leaves` has one entry per LP leaf (`inside`, `outside`) or identities node (`nodes`) of the
  root's source tree, in the order the replay meets them (`index`).

**Leaf entry.** Every entry has three fields:
* `index`;
* `boxes`, the number of boxes;
* `maximum`, the largest certified bound as a numerator over `S = 10¹⁶`. A certified leaf has
  `maximum < S`.

The rest takes one of two forms. The first is a certificate:
* `rows`: the near rows of the leaf LP (PROOF.md §§6.5–6.6), each
  `{"kind": "graded" | "family" | "shifted" | "old", "parameters": {...}}`;
* `tree`: a bisection tree over the rows' threshold boxes (PROOF.md §7). An internal node is
  `{"split": row, "mid": threshold, "children": [lower, upper]}`. A terminal node is
  `{"orders", "cases", "value"}` with:
  * `orders`: first (1) or second (2) order per row;
  * `cases`: one exact integer dual `{"Y", "V", "U", "P", "M", "Z"}` or `"excluded"` for each
    tangent case. The duals are `Y` for the far budget, `V` the count, `U` the hidden count,
    `P − M` the second-family equality and `Z` one per near row;
  * `value`: the proposer's bound, which the checker recomputes;
* `second_columns` (optional): `400` when the reserved second family is carried as LP columns on
  a 400-point grid (PROOF.md §7).

The second form is a split of the case into sub-cases, each with its own entry:
* `split` with `children`: second-zero splits at the listed `λ₂` points;
* `reserve` with three `children`: the reservation split at the given height;
* `mu_split`: the rc height split of the conjugate-pair term;
* `dz_split`: the height split of the first family's second zero.

The children of `split` and `reserve` carry their refinement `path`.

`graded_driver.verify_leaf` and `graded_cert.verify_tree` define the exact acceptance rules.
