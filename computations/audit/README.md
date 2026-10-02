# Audit programs

## The independent certificate checker (3.99)

These programs check the leaf certificates of the 3.99 proof without the replay's checking code
(`computations/graded/graded_cert.py`). They are described in
[research/notes/independent-checker-2026-09-30.md](../../research/notes/independent-checker-2026-09-30.md).

- `independent_cert_check.py`: an exact checker written from the paper's §10 alone
  (`paper/sections/10-lp.tex`). It reads the protocol of the Lean runner `certrun`
  (`{"name", "leaf", "tree"}` per line) and prints `name value boxes`, so the replay's exporter
  can drive it and compare every value and box count with the replay's:
  `computations/graded/graded_lean_export.py --kind inside|outside --roots all --jsonl --checker
  "python3 .../independent_cert_check.py --stats STATS.jsonl"`. It imports nothing from the
  repository, and uses only integer and `Fraction` arithmetic.
- `independent_cert_forgeries.py`: the negative test. It forges certificates in 51 ways and
  checks that the checker rejects each invalid one. It checks too that the checker accepts the
  controls: the same perturbations one unit short of breaking.
- `capture_leaves.py`: a wrapper for the exporter that saves the leaves it streams, as input for
  the forgery test.
- `independent_cert_3.99.json`: the results over the whole corpus and the large first-zero range.
  `independent_cert_forgeries_3.99.txt`: the log of the forgery test.

- `hb_tables_recompute.py`: recomputes Heath-Brown's Tables 4 and 7 (with the side conditions
  (8.6) and (8.8)) and rows .10 of his Tables 2 and 5, from his printed parameters
  (`hb_tables_recompute.json`).
- `printed_tables_check.py`: compares every printed number that the proof uses, in the code and
  in the paper, with the text of the source pages and with its printed scope
  (`printed_tables_check.json`).

The checker of the same name recorded on 2026-09-29
([independent checks](../../research/notes/independent-checks-2026-09-29.md)) was not preserved.
These programs replace it, and those of the source-table audit
([rebuilt checks](../../research/notes/rebuilt-checks-2026-10-01.md)).

## The adversarial reviews (2026-10-01 and 2026-10-02)

The two review reports are in [`paper/reviews/`](../../paper/reviews/). Their programs and raw
results are here:
- `adversarial_source_checks.py`: sign checks of the source tables and a local counterexample
  test (`adversarial_20261001/source-signs.json`);
- `paper_root_cover_check.py`: an exact check of the root cover against the paper's census
  (`adversarial_20261002/root-cover.json`);
- `fallback_integral_attack.py`: independent high-precision numerical checks of all 37 two-test
  (fallback) rows (`adversarial_20261002/fallback-integrals.json`);
- `adversarial_20261001/`: the first review's reruns: the full replay through the independent
  checker (`inside-replay.json`, `outside-replay.json` and the per-leaf statistics), the printed
  tables, the two-test comparison, Heath-Brown's tables, the location checks, the small and large
  exterior ranges, and `summary.json` with the counts, maxima and file hashes;
- `adversarial_20261002/provenance.json`: the hashes of every input and program of the second review.
