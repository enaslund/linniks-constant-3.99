#!/usr/bin/env python3
"""Capture the leaves that the replay's exporter streams to a checker, for the forgery test.

Use it as the exporter's checker: it answers every line with ``independent_cert_check.py`` (so
the exporter still compares values and box counts), and appends each input line to
``<dir>/<tag>_<pid>.jsonl``, one file per worker process. The captured lines are the input of
``independent_cert_forgeries.py``:

    python3 computations/graded/graded_lean_export.py --kind inside --roots 1416,2432,1671 --jsonl \\
        --workers 3 --checker "$PWD/.venv/bin/python $PWD/computations/audit/capture_leaves.py OUTDIR inside" \\
        --out OUTDIR/sample_inside.json
    cat OUTDIR/inside_*.jsonl > OUTDIR/leaves.jsonl
    python3 computations/audit/independent_cert_forgeries.py OUTDIR/leaves.jsonl
"""
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import independent_cert_check as icc  # noqa: E402


def main():
    out_dir, tag = sys.argv[1], (sys.argv[2] if len(sys.argv) > 2 else 'cap')
    os.makedirs(out_dir, exist_ok=True)
    with open(os.path.join(out_dir, f'{tag}_{os.getpid()}.jsonl'), 'a', encoding='utf-8') as out:
        for line in sys.stdin:
            if not line.strip():
                continue
            out.write(line if line.endswith('\n') else line + '\n')
            out.flush()
            sys.stdout.write(icc.output_line(icc.check_line(line)) + '\n')
            sys.stdout.flush()


if __name__ == '__main__':
    main()
