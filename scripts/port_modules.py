"""Port the Lean sources of this project to Lean's module system (one-time conversion).

Palomar requires every regular `.lean` file of a submitted repository to be a module
(PalomarPolicy CONTRIBUTING.md, "Lean source requirements"). The conversion keeps the meaning of
the non-module files as closely as the module system allows:
* `module` becomes the first line (the module header), followed by the imports;
* every `import X` becomes `public import X`, so importers see what they saw before;
* the module documentation stays right after the imports;
* the rest of the file is wrapped in `@[expose] public section`: every declaration that was not
  `private` stays public, and definition bodies stay visible to importers. The kernel-checked
  certificates evaluate `checkLeaf` from another module and need that; proofs of theorems stay
  private, as the module system requires.

  python3 scripts/port_modules.py [files...]      # default: every .lean file outside .lake
  python3 scripts/port_modules.py --check          # exit 1 if some file is not yet a module

Already converted files are left unchanged, so the script is idempotent.
"""
import re
import sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent


def lean_files():
    return sorted(p for p in root.rglob('*.lean')
                  if '.lake' not in p.relative_to(root).parts and not p.is_symlink())


def is_module(text):
    """Whether the header (after leading comments and blank lines) starts with `module`."""
    rest = text
    while True:
        rest = rest.lstrip()
        if rest.startswith('--'):
            rest = rest.split('\n', 1)[1] if '\n' in rest else ''
        elif rest.startswith('/-') and not rest.startswith('/-!') and not rest.startswith('/--'):
            rest = rest[rest.index('-/') + 2:]
        else:
            break
    return re.match(r'module\b', rest) is not None


def port(text):
    assert not is_module(text)
    lines = text.split('\n')
    i = 0
    imports = []
    # imports come first in these files (no leading comments)
    while i < len(lines) and (lines[i].startswith('import ') or lines[i].strip() == ''):
        if lines[i].startswith('import '):
            imports.append('public ' + lines[i])
        i += 1
    body = lines[i:]
    # the module documentation, if the body starts with it, stays before the public section
    doc = []
    if body and body[0].startswith('/-!'):
        j = 0
        while '-/' not in body[j]:
            j += 1
        doc = body[:j + 1]
        body = body[j + 1:]
        while body and body[0].strip() == '':
            body = body[1:]
    out = ['module', '']
    if imports:
        out += imports + ['']
    if doc:
        out += doc + ['']
    out += ['@[expose] public section', ''] + body
    return '\n'.join(out)


def main(argv):
    check = '--check' in argv
    args = [a for a in argv if not a.startswith('--')]
    files = [Path(a).resolve() for a in args] if args else lean_files()
    pending = [f for f in files if not is_module(f.read_text())]
    if check:
        for f in pending:
            print(f'not a module: {f.relative_to(root)}')
        return 1 if pending else 0
    for f in pending:
        f.write_text(port(f.read_text()))
        print(f'ported {f.relative_to(root)}')
    return 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
