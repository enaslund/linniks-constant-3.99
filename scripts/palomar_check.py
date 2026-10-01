"""Local pre-check of Palomar's static submission requirements for this Lean project.

It checks what can be checked without Palomar's own workflow, following the policy of
2026-09-29 (https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md):
* every regular `.lean` file outside `.lake` is a module (its header starts with `module`) and has
  at most 10,000 physical lines; no `.lean` file is a symbolic link;
* the Challenge has at most 1,000 lines and 100 KiB (above 300 lines or 32 KiB Palomar warns), and
  imports only Mathlib;
* exactly one Lakefile, a TOML file of at most 1 MiB; `lake-manifest.json` pins every Git package
  to a full 40-character commit of a `https://github.com/owner/repo` URL;
* `lean-toolchain` names a Lean release no older than Palomar's minimum and equal to the pinned
  Mathlib's toolchain;
* `comparator.json` has only the accepted keys and the three permitted axioms;
* exactly one licence file at the project root, whose SPDX identifier (Apache-2.0 here) is the
  `project.license` of `formalization.yaml`;
* `formalization.yaml` has the mechanically required fields, in the required shapes, and a
  consistent source origin; placeholders (`TO CONFIRM`) are reported;
* no compiled Lean or native build output outside `.lake`, and the tree is under 500 MiB.

It does not replace Palomar's mechanical workflow (Challenge compilation against trusted Mathlib,
Comparator with NanoDa under Landrun), which `scripts/verify.sh` approximates locally.

  python3 scripts/palomar_check.py            # from the project root; exit 1 on a failure
  python3 scripts/palomar_check.py --root DIR  # a standalone export of the project
  python3 scripts/palomar_check.py --allow-placeholders   # report `TO CONFIRM` fields as warnings
"""
import argparse
import json
import re
import sys
import tomllib
from pathlib import Path

import yaml

MIN_TOOLCHAIN = 'v4.35.0-rc2'   # PalomarSubmission/toolchains.json, 2026-09-29
AXIOMS = {'propext', 'Quot.sound', 'Classical.choice'}
CONFIG_KEYS = {'challenge_module', 'solution_module', 'theorem_names', 'definition_names',
               'permitted_axioms', 'enable_nanoda'}
COMPILED = {'.olean', '.ilean', '.a', '.bc', '.dll', '.dylib', '.o', '.obj', '.so', '.trace'}
LICENCE_NAMES = {n + e for n in ('LICENSE', 'LICENCE', 'COPYING', 'UNLICENSE', 'OFL')
                 for e in ('', '.md', '.markdown', '.txt')}
RELATIONSHIPS = {'formalizes', 'adapts', 'independently-proves', 'background', 'other'}
SOURCE_TYPES = {'paper', 'book', 'web discussion', 'folklore', 'original-proof', 'other'}


def physical_lines(data: bytes) -> int:
    """Lines as Palomar counts them: LF and CRLF each end one line, an unterminated final line
    counts, and a final newline adds no line."""
    if not data:
        return 0
    n = data.count(b'\n')
    return n if data.endswith(b'\n') else n + 1


def is_module(text: str) -> bool:
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


def version_key(v: str):
    m = re.fullmatch(r'v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?', v)
    assert m, v
    a, b, c, rc = m.groups()
    return (int(a), int(b), int(c), int(rc) if rc else 10 ** 6)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--root', default=str(Path(__file__).resolve().parent.parent))
    ap.add_argument('--allow-placeholders', action='store_true',
                    help='report the submitter\'s open decisions (`TO CONFIRM`) as warnings')
    a = ap.parse_args()
    root = Path(a.root).resolve()
    fail, warn = [], []

    # Lean sources
    for p in sorted(root.rglob('*.lean')):
        rel = p.relative_to(root)
        if '.lake' in rel.parts or '.git' in rel.parts:
            continue
        if p.is_symlink():
            fail.append(f'{rel}: a .lean symbolic link')
            continue
        data = p.read_bytes()
        n = physical_lines(data)
        if n > 10_000:
            fail.append(f'{rel}: {n} lines (limit 10,000)')
        if rel.name != 'lakefile.lean' and not is_module(data.decode()):
            fail.append(f'{rel}: not a module (no `module` header)')

    # Comparator configuration and the Challenge
    cfg = json.loads((root / 'comparator.json').read_text())
    if set(cfg) - CONFIG_KEYS:
        fail.append(f'comparator.json: unknown keys {sorted(set(cfg) - CONFIG_KEYS)}')
    if not cfg.get('theorem_names'):
        fail.append('comparator.json: empty theorem_names')
    if not set(cfg.get('permitted_axioms', [])) <= AXIOMS:
        fail.append('comparator.json: axioms beyond propext, Quot.sound, Classical.choice')
    ch = root / (cfg['challenge_module'].replace('.', '/') + '.lean')
    data = ch.read_bytes()
    n, size = physical_lines(data), len(data)
    if n > 1000 or size > 100 * 1024:
        fail.append(f'{ch.name}: {n} lines, {size} bytes (limits 1,000 lines, 100 KiB)')
    elif n > 300 or size > 32 * 1024:
        warn.append(f'{ch.name}: {n} lines, {size} bytes (Palomar warns above 300 lines or 32 KiB)')
    imports = re.findall(r'^(?:public |meta |private )*import\s+(\S+)', data.decode(), re.M)
    if any(i != 'Mathlib' and not i.startswith('Mathlib.') for i in imports):
        fail.append(f'{ch.name}: imports beyond Mathlib: {imports}')
    if cfg['challenge_module'] == cfg['solution_module']:
        fail.append('comparator.json: the Challenge and Solution modules are the same')

    # Lake files and the toolchain
    lakefiles = [f for f in ('lakefile.toml', 'lakefile.lean') if (root / f).exists()]
    if len(lakefiles) != 1:
        fail.append(f'lakefiles: {lakefiles} (exactly one is required)')
    elif lakefiles[0] == 'lakefile.toml':
        if (root / 'lakefile.toml').stat().st_size > 1 << 20:
            fail.append('lakefile.toml: over 1 MiB')
        tomllib.loads((root / 'lakefile.toml').read_text())
    manifest = json.loads((root / 'lake-manifest.json').read_text())
    for pkg in manifest['packages']:
        if pkg.get('type') == 'git':
            if not re.fullmatch(r'https://github\.com/[\w.-]+/[\w.-]+', pkg['url'].removesuffix('.git')):
                fail.append(f'manifest: {pkg["name"]} URL {pkg["url"]}')
            if not re.fullmatch(r'[0-9a-f]{40}', pkg['rev']):
                fail.append(f'manifest: {pkg["name"]} is not pinned to a full commit')
        elif pkg.get('type') == 'path':
            warn.append(f'manifest: path dependency {pkg["name"]}')
    tc = (root / 'lean-toolchain').read_text().strip()
    m = re.fullmatch(r'leanprover/lean4:(v[\d.]+(?:-rc\d+)?)', tc)
    if not m:
        fail.append(f'lean-toolchain: {tc!r} is not a Lean release')
    elif version_key(m.group(1)) < version_key(MIN_TOOLCHAIN):
        fail.append(f'lean-toolchain: {m.group(1)} is older than Palomar\'s minimum {MIN_TOOLCHAIN}')
    mtc = root / '.lake/packages/mathlib/lean-toolchain'
    if mtc.exists() and mtc.read_text().strip() != tc:
        fail.append(f'lean-toolchain: {tc} differs from Mathlib\'s {mtc.read_text().strip()}')

    # Licence and metadata
    lic = [p.name for p in root.iterdir() if p.is_file() and p.name.upper() in LICENCE_NAMES]
    spdx = None
    if len(lic) != 1:
        fail.append(f'licence files at the root: {lic} (exactly one is required)')
    else:
        text = (root / lic[0]).read_text()
        if 'Apache License' in text and 'Version 2.0' in text:
            spdx = 'Apache-2.0'
        else:
            warn.append(f'{lic[0]}: licence not recognized by this check')
    meta = yaml.safe_load((root / 'formalization.yaml').read_text())
    proj = meta.get('project', {})

    def need(cond, what):
        if not cond:
            fail.append(f'formalization.yaml: {what}')
    need(isinstance(proj.get('name'), str) and 0 < len(proj['name']) <= 300, 'project.name (1-300 characters)')
    need(isinstance(proj.get('description'), str) and 0 < len(proj['description']) <= 10_000,
         'project.description (1-10,000 characters)')
    for key in ('authors', 'responsible_maintainers'):
        v = proj.get(key)
        need(isinstance(v, list) and v and all(isinstance(x, str) and x.strip() for x in v),
             f'project.{key}: a nonempty list of names')
    need(proj.get('license') == spdx, f'project.license {proj.get("license")!r} vs licence file {spdx!r}')
    cl = meta.get('classification', {})
    arx = cl.get('arxiv') or []
    need(1 <= len(arx) <= 8 and len(set(arx)) == len(arx), 'classification.arxiv: 1-8 distinct codes')
    need(all(re.fullmatch(r'[a-z-]+(\.[A-Za-z-]+)?', c) for c in arx), 'classification.arxiv: code format')
    msc = cl.get('msc2020') or []
    need(len(msc) <= 8 and len(set(msc)) == len(msc), 'classification.msc2020: at most 8 distinct codes')
    need(all(re.fullmatch(r'\d\d[A-Z-]\d\d|\d\d-\d\d', c) for c in msc), 'classification.msc2020: code format')
    methods = (meta.get('automation') or {}).get('methods')
    need(isinstance(methods, list) and methods and all(isinstance(x, dict) and x.get('method') for x in methods),
         'automation.methods: a nonempty list of mappings with `method`')
    need(isinstance((meta.get('review') or {}).get('status'), str) and meta['review']['status'].strip(),
         'review.status')
    srcs = meta.get('sources')
    need(isinstance(srcs, list) and srcs, 'sources: a nonempty list')
    if isinstance(srcs, list):
        for s in srcs:
            need(isinstance(s, dict) and s.get('title') and s.get('relationship') in RELATIONSHIPS,
                 f'sources: {s.get("title") if isinstance(s, dict) else s!r} needs a title and a known relationship')
            if isinstance(s, dict) and 'type' in s:
                need(s['type'] in SOURCE_TYPES, f'sources: type {s["type"]!r}')
        orig = [s for s in srcs if isinstance(s, dict) and s.get('type') == 'original-proof']
        rels = {s.get('relationship') for s in srcs if isinstance(s, dict)}
        if orig:
            need(all(s.get('relationship') == 'other' for s in orig) and rels <= {'background', 'other'},
                 'sources: an original-proof entry needs relationship `other`, and all others background/other')
        else:
            need(rels & {'formalizes', 'adapts', 'independently-proves'},
                 'sources: a source-based list needs a formalizes/adapts/independently-proves entry')
    placeholders = re.findall(r'TO CONFIRM[^\n"]*', (root / 'formalization.yaml').read_text())
    for ph in placeholders:
        (warn if a.allow_placeholders else fail).append(
            f'formalization.yaml: placeholder "{ph.strip()}" (a decision for the submitter)')

    # Build output and size
    total = 0
    for p in root.rglob('*'):
        rel = p.relative_to(root)
        if '.lake' in rel.parts or '.git' in rel.parts or p.is_symlink() or not p.is_file():
            continue
        total += p.stat().st_size
        if p.suffix in COMPILED:
            fail.append(f'{rel}: compiled output outside .lake')
    if total > 500 * 2 ** 20:
        fail.append(f'tree size {total / 2 ** 20:.1f} MiB (limit 500 MiB)')

    for w in warn:
        print('warning:', w)
    for f in fail:
        print('FAIL:', f)
    print(f'{"FAIL" if fail else "PASS"}: {len(fail)} failures, {len(warn)} warnings '
          f'({total / 2 ** 20:.1f} MiB, Challenge {n} lines)')
    return 1 if fail else 0


if __name__ == '__main__':
    sys.exit(main())
