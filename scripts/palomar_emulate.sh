#!/usr/bin/env bash
# Local emulation of Palomar's mechanical verification, sized like Palomar's hosted
# profile `palomar-standard-v1` (a GitHub-hosted ubuntu-24.04 runner with 4 CPUs and 16 GB;
# Palomar caps memory at 98% of the host's).
#
# It follows the `execute` stage of PalomarSubmission's scripts/verify_submission.py:
#   1. build the Challenge and export its declarations with `leanexport`;
#   2. build the Solution (`lake build Solution`) and export it;
#   3. judge the two exports with the toolchain's `lake comparator`, registering the
#      toolchain's bundled external kernels (nanoda and con-ron) as Palomar does.
# Each step runs on 4 CPUs under a 15 GiB memory ceiling (via a systemd user scope, when one is
# available) and reports its wall time and peak memory.
#
# It is NOT Palomar's preflight. Palomar requires its own reusable workflow
# (.github/workflows/palomar-preflight.yml in the submitted repository) to report
# `status: pass`; this script is a quick local check before that.
#
# Requirements: the project's dependencies already built or fetched
# (`lake exe cache get` for Mathlib), bubblewrap, python3, and git.
# Usage, from the project root:  scripts/palomar_emulate.sh
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
TOOLCHAIN=$(tr -d '[:space:]' < "$ROOT/lean-toolchain")        # leanprover/lean4:vX.Y.Z
T="$HOME/.elan/toolchains/$(echo "$TOOLCHAIN" | sed 's#/#--#; s#:#---#')"
[ -x "$T/bin/lake" ] || { echo "toolchain $TOOLCHAIN is not installed (elan toolchain install)"; exit 1; }
[ -d "$ROOT/.lake/packages" ] || { echo "dependencies missing: run 'lake exe cache get' first"; exit 1; }
BWRAP=$(command -v bwrap) || { echo "bubblewrap (bwrap) is required"; exit 1; }
export PATH="$T/bin:$PATH"

WORK=$(mktemp -d)
trap 'rm -rf "${WORK:?}"' EXIT
REPO="$WORK/repo"
mkdir -p "$REPO/.lake" "$WORK/judge/project" "$WORK/judge/home" "$WORK/judge/tmp"
# The committed files only, as Palomar checks them out, with fresh build directories and the
# dependencies copied in (Palomar unpacks the pinned Mathlib cache).
git -C "$ROOT" ls-files -z | (cd "$ROOT" && xargs -0 cp --parents -t "$REPO")
cp -a "$ROOT/.lake/packages" "$REPO/.lake/packages"

cat > "$WORK/measure.py" <<'PY'
import json, os, subprocess, sys, time
def tree_anon(root):
    procs = {}
    for p in os.listdir('/proc'):
        if p.isdigit():
            try:
                s = open(f'/proc/{p}/stat').read()
                ppid = int(s[s.rfind(')') + 2:].split()[1])
                anon = next((int(l.split()[1]) * 1024 for l in open(f'/proc/{p}/status')
                             if l.startswith('RssAnon:')), 0)
                procs[int(p)] = (ppid, anon)
            except Exception:
                pass
    kids = {}
    for pid, (pp, _) in procs.items():
        kids.setdefault(pp, []).append(pid)
    total, stack, seen = 0, [root], set()
    while stack:
        x = stack.pop()
        if x not in seen:
            seen.add(x); total += procs.get(x, (0, 0))[1]; stack.extend(kids.get(x, []))
    return total
label, cmd = sys.argv[1], sys.argv[sys.argv.index('--') + 1:]
t0, peak = time.time(), 0
proc = subprocess.Popen(cmd)
while proc.poll() is None:
    peak = max(peak, tree_anon(proc.pid)); time.sleep(0.5)
cg = None
try:
    path = open('/proc/self/cgroup').read().strip().split('::', 1)[1]
    cg = round(int(open(f'/sys/fs/cgroup{path}/memory.peak').read()) / 2**30, 2)
except Exception:
    pass
print(json.dumps({'step': label, 'exit': proc.returncode, 'wall_s': round(time.time() - t0, 1),
                  'peak_anon_GiB': round(peak / 2**30, 2), 'cgroup_peak_GiB': cg}), flush=True)
sys.exit(proc.returncode)
PY

# Export targets and the protected configuration, as Palomar computes them.
python3 - "$REPO/comparator.json" "$T/src/lean/lake/Lake/CLI/Check.lean" "$T/bin" \
    "$WORK/targets.txt" "$WORK/protected.json" <<'PY'
import json, re, sys
cfg = json.load(open(sys.argv[1])); text = open(sys.argv[2]).read(); b = sys.argv[3]
body = re.search(r"^def primitiveTargets[^\n]*\n(?P<b>.*?)^def ", text, re.M | re.S).group("b")
body = "\n".join(l.split("--", 1)[0] for l in re.sub(r"/-.*?-/", "", body, flags=re.S).splitlines())
prims = re.findall(r"``([A-Za-z_][A-Za-z0-9_'.]*)", body)
ax = cfg["permitted_axioms"]
quot = ["Quot", "Quot.mk", "Quot.lift", "Quot.ind"] if "Quot.sound" in ax else []
open(sys.argv[4], "w").write(" ".join(quot + cfg["theorem_names"] + ax + prims
                                      + cfg.get("definition_names", [])))
json.dump({"challenge_module": cfg["challenge_module"], "solution_module": cfg["solution_module"],
           "theorem_names": cfg["theorem_names"],
           "definition_names": cfg.get("definition_names", []),
           "permitted_axioms": ax,
           "external_kernels": {"nanoda": [b + "/nanoda_bin"], "con-ron": [b + "/con-ron"]}},
          open(sys.argv[5], "w"), indent=1)
PY
TARGETS=$(cat "$WORK/targets.txt")
CHALLENGE=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["challenge_module"])' "$REPO/comparator.json")
SOLUTION=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["solution_module"])' "$REPO/comparator.json")

run() {
  local label=$1; shift
  if systemd-run --user --scope --quiet true 2>/dev/null; then
    systemd-run --user --scope --quiet -p MemoryMax=15G -p MemoryHigh=14700M -p CPUQuota=400% \
      taskset -c 0-3 python3 "$WORK/measure.py" "$label" -- "$@"
  else
    echo "(no systemd user scope: $label runs without the memory cap)"
    taskset -c 0-3 python3 "$WORK/measure.py" "$label" -- "$@"
  fi
}

cd "$REPO"
run challenge-build lake build "$CHALLENGE"
run challenge-export bash -c "lake env leanexport $CHALLENGE -- $TARGETS > '$WORK/challenge.export'"
run solution-build lake build "$SOLUTION"
run solution-export bash -c "lake env leanexport $SOLUTION -- $TARGETS > '$WORK/solution.export'"
cd "$WORK/judge/project"
HOME="$WORK/judge/home" TMPDIR="$WORK/judge/tmp" COMPARATOR_BWRAP="$BWRAP" LEAN_ABORT_ON_PANIC=1 \
  run comparator lake comparator --config "$WORK/protected.json" \
    --challenge-from-export "$WORK/challenge.export" --solution-from-export "$WORK/solution.export"
echo "palomar_emulate: all steps passed"
