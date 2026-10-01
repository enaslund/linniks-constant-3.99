#!/usr/bin/env bash
# Local verification of the formalization.
#   0. Palomar's static source requirements (scripts/palomar_check.py): every .lean file is a module
#      of at most 10,000 lines, the Challenge limits, pins, licence and metadata shapes;
#   1. regenerate Challenge.lean from the library and check it is unchanged;
#   2. build every target (GradedNear, Challenge, Solution, the kernel-checked Samples, which
#      need 7-16 GB of memory per leaf, and the native runners certrun, leafcheck and rowcheck);
#   3. compare the Challenge with the Solution (scripts/Compare.lean, a stand-in for Palomar's
#      comparator) and audit the axioms of the compared theorems;
#   4. replay the kernel checks of every project module with leanchecker (this includes the
#      kernel evaluation of the sample certificates in GradedNear.Cert.Samples, and the
#      Mathlib-free cores that the native runners compile).
set -euo pipefail
cd "$(dirname "$0")/.."
python3 scripts/palomar_check.py --allow-placeholders
before=$(mktemp)
cp Challenge.lean "$before"
python3 scripts/make_challenge.py
cmp -s Challenge.lean "$before" || { echo "Challenge.lean was stale"; rm -f "$before"; exit 1; }
rm -f "$before"
cores="CertCore IntervalCore LeafNumCore LeafMetaCore LeafCheckCore RowCheckCore"
if grep -rn --include=*.lean -E '\bsorry\b|\badmit\b|native_decide|^axiom ' GradedNear Solution.lean \
    $(for c in $cores; do echo "$c.lean"; done); then
  echo "forbidden construct in the library"; exit 1
fi
lake build
# The kernel-checked samples need 7-16 GB of memory each: build them one at a time.
for f in GradedNear/Cert/Samples/*.lean; do
  m=$(echo "${f%.lean}" | tr / .)
  lake build "$m"
done
lake build certrun leafcheck rowcheck
lake env lean --run scripts/Compare.lean
axioms=$(lake env lean Audit.lean)
echo "$axioms"
n=$(echo "$axioms" | grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]")
[ "$n" -eq "$(echo "$axioms" | grep -c "depends on axioms")" ] || { echo "nonstandard axioms"; exit 1; }
for m in $cores $(find GradedNear -name '*.lean' | sort | sed 's#/#.#g; s#\.lean$##') Solution; do
  lake env leanchecker "$m"
  echo "leanchecker $m: ok"
done
echo "PASS"
