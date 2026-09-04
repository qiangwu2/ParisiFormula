#!/usr/bin/env bash
# Full project check: build both local tiers, then scan the verified tier for placeholders.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Tier 2: ParisiFormula =="
lake build ParisiFormula
echo "== Tier 3: Targets (sorry warnings expected) =="
lake build Targets || echo "WARNING: Targets failed to build; see errors above (allowed for now)."

echo "== Placeholder scan (Tier 2) =="
if grep -rnE "\bsorry\b|\badmit\b|^axiom " --include='*.lean' ParisiFormula; then
  echo "FAIL: placeholder or project-local axiom found in verified tier"; exit 1
fi
echo "OK: no sorry/admit/axiom in ParisiFormula/"

echo "== Remaining sorries in Targets =="
grep -cn "sorry" Targets/Milestones.lean || true
