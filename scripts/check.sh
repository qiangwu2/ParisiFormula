#!/usr/bin/env bash
# Build both local libraries (including axiom guards), then scan/report placeholders.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== Supporting library: ParisiFormula =="
lake build ParisiFormula
echo "== Targets and completed-theorem axiom guards =="
lake build Targets

echo "== Placeholder scan (ParisiFormula) =="
if grep -rnE '(^|[^[:alnum:]_])(sorry|admit)([^[:alnum:]_]|$)|^[[:space:]]*axiom[[:space:]]' --include='*.lean' ParisiFormula; then
  echo "FAIL: placeholder or project-local axiom found in ParisiFormula/"
  exit 1
else
  scan_status=$?
  if [ "$scan_status" -ne 1 ]; then
    exit "$scan_status"
  fi
fi
echo "OK: no sorry/admit/axiom in ParisiFormula/"

echo "== Remaining explicit proof placeholders in Targets (not comment mentions) =="
if grep -rnE '^[[:space:]]*(sorry|admit)([[:space:]]|$)' --include='*.lean' Targets; then
  echo "These targets remain open; GuerraAudit separately checks completed results."
else
  scan_status=$?
  if [ "$scan_status" -ne 1 ]; then
    exit "$scan_status"
  fi
  echo "No standalone sorry/admit lines found."
fi
