#!/usr/bin/env bash
# Generate and check a native Lean Runge solution from ascending integer coefficients.
set -euo pipefail
cd "$(dirname "$0")/.."
certificate=0
source_only=0
while [[ $# -gt 0 && $1 == --* ]]; do
  case "$1" in
    --certificate-only) certificate=1 ;;
    --source-only) source_only=1 ;;
    *) echo "Unknown option: $1" >&2; exit 2 ;;
  esac
  shift
done
if [[ $# != 1 ]]; then
  echo "Usage: $0 [--certificate-only] [--source-only] 'a0,a1,...,an'" >&2
  exit 2
fi
coefficients=${1//[[:space:]]/}
if [[ ! $coefficients =~ ^-?[0-9]+(,-?[0-9]+)*$ ]]; then
  echo 'Coefficients must be comma-separated decimal integers.' >&2
  exit 2
fi
command=native_runge
if [[ $certificate == 1 ]]; then command=native_runge_certificate; fi
emit_source() {
  printf 'import PerfectPower.Tactic.RungePolynomial\n\n'
  printf 'set_option maxRecDepth 100000\nset_option maxHeartbeats 4000000\n'
  printf '%s runge_result for [%s]\n' "$command" "$coefficients"
  printf '#check runge_result_complete\n#print axioms runge_result_complete\n'
  if [[ $certificate == 0 ]]; then
    cat <<'LEAN'
run_cmd do
  if (← Lean.getEnv).contains `runge_result then
    Lean.Elab.Command.elabCommand (← `(#print runge_result))
LEAN
  fi
}
if [[ $source_only == 1 ]]; then emit_source; exit 0; fi
lake build PerfectPower.Tactic.RungePolynomial >&2
source_file=$(mktemp --suffix=.lean)
trap 'rm -f "$source_file"' EXIT
emit_source > "$source_file"
lake env lean -s 65536 "$source_file"
