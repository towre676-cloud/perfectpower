#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/PerfectPower"
cp "$root/PerfectPower/BoundedNative.lean" "$root/PerfectPower/QueryNative.lean" "$scratch/PerfectPower/"
export LEAN_PATH="$scratch"
lean_bin="${PERFECTPOWER_LEAN:-lean}"
cd "$scratch"
"$lean_bin" PerfectPower/BoundedNative.lean -o PerfectPower/BoundedNative.olean
"$lean_bin" PerfectPower/QueryNative.lean -o PerfectPower/QueryNative.olean
"$lean_bin" "$root/audit/QueryNative.lean" > "$scratch/axioms.txt"
python3 - "$scratch/axioms.txt" <<'PY'
from pathlib import Path
import re
import sys
text=Path(sys.argv[1]).read_text()
rows=re.findall(r'(?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)',text)
assert len(rows)==16,text
assert all({v.strip() for v in row.split(',') if v.strip()} <=
           {'propext','Classical.choice','Quot.sound'} for row in rows),text
assert 'sorry' not in text and 'ofReduceBool' not in text,text
print('Population query audit: 16 generic theorems, standard axioms only')
PY
export PYTHONPATH="$root/python"
export PERFECTPOWER_LEAN="$lean_bin"
python3 -m unittest discover -s "$root/python/tests" -p 'test_checked_population.py' -v
