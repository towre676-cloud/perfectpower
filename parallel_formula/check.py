"""Regenerate and compile the whole-query theorem for the pinned cvc5 input."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))
from perfectpower.formula_transport import emit_square_cube

source = ROOT / 'independent_nia/corpus/cvc5__cvc5/test/regress/cli/regress1/nl/disj-eval.smt2'
output = ROOT / 'parallel_formula/DisjEval.lean'
output.write_text(emit_square_cube(source.read_text()))
subprocess.run(['lake', 'build', 'PerfectPower.FormulaTransport',
                'PerfectPower.Generated.ClassLists.K2'], cwd=ROOT, check=True)
for path in ['parallel_formula/DisjEval.lean', 'parallel_formula/MordellConsumer.lean']:
    p = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT,
                       capture_output=True, text=True)
    print(p.stdout, end='')
    print(p.stderr, end='', file=sys.stderr)
    if p.returncode or 'sorryAx' in p.stdout:
        raise SystemExit('Lean compilation or axiom check failed')
