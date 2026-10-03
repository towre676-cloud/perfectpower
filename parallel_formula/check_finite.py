"""Regenerate, compile and inspect every finite formula proof fixture."""
from pathlib import Path
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.finite_formula import emit_finite_query
sources=sorted(p for p in (ROOT/'parallel_formula/finite').glob('*.smt2') if not p.name.endswith('.reduced.smt2'))
modules=sorted({module for path in sources for module in
    emit_finite_query(path.read_bytes().decode('utf-8')).imports})
subprocess.run(['lake','build',*modules],cwd=ROOT,check=True)
for path in sources:
    output=emit_finite_query(path.read_bytes().decode('utf-8'))
    leaf=path.with_suffix('.lean');leaf.write_text(output.lean)
    path.with_suffix('.reduced.smt2').write_text(output.smt)
    result=subprocess.run(['lake','env','lean',str(leaf)],cwd=ROOT,capture_output=True,text=True)
    print(path.name,output.points)
    print(result.stdout,end='');print(result.stderr,end='',file=sys.stderr)
    if result.returncode or 'sorryAx' in result.stdout:
        raise SystemExit('Lean compilation or axiom check failed')
