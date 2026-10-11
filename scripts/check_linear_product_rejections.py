"""Reject a changed polynomial and an omitted solution in emitted Lean proofs."""
import os
import subprocess
import tempfile
from pathlib import Path

source=Path('receipts/linear_product/Six.lean').read_text()
variants={
    'changed-polynomial':source.replace('def F : List Int := [0,6,1]','def F : List Int := [1,6,1]'),
    'omitted-solution':source.replace('def solutions : List (Int × Int) := [(-8,-4),','def solutions : List (Int × Int) := [')
}
for name,content in variants.items():
    if content==source:raise AssertionError('rejection mutation did not apply')
    with tempfile.TemporaryDirectory() as directory:
        path=Path(directory)/'Rejected.lean';path.write_text(content)
        result=subprocess.run([os.environ.get('PERFECTPOWER_LEAN','lean'),str(path)],capture_output=True,text=True)
    if result.returncode==0:raise AssertionError(f'{name} unexpectedly accepted')
    print(name+': rejected by Lean (exit '+str(result.returncode)+')')
    print(result.stdout+result.stderr)
