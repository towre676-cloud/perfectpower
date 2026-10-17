"""Build and audit the new finite phase/Coxeter/induction Lean theorems.

Only the finite statements named in the output are certified here. The
convergence and analytic identifications in the monograph are not silently
promoted to Lean theorems. Uses the repository's pinned toolchain/mathlib.
"""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = ('PhaseFiber', 'CoxeterPhaseBridge', 'RaghavaInduction')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def run(command):
    result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
    if result.returncode:
        raise RuntimeError(' '.join(command) + '\n' + result.stdout + result.stderr)
    return result.stdout


def check():
    paths = [ROOT/'PerfectPower'/f'{name}.lean' for name in MODULES]
    sources=paths+[ROOT/'lean-toolchain',ROOT/'lake-manifest.json',Path(__file__).resolve()]
    hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}
    declarations = []
    for module, path in zip(MODULES, paths):
        for name in re.findall(r'^\s*(?:theorem|lemma)\s+(\w+)', path.read_text(), re.M):
            declarations.append(f'PerfectPower.{module}.{name}')
    if not declarations or len(set(declarations)) != len(declarations):
        raise ValueError('Missing or duplicate theorem declarations')
    build = run(['lake', 'build', *('PerfectPower.'+name for name in MODULES)])
    target = ROOT/'tmp/raghava-coxeter/Axioms.lean'
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_text('\n'.join(['import PerfectPower.'+name for name in MODULES]
                               + ['#print axioms '+name for name in declarations])+'\n')
    output = run(['lake', 'env', 'lean', str(target)])
    # Lean wraps long axiom lines; parse across whitespace, and require every
    # requested declaration to have a complete machine-produced audit entry.
    entries = {}
    pattern = r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)"
    for name, axioms in re.findall(pattern, output, re.S):
        entries[name] = sorted(a.strip() for a in axioms.split(',') if a.strip())
    if set(entries) != set(declarations):
        raise ValueError('Axiom audit did not cover exactly the requested declarations: '+output)
    for name, axioms in entries.items():
        if set(axioms)-ALLOWED_AXIOMS:
            raise ValueError('Nonstandard axiom in '+name+': '+str(axioms))
    if hashes != {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in sources}:
        raise ValueError('Proof source changed while checking')
    result = dict(schema='pp-raghava-coxeter-lean/1',
                  lean_version=run(['lake', 'env', 'lean', '--version']).strip(),
                  mathlib_revision=run(['git','-C','.lake/packages/mathlib','rev-parse','HEAD']).strip(),
                  modules=list(MODULES), theorem_count=len(entries),
                  declarations=entries, source_sha256=hashes,
                  kernel_checked=True, custom_axioms=False, native_decision_oracle=False,
                  analytic_series_formalized=False,
                  scope='Finite Fourier filters, actual integral Coxeter matrix transport, and rational phase-moment induction; the analytic series proof is separate.')
    out=ROOT/'receipts/period_bridge_deep/unification_lean.json'
    out.write_text(json.dumps(result, sort_keys=True, indent=2)+'\n')
    (target.parent/'build.log').write_text(build)
    (target.parent/'axioms.log').write_text(output)
    return result


if __name__ == '__main__':
    result=check()
    print(json.dumps({key:result[key] for key in ('schema','lean_version','theorem_count','kernel_checked','analytic_series_formalized')}))
