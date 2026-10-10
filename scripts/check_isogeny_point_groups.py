"""Kernel-check actual elliptic group maps, dual composition, and the rank bridge."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
MODULES = ['PerfectPower/TwoIsogenyPointMap.lean', 'PerfectPower/TwoIsogenyDual.lean',
           'PerfectPower/DescentRankBridge.lean']
OUT = ROOT / 'receipts/isogeny_point_groups'
AUDIT = 'audit/IsogenyPointGroups.lean'
CASES = {
    'actual_addition': (True, '''
example (a b : ℚ) (hb : b ≠ 0) (hd : a^2-4*b ≠ 0)
    (P Q : (PerfectPower.TwoIsogenyPointMap.E a b).Point) :
    PerfectPower.TwoIsogenyPointMap.phi a b hb hd (P+Q) =
      PerfectPower.TwoIsogenyPointMap.phi a b hb hd P+
        PerfectPower.TwoIsogenyPointMap.phi a b hb hd Q :=
  PerfectPower.TwoIsogenyPointMap.phi_add a b hb hd P Q
'''),
    'dual_sign': (True, '''
example : PerfectPower.TwoIsogenyPointMap.Y (-12) 4 (-4)/8 = (-7/8:ℚ) := by norm_num [PerfectPower.TwoIsogenyPointMap.Y]
'''),
    'reversed_map_sign': (False, '''
example : PerfectPower.TwoIsogenyPointMap.Y 3 1 2 = (4:ℚ) := by norm_num [PerfectPower.TwoIsogenyPointMap.Y]
'''),
    'reversed_dual_sign': (False, '''
example : PerfectPower.TwoIsogenyPointMap.Y (-12) 4 (-4)/8 = (7/8:ℚ) := by norm_num [PerfectPower.TwoIsogenyPointMap.Y]
'''),
    'dropped_torsion_factor': (False, '''
example : 2^1*2 = (2:ℕ) := by decide
'''),
}


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    names = []
    for name in MODULES:
        source = (ROOT/name).read_text()
        namespace = re.search(r'^namespace (\S+)', source, re.M).group(1)
        names += [namespace+'.'+n for n in re.findall(r'^theorem (\w+)', source, re.M)]
        assert not re.search(r'\b(sorry|admit|axiom)\b', source), name
    assert len(names) == len(set(names))
    audit = ''.join('import '+p[:-5].replace('/', '.')+'\n' for p in MODULES)
    audit += ''.join('#print axioms '+n+'\n' for n in names)
    assert (ROOT/AUDIT).read_text() == audit, 'incomplete declaration audit'
    for path in MODULES:
        dest = ROOT/'.lake/build/lib/lean'/Path(path).with_suffix('.olean')
        dest.parent.mkdir(parents=True, exist_ok=True)
        run = subprocess.run(['lake', 'env', 'lean', '-o', str(dest), path], cwd=ROOT,
                             text=True, capture_output=True)
        (OUT/(Path(path).stem+'.log')).write_text(run.stdout+run.stderr)
        assert run.returncode == 0 and not (run.stdout+run.stderr).strip(), path+'\n'+run.stdout+run.stderr
        print('compiled: '+path, flush=True)
    run = subprocess.run(['lake', 'env', 'lean', AUDIT], cwd=ROOT, text=True, capture_output=True)
    pattern = re.compile(r"'([^']+)'\s+(?:does not depend on any axioms|depends on axioms:\s*\[([^\]]*)\])")
    records = list(pattern.finditer(run.stdout))
    assert run.returncode == 0 and not run.stderr.strip()
    assert [m.group(1) for m in records] == names and not pattern.sub('', run.stdout).strip()
    declarations = []
    for m in records:
        axioms = [a.strip() for a in (m.group(2) or '').split(',') if a.strip()]
        assert set(axioms) <= {'propext', 'Classical.choice', 'Quot.sound'}, m.group(1)
        declarations.append(dict(declaration=m.group(1), axioms=axioms))
    (OUT/'axioms.log').write_text(run.stdout)
    controls = []
    for name, (expected, source) in CASES.items():
        path = OUT/(name+'.lean')
        path.write_text('import PerfectPower.DescentRankBridge\n'+source)
        run = subprocess.run(['lake', 'env', 'lean', str(path.relative_to(ROOT))], cwd=ROOT,
                             text=True, capture_output=True)
        (OUT/(name+'.log')).write_text(run.stdout+run.stderr)
        assert (run.returncode == 0) == expected, name+'\n'+run.stdout+run.stderr
        if expected:
            assert not (run.stdout+run.stderr).strip(), name
        else:
            assert ("tactic 'decide'" in run.stdout and 'is false' in run.stdout) or ('unsolved goals' in run.stdout and '⊢ False' in run.stdout), name
        controls.append(dict(case=name, expected_acceptance=expected, accepted=run.returncode == 0))
    sources = MODULES+[AUDIT, 'scripts/check_isogeny_point_groups.py']
    sources += [str(p.relative_to(ROOT)) for p in sorted(OUT.glob('*.lean'))]
    receipt = dict(schema='pp-isogeny-point-groups/1', compiled=True, lean_version='4.20.0',
                   declaration_count=len(names), declarations=declarations, controls=controls,
                   source_sha256={p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources},
                   scope='actual elliptic group homomorphisms and dual composition; rank identity from an explicit free-plus-finite decomposition; squareclass quotient identification and unconditional Mordell-Weil rank remain open')
    (OUT/'verification.json').write_text(json.dumps(receipt, indent=2, sort_keys=True)+'\n')
    print(json.dumps(dict(compiled=True, declarations=len(names), controls=len(controls))), flush=True)


if __name__ == '__main__':
    main()
