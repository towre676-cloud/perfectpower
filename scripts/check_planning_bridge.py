"""Reproduce the Petersen50 semantic bridge build and axiom/rejection audits.

No full witness replay or historical search is performed. Uses only Lean's
pinned standard library; no Mathlib download or native reflection is needed.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

from check_planning_lean import source_binding

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    'PlanningDiagram', 'PlanningCertificate', 'PlanningCertificateExamples',
    'PetersenPlanning', 'PlanningPermutation', 'PlanningReplayBridge',
    'PlanningTraceDecode', 'PlanningReplayExamples', 'Petersen50Bridge',
)
NEW_MODULES = MODULES[4:]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--lean', default='lean')
    parser.add_argument('--out', type=Path, default=ROOT/'receipts/planning/bridge')
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    commands = []
    with tempfile.TemporaryDirectory(prefix='planning-bridge-') as temporary:
        work = Path(temporary)
        (work/'PerfectPower').mkdir()
        env['LEAN_PATH'] = str(work)
        version = subprocess.check_output([args.lean, '--version'], text=True, env=env).strip()
        if 'version 4.20.0,' not in version:
            raise RuntimeError('Requires pinned Lean 4.20.0')
        declarations = []
        for module in MODULES:
            path = ROOT/f'PerfectPower/{module}.lean'
            source = path.read_text()
            if module in NEW_MODULES and re.search(r'\b(sorry|admit|native_decide|axiom|unsafe)\b',
                                                  re.sub(r'/\-.*?\-/', '', source, flags=re.S)):
                raise RuntimeError(f'Unapproved proof escape in {module}')
            declarations.extend(f'PerfectPower.{module}.{name}' for name in
                                re.findall(r'^theorem (\w+)', source, re.M))
            run = subprocess.run([args.lean, '-o', str(work/f'PerfectPower/{module}.olean'), str(path)],
                                 cwd=ROOT, env=env, text=True, capture_output=True, timeout=180)
            commands.append({'module':module, 'exit_code':run.returncode,
                             'stdout':run.stdout, 'stderr':run.stderr})
            if run.returncode:
                raise RuntimeError(run.stdout+run.stderr)
        imports = ''.join(f'import PerfectPower.{module}\n' for module in MODULES)
        audit = work/'Audit.lean'
        audit.write_text(imports+'\n'.join('#print axioms '+name for name in declarations)+'\n')
        run = subprocess.run([args.lean, str(audit)], cwd=ROOT, env=env,
                             text=True, capture_output=True, timeout=180)
        if run.returncode:
            raise RuntimeError(run.stdout+run.stderr)
        (args.out/'axioms.log').write_text(run.stdout+run.stderr)
        parsed = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|(does not depend on any axioms))",
                            run.stdout.replace('\n',' '))
        axioms = {name:[] if no_axioms else [x.strip() for x in values.split(',') if x.strip()]
                  for name,values,no_axioms in parsed}
        if set(axioms) != set(declarations):
            raise RuntimeError('Incomplete axiom audit')
        if any(set(values)-{'propext','Quot.sound','Classical.choice'} for values in axioms.values()):
            raise RuntimeError('Unapproved axiom in kernel proof')
        attacks = {
            'false_population': 'theorem attack : PlanningDiagram.census 3 (PlanningDiagram.feasible PlanningReplayExamples.rows PlanningReplayExamples.caps) = 4 := by decide',
            'duplicate_coordinate': 'theorem attack : List.Perm [0,0,2] (List.range 3) := by decide',
            'negative_capacity_truncation': 'theorem attack : PlanningDiagram.census 2 (fun xs => decide ((PlanningDiagram.dot [0,0] xs : Int) ≤ -1)) = 4 := by decide',
            'wrong_little_endian_count': 'theorem attack : PlanningTraceDecode.readRecord PlanningTraceDecode.fixture = some (.node 1 1 0 33554432, []) := by decide',
            'accepted_bad_padding': 'theorem attack : PlanningTraceDecode.fromWords [1,1,1,0,2,0,1,0] = some (.node 1 1 0 2) := by decide',
        }
        rejected = {}
        for name,statement in attacks.items():
            path = work/(name+'.lean')
            path.write_text(imports+'open PerfectPower\n'+statement+'\n')
            run = subprocess.run([args.lean, str(path)], cwd=ROOT, env=env,
                                 text=True, capture_output=True, timeout=60)
            # Rejecting because of an unknown name or missing instance is not
            # evidence that Lean detected a false proposition.
            if run.returncode == 0 or "is false" not in run.stdout or "tactic 'decide' proved" not in run.stdout:
                raise RuntimeError(f'Unexpected rejection outcome {name}: '+run.stdout+run.stderr)
            rejected[name] = {'exit_code':run.returncode, 'diagnostic':run.stdout+run.stderr}
        # Build the same dependency closure through Lake as well. This isolated
        # standard-library project avoids downloading unrelated Mathlib caches.
        lake_project = work/'lake-project'
        (lake_project/'PerfectPower').mkdir(parents=True)
        for module in MODULES:
            shutil.copy2(ROOT/f'PerfectPower/{module}.lean', lake_project/'PerfectPower')
        (lake_project/'lakefile.toml').write_text('name = "PlanningBridgeReview"\n[[lean_lib]]\nname = "PerfectPower"\n')
        lake = str(Path(shutil.which(args.lean) or args.lean).resolve().with_name('lake'))
        lake_env = env.copy()
        lake_env.pop('LEAN_PATH', None)
        lake_run = subprocess.run([lake, 'build', 'PerfectPower.PlanningReplayExamples',
                                   'PerfectPower.Petersen50Bridge'], cwd=lake_project,
                                  env=lake_env, text=True, capture_output=True, timeout=180)
        (args.out/'lake.log').write_text(lake_run.stdout+lake_run.stderr)
        if lake_run.returncode:
            raise RuntimeError(lake_run.stdout+lake_run.stderr)
    receipt = json.loads((ROOT/'receipts/planning/independent/certificate50.json').read_text())
    bridge_source = (ROOT/'PerfectPower/Petersen50Bridge.lean').read_text()
    order = json.loads(re.search(r'^def order : List Nat := (.*)$', bridge_source, re.M).group(1))
    if order != receipt['order_original_indices'] or sorted(order) != list(range(50)):
        raise RuntimeError('Order differs from retained replay receipt')
    result = {
        'schema':'pp-planning-lean-bridge/1', 'status':'kernel_checked_semantic_bridge',
        'lean_version':version, 'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),
        'source_binding':source_binding(), 'theorems':len(declarations),
        'new_theorems':sum(name.split('.')[1] in NEW_MODULES for name in declarations),
        'axioms':axioms, 'rejections':rejected,
        'sources':{f'PerfectPower/{m}.lean':sha(ROOT/f'PerfectPower/{m}.lean') for m in MODULES},
        'verification_script_sha256':sha(Path(__file__)),
        'support_sources':{p:sha(ROOT/p) for p in (
            'python/tests/test_planning_bridge.py', 'python/tests/test_planning_certificate.py',
            'python/perfectpower/planning_certificate.py', 'scripts/check_planning_lean.py',
            'native/independent_planning_bdd.cpp', 'native/planning_certificate_trace.hpp')},
        'retained_external_receipt_sha256':sha(ROOT/'receipts/planning/independent/certificate50.json'),
        'retained_external_count':receipt['count'], 'receipt_order_matches_literal':True,
        'small_source_population_kernel_proved':3,
        'negative_capacity_population_kernel_proved':0,
        'literal_allocation_bytes_kernel_decoded_and_count_checked':True,
        'source_permutation_transport_kernel_proved':True,
        'full_stream_to_stage_evidence_kernel_proved':False,
        'full_population_kernel_proved':False,
        'scoped_lake_build_passed':True, 'large_witness_replayed':False, 'historical_search_rerun':False,
        'remaining_trusted_components':[
            'Original file-to-literal source acquisition; checked independently in Python, not proved in Lean',
            'Decompression, file I/O and digest identity for the complete witness',
            'Full header/record stream parser and numeric reference-table invariants',
            'Production Python/packed-table replay refinement to semantic evidence',
            'Construction and kernel checking of complete Petersen50 stage evidence',
        ],
    }
    (args.out/'verification.json').write_text(json.dumps(result,indent=2)+'\n')
    (args.out/'build.log').write_text(json.dumps(commands,indent=2)+'\n')
    (args.out/'rejections.json').write_text(json.dumps(rejected,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ('status','theorems','new_theorems','small_source_population_kernel_proved',
                                           'full_population_kernel_proved')}))


if __name__ == '__main__':
    main()
