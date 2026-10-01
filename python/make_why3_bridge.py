"""Run the Why3 consumer bridge on the example verification conditions.

For each `examples/smt/*.smt2` task with a checked replacement, the WhyML module and its control
are written to `examples/why3/`, and Why3 (prover z3) is run on both:
- `accepted` requires the replacement lemma **and** the VC to be proved;
- the control (the same VC without the imported curve theorem) is reported as Why3 answers it.

The tasks are constructed examples, not an independent workload.
Run: python3 python/make_why3_bridge.py   (needs why3 and z3; about 1 minute)
Writes receipts/why3_bridge.json.
"""
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.why3_bridge import Untranslatable, emit, run_why3  # noqa: E402


def main():
    out = ROOT / 'examples' / 'why3'
    out.mkdir(parents=True, exist_ok=True)
    rows = []
    for task in sorted((ROOT / 'examples' / 'smt').glob('*.smt2')):
        text = task.read_text()
        try:
            why, control, meta = emit(text)
        except Untranslatable as ex:
            rows.append({'task': task.name, 'bridged': False, 'reason': str(ex)})
            print(f'{task.name}: not bridged ({ex})')
            continue
        (out / f'{task.stem}.mlw').write_text(why)
        (out / f'{task.stem}_control.mlw').write_text(control)
        res = run_why3(out / f'{task.stem}.mlw', 10)['goals']
        ctl = run_why3(out / f'{task.stem}_control.mlw', 10)['goals']
        accepted = bool(res) and all(v == 'Valid' for v in res.values()) and 'vc' in res \
            and any(g.startswith('replacement') for g in res)
        rows.append({'task': task.name, 'bridged': True, 'theorems': [r['theorem'] for r in meta['replacements']],
                     'goals': res, 'accepted': accepted, 'control': ctl})
        print(f'{task.name}: {res} accepted={accepted} control={ctl}')
    import subprocess
    ver = subprocess.run(['why3', '--version'], capture_output=True, text=True).stdout.strip()
    rec = {'label': 'CONSTRUCTED example VCs; Why3 (prover z3) checks the replacement lemma and the VC; the '
                    'curve theorem is imported as a val lemma whose proof is in Lean',
           'why3': ver, 'tasks': rows}
    (ROOT / 'receipts' / 'why3_bridge.json').write_text(json.dumps(rec, indent=1) + '\n')


if __name__ == '__main__':
    main()
