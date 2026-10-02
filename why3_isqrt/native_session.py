"""Native Why3 proof sessions for the Von Neumann integer square root, with and without the guarded
unsigned rule (`receipts/why3_session.json`, sessions under `why3_isqrt/sessions/`).

The program is Why3's own `examples/isqrt_von_neumann.mlw` (C. Marché and S. Dailler), unmodified in
the baseline arm.  The rule arm adds one lemma per module, the guarded unsigned subtraction bound

    lemma pp_sub_le_bound: forall n b x: t. ule b n -> ule n x -> ule (sub n b) x

which is `PerfectPower.BVWorkflow.sub_le_bound` (proved in Lean for every word width).  Why3 must
prove the lemma itself in the session as well; nothing is admitted.

Both arms use the same automatic proof script: `split_vc` on every program VC, then Z3 on every
leaf, at the same time limit.  The sessions are created with Why3's own tools: a skeleton
`why3session.xml` names the top-level goals, `why3 replay -f` expands `split_vc` (Why3 computes the
subgoals and their shapes), a Z3 attempt is attached to every leaf, and `why3 replay -f` runs them
and records the results.  `--check` replays the committed sessions without `-f` from a clean
checkout.  No human proof step is used in either arm.

Run:  python3 why3_isqrt/native_session.py          (create both sessions, write the receipt)
      python3 why3_isqrt/native_session.py --check  (replay the committed sessions)
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
UPSTREAM = HERE / 'upstream' / 'hipsleek__why3' / 'examples' / 'isqrt_von_neumann.mlw'
SESS = HERE / 'sessions'
NAME = 'isqrt_von_neumann'
THEORIES = [('VonNeumann16', 'isqrt16'), ('VonNeumann32', 'isqrt32'), ('VonNeumann64', 'isqrt64')]
TIME = 3
RULE = ('  lemma pp_sub_le_bound: forall n b x: t. ule b n -> ule n x -> ule (sub n b) x\n'
        '  (* PerfectPower.BVWorkflow.sub_le_bound, proved in Lean for every width *)\n')


def rule_source(src: str) -> str:
    """Insert the rule after `sqr_add2` in each module (the only change)."""
    pat = re.compile(r'(  lemma sqr_add2: forall x y\.\n    sqr \(add x y\) = add \(sqr x\) \(mul y \(add \(mul \(2:t\) x\) y\)\)\n)')
    out, n = pat.subn(lambda m: m.group(1) + '\n' + RULE, src)
    assert n == 3, n
    return out


def skeleton(lemmas: list[str]) -> str:
    th = []
    for theory, fn in THEORIES:
        goals = ''.join(f' <goal name="{g}"><proof prover="0"><result status="valid" time="0.00"/></proof></goal>\n'
                        for g in lemmas)
        th.append(f'<theory name="{theory}">\n{goals} <goal name="{fn}&apos;vc"><transf name="split_vc"></transf></goal>\n</theory>\n')
    return ('<?xml version="1.0" encoding="UTF-8"?>\n'
            '<!DOCTYPE why3session PUBLIC "-//Why3//proof session v5//EN"\n"https://www.why3.org/why3session.dtd">\n'
            '<why3session shape_version="6">\n'
            f'<prover id="0" name="Z3" version="5.1.0" timelimit="{TIME}" steplimit="0" memlimit="1000"/>\n'
            f'<file format="whyml">\n<path name=".."/><path name="{NAME}.mlw"/>\n' + ''.join(th) +
            '</file>\n</why3session>\n')


def attach_attempts(xml: str) -> str:
    """Give every leaf goal (no proof, no transformation) a Z3 attempt."""
    return re.sub(r'(<goal name="[^"]*"[^>]*>)\n(\s*)</goal>',
                  lambda m: f'{m.group(1)}\n{m.group(2)}<proof prover="0"><result status="valid" time="0.00"/></proof>\n'
                            f'{m.group(2)}</goal>', xml)


def replay(d: Path, force: bool) -> tuple[int, str, float]:
    t0 = time.perf_counter()
    p = subprocess.run(['why3', 'replay'] + (['-f'] if force else []) + [str(d)],
                       capture_output=True, text=True, timeout=3600)
    return p.returncode, p.stdout + p.stderr, time.perf_counter() - t0


def results(xml: str) -> dict[str, dict]:
    """Leaf goal name -> {status, time} from a session file."""
    out = {}
    for m in re.finditer(r'<goal name="([^"]*)"[^>]*>\s*<proof prover="0"[^>]*><result status="(\w+)" time="([\d.]+)"',
                         xml):
        out[m.group(1).replace('&#39;', "'")] = {'status': m.group(2), 'time': float(m.group(3))}
    return out


def create(arm: str, src: str, lemmas: list[str]) -> dict:
    base = SESS / arm
    if base.exists():
        shutil.rmtree(base)
    (base / NAME).mkdir(parents=True)
    (base / f'{NAME}.mlw').write_text(src)
    xml = base / NAME / 'why3session.xml'
    xml.write_text(skeleton(lemmas))
    replay(base / NAME, True)                       # Why3 expands split_vc
    xml.write_text(attach_attempts(xml.read_text()))
    code, log, secs = replay(base / NAME, True)     # Why3 runs Z3 on every leaf
    res = results(xml.read_text())
    return {'arm': arm, 'mlw_sha256': hashlib.sha256(src.encode()).hexdigest(), 'goals': len(res),
            'valid': sum(r['status'] == 'valid' for r in res.values()),
            'prover_seconds': round(sum(r['time'] for r in res.values()), 2),
            'wall_seconds': round(secs, 2), 'results': res}


def check() -> dict:
    out = {}
    for arm in ('baseline', 'rule'):
        code, log, secs = replay(SESS / arm / NAME, False)
        out[arm] = {'exit_code': code, 'wall_seconds': round(secs, 2), 'tail': log.strip().splitlines()[-1:]}
    return out


def main():
    if sys.argv[1:] == ['--check']:
        print(json.dumps(check(), indent=1))
        return
    src = UPSTREAM.read_text()
    arms = [create('baseline', src, ['sqr_add2']),
            create('rule', rule_source(src), ['sqr_add2', 'pp_sub_le_bound'])]
    b, r = arms[0]['results'], arms[1]['results']
    newly = sorted(g for g in b if b[g]['status'] != 'valid' and r.get(g, {}).get('status') == 'valid')
    regress = sorted(g for g in b if b[g]['status'] == 'valid' and r.get(g, {}).get('status') != 'valid')
    replays = check()
    versions = {'why3': subprocess.run(['why3', '--version'], capture_output=True, text=True).stdout.strip(),
                'z3': subprocess.run(['z3', '--version'], capture_output=True, text=True).stdout.strip()}
    out = {'scope': 'native Why3 proof sessions (why3 replay) for an independently written program; '
                    'paired baseline / guarded-rule arms; one machine, one run',
           'source_program': str(UPSTREAM.relative_to(ROOT)),
           'source_sha256': hashlib.sha256(src.encode()).hexdigest(),
           'transformation': {'added_lemma': RULE.strip(), 'lean_theorem': 'PerfectPower.BVWorkflow.sub_le_bound',
                              'admitted': False},
           'proof_script': f'split_vc on each program VC, Z3 5.1.0 on every leaf, {TIME} s; no manual steps',
           'tools': versions,
           'summary': {a['arm']: {k: a[k] for k in ('goals', 'valid', 'prover_seconds', 'wall_seconds')} for a in arms},
           'newly_discharged': newly, 'regressions': regress,
           'replay_check': replays,
           'arms': arms}
    (ROOT / 'receipts' / 'why3_session.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out['summary'], indent=1), 'new:', newly, 'regressions:', regress)
    print(json.dumps(replays))


if __name__ == '__main__':
    main()
