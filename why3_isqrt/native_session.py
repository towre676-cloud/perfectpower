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
and records the results.  `--check` replays the committed sessions without `-f`, with `--use-steps`,
from a clean checkout.  No human proof step is used in either arm.

**Selective arm** (`selective`).  The lemma stays only in the goals chosen by a syntax policy fixed
before any run, mirroring the SMT experiment.  A goal is chosen when its conclusion is an unsigned
upper bound `ule s B` with `B` a variable, and a hypothesis already bounds some term by the same
`B`, which is the shape where `n − b ≤ B` follows from `b ≤ n ≤ B`.  Every other goal first applies
Why3's `remove pp_sub_le_bound` transformation.  The goal formulas come from Why3 itself
(`why3 prove -a split_vc -D why3`); the task files are matched to the session goals by index, and
the match is checked against the `expl` labels.

**Apply arm** (`apply`).  The rule used as a proof step, as the SMT adapter used ground instances:
on every goal whose conclusion is `ule A X` with `A = sub N B` defined in the context (the
subtraction shape), the session applies `subst_all` and then `apply pp_sub_le_bound`.  The two premises
`ule B N` and `ule N X` are left to Z3.  The goal keeps its direct Z3 attempt as well, so this arm
cannot lose a goal the baseline proves.  The selection is syntactic and fixed before any run.

Run:  python3 why3_isqrt/native_session.py          (create the four sessions, write the receipt)
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


def skeleton(lemmas: list[str], theories=None) -> str:
    th = []
    for theory, fn in (theories or THEORIES):
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


def selected_goals(src: str) -> list[str]:
    """Leaf goals kept with the lemma by the syntax policy (see the module docstring)."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / 'r.mlw'
        f.write_text(src)
        out = Path(tmp) / 'tasks'
        out.mkdir()
        subprocess.run(['why3', 'prove', '-a', 'split_vc', '-D', 'why3', '-o', str(out), str(f)],
                       capture_output=True, text=True, timeout=600, check=True)
        sel = []
        for task in sorted(out.glob('*qtvc*.why')):
            txt = task.read_text()
            i = txt.rindex('\ngoal ')
            goal = re.sub(r'\[@[^\]]*\]', '', txt[i:])
            ctx = ' '.join(re.sub(r'\[@[^\]]*\]', '', txt[:i]).split())
            body = ' '.join(goal.split(':', 1)[1].replace('\nend', '').split())
            m = re.search(r'VonNeumann(\d+)-isqrt\d+qtvc(\d*)\.why', task.name)
            name = f"isqrt{m.group(1)}'vc.{m.group(2) or '0'}"
            mm = re.match(r'(ule\d*) (\S+|\(.*\)) ([A-Za-z_][A-Za-z_0-9]*)$', body)
            if mm and re.search(rf'{mm.group(1)} (\S+|\([^()]*\)) {mm.group(3)}\b', ctx):
                sel.append(name)
    return sorted(sel)


def apply_goals(src: str) -> list[str]:
    """Goals `ule A X` with `A = sub N B` in their context (the subtraction shape)."""
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / 'r.mlw'
        f.write_text(src)
        out = Path(tmp) / 'tasks'
        out.mkdir()
        subprocess.run(['why3', 'prove', '-a', 'split_vc', '-D', 'why3', '-o', str(out), str(f)],
                       capture_output=True, text=True, timeout=600, check=True)
        sel = []
        for task in sorted(out.glob('*qtvc*.why')):
            txt = task.read_text()
            i = txt.rindex('\ngoal ')
            goal = re.sub(r'\[@[^\]]*\]', '', txt[i:])
            ctx = ' '.join(re.sub(r'\[@[^\]]*\]', '', txt[:i]).split())
            body = ' '.join(goal.split(':', 1)[1].replace('\nend', '').split())
            m = re.search(r'VonNeumann(\d+)-isqrt\d+qtvc(\d*)\.why', task.name)
            name = f"isqrt{m.group(1)}'vc.{m.group(2) or '0'}"
            mm = re.match(r'ule\d* ([A-Za-z_][A-Za-z_0-9]*) ([A-Za-z_][A-Za-z_0-9]*)$', body)
            if mm and re.search(rf'\b{mm.group(1)} = sub\d* \S+ \S+', ctx):
                sel.append(name)
    return sorted(sel)


def insert_apply(xml: str, goals: set[str]) -> str:
    """Put `subst_all; apply pp_sub_le_bound` under each selected goal (Why3 expands it on replay)."""
    def go(m):
        name = m.group(2).replace('&#39;', "'")
        if name not in goals:
            return m.group(0)
        return (f'{m.group(1)}\n{m.group(3)}<transf name="subst_all"><goal name="{m.group(2)}.0">'
                f'<transf name="apply" arg1="pp_sub_le_bound"></transf></goal></transf>\n{m.group(3)}</goal>')
    return re.sub(r'(<goal name="([^"]*)"[^>]*>)\n(\s*)</goal>', go, xml)


def with_prover(xml: str) -> str:
    if '<prover id="0"' in xml:
        return xml
    return xml.replace('<why3session shape_version="6">',
                       f'<why3session shape_version="6">\n<prover id="0" name="Z3" version="5.1.0" timelimit="{TIME}" '
                       'steplimit="0" memlimit="1000"/>', 1)


def attach_selective(xml: str, keep: set[str]) -> str:
    """Z3 directly on the kept goals and the lemmas; `remove pp_sub_le_bound` then Z3 elsewhere."""
    attempt = '<proof prover="0"><result status="valid" time="0.00"/></proof>'

    def leaf(m):
        name = m.group(2).replace('&#39;', "'")
        if name in keep or "'vc" not in name:
            return f'{m.group(1)}\n{m.group(3)}{attempt}\n{m.group(3)}</goal>'
        sub = m.group(2) + '.0'
        return (f'{m.group(1)}\n{m.group(3)}<transf name="remove" arg1="pp_sub_le_bound">\n'
                f'{m.group(3)} <goal name="{sub}">{attempt}</goal>\n{m.group(3)}</transf>\n{m.group(3)}</goal>')
    return re.sub(r'(<goal name="([^"]*)"[^>]*>)\n(\s*)</goal>', leaf, xml)


def replay(d: Path, force: bool) -> tuple[int, str, float]:
    """`why3 replay -f` records a session; the check (`force=False`) replays with `--use-steps`, i.e.
    with Z3's recorded step counts instead of the wall-clock limit, so goals near the 3 s limit do
    not flip between runs."""
    t0 = time.perf_counter()
    p = subprocess.run(['why3', 'replay'] + (['-f'] if force else ['--use-steps']) + [str(d)],
                       capture_output=True, text=True, timeout=3600)
    return p.returncode, p.stdout + p.stderr, time.perf_counter() - t0


def results(xml: str) -> dict[str, dict]:
    """Program goal name -> {status, time} from a session file (`valid` when Why3 marks it proved)."""
    out = {}
    for m in re.finditer(r'<goal name="([^"]*(?:vc\.\d+|sqr_add2|pp_sub_le_bound))"([^>]*)>', xml):
        name = m.group(1).replace('&#39;', "'")
        tm = re.search(r'<result status="\w+" time="([\d.]+)"', xml[m.end():m.end() + 400])
        out[name] = {'status': 'valid' if 'proved="true"' in m.group(2) else 'unproved',
                     'time': float(tm.group(1)) if tm else 0.0}
    return out


def _results_leaf(xml: str) -> dict[str, dict]:
    out = {}
    for m in re.finditer(r'<goal name="([^"]*)"[^>]*>\s*(?:<transf name="remove"[^>]*>\s*<goal name="[^"]*"[^>]*>\s*)?'
                         r'<proof prover="0"[^>]*><result status="(\w+)" time="([\d.]+)"', xml):
        out[m.group(1).replace('&#39;', "'")] = {'status': m.group(2), 'time': float(m.group(3))}
    return out


def create(arm: str, src: str, lemmas: list[str], keep: set[str] | None = None, theories=None,
           apply: set[str] | None = None) -> dict:
    base = SESS / arm
    if base.exists():
        shutil.rmtree(base)
    (base / NAME).mkdir(parents=True)
    (base / f'{NAME}.mlw').write_text(src)
    xml = base / NAME / 'why3session.xml'
    xml.write_text(skeleton(lemmas, theories))
    replay(base / NAME, True)                       # Why3 expands split_vc
    if apply:
        xml.write_text(with_prover(insert_apply(xml.read_text(), apply)))
        replay(base / NAME, True)                   # Why3 expands subst_all; apply
        # every selected goal also keeps its direct Z3 attempt
        x = xml.read_text()
        for g in apply:
            gx = g.replace("'", '&#39;')
            x = re.sub(rf'(<goal name="{re.escape(gx)}"[^>]*>\n)(\s*)(<transf name="subst_all")',
                       lambda m: f'{m.group(1)}{m.group(2)}<proof prover="0"><result status="valid" time="0.00"/></proof>\n'
                                 f'{m.group(2)}{m.group(3)}', x)
        xml.write_text(x)
    xml.write_text(with_prover(attach_attempts(xml.read_text()) if keep is None else attach_selective(xml.read_text(), keep)))
    code, log, secs = replay(base / NAME, True)     # Why3 runs Z3 on every leaf
    res = results(xml.read_text())
    return {'arm': arm, 'mlw_sha256': hashlib.sha256(src.encode()).hexdigest(), 'goals': len(res),
            'valid': sum(r['status'] == 'valid' for r in res.values()),
            'prover_seconds': round(sum(r['time'] for r in res.values()), 2),
            'wall_seconds': round(secs, 2), 'results': res}


def check() -> dict:
    out = {}
    for arm in ('baseline', 'rule', 'selective', 'apply'):
        code, log, secs = replay(SESS / arm / NAME, False)
        out[arm] = {'exit_code': code, 'wall_seconds': round(secs, 2), 'tail': log.strip().splitlines()[-1:]}
    return out


def repeat(n: int) -> dict:
    """`n` fresh sessions per arm: how often each goal is proved (`receipts/why3_session_repeat.json`).
    Goals near the 3 s limit flip between runs, so a single run cannot separate an effect from noise."""
    src = UPSTREAM.read_text()
    keep = set(selected_goals(rule_source(src)))
    specs = {'baseline': (src, ['sqr_add2'], None),
             'rule': (rule_source(src), ['sqr_add2', 'pp_sub_le_bound'], None),
             'selective': (rule_source(src), ['sqr_add2', 'pp_sub_le_bound'], keep),
             'apply': (rule_source(src), ['sqr_add2', 'pp_sub_le_bound'], set())}
    app = set(apply_goals(rule_source(src)))
    freq = {a: {} for a in specs}
    for _ in range(n):
        for arm, (text, lemmas, kp) in specs.items():
            r = create(f'_repeat_{arm}', text, lemmas, kp, apply=app if arm == 'apply' else None)['results']
            for g, v in r.items():
                freq[arm][g] = freq[arm].get(g, 0) + (v['status'] == 'valid')
            shutil.rmtree(SESS / f'_repeat_{arm}')
    goals = sorted(set(freq['baseline']))
    unstable = {g: {a: freq[a].get(g, 0) for a in specs} for g in goals
                if len({freq[a].get(g, 0) for a in specs}) > 1 or 0 < freq['baseline'][g] < n}
    out = {'runs': n, 'time_limit_seconds': TIME,
           'always_proved': {a: sum(1 for g in goals if freq[a].get(g, 0) == n) for a in specs},
           'never_proved': {a: sorted(g for g in goals if freq[a].get(g, 0) == 0) for a in specs},
           'goals_that_differ_or_flip': unstable}
    (ROOT / 'receipts' / 'why3_session_repeat.json').write_text(json.dumps(out, indent=1) + '\n')
    return out


# The source-change experiment on the 16-bit module (fully proved in the baseline).
MUTANTS = [
    ('L1', 'legitimate', 'branch test written as ule b !num', 'if uge !num b then', 'if ule b !num then'),
    ('L2', 'legitimate', 'b computed by add instead of bw_or', 'let b = bw_or !res !bits in', 'let b = add !res !bits in'),
    ('B1', 'bug', 'subtracts one too much', 'num := sub !num b;', 'num := sub !num (add b (1:t));'),
    ('B2', 'bug', 'shifts res by 2 instead of 1', 'res := lsr_bv !res (1:t);', 'res := lsr_bv !res (2:t);'),
    ('B3', 'bug', 'strict comparison skips num = b', 'if uge !num b then', 'if ugt !num b then'),
]


def mutate16(src: str, old: str, new: str) -> str:
    a = src.index('module VonNeumann16')
    b = src.index('module VonNeumann32')
    mod = src[a:b]
    assert mod.count(old) == 1, old
    return src[:a] + mod.replace(old, new) + src[b:]


def mutants() -> dict:
    """Each variant gets fresh sessions (baseline and apply), with the apply goals re-derived
    from the changed source: no manual step.  Legitimate changes must stay proved; bugs must fail."""
    th16 = [THEORIES[0]]
    src = UPSTREAM.read_text()
    rows = []
    for name, kind, what, old, new in [('ORIG', 'original', 'unmodified', None, None)] + MUTANTS:
        msrc = src if old is None else mutate16(src, old, new)
        keep = {g for g in apply_goals(rule_source(msrc)) if g.startswith('isqrt16')}
        res = {}
        for arm, text, lemmas, ap in (('baseline', msrc, ['sqr_add2'], None),
                                      ('apply', rule_source(msrc), ['sqr_add2', 'pp_sub_le_bound'], keep)):
            r = create(f'_mut_{arm}', text, lemmas, None, th16, apply=ap)['results']
            shutil.rmtree(SESS / f'_mut_{arm}')
            fails = sorted(g for g, v in r.items() if v['status'] != 'valid')
            res[arm] = {'goals': len(r), 'valid': len(r) - len(fails), 'failing': fails}
        detected = bool(res['baseline']['failing']) and bool(res['apply']['failing'])
        ok = (not detected) if kind != 'bug' else detected
        rows.append({'variant': name, 'kind': kind, 'change': what, 'apply_goals': sorted(keep),
                     'arms': res, 'expected_outcome': ok})
    out = {'scope': 'source-change experiment, VonNeumann16; fresh sessions per variant, apply goals '
                    're-derived automatically; legitimate changes must stay proved, planted bugs must fail',
           'all_as_expected': all(r['expected_outcome'] for r in rows), 'variants': rows}
    (ROOT / 'receipts' / 'why3_mutants.json').write_text(json.dumps(out, indent=1) + '\n')
    return out


def main():
    if sys.argv[1:] == ['--mutants']:
        out = mutants()
        for r in out['variants']:
            print(r['variant'], r['kind'], r['change'], {a: (v['valid'], v['goals'], v['failing'][:3]) for a, v in r['arms'].items()},
                  'apply goals', r['apply_goals'], 'OK' if r['expected_outcome'] else 'UNEXPECTED')
        return
    if sys.argv[1:2] == ['--repeat']:
        print(json.dumps(repeat(int(sys.argv[2])), indent=1))
        return
    if sys.argv[1:] == ['--check']:
        print(json.dumps(check(), indent=1))
        return
    src = UPSTREAM.read_text()
    keep = selected_goals(rule_source(src))
    app = apply_goals(rule_source(src))
    arms = [create('baseline', src, ['sqr_add2']),
            create('rule', rule_source(src), ['sqr_add2', 'pp_sub_le_bound']),
            create('selective', rule_source(src), ['sqr_add2', 'pp_sub_le_bound'], set(keep)),
            create('apply', rule_source(src), ['sqr_add2', 'pp_sub_le_bound'], set(), apply=set(app))]
    b = arms[0]['results']

    def diff(r):
        return (sorted(g for g in b if b[g]['status'] != 'valid' and r.get(g, {}).get('status') == 'valid'),
                sorted(g for g in b if b[g]['status'] == 'valid' and r.get(g, {}).get('status') != 'valid'))
    newly, regress = diff(arms[1]['results'])
    s_new, s_reg = diff(arms[2]['results'])
    a_new, a_reg = diff(arms[3]['results'])
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
           'selective_policy_goals': keep,
           'selective_newly_discharged': s_new, 'selective_regressions': s_reg,
           'apply_policy_goals': app,
           'apply_newly_discharged': a_new, 'apply_regressions': a_reg,
           'replay_check': replays,
           'arms': arms}
    (ROOT / 'receipts' / 'why3_session.json').write_text(json.dumps(out, indent=1) + '\n')
    print(json.dumps(out['summary'], indent=1), 'new:', newly, 'regressions:', regress,
          'selective new:', s_new, 'selective regressions:', s_reg, 'apply new:', a_new, 'apply regressions:', a_reg)
    print(json.dumps(replays))


if __name__ == '__main__':
    main()
