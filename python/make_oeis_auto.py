"""Generated Lean for OEIS definitions, from the definition language `perfectpower.oeis_dsl`.

Input: the committed snapshot `data/oeis/` (unmodified `.seq` files) and its candidate lists,
`discovery_{sqrt2,phi,sqrt3}.json` (orbit coordinates found in the global index) and
`setsq_candidates.json` (entries named `Numbers k such that D*k^2 + c is a square`).

For every candidate entry the name (`%N`) is translated into the definition language, the
encoding is re-evaluated against **every** listed term at the entry's offset, a coordinate of a
known unit orbit is fitted (or, for sets, the engine's seed certificate is computed), and a Lean
block is emitted: a definition generated from the encoding, and the theorem tying it to the orbit.

    python3 python/make_oeis_auto.py --accept    # compile every block alone; record the accepted
    python3 python/make_oeis_auto.py             # (make verify) regenerate, deterministically

`--accept` compiles each block in isolation with Lean and writes `data/oeis/auto_accepted.json`
(entry -> SHA-256 of its block).  The default mode regenerates every block, requires each accepted
block to be reproduced byte for byte, and writes `PerfectPower/Generated/OEISAuto.lean` (built by
`lake build`) and `receipts/oeis_auto.json`.  A block that changes, or a new block, fails the run
until it is accepted again.

`sqrt3` is the withheld family: the receipt reports, for each of its discovery candidates, the
coordinate discovery proposed and the mechanism the compiler proved.
"""
import argparse
import hashlib
import json
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'python'))

from perfectpower.oeis_dsl import compile_entry  # noqa: E402
from perfectpower.oeis_source import SeqDir, parse_seq  # noqa: E402

DATA = ROOT / 'data' / 'oeis'
OUT = ROOT / 'PerfectPower' / 'Generated' / 'OEISAuto.lean'
ACCEPTED = DATA / 'auto_accepted.json'
GROUPS = ('sqrt2', 'phi', 'sqrt3')

HEADER = '''import PerfectPower.FibOrbit
import PerfectPower.SqrtTwoOrbit
import PerfectPower.OEISLib

/-!
# OEIS definitions, generated (do not edit)

Written by `python/make_oeis_auto.py` from the committed `.seq` files in `data/oeis/` through the
definition language `python/perfectpower/oeis_dsl.py`.  Each block quotes the entry's name, defines
the entry **from that text** (recurrence with its initial values, rational generating function,
coordinate expression, or set with its domain) at the entry's own offset, and proves it equal to a
coordinate of a quadratic-unit orbit, or, for a set, that it lists the set in increasing order via
a seed certificate of `QuadOrbit`.  OEIS content: CC BY-SA 4.0, The OEIS Foundation.
-/

namespace PerfectPower.OEISAuto

'''


def candidates():
    """(entry id, groups) in a fixed order."""
    groups = {}
    for g in GROUPS:
        for c in json.loads((DATA / f'discovery_{g}.json').read_text()):
            groups.setdefault(c['oeis'], []).append(g)
    for aid in json.loads((DATA / 'setsq_candidates.json').read_text()):
        groups.setdefault(aid, []).append('setsq')
    return sorted(groups.items())


def compile_all():
    src = SeqDir(DATA)
    out = []
    for aid, groups in candidates():
        r = compile_entry(parse_seq(src.text(aid)))
        r['groups'] = groups
        if r['lean']:
            r['sha256'] = hashlib.sha256(r['lean'].encode()).hexdigest()
        out.append(r)
    return out


def lean_check(block: str) -> str | None:
    """None if the block compiles alone, else the first error lines."""
    with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=ROOT / '.lake', delete=False) as f:
        f.write(HEADER + block + '\nend PerfectPower.OEISAuto\n')
        path = f.name
    try:
        p = subprocess.run(['lake', 'env', 'lean', path], cwd=ROOT, capture_output=True, text=True)
        return None if p.returncode == 0 else (p.stdout + p.stderr)[:600]
    finally:
        Path(path).unlink()


def accept():
    recs = compile_all()
    acc, failed = {}, {}
    for r in recs:
        if not r['lean']:
            continue
        err = lean_check(r['lean'])
        if err is None:
            acc[r['oeis']] = r['sha256']
        else:
            failed[r['oeis']] = err
        print(r['oeis'], 'ok' if err is None else 'FAILED')
    ACCEPTED.write_text(json.dumps({'accepted': acc, 'failed_to_compile': failed}, indent=1) + '\n')
    print(f'{len(acc)} accepted, {len(failed)} failed')


def withheld_report(recs):
    """The sqrt3 family was added last: what discovery proposed vs what was proved."""
    disc = {c['oeis']: c for c in json.loads((DATA / 'discovery_sqrt3.json').read_text())}
    rows = []
    for r in recs:
        if 'sqrt3' not in r['groups']:
            continue
        c = disc[r['oeis']]
        rows.append({'oeis': r['oeis'],
                     'discovered': f"{c['map']} on {c['filter']} powers, shift {c['power_index_of_first_term']}",
                     'status': r['status'], 'proved_family': r.get('family'),
                     'fit': r.get('fit'), 'relation': r.get('relation'),
                     'mechanism_agrees': r.get('family') == 'sqrt3' if r['status'] == 'PROVED' else None})
    return rows


def build():
    acc = json.loads(ACCEPTED.read_text())['accepted']
    recs = compile_all()
    blocks, drift = [], []
    for r in recs:
        if not r['lean']:
            continue
        if acc.get(r['oeis']) == r['sha256']:
            blocks.append(r['lean'])
            r['status'] = 'PROVED'
        else:
            drift.append(r['oeis'])
            r['status'] = 'EMITTED_NOT_ACCEPTED'
    missing = sorted(set(acc) - {r['oeis'] for r in recs if r['status'] == 'PROVED'})
    OUT.write_text(HEADER + '\n'.join(blocks) + '\nend PerfectPower.OEISAuto\n')
    for r in recs:
        r.pop('lean', None)
    tally = {}
    for r in recs:
        tally[r['status']] = tally.get(r['status'], 0) + 1
    receipt = {'snapshot': SeqDir(DATA).version(), 'lean_file': str(OUT.relative_to(ROOT)),
               'namespace': 'PerfectPower.OEISAuto',
               'promotion_rule': 'the encoding, read from the entry name, reproduces every listed term '
                                 'at the entry offset; the generated Lean definition is that encoding; '
                                 'the generated theorem compiles',
               'tally': tally, 'withheld_sqrt3': withheld_report(recs), 'entries': recs}
    (ROOT / 'receipts' / 'oeis_auto.json').write_text(json.dumps(receipt, indent=1) + '\n')
    print(f'{len(recs)} candidate entries {tally} -> {OUT.relative_to(ROOT)}')
    if drift or missing:
        raise SystemExit(f'generated blocks changed or disappeared: {drift + missing}; re-run --accept')


if __name__ == '__main__':
    ap = argparse.ArgumentParser()
    ap.add_argument('--accept', action='store_true')
    accept() if ap.parse_args().accept else build()
