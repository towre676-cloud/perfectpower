"""The solved-family registry: every generated complete list of y^2 = x^3 - D, as structured data.

Entries come from the generators' own receipts (`receipts/mordell_branch.json`,
`receipts/thue_graph.json`), not from Lean text.  Each entry is then **checked against the Lean
theorem statement** it cites, in both directions, and the script fails loudly on any gap:
- every `theorem minusD` in `Generated/MordellBranch.lean` and `Generated/MordellThue.lean` must
  parse **completely** (a full match of the statement and of its point list; a partial parse is
  an error, not an omission);
- every parsed theorem must have a registry entry, and every entry a theorem;
- the points must agree exactly.

Two further sections, built and checked the same way (strict parse of every statement, points
compared with an independent source, here the committed Sage/PARI census):
- `positive_curves`: `theorem plus{k}` of `Generated/ClassLists/K*.lean`, complete lists of
  `y^2 = x^3 + k` with no premise;
- `conditional_curves`: `theorem minus{D}` of `Generated/Minus*.lean` and `Field756.lean`,
  complete lists **conditional on the named Matveev hypotheses** listed with each entry.

The compiler (`compiler.mordell_complete`, `compiler.mordell_conditional`) reads only this registry.  A formatting change in the
generated Lean therefore makes `make receipts` fail instead of silently dropping a curve.

Writes receipts/mordell_registry.json.
"""
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

SOURCES = {'MordellBranch': 'PerfectPower.DescentBranch.complete_of_branch',
           'MordellThue': 'PerfectPower.DescentThue.complete_of_thue'}

_INT = r'(?:-?\d+|\(-\d+\))'
_PT = rf'\(({_INT}), ({_INT})\)'
_STMT = re.compile(r'^theorem minus(\d+) \(x y : ℤ\) : y \^ 2 = x \^ 3 - (\d+) ↔ '
                   r'\(x, y\) ∈ \(\[(.*)\] : List \(ℤ × ℤ\)\) :=$')
_LIST = re.compile(rf'^(?:{_PT}(?:, {_PT})*)?$')


def _int(tok: str) -> int:
    return int(tok.strip('()'))


class RegistryError(Exception):
    pass


def lean_lists(root: Path = ROOT) -> dict[int, tuple[str, list[list[int]]]]:
    """D -> (Lean name, sorted points), parsed strictly from the generated statements."""
    out = {}
    for mod in SOURCES:
        text = (root / 'PerfectPower' / 'Generated' / f'{mod}.lean').read_text()
        lines = [ln for ln in text.splitlines() if ln.startswith('theorem minus')]
        for ln in lines:
            m = _STMT.match(ln)
            if m is None:
                raise RegistryError(f'{mod}: unparsed theorem statement: {ln[:120]}')
            name, D, body = m.groups()
            if name != D:
                raise RegistryError(f'{mod}: theorem minus{name} states D = {D}')
            if _LIST.match(body) is None:
                raise RegistryError(f'{mod}.minus{D}: unparsed point list: {body[:120]}')
            pts = sorted([_int(x), _int(y)] for x, y in re.findall(_PT, body))
            if int(D) in out:
                raise RegistryError(f'D = {D} proved twice')
            out[int(D)] = (f'PerfectPower.Generated.{mod}.minus{D}', pts)
    return out


def registry_entries(root: Path = ROOT) -> list[dict]:
    """Entries from the generators' receipts."""
    rows = []
    branch = json.loads((root / 'receipts' / 'mordell_branch.json').read_text())
    for c in branch['curves_detail']:
        if c['status'] == 'COMPLETE':
            rows.append({'D': c['D'], 'points': sorted(c['points']), 'lean': c['lean'],
                         'via': SOURCES['MordellBranch'], 'receipt': 'receipts/mordell_branch.json'})
    thue = json.loads((root / 'receipts' / 'thue_graph.json').read_text())
    for c in thue['curves']:
        if c['status'] == 'COMPLETE':
            rows.append({'D': c['D'], 'points': sorted(c['points']), 'lean': c['lean'],
                         'via': SOURCES['MordellThue'], 'receipt': 'receipts/thue_graph.json'})
    return sorted(rows, key=lambda r: r['D'])


def check(rows: list[dict], lean: dict) -> None:
    by_d = {r['D']: r for r in rows}
    if len(by_d) != len(rows):
        raise RegistryError('duplicate D in the receipts')
    for D in sorted(set(by_d) | set(lean)):
        if D not in lean:
            raise RegistryError(f'D = {D}: registry entry without a Lean theorem')
        if D not in by_d:
            raise RegistryError(f'D = {D}: Lean theorem {lean[D][0]} missing from the receipts')
        name, pts = lean[D]
        if by_d[D]['lean'] != name:
            raise RegistryError(f'D = {D}: receipt cites {by_d[D]["lean"]}, Lean has {name}')
        if by_d[D]['points'] != pts:
            raise RegistryError(f'D = {D}: receipt points {by_d[D]["points"]} != Lean {pts}')


_PLUS = re.compile(r'^theorem plus(\d+) \(x y : ℤ\) : y \^ 2 = x \^ 3 \+ (\d+) ↔ '
                   r'\(x, y\) ∈ \(\[(.*)\] : List \(ℤ × ℤ\)\) :=$')
_COND = re.compile(r'^theorem minus(\d+) ((?:\(\S+ : \S+\) ?)+)\n    \(x y : ℤ\) : y \^ 2 = x \^ 3 - (\d+) ↔ '
                   r'\(x, y\) ∈ \(\[(.*)\] : List \(ℤ × ℤ\)\) :=$', re.M)
_HYP = re.compile(r'\((\S+) : (\S+)\)')


def census_points(root: Path = ROOT) -> dict[int, list[list[int]]]:
    """k -> sorted points, from the committed census (an independent Sage/PARI computation)."""
    import math
    out = {}
    for line in (root / 'data' / 'mordell_census.jsonl').read_text().splitlines():
        r = json.loads(line)
        pts = []
        for x in r['x_coordinates']:
            y = math.isqrt(x ** 3 + r['k'])
            pts += [[x, y], [x, -y]] if y else [[x, 0]]
        out[r['k']] = sorted(pts)
    return out


def _points(body: str, where: str) -> list[list[int]]:
    if _LIST.match(body) is None:
        raise RegistryError(f'{where}: unparsed point list: {body[:120]}')
    return sorted([_int(x), _int(y)] for x, y in re.findall(_PT, body))


def positive_lists(root: Path = ROOT, cen=None) -> list[dict]:
    cen = cen or census_points(root)
    out = []
    for path in sorted((root / 'PerfectPower' / 'Generated' / 'ClassLists').glob('K*.lean')):
        for ln in path.read_text().splitlines():
            if not ln.startswith('theorem plus'):
                continue
            m = _PLUS.match(ln)
            if m is None:
                raise RegistryError(f'{path.name}: unparsed theorem statement: {ln[:120]}')
            k, k2, body = m.groups()
            if k != k2 or path.stem != f'K{k}':
                raise RegistryError(f'{path.name}: theorem plus{k} states k = {k2}')
            pts = _points(body, f'{path.name}.plus{k}')
            if pts != cen[int(k)]:
                raise RegistryError(f'k = {k}: Lean points {pts} != census {cen[int(k)]}')
            out.append({'k': int(k), 'points': pts, 'lean': f'PerfectPower.Generated.ClassLists.K{k}.plus{k}',
                        'premises': []})
    return sorted(out, key=lambda r: r['k'])


def conditional_lists(root: Path = ROOT, cen=None) -> list[dict]:
    cen = cen or census_points(root)
    out = []
    files = sorted((root / 'PerfectPower' / 'Generated').glob('Minus*.lean')) + \
        [root / 'PerfectPower' / 'Generated' / 'Field756.lean']
    for path in files:
        text = path.read_text()
        n_stmt = sum(1 for ln in text.splitlines() if ln.startswith('theorem minus'))
        found = list(_COND.finditer(text))
        if len(found) != n_stmt:
            raise RegistryError(f'{path.name}: {n_stmt} statements, {len(found)} parsed')
        for m in found:
            D, hyps, D2, body = m.groups()
            if D != D2:
                raise RegistryError(f'{path.name}: theorem minus{D} states D = {D2}')
            prem = [t for _, t in _HYP.findall(hyps)]
            if not prem or not all('matveev' in t for t in prem):
                raise RegistryError(f'{path.name}.minus{D}: unexpected hypotheses {prem}')
            pts = _points(body, f'{path.name}.minus{D}')
            if pts != cen[-int(D)]:
                raise RegistryError(f'D = {D}: Lean points {pts} != census {cen[-int(D)]}')
            out.append({'D': int(D), 'points': pts, 'lean': f'PerfectPower.Generated.{path.stem}.minus{D}',
                        'premises': prem})
    return sorted(out, key=lambda r: r['D'])


def main():
    rows = registry_entries()
    try:
        check(rows, lean_lists())
        cen = census_points()
        pos = positive_lists(cen=cen)
        cond = conditional_lists(cen=cen)
    except RegistryError as e:
        raise SystemExit(f'registry check failed: {e}')
    out = {'label': 'complete lists of y^2 = x^3 - D proved in Lean; each entry checked against '
                    'its theorem statement (full parse, both directions)',
           'entries': len(rows), 'curves': rows,
           'positive_curves': pos,
           'conditional_label': 'complete lists of y^2 = x^3 - D conditional on the named Matveev '
                                'hypotheses; NOT unconditional theorems',
           'conditional_curves': cond}
    (ROOT / 'receipts' / 'mordell_registry.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f'{len(rows)} registry entries, {len(pos)} positive-k and {len(cond)} conditional curves, all '
          f'checked against their Lean statements -> receipts/mordell_registry.json')


if __name__ == '__main__':
    main()
