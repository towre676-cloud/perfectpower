"""The solved-family registry: every generated complete list of y^2 = x^3 - D, as structured data.

Entries come from the generators' own receipts (`receipts/mordell_branch.json`,
`receipts/thue_graph.json`), not from Lean text.  Each entry is then **checked against the Lean
theorem statement** it cites, in both directions, and the script fails loudly on any gap:
- every `theorem minusD` in `Generated/MordellBranch.lean` and `Generated/MordellThue.lean` must
  parse **completely** (a full match of the statement and of its point list; a partial parse is
  an error, not an omission);
- every parsed theorem must have a registry entry, and every entry a theorem;
- the points must agree exactly.

The compiler (`compiler.mordell_complete`) reads only this registry.  A formatting change in the
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


def main():
    rows = registry_entries()
    try:
        check(rows, lean_lists())
    except RegistryError as e:
        raise SystemExit(f'registry check failed: {e}')
    out = {'label': 'complete lists of y^2 = x^3 - D proved in Lean; each entry checked against '
                    'its theorem statement (full parse, both directions)',
           'entries': len(rows), 'curves': rows}
    (ROOT / 'receipts' / 'mordell_registry.json').write_text(json.dumps(out, indent=1) + '\n')
    print(f'{len(rows)} registry entries, all checked against their Lean statements '
          f'-> receipts/mordell_registry.json')


if __name__ == '__main__':
    main()
