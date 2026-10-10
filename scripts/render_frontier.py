"""Render docs/FRONTIER.md from contracts/current_frontier.json (the single source of status).

python scripts/render_frontier.py          writes the page
python scripts/render_frontier.py --check  exits nonzero if the page is out of date
"""
from pathlib import Path
import json, sys

ROOT = Path(__file__).resolve().parents[1]
SRC, OUT = ROOT/'contracts/current_frontier.json', ROOT/'docs/FRONTIER.md'
ORDER = ('open', 'bounded_route_delivered', 'mitigated', 'implemented')
LABEL = {'open': 'Open', 'bounded_route_delivered': 'Bounded route delivered',
         'mitigated': 'Mitigated', 'implemented': 'Implemented'}


def link(ev):
    if not ev:
        return ''
    out = []
    for e in str(ev).replace(';', ',').split(','):
        e = e.strip()
        if e.startswith('docs/'):
            out.append(f'[{e[5:]}]({e[5:]})')
        elif e:
            out.append(f'`{e}`' if (ROOT/e).exists() or '/' in e else e)
    return ', '.join(out)


def render():
    d = json.loads(SRC.read_text())
    f = d['findings']
    lines = ['# Frontier status', '',
             f'Generated from [`contracts/current_frontier.json`](../contracts/current_frontier.json) '
             f'(schema `{d["schema"]}`, dated {d["date"]}) by `scripts/render_frontier.py`; edit the contract, not this page.', '',
             '| Status | Count |', '|---|---|']
    lines += [f'| {LABEL.get(s, s)} | {sum(x["status"] == s for x in f)} |' for s in ORDER if any(x['status'] == s for x in f)]
    for s in ORDER + tuple(sorted({x['status'] for x in f} - set(ORDER))):
        rows = [x for x in f if x['status'] == s]
        if not rows:
            continue
        lines += ['', f'## {LABEL.get(s, s)}', '', '| # | Finding | Contract | Evidence |', '|---|---|---|---|']
        for x in rows:
            c = str(x.get('contract', '')).replace('|', '\\|').replace('\n', ' ')
            lines.append(f'| {x["id"]} | {x["title"]} | {c} | {link(x.get("evidence"))} |')
    lines += ['', 'Historical, append-only logs of how these findings evolved: '
              '[OPEN_CONTENT_ASSEMBLY.md](OPEN_CONTENT_ASSEMBLY.md) and [OPEN_FRONTS.md](OPEN_FRONTS.md).', '']
    return '\n'.join(lines)


if __name__ == '__main__':
    text = render()
    if '--check' in sys.argv:
        ok = OUT.exists() and OUT.read_text() == text
        print('docs/FRONTIER.md is current' if ok else 'docs/FRONTIER.md is stale: run python scripts/render_frontier.py')
        sys.exit(0 if ok else 1)
    OUT.write_text(text)
    print('wrote', OUT.relative_to(ROOT))
