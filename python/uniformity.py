"""Uniformity data from the Mordell census (NUMERICAL EVIDENCE ONLY; proves nothing).

Reads data/mordell_census.csv and writes
  receipts/uniformity_summary.json   per-rank and per-|k|-bin statistics
  docs/figures/uniformity.html       two small panels + table view (static, no dependencies)

Lang's conjecture predicts #integral points <= C^(1 + rank) on quasi-minimal models; the census
reports max over curves of N^(1/(1+rank)) as an empirical lower bound for any such C on this
family.  Counts are of integral points up to the sign of y.  Only rows whose completeness is
certified (or conditional on an unproven rank, flagged separately) enter the statistics.
"""
import csv
import json
import math
from collections import defaultdict
from pathlib import Path

root = Path(__file__).resolve().parents[1]
rows = list(csv.DictReader(open(root / 'data' / 'mordell_census.csv')))
use = [r for r in rows if r['certification'] not in ('scan_only', 'SCAN_EVIDENCE_ONLY')]
by_rank = defaultdict(list)
for r in use:
    by_rank[int(r['rank'])].append(r)
rank_stats = []
for rk in sorted(by_rank):
    rs = by_rank[rk]
    counts = sorted(int(r['n_points_up_to_sign']) for r in rs)
    best = max(rs, key=lambda r: (int(r['n_points_up_to_sign']), -abs(int(r['k']))))
    rank_stats.append({
        'rank': rk, 'curves': len(rs), 'max_points': counts[-1], 'median_points': counts[len(counts) // 2],
        'k_attaining_max': int(best['k']),
        'conditional_rows': sum(1 for r in rs if r['certification'] not in ('INDEPENDENT_COMPUTATION', 'certified_by_independent_computation')),
    })
bins = defaultdict(list)
for r in use:
    b = int(math.floor(math.log10(abs(int(r['k'])) ) * 2)) / 2      # half-decade bins
    bins[b].append(int(r['n_points_up_to_sign']))
bin_stats = [{'log10_k_bin_start': b, 'curves': len(v), 'max_points': max(v)} for b, v in sorted(bins.items())]
lang_C = max((int(r['n_points_up_to_sign']) ** (1 / (1 + int(r['rank']))), int(r['k']))
             for r in use if int(r['n_points_up_to_sign']) > 0)
summary = {
    'label': 'NUMERICAL EVIDENCE - proves nothing about Lang, Hindry-Silverman or uniform bounds',
    'curves_used': len(use), 'curves_excluded_scan_only': len(rows) - len(use),
    'by_rank': rank_stats, 'by_log10_abs_k': bin_stats,
    'empirical_lang_constant': {'max_N^(1/(1+rank))': round(lang_C[0], 4), 'k': lang_C[1]},
}
(root / 'receipts' / 'uniformity_summary.json').write_text(json.dumps(summary, indent=1) + '\n')

# ---------------------------------------------------------------- figure (static HTML + SVG)
W, H, PAD = 420, 260, 44


def panel(title, xs, ys, xlabel, tips, xticks):
    x0, x1 = min(xticks), max(xticks)
    ymax = max(ys) if ys else 1
    ystep = max(1, math.ceil(ymax / 5))
    ytop = ystep * math.ceil(ymax / ystep)
    sx = lambda x: PAD + (x - x0) / (x1 - x0 or 1) * (W - 2 * PAD)
    sy = lambda y: H - PAD - y / ytop * (H - 2 * PAD)
    g = [f'<figure class="panel"><figcaption>{title}</figcaption>'
         f'<svg viewBox="0 0 {W} {H}" role="img" aria-label="{title}">']
    for yt in range(0, ytop + 1, ystep):
        g.append(f'<line class="grid" x1="{PAD}" x2="{W - PAD}" y1="{sy(yt):.1f}" y2="{sy(yt):.1f}"/>'
                 f'<text class="tick" x="{PAD - 6}" y="{sy(yt) + 4:.1f}" text-anchor="end">{yt}</text>')
    for xt in xticks:
        g.append(f'<text class="tick" x="{sx(xt):.1f}" y="{H - PAD + 16}" text-anchor="middle">{xt:g}</text>')
    g.append(f'<text class="axis" x="{W / 2}" y="{H - 6}" text-anchor="middle">{xlabel}</text>')
    pts = ' '.join(f'{sx(x):.1f},{sy(y):.1f}' for x, y in zip(xs, ys))
    g.append(f'<polyline class="line" points="{pts}"/>')
    for x, y, t in zip(xs, ys, tips):
        g.append(f'<g class="dot"><circle class="hit" cx="{sx(x):.1f}" cy="{sy(y):.1f}" r="10"/>'
                 f'<circle class="mark" cx="{sx(x):.1f}" cy="{sy(y):.1f}" r="4.5"/><title>{t}</title></g>')
    g.append('</svg></figure>')
    return '\n'.join(g)


p1 = panel('Maximum number of integral points vs. Mordell–Weil rank',
           [s['rank'] for s in rank_stats], [s['max_points'] for s in rank_stats], 'rank',
           [f"rank {s['rank']}: max {s['max_points']} points (k = {s['k_attaining_max']}), "
            f"{s['curves']} curves" for s in rank_stats],
           list(range(0, max(s['rank'] for s in rank_stats) + 1)))
p2 = panel('Maximum number of integral points vs. log10 |k| (half-decade bins)',
           [b['log10_k_bin_start'] for b in bin_stats], [b['max_points'] for b in bin_stats], 'log10 |k|',
           [f"log10|k| in [{b['log10_k_bin_start']}, {b['log10_k_bin_start'] + 0.5}): max {b['max_points']}, "
            f"{b['curves']} curves" for b in bin_stats],
           [b['log10_k_bin_start'] for b in bin_stats])
table = ''.join(f"<tr><td>{s['rank']}</td><td>{s['curves']}</td><td>{s['median_points']}</td>"
                f"<td>{s['max_points']}</td><td>{s['k_attaining_max']}</td></tr>" for s in rank_stats)
K = max(abs(int(r['k'])) for r in rows)
html = f'''<!doctype html>
<html lang="en"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>Mordell uniformity data</title>
<style>
.viz-root {{ color-scheme: light; --surface-1:#fcfcfb; --text-primary:#0b0b0b; --text-secondary:#52514e;
  --grid:#e4e3de; --series-1:#2a78d6; }}
@media (prefers-color-scheme: dark) {{ :root:where(:not([data-theme="light"])) .viz-root {{
  color-scheme: dark; --surface-1:#1a1a19; --text-primary:#ffffff; --text-secondary:#c3c2b7;
  --grid:#34332f; --series-1:#3987e5; }} }}
:root[data-theme="dark"] .viz-root {{ color-scheme: dark; --surface-1:#1a1a19; --text-primary:#ffffff;
  --text-secondary:#c3c2b7; --grid:#34332f; --series-1:#3987e5; }}
body {{ margin:0; }}
.viz-root {{ background:var(--surface-1); color:var(--text-primary); font:14px/1.45 system-ui, sans-serif;
  padding:16px; max-width:900px; margin:0 auto; }}
.note {{ color:var(--text-secondary); }}
.panels {{ display:flex; flex-wrap:wrap; gap:16px; }}
.panel {{ flex:1 1 380px; margin:0; }}
figcaption {{ font-weight:600; margin-bottom:4px; }}
svg {{ width:100%; height:auto; display:block; }}
.grid {{ stroke:var(--grid); stroke-width:1; }}
.tick, .axis {{ fill:var(--text-secondary); font-size:11px; }}
.line {{ fill:none; stroke:var(--series-1); stroke-width:2; stroke-linejoin:round; stroke-linecap:round; }}
.mark {{ fill:var(--series-1); stroke:var(--surface-1); stroke-width:2; }}
.hit {{ fill:transparent; }}
.dot:hover .mark {{ r:6; }}
table {{ border-collapse:collapse; margin-top:12px; }}
td, th {{ border-bottom:1px solid var(--grid); padding:4px 10px; text-align:right; }}
</style></head>
<body><main class="viz-root">
<h1>Integral points on y² = x³ + k, 0 &lt; |k| ≤ {K}</h1>
<p class="note"><strong>Numerical evidence only.</strong> Counts are of integral points up to the sign
of y, from Sage <code>integral_points</code> (rows with an unproven rank are included and flagged in
the table; engine failures are excluded). Lang's conjecture predicts at most C<sup>1+rank</sup> points;
the largest N<sup>1/(1+rank)</sup> observed here is {summary['empirical_lang_constant']['max_N^(1/(1+rank))']}
(k = {summary['empirical_lang_constant']['k']}). Nothing here proves or refutes a uniform bound.</p>
<div class="panels">{p1}{p2}</div>
<table><thead><tr><th>rank</th><th>curves</th><th>median points</th><th>max points</th><th>k at max</th></tr></thead>
<tbody>{table}</tbody></table>
<p class="note">Source: data/mordell_census.csv; regenerate with <code>python3 python/uniformity.py</code>.</p>
</main></body></html>
'''
(root / 'docs' / 'figures').mkdir(parents=True, exist_ok=True)
(root / 'docs' / 'figures' / 'uniformity.html').write_text(html)
print(json.dumps({k: summary[k] for k in ('curves_used', 'empirical_lang_constant')}), rank_stats)
