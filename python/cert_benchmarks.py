"""Benchmarks for the pp-cert/1 certificates (docs/CERTIFICATE_FORMAT.md).  Timings vary by machine.

For every certificate in certs/: producer time, JSON and Lean sizes, Lean check time (elaboration
plus kernel, measured as the time of `lake env lean` on a file with just that certificate, minus
the time of the same file with only the import), the range covered by explicit segments, and, for
comparison, the time of an exact sieve scan of that range (which proves nothing beyond it, whereas
the certificate covers all n >= 1).  Writes receipts/cert_benchmarks.json.
"""
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.certfmt import canonical, produce_runge, produce_sandwich, to_lean  # noqa: E402
from perfectpower.sieve import sieve_hits  # noqa: E402

root = Path(__file__).resolve().parents[1]
HEAD = 'import PerfectPower.Reflect\nnamespace PerfectPower.Generated\nopen PerfectPower\n'


def lean_time(body):
    with tempfile.NamedTemporaryFile('w', suffix='.lean', dir=root / 'audit', delete=False) as fh:
        fh.write(HEAD + body + '\nend PerfectPower.Generated\n')
        path = fh.name
    t = time.time()
    r = subprocess.run(['lake', 'env', 'lean', path], cwd=root, capture_output=True, text=True)
    dt = time.time() - t
    Path(path).unlink()
    if r.returncode:
        raise RuntimeError(r.stdout + r.stderr)
    return dt


def main():
    base = min(lean_time('') for _ in range(2))
    rows = []
    for p in sorted((root / 'certs').glob('*/*.json')):
        c = json.loads(p.read_text())
        st = c['statement']
        t0 = time.time()
        (produce_runge if c['kind'] == 'runge' else produce_sandwich)(c['name'], st['F'], st['d'])
        tprod = time.time() - t0
        lean = to_lean(c)
        tl = lean_time(lean)
        end = c['data']['tail_start'] if c['kind'] == 'sandwich' else c['data']['x0']
        t1 = time.time()
        sieve_hits(st['F'], st['d'], end)
        tsieve = time.time() - t1
        rows.append({'name': c['name'], 'kind': c['kind'], 'degree': len(st['F']) - 1, 'd': st['d'],
                     'hits': st['hits'], 'segments': len(c['data']['segments']),
                     'explicit_range_end': end, 'json_bytes': len(canonical(c)),
                     'lean_bytes': len(lean.encode()), 'producer_seconds': round(tprod, 3),
                     'lean_check_seconds': round(max(tl - base, 0.0), 2),
                     'sieve_scan_of_explicit_range_seconds': round(tsieve, 4)})
        print(rows[-1])
    out = {'note': 'timings vary by machine; lean_check_seconds = time(lake env lean file) - '
                   'time(import only); a certificate covers all n >= 1, a scan only its range',
           'import_baseline_seconds': round(base, 2), 'certificates': rows,
           'totals': {'json_bytes': sum(r['json_bytes'] for r in rows),
                      'lean_bytes': sum(r['lean_bytes'] for r in rows),
                      'lean_check_seconds': round(sum(r['lean_check_seconds'] for r in rows), 2)}}
    (root / 'receipts' / 'cert_benchmarks.json').write_text(json.dumps(out, indent=1) + '\n')
    print(out['totals'])


if __name__ == '__main__':
    main()
