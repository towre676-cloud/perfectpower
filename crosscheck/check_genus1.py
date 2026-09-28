"""Plain-Python gate for receipts/genus1_crossval.json (no Sage needed; run by `make receipts`).

For every row it recomputes the integral Weierstrass model from F, checks that every stored model
point lies on the model, recomputes the pull-back of those points to hits n >= 1, checks that each
hit is exact, reruns the exact sieve scan to the stored bound, and recomputes the label from
rank_proved, saturation_index and the scan comparison.  The Sage side (generators, saturation,
elliptic-logarithm sieving) is not rerun here; `make crosscheck` does that.
"""
import hashlib
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'python'))
sys.path.insert(0, str(Path(__file__).resolve().parent))
from perfectpower.sieve import sieve_hits  # noqa: E402
from genus1_sage import is_hit, pullback, weierstrass  # noqa: E402

root = Path(__file__).resolve().parents[1]


def check_row(r):
    kind, f = r['kind'], r['F_low_to_high']
    A, B = weierstrass(kind, f)
    assert r['model_a_invariants'] == [0, 0, 0, A, B], ('model', f)
    scan = sieve_hits(f, r['d'], r['scan_bound'] + 1)
    assert scan == r['scan_hits'], ('scan', f)
    if r['certification'] == 'SCAN_EVIDENCE_ONLY':
        return
    pts = [tuple(p) for p in r['model_integral_points']]
    assert pts == sorted(set(pts)), ('points not sorted/unique', f)
    for U, V in pts:
        assert V * V == U ** 3 + A * U + B, ('off model', f, U, V)
    hits = sorted({n for U, V in pts for n in pullback(kind, f, U, V)})
    assert hits == r['hits'], ('pullback', f)
    assert all(is_hit(kind, f, n) for n in hits), ('hit', f)
    agrees = [n for n in hits if n <= r['scan_bound']] == scan
    assert agrees == r['scan_agrees'], ('scan flag', f)
    expected = ('SCAN_DISAGREEMENT' if not agrees else
                'CONDITIONAL_ON_UNPROVEN_RANK' if not r['rank_proved'] else
                'CONDITIONAL_ON_UNSATURATED_BASIS' if r['saturation_index'] != 1 else
                'INDEPENDENT_COMPUTATION')
    assert r['certification'] == expected, ('label', f, r['certification'], expected)


def main():
    rec = json.loads((root / 'receipts' / 'genus1_crossval.json').read_text())
    rows = rec['rows']
    assert hashlib.sha256(json.dumps(rows, separators=(',', ':')).encode()).hexdigest() == rec['rows_sha256']
    keys = [(r['kind'], tuple(r['F_low_to_high'])) for r in rows]
    assert len(keys) == len(set(keys)) == rec['trials'], 'duplicate or missing families'
    for r in rows:
        check_row(r)
    print(f"genus-1 gate OK: {len(rows)} families, labels {rec['labels']}, "
          f"{len(rec['hits_beyond_scan'])} certified hits beyond the scan")


if __name__ == '__main__':
    main()
