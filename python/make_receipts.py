"""Deterministically regenerate exact experiment receipts; stdlib only."""
import hashlib
import json
import sys
from dataclasses import asdict
from pathlib import Path
sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.core import count, rigid_certificate, verify_certificate

root = Path(__file__).resolve().parents[1]
base = [
    ('linear_4n_plus_1', (1, 4), 2, 0),
    ('singular_cubic', (0, 0, 0, 1), 2, 0),
    ('elliptic_a0_b1_k0', (1, 0, 0, 1), 2, 0),
    ('elliptic_am2_b1_k0', (1, -2, 0, 1), 2, 0),
    ('elliptic_a1_b1_k3', (1, 1, 0, 1), 2, 3),
    ('square_polynomial', (0, 0, 1), 2, 0),
    ('n_squared_plus_n', (0, 1, 1), 2, 0),
    ('pell_2n_squared_plus_1', (1, 0, 2), 2, 0),
    ('rigid_quartic_x4_plus_1', (1, 0, 0, 0, 1), 2, 0),
]
cutoffs = (1000, 10000, 100000)
rows = []
for name, coeff, d, k in base:
    f = list(coeff)
    f[0] += k
    c = rigid_certificate(f, d)
    rows.append({'name': name, 'coefficients_S_low_to_high': coeff, 'd': d, 'k': k,
                 'cutoffs': cutoffs, 'counts': [count(coeff, d, k, N) for N in cutoffs],
                 'rigid_certificate': None if c is None else c.to_json(),
                 'certificate_valid': None if c is None else verify_certificate(c)})
result = {'status': 'exact finite computations; asymptotic statements supplied by separate proofs',
          'generator_exit_code_on_success': 0,
          'generator': 'python3 python/make_receipts.py',
          'definition': 'count n in [1,N] with S(n)+k=m**d for an integer m',
          'rows': rows}
out = root / 'receipts' / 'exact_benchmarks.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print(out)
print(hashlib.sha256(out.read_bytes()).hexdigest())
