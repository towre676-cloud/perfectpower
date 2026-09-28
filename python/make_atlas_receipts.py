"""Deterministically regenerate receipts/atlas_benchmarks.json; stdlib only.

Every structural count below N_SCAN is cross-checked against the defining scan
(count n in [1, N] with F(n) = m^d); larger N use the structural formulas only.
"""
import hashlib
import json
import sys
from dataclasses import asdict
from fractions import Fraction
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.atlas import classify, structural_count, structural_hits
from perfectpower.core import count, hit_indices, mul, rigid_certificate
from perfectpower.runge import runge_enumerate

root = Path(__file__).resolve().parents[1]
N_SCAN = 10 ** 5
N_BIG = (10 ** 6, 10 ** 12, 10 ** 24)


def consecutive(k):
    p = (Fraction(1),)
    for i in range(k):
        p = mul(p, (Fraction(i), Fraction(1)))
    return [int(x) for x in p]


families = [
    # (name, F low-to-high, d)
    ('square_polynomial_n2', [0, 0, 1], 2),
    ('twisted_power_2n2', [0, 0, 2], 2),
    ('grunwald_wang_16n8', [0] * 8 + [16], 8),
    ('linear_4n_plus_1', [1, 4], 2),
    ('linear_2n_minus_5', [-5, 2], 2),
    ('linear_3n_plus_2_d6', [2, 3], 6),
    ('singular_cubic_n3', [0, 0, 0, 1], 2),
    ('cube_twist_5_plus_3n', [5, 3], 3),
    ('radical_12n2_d3', [0, 0, 12], 3),
    ('radical_n3_times_square', [0, 0, 0, 1, 2, 1], 2),
    ('monomial_n4_d6', [0, 0, 0, 0, 1], 6),
    ('pell_2n2_plus_1', [1, 0, 2], 2),
    ('pell_3n2_plus_1', [1, 0, 3], 2),
    ('pell_2n2_minus_7', [-7, 0, 2], 2),
    ('pell_5n2_plus_n_plus_3', [3, 1, 5], 2),
    ('pell_2n2_plus_n', [0, 1, 2], 2),
    ('pell_quartic_(2n2+1)^2_d4', [1, 0, 4, 0, 4], 4),
    ('elliptic_n3_plus_1', [1, 0, 0, 1], 2),
    ('elliptic_n3_minus_2n_plus_1', [1, -2, 0, 1], 2),
    ('elliptic_n3_plus_n_plus_4', [4, 1, 0, 1], 2),
    ('rigid_quartic_n4_plus_1', [1, 0, 0, 0, 1], 2),
    ('rigid_n2_plus_n', [0, 1, 1], 2),
    ('ljunggren_1_plus_n_to_n4', [1, 1, 1, 1, 1], 2),
    ('n4_plus_1_sixth_power', [1, 0, 0, 0, 1], 6),
]
for k, ds in ((4, (2, 4)), (6, (2, 3, 6)), (8, (2, 4, 8)), (10, (2, 5)), (12, (2, 3, 4, 6))):
    for d in ds:
        families.append((f'consecutive_product_{k}_d{d}', consecutive(k), d))

rows = []
for name, f, d in families:
    cl = classify(f, d)
    row = {'name': name, 'coefficients_F_low_to_high': f, 'd': d, 'kind': cl.kind,
           'multiplicity_profile': cl.multiplicity_profile, 't_profile': cl.t_profile,
           'growth': cl.growth, 'exponent': str(cl.exponent), 'infinite': cl.infinite,
           'effective': cl.effective}
    if cl.kind in ('radical', 'pell'):
        row['kappa'] = round(cl.details['kappa'], 12)
    if cl.kind == 'finite':
        row['runge_divisors'] = cl.details['runge_divisors']
    scan = count(f, d, 0, N_SCAN)
    if cl.effective:
        structural = structural_count(f, d, N_SCAN)
        if structural != scan:
            raise AssertionError(f'{name}: structural {structural} != scan {scan}')
        row['count_at_1e5_structural_equals_scan'] = scan
        if cl.kind in ('power', 'radical', 'pell', 'constant'):
            row['counts_structural'] = {f'1e{len(str(N)) - 1}': structural_count(f, d, N)
                                        for N in N_BIG}
        if cl.kind in ('finite', 'power', 'pell', 'radical') and not cl.infinite:
            row['complete_hit_list'] = structural_hits(f, d, 10 ** 30)
    else:
        row['count_at_1e5_scan_only'] = scan
        row['scan_hits_up_to_1e5'] = [n for n, _ in hit_indices(f, d, 0, N_SCAN)]
    if cl.kind == 'finite' and cl.details['rigid_runge_branch']:
        e = runge_enumerate(f, d)
        c = rigid_certificate(f, d)
        row['runge'] = {'hits': e.hits, 'scan_below': e.scan_below, 'max_t': e.max_t,
                        'polynomials_solved': e.polynomials_solved, 'tail_start': e.tail_start,
                        'v05_certificate_cutoff': c.cutoff}
    rows.append(row)

result = {'status': 'exact computations; structural counts cross-checked against the defining '
                    'scan up to 1e5; complete hit lists are proofs relative to Theorems P, B, C, R',
          'generator': 'python3 python/make_atlas_receipts.py',
          'definition': 'count n in [1,N] with F(n)=m**d for an integer m',
          'rows': rows}
out = root / 'receipts' / 'atlas_benchmarks.json'
out.write_text(json.dumps(result, indent=2) + '\n')
print(out)
print(hashlib.sha256(out.read_bytes()).hexdigest())
