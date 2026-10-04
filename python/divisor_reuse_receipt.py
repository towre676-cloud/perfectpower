"""Regenerate the deterministic operation-count and arithmetic reuse receipt."""
import json
from pathlib import Path
from perfectpower.divisor_square import solve
from perfectpower.quotient_algebra import QuotientAlgebra
from perfectpower.local_quartic import primitive_residue_certificate

cases = []
for coefficients, k in (([1000000, 1], 1), ([0, 0, 0, 1], 8),
                        ([4, -4, 1], 1), ([0, 0, -2], -1)):
    result = solve(coefficients, k)
    bound = sum(map(abs, coefficients))+abs(k)+1
    result['prior_rectangle_candidates'] = (2*bound+1)*(2*abs(k)+1)
    cases.append(result)
receipt = {'schema': 'pp-divisor-reuse/1', 'cases': cases,
           'arithmetic': QuotientAlgebra((-2, 0, 0, 1)).element((1, 1)).receipt(),
           'quartic': primitive_residue_certificate(2, 1, 2, 3),
           'measurement': 'deterministic Python divisor trials, not Lean reduction steps or wall time'}
target = Path(__file__).resolve().parents[1]/'data/divisor_reuse_receipt.json'
target.write_text(json.dumps(receipt, indent=2)+'\n')
print(target.relative_to(Path(__file__).resolve().parents[1]))
