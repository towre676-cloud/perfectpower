"""Optional independent development cross-check; requires SymPy."""
import json
import random
from pathlib import Path
import sympy as sympy
from perfectpower.residue_determinant import (
    determinant, determinant_packet, kernel_packet, verify_determinant, verify_kernel)


def main():
    rng = random.Random(20261007)
    count, closed = 0, 0
    for n in range(1, 7):
        for j in range(20):
            a = [[rng.randrange(-8, 9) for _ in range(n)] for _ in range(n)]
            if j % 2 == 0 and n > 1:
                a[-1] = [sum(a[i][k] for i in range(n-1)) for k in range(n)]
            assert determinant(a) == int(sympy.Matrix(a).det())
            k = kernel_packet(a)
            assert verify_kernel(k) and k['rank'] == sympy.Matrix(a).rank()
            p = determinant_packet(a, 1000003)
            assert verify_determinant(p)
            if p['status'] == 'zero-certified':
                assert determinant(a) == 0
                closed += 1
            count += 1
    receipt = {'seed': 20261007, 'independent_engine': 'SymPy '+sympy.__version__,
               'matrix_cases': count, 'dimensions': [1, 2, 3, 4, 5, 6],
               'determinant_and_rank_agree': True, 'certified_zero_cases': closed,
               'false_zero_claims': 0}
    destination = Path(__file__).resolve().parents[1]/'receipts'/'residue_determinant'/'crosscheck.json'
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(receipt, indent=2)+'\n')
    print(count, 'independent matrix comparisons;', closed, 'bounded zero certificates')


if __name__ == '__main__':
    main()
