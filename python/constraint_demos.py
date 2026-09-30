"""Specialization demonstrations for the constraint compiler (deterministic; part of `make verify`).

Each demo is a brute-force loop over n.  For each one the receipt records the original program,
the compiled plan (reductions, method, status, justification), the generated specialized program,
and the outputs of both at N = 10^4, which must agree.  A plan with no enumeration gets no
specialized program, only bounded evidence labelled as such.  Writes receipts/constraint_demos.json.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).parent))
from perfectpower.specialize import LoopProgram, specialize  # noqa: E402

root = Path(__file__).resolve().parents[1]
N = 10 ** 4

DEMOS = [
    ('cube_transport', 'is (5n - 7)^3 - 2 a square?  (Lean: transport of MordellMinus2)',
     LoopProgram('(5*n - 7)**3 - 2', ('power', 2))),
    ('pell_2n2_plus_1', 'is 2n^2 + 1 a square?  (Pell orbit iteration)',
     LoopProgram('2*n**2 + 1', ('power', 2))),
    ('square_triangular', 'is n^2 a triangular number y(y+1)/2, y >= 0?',
     LoopProgram('n**2', ('triangular', 'nonneg'))),
    ('triangular_cube', 'is 64n^3 - 120n^2 + 75n - 16 triangular?  (Lean: tri_cube_complete)',
     LoopProgram('64*n**3 - 120*n**2 + 75*n - 16', ('triangular', 'int'))),
    ('quadratic_filter', 'does 2y^2 + y = n have a root y >= 0?  (divisibility filter)',
     LoopProgram('n', ('root', 2, 1, 0, 'nonneg'))),
    ('pell_large_unit', 'is 991n^2 + 1 a square?  (first hit far beyond any scan)',
     LoopProgram('991*n**2 + 1', ('power', 2))),
    ('ljunggren', 'is n^4 + n^3 + n^2 + n + 1 a square?  (pp-cert/1 certificate)',
     LoopProgram('n**4 + n**3 + n**2 + n + 1', ('power', 2))),
    ('unresolved_mordell', 'is n^3 + 17 a square?  (finite, no complete list here)',
     LoopProgram('n**3 + 17', ('power', 2))),
]


def main():
    out = []
    for key, title, prog in DEMOS:
        sp = specialize(prog)
        orig = sp.run_original(N)
        row = {'demo': key, 'title': title, **sp.explain(),
               'original_program': sp.original, 'specialized_program': sp.source, 'N': N,
               'original_output': [[n, w] for n, w in orig]}
        if sp.source is not None:
            spec = sp.run_specialized(N)
            row['specialized_output'] = [[n, w] for n, w in spec]
            row['outputs_agree'] = spec == orig
            assert spec == orig, key
        else:
            ev = sp.plan.bounded_evidence(N)
            row['bounded_evidence'] = {**ev, 'hits': [[n, w] for n, w in ev['hits']]}
        out.append(row)
        print(f"{key:20s} {sp.plan.status:20s} {sp.plan.method}")
    path = root / 'receipts' / 'constraint_demos.json'
    path.write_text(json.dumps(out, indent=1) + '\n')
    print(f'{len(out)} demos -> {path.relative_to(root)}')


if __name__ == '__main__':
    main()
