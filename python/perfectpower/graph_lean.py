"""Source-bound small CNF kernel proof emitter; explicitly exponential acceptance.

General separator execution is tested/replayed Python, not proved by this emitter.
"""
import hashlib
import json
from .graph_counting import cnf_model, count_factors
from .divisor_square import WorkLimit


def compile_cnf(variables, clauses, *, assignment_limit=4096):
    clauses=[list(c) for c in clauses]; model=cnf_model(variables,clauses)
    if 2**variables > assignment_limit: raise WorkLimit('finite kernel enumeration assignment limit exceeded')
    packet=count_factors(model)
    binding=json.dumps({'variables':variables,'clauses':clauses},sort_keys=True,separators=(',',':'))
    digest=hashlib.sha256(binding.encode()).hexdigest()
    def literal(l): return f'(x / {2**(abs(l)-1)} % 2 == {1 if l>0 else 0})'
    expression=' && '.join('('+' || '.join(map(literal,c))+')' if c else 'false' for c in clauses) or 'true'
    bound=2**variables
    source=f'''import Std
namespace PerfectPower.CheckedGraph.P{digest}
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
def satisfies (x : Nat) : Bool := {expression}
theorem exact_count : ((List.range {bound}).filter satisfies).length = {packet['count']} := by decide
#print axioms exact_count
end PerfectPower.CheckedGraph.P{digest}
'''
    return {'schema':'pp-checked-cnf-source/1','source':source,'model':model,
            'specification_sha256':digest,'count':packet['count'],
            'source_sha256':hashlib.sha256(source.encode()).hexdigest(),
            'kernel_checked':False,'scope':'exhaustive Boolean assignments of the supplied DIMACS clauses'}
