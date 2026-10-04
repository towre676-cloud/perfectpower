"""Reproducible integration experiments; stdout JSON, no hidden downloads."""
import json
from perfectpower.information import (InformationProblem, Observation,
    polynomial_information, compile_square_query, AffineTransport)
from orbit_lattice import information_plan


def receipt():
    lift=InformationProblem(range(4),lambda n:n % 4,
        [Observation('mod2',lambda n:n % 2),Observation('mod4',lambda n:n % 4)],
        scope='Z/4Z lift collision')
    polynomial=polynomial_information([-2,0,0,1],2,-100,101,[2,3,5,7,11,13])
    units=information_plan(9,6,[(-1,-3,1),(-1,0,2)],(-3,-3,1),9,-3,
        plane=(0,1,0),scope='D=72 signed unit orbit modulo 9; all certified period classes')
    transport=AffineTransport((4,8),(0,0))
    return {'schema':'pp-information/1','execution_verified':False,
        'lift_collision':lift.ambiguity(['mod2']), 'lift_plan':lift.compile(['mod2']),
        'mordell_interval':polynomial.compile(), 'd72_modular_plan':units,
        'square_query_sat':compile_square_query([-1,0,1],1,lambda p:p[0]==1),
        'square_query_unsat':compile_square_query([-1,0,1],1,lambda p:p[0]>10),
        'square_query_partial':compile_square_query([1_000_000,1],1,lambda p:True,
                                                    fibre_work_limit=10),
        'scaling_pullbacks':{'admissible':transport.pullback((12,40)),
                             'inadmissible':transport.pullback((3,5))}}


if __name__=='__main__':print(json.dumps(receipt(),indent=2))
