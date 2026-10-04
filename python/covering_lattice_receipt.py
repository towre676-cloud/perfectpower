"""Replay recovered coverings and attach lattice data to all existing order maps."""
import json
from pathlib import Path
from perfectpower.covering import fisher_571_replay, covering_point, two_isogeny_point
from perfectpower.integral_lattice import smith_invariants,inverse_lattice_conditions,basis_pullback
from perfectpower.decomposition import supplied_decomposition,compose
from orbit_lattice import order_image_allowed

ROOT=Path(__file__).resolve().parents[1]


def receipt():
    maps=json.loads((ROOT/'receipts/order_transports.json').read_text())['embeddings']
    entries=[]
    for i,e in enumerate(maps):
        lattice=smith_invariants(e['matrix'])
        if lattice['torsion_order']!=e['index']:
            raise AssertionError('order index mismatch')
        entries.append({'map_index':i,'domain':e['domain'],'codomain':e['codomain'],
                        'lattice':lattice,'inverse_conditions':inverse_lattice_conditions(e['matrix'])})
    x,y=covering_point(-1,1,1,1,1)
    X,Y=two_isogeny_point(-1,1,x,y)
    matrix=[[3,0,0],[0,1,0],[0,0,1]]
    order_filter=order_image_allowed(matrix,9,6,[(1,0,0)],(1,0,0),2,1)
    outer=(0,0,1);F=(0,1);G=(0,-1)
    return {'schema':'pp-covering-lattice/1','execution_verified':False,
            'fisher_571':fisher_571_replay(),'order_maps':entries,
            'order_map_count':len(entries),
            'prime_power_example':smith_invariants([[19,0],[0,19**2]]),
            'two_isogeny_example':{'source_point':list(map(str,(x,y))),
                'target_point':list(map(str,(X,Y))),'source_model':[-1,1],'target_model':[2,-3]},
            'nonmonic_image_exclusion':order_filter,
            'nonmonic_inverse_witness':basis_pullback(matrix,(1,0,0)),
            'outer_cancellation_counterexample':supplied_decomposition(
                compose(outer,F),compose(outer,G),outer,F,G)}


if __name__=='__main__':print(json.dumps(receipt(),indent=2))
