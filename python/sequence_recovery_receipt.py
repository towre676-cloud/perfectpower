"""Actual staged OEIS scan plus reproducible recovered arithmetic examples."""
import json
from pathlib import Path
from perfectpower.recurrence import Recurrence,filter_count,scan_seq_directory
from perfectpower.primary_modules import subgroup_census,cyclic_phase,presentation_cyclic_counts
from perfectpower.exact_operators import hypergeometric_replay,quotient_projectors

ROOT=Path(__file__).resolve().parents[1]


def receipt():
    atlas=scan_seq_directory(ROOT/'data/oeis/seq')
    padovan=Recurrence((1,1,0),(1,1,1));f=padovan.residue_filter(7,lambda s:s[0]==0)
    return {'schema':'pp-sequence-recovery/1','execution_verified':False,
        'oeis_scan':atlas,
        'padovan':{'annihilator':list(map(str,padovan.annihilator)),
                   'prefix':list(map(str,padovan.terms(16))),
                   'negative_indices':{str(n):str(padovan.nth(n)) for n in range(-10,0)},
                   'mod7_period':f['period'],'mod7_preperiod':f['preperiod'],
                   'mod7_cycle_hits':f['cycle_hits'],
                   'zeros_mod7_before_10pow12':filter_count(f,10**12)},
        'formation_censuses':[subgroup_census(2,(3,2,1)),subgroup_census(2,(2,2,2)),subgroup_census(3,(2,2))],
        'phase_collision':{'first':cyclic_phase(2,(2,2),(1,1)),
                           'second':cyclic_phase(2,(2,2),(1,3)),
                           'shared_mod2_shadow':[1,1]},
        'lattice_primary_module':presentation_cyclic_counts([[19,0],[0,361]],19),
        'hypergeometric':hypergeometric_replay(),
        'wilson_current_projectors':quotient_projectors((0,11,0,1),[(0,1),(11,0,1)])}


if __name__=='__main__':print(json.dumps(receipt(),indent=2))
