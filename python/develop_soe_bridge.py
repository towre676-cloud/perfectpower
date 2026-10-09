"""Independent finite-corpus comparisons and connected arithmetic examples."""
import json
from fractions import Fraction as Q
from itertools import combinations,product
from pathlib import Path
import random
from perfectpower.semantic_fibres import ImplementationFamily,Transport,check_composition,polynomial_chart
from perfectpower.future_states import future_quotient,check_quotient,diagnosis_plan,compare_models
from perfectpower.psg_polynomial import parse
from perfectpower.psg_algebra import affine_norm_population

ROOT=Path(__file__).resolve().parents[1];OUT=ROOT/'receipts/soe_bridge'

def save(name,data):
    (OUT/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')

def trace(spec,s,word):
    out=[spec['observations'][s]]
    for k,a in enumerate(word):
        s=spec['actions'][a][s]
        if s is None:return out+[('disabled',a,k)]
        out.append(spec['observations'][s])
    return out


def main():
    OUT.mkdir(exist_ok=True,parents=True);models=[]
    words=[word for k in range(5) for word in product(('a','b'),repeat=k)]
    for observations in product(range(2),repeat=2):
        for transitions in product((None,0,1),repeat=4):
            model={'observations':list(observations),'actions':{'a':list(transitions[:2]),'b':list(transitions[2:])}}
            packet=future_quotient(model);check_quotient(packet,model)
            same=all(trace(model,0,w)==trace(model,1,w) for w in words)
            assert same==(packet['projection'][0]==packet['projection'][1])
            if not same:
                shortest=next(w for w in words if trace(model,0,w)!=trace(model,1,w))
                assert len(packet['distinguishing_witnesses'][0]['word'])==len(shortest)
            models.append({'model':model,'packet':packet})
    save('all_two_state_automata.json',models)
    rng=random.Random(803);transports=[]
    for case in range(120):
        for mode in Transport.MODES:
            left=Transport(['i0','i1','i2'],['j0','j1','j2'],[[f'i{i}',f'j{j}',rng.randrange(4)] for i,j in product(range(3),repeat=2)],mode=mode)
            right=Transport(['j0','j1','j2'],['k0','k1'],[[f'j{j}',f'k{k}',rng.randrange(4)] for j,k in product(range(3),range(2))],mode=mode)
            joined=left.compose(right);check_composition(joined.packet(),left,right)
            # Exhaust every original two-edge path using independent arithmetic.
            expected={}
            for i,k in product(left.source,right.target):
                paths=[(a+b if mode=='minplus' else a*b) for (u,j),a in left._entries.items() for (v,w),b in right._entries.items() if u==i and w==k and j==v]
                value=min(paths) if mode=='minplus' and paths else sum(paths,Q(0)) if mode!='minplus' else None
                if value is not None and (mode=='minplus' or value):expected[i,k]=value
            assert joined._entries==expected
            transports.append({'case':case,'left':left.packet(),'right':right.packet(),'composition':joined.packet()})
    save('semiring_path_corpus.json',transports)
    model={'observations':[0,0,0,0,1,2],'actions':{'a':[4,4,5,5,4,5],'b':[4,5,4,4,4,5],'c':[4,4,4,5,4,5]}}
    probes=[{'name':a,'word':[a],'cost':1} for a in model['actions']]
    plan=diagnosis_plan(model,probes);assert plan['worst_case_cost']=='2'
    fixed={}
    for k in range(1,4):
        fixed[k]=[list(menu) for menu in combinations(model['actions'],k) if len({tuple(str(trace(model,s,[a])) for a in menu) for s in range(4)})==4]
    assert not fixed[1] and not fixed[2] and fixed[3]
    save('adaptive_diagnosis.json',{'model':model,'probes':probes,'plan':plan,'distinguishing_fixed_menus':fixed,'optimal_adaptive_cost':2,'optimal_fixed_cost':3})
    arithmetic=affine_norm_population(parse('2*x+1',('x','y')),parse('y',('x','y')),2,-1,1000)
    family={'variables':['x','y'],'semantics':['(2*x+1)^2-2*y^2'],'rows':[{'id':json.dumps(point),'values':point} for point in arithmetic['points']]}
    query={'semantic_value':[-1],'constraints':[{'expression':'y','relation':'ge','value':0}],'objectives':['x^2+y^2']}
    result=ImplementationFamily(family).query(**query)
    save('pell_implementation_family.json',{'family':family,'query':query,'result':result,'original_point_count':len(arithmetic['points'])})
    assert result['minimum']=='1'
    chart={'variables':['x','y'],'forward':['x+y^2','y'],'inverse':['x-y^2','y'],'source_outputs':['x+y^2','x+y^2+y'],'target_outputs':['x','x+y']}
    save('nonlinear_chart.json',{'specification':chart,'certificate':polynomial_chart(**chart)})
    save('cli_family.json',{'family':family,'query':query});save('cli_states.json',model);save('cli_plan.json',{'model':model,'probes':probes});save('cli_chart.json',chart)
    save('cli_transport.json',{'left':{'source':['s'],'target':['a','b'],'mode':'minplus','entries':[['s','a',2],['s','b',3]]},'right':{'source':['a','b'],'target':['t'],'mode':'minplus','entries':[['a','t',5],['b','t',7]]},'values':{'s':0}})
    equivalent={'left':{'observations':[0,1,0,1],'actions':{'tick':[1,0,3,2]}},'right':{'observations':[0,1],'actions':{'tick':[1,0]}}}
    save('cli_equivalence.json',equivalent);save('model_equivalence.json',compare_models(**equivalent))
    summary={'all_two_state_partial_two_action_binary_observation_models':len(models),'independent_semiring_path_cases':len(transports),'adaptive_worst_case_cost':2,'minimum_fixed_schedule_cost':3,'arithmetic_original_points':len(arithmetic['points']),'arithmetic_legal_points':result['count'],'arithmetic_minimum':result['minimum'],'new_console_routes':6,'formal_status':'tested exact Python; no new Lean kernel claim','source_status':'enhanced bridge derived from recovered SOE program context; canonical SOE sources unavailable'}
    save('summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
