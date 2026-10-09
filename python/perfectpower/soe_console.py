"""Exact finite semantic-family, transport and temporal diagnosis console."""
import json
from pathlib import Path
from .semantic_fibres import ImplementationFamily,Transport,check_composition,polynomial_chart
from .future_states import future_quotient,check_quotient,diagnosis_plan,compare_models


def add_commands(sub):
    for name in ('soe-family','soe-transport','soe-states','soe-plan','soe-chart','soe-equivalence'):
        p=sub.add_parser(name,help='exact finite SOE/PerfectPower bridge')
        p.add_argument('specification',type=Path,help='JSON specification file')
        p.add_argument('--out',type=Path)


def cli(args):
    if not args.command.startswith('soe-'):return False
    spec=json.loads(args.specification.read_text())
    if args.command=='soe-family':
        if set(spec)-{'family','population','semantics','query'}:raise ValueError('unknown implementation query field')
        if 'population' in spec:
            if 'family' in spec:raise ValueError('choose family or population')
            from .populations import ExactPopulation
            family=ImplementationFamily.from_population(ExactPopulation(spec['population']),spec['semantics'])
        else:family=ImplementationFamily(spec['family'])
        result=family.query(**spec.get('query',{}))
    elif args.command=='soe-transport':
        left=Transport.from_packet(spec['left']);right=Transport.from_packet(spec['right']);composed=left.compose(right)
        check_composition(composed.packet(),left,right)
        result={'composition':composed.packet(),'replayed':True}
        if 'values' in spec:result['transported_values']=composed.apply(spec['values'])
        if composed.mode=='mass':result['mass_preservation']=composed.mass_preserving()
    elif args.command=='soe-equivalence':result=compare_models(**spec)
    elif args.command=='soe-chart':result=polynomial_chart(**spec)
    elif args.command=='soe-states':result=future_quotient(spec);check_quotient(result,spec)
    else:result=diagnosis_plan(spec['model'],spec['probes'],work_limit=spec.get('work_limit',100000))
    encoded=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(encoded)
    else:print(encoded,end='')
    return True
