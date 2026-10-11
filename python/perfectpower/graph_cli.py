"""JSON command line for exact graph methods: python -m perfectpower.graph_cli."""
import argparse
import json
from .graph_counting import count_cnf, count_factors
from .graph_optimization import matching, max_flow, distinct_assignment
from .graph_structure import machine_structure, elimination_forest
from .graph_topology import cellular_homology, mesh_homology, string_enclosures


def dispatch(kind, spec, cell_limit=1000000):
    if kind=='cnf': return count_cnf(spec['variables'],spec['clauses'],cell_limit=cell_limit)
    if kind=='factors': return count_factors(spec,cell_limit=cell_limit)
    if kind=='matching': return matching(spec['left'],spec['right'],spec['edges'])
    if kind=='distinct': return distinct_assignment(spec['domains'])
    if kind=='flow': return max_flow(spec['vertices'],spec['arcs'],spec['source'],spec['sink'])
    if kind=='decompose': return elimination_forest(spec['vertices'],spec['edges'])
    if kind=='machine': return machine_structure(spec)
    if kind=='homology': return cellular_homology(spec['vertices'],spec['edges'],spec['faces'],matrix_cell_limit=cell_limit)
    if kind=='mesh': return mesh_homology(spec,matrix_cell_limit=cell_limit)
    if kind=='string': return string_enclosures(spec['path'],spec['objects'])
    raise ValueError('unknown graph operation')


def add_commands(sub):
    p=sub.add_parser('graph',help='exact separator counting, graph certificates and topology')
    p.add_argument('operation',choices=['cnf','factors','matching','distinct','flow','decompose','machine','homology','mesh','string'])
    p.add_argument('input',help='JSON specification file')
    p.add_argument('--cell-limit',type=int,default=1000000)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('operation',choices=['cnf','factors','matching','distinct','flow','decompose','machine','homology','mesh','string'])
    p.add_argument('input',help='JSON specification file'); p.add_argument('--cell-limit',type=int,default=1000000)
    args=p.parse_args()
    with open(args.input) as f: spec=json.load(f)
    print(json.dumps(dispatch(args.operation,spec,args.cell_limit),sort_keys=True,indent=2))


if __name__=='__main__': main()
