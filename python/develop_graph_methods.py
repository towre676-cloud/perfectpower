"""Generate replayable examples and small source-bound Lean count fixtures."""
import json
from pathlib import Path
from perfectpower.graph_cli import dispatch
from perfectpower.graph_lean import compile_cnf


def main():
    out=Path('receipts/graph_methods');out.mkdir(parents=True,exist_ok=True)
    for operation,name in [('cnf','cnf'),('flow','flow'),('matching','matching'),('machine','machine'),('homology','torus'),('string','string')]:
        spec=json.loads(Path(f'examples/graph_methods/{name}.json').read_text())
        (out/f'{name}.json').write_text(json.dumps(dispatch(operation,spec),indent=2)+'\n')
    spec=json.loads(Path('examples/graph_methods/cnf.json').read_text());compiled=compile_cnf(spec['variables'],spec['clauses'])
    (out/'SourceBoundCNF.lean').write_text(compiled.pop('source'))
    (out/'SourceBoundCNF.json').write_text(json.dumps(compiled,indent=2)+'\n')


if __name__=='__main__':main()
