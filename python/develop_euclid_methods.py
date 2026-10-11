"""Regenerate Euclid-derived arithmetic and geometry examples and Lean fixtures."""
import json
from pathlib import Path
from perfectpower.euclid_cli import dispatch
from perfectpower.euclid_descent import resultant_certificate,classify_input,gcd_receipt
from perfectpower.euclid_lean import compile_resultant,compile_sqrt_bounds


def main():
    out=Path('receipts/euclid_methods');out.mkdir(parents=True,exist_ok=True)
    records={}
    for operation in ('descent','voronoi','contacts','pell','sqrt-bounds','root-bounds'):
        spec=json.loads(Path(f'examples/euclid_methods/{operation}.json').read_text());packet=dispatch(operation,spec)
        (out/f'{operation}.json').write_text(json.dumps(packet,indent=2)+'\n');records[operation]=packet
    string_spec=json.loads(Path('examples/euclid_methods/contacts.json').read_text())
    (out/'string.json').write_text(json.dumps(dispatch('string',string_spec),indent=2)+'\n')
    from perfectpower.euclid_geometry import orientation,nearest_sites
    big=2**60
    precision={'coordinate_scale':big,'exact_orientation':str(orientation([0,0],[big,big-1],[big+1,big])),
               'binary64_orientation':float(big)*float(big)-float(big-1)*float(big+1),
               'exact_nearest':nearest_sites({'left':[big,0],'right':[big+1,0]},[f'{4*big+1}/4',0]),
               'binary64_sites_coincide':float(big)==float(big+1)}
    (out/'precision-stress.json').write_text(json.dumps(precision,indent=2)+'\n')
    p=records['descent']
    examples={'gcds':[gcd_receipt(p['bezout'],n) for n in (-10,-2,0,1,4,24)],
              'classifications':[classify_input(p,n) for n in (-10,-2,0,1,4,24,140)]}
    (out/'descent-evaluations.json').write_text(json.dumps(examples,indent=2)+'\n')
    for name,compiled in [('SourceBoundBezout',compile_resultant(p['bezout'])),
                          ('HigherDegreeBezout',compile_resultant(resultant_certificate([-2,0,1],[3,1]))),
                          ('SourceBoundSqrt',compile_sqrt_bounds(records['sqrt-bounds']))]:
        (out/f'{name}.lean').write_text(compiled.pop('source'))
        (out/f'{name}.json').write_text(json.dumps(compiled,indent=2)+'\n')


if __name__=='__main__':main()
