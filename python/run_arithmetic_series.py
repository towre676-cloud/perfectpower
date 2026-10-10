"""Regenerate exact arithmetic-series examples and receipts, without timing noise."""
import json
from pathlib import Path
from perfectpower.generating_arithmetic import compile_spec,replay,modular_count
from perfectpower.binary64 import bits,from_bits,dot_bits
from perfectpower.generating import RationalGF

ROOT=Path(__file__).resolve().parents[1]


def main():
    destination=ROOT/'receipts/arithmetic_series'
    destination.mkdir(parents=True,exist_ok=True)
    packets={}
    for path in sorted((ROOT/'examples/arithmetic_series').glob('*.json')):
        packet=compile_spec(json.loads(path.read_text()))
        assert replay(packet)
        packets[path.stem]=packet
        (destination/path.name).write_text(json.dumps(packet,indent=2)+'\n')
    pell=packets['pell'];gx=RationalGF(pell['x']['numerator'],pell['x']['denominator'])
    gy=RationalGF(pell['y']['numerator'],pell['y']['denominator'])
    summary={'pell_unit':pell['unit'],'pell_index':100,'pell_x100':str(gx.nth(100)),
             'pell_y100':str(gy.nth(100)),
             'fibonacci_square_residue_filter':{'modulus':8,'exclusive_stop':10**12,
                'passing_indices':modular_count(packets['modular_fibonacci'],10**12),
                'scope':'necessary congruence condition; not a count of actual Fibonacci squares'},
             'stored_point_one_squared':packets['binary_polynomial'],
             'cancellation':{'sequential':(1e16+1.0)-1e16,
                'exact_dot_round_once':from_bits(dot_bits(list(map(bits,[1e16,1.0,-1e16])),[bits(1.0)]*3))}}
    (destination/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
