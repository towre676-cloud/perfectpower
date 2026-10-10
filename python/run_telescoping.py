"""Reproduce A=B-inspired proof packets and exact power-query examples."""
import json
from math import comb
from pathlib import Path
from perfectpower.telescoping import (discover_binomial_sum,replay_binomial_sum,
    BinomialSumSequence,certify_hypergeometric_solution,replay_hypergeometric_solution,
    discover_antidifference,replay_antidifference,sum_from_antidifference)
from perfectpower.generating_cli import execute
from perfectpower.catalogue import encoded
ROOT=Path(__file__).resolve().parents[1]

def main():
    out=ROOT/'receipts/telescoping';out.mkdir(parents=True,exist_ok=True)
    summaries={}
    for path in sorted((ROOT/'examples/telescoping').glob('*.json')):
        result=execute(json.loads(path.read_text()))
        packet=result['definition']
        if packet['schema']=='pp-binomial-telescoping/1':
            replay_binomial_sum(packet)
            seq=BinomialSumSequence(packet)
            p=packet['power']
            assert seq.terms(size=101)==[sum(comb(n,k)**p for k in range(n+1)) for n in range(101)]
            summaries[path.stem]={'power':p,'order':packet['order'],'value_at_100':str(seq.coefficient(100)),
                'square_hits_0_through_100':seq.power_hits(size=101),
                'direct_sum_cross_check_count':101}
        elif packet['schema']=='pp-antidifference/1':replay_antidifference(packet)
        (out/path.name).write_text(encoded(result)+'\n')
    for p,ratio in ((1,2),(2,{'numerator':[2,4],'denominator':[1,1]})):
        packet=certify_hypergeometric_solution(discover_binomial_sum(p),ratio)
        replay_hypergeometric_solution(packet)
        (out/('closed_form_'+str(p)+'.json')).write_text(encoded(packet)+'\n')
    (out/'summary.json').write_text(encoded(summaries)+'\n')
    print(encoded(summaries))
if __name__=='__main__':main()
