"""Independent-source factorial corpus: correctness and transformation costs."""
import argparse,json
from fractions import Fraction as Q
from math import factorial,prod
from pathlib import Path
from time import perf_counter
from perfectpower.gamma_arithmetic import (landau,verify_landau,factorial_power,verify_factorial_power,
    hypergeometric,hypergeometric_terms,analyze_gamma)
from perfectpower.core import integer_power_root
from perfectpower.divisor_square import WorkLimit

root=Path(__file__).resolve().parents[1]
source=json.loads((root/'data/gamma_bober52.json').read_text());rows=[];checks=0
for row in source['rows']:
    a,b=row['numerator'],row['denominator'];start=perf_counter();cert=landau(a,b)
    assert cert['integral_for_all_n'] and verify_landau(cert)
    landau_seconds=perf_counter()-start
    recurrence=None
    try:recurrence=hypergeometric(a,b)
    except WorkLimit:pass
    exact=[]
    for n in range(9):
        value=Q(prod(factorial(c*n) for c in a),prod(factorial(c*n) for c in b))
        assert value.denominator==1
        exact.append(str(value))
        for d in (2,3,5):
            decision=factorial_power(n,a,b,d,complete=True)
            assert decision['status']!='UNRESOLVED'
            assert (decision['status']=='POWER')==(integer_power_root(value.numerator,d) is not None)
            assert verify_factorial_power(decision)
            checks+=1
    if recurrence is not None:assert hypergeometric_terms(recurrence,9)==exact
    start=perf_counter();large=factorial_power(1000,a,b,2,complete=False);decision_seconds=perf_counter()-start
    rows.append({'table_line':row['table_line'],'landau_cells':len(cert['intervals']),
                 'integrality':True,'landau_seconds':landau_seconds,'recurrence_supported':recurrence is not None,
                 'large_n':1000,'large_status':large['status'],'decision_seconds':decision_seconds,
                 'obstruction':large.get('proof'),'factorials_constructed':large['factorials_constructed']})
central=analyze_gamma({'kind':'central_binomial'},n=10**100)
result={'source':source['source'],'source_sha256':source['source_sha256'],'rows':rows,
        'independent_small_decision_checks':checks,'all_52_integrality_certificates_replayed':True,
        'hypergeometric_rows':sum(r['recurrence_supported'] for r in rows),
        'large_n_obstructions':sum(r['large_status']=='NOT_POWER' for r in rows),
        'large_n_unresolved':sum(r['large_status']=='UNRESOLVED' for r in rows),
        'central_binomial_symbolic_index':str(10**100),'central_status':central['point']['status'],
        'scope':'measured transformation cost and exact decisions; no general end-to-end solver speedup claim'}
parser=argparse.ArgumentParser();parser.add_argument('--out',default=str(root/'receipts/gamma_arithmetic/independent_corpus.json'))
args=parser.parse_args();Path(args.out).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='rows'},indent=2))
