"""Reproduce the structural arithmetic, inequalities and native descent corpus."""
import json
from collections import Counter
from pathlib import Path
from perfectpower.species import SpeciesPopulation, invariants
from perfectpower.psg_polynomial import parse, power_coordinates
from perfectpower.inequality_certificates import (squares_certificate, lower_bound_certificate,
    check_lower_bound, quadratic_minimum, quadratic_certificate, synthesize_lyapunov,
    check_lyapunov, toeplitz_certificate, check_toeplitz)
from perfectpower.descent_squareclasses import two_isogeny_rank_bound, check_rank_bound


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT/'receipts/structural_math'


def write(name, payload):
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT/name).write_text(json.dumps(payload, indent=2, sort_keys=True)+'\n')


def main():
    species = []
    for n, filters in ((10**6, {}), (10**12, {}),
                       (10**100, {'power':2, 'divisor_count':81})):
        p = SpeciesPopulation(n, **filters)
        packet = p.packet()
        ranks = sorted({0, p.count()//2, p.count()-1}) if p.count() else []
        packet['selected'] = []
        for i in ranks:
            a = p.select(i)
            assert p.rank(a) == i
            packet['selected'].append(dict(rank=i, **invariants(a)))
        species.append(packet)
    write('species.json', species)

    # Actual six PSG Darboux factors, already retained in the source recovery.
    vs = ('v','a','p')
    expressions = ('v','a','2*a-1','v+4-8*a','a*v-2*a-2*p*v+1',
                   '2*a*v+4*a-4*p*v-v-2')
    factors = list(map(lambda s:parse(s,vs), expressions))
    energy = sum((h*h for h in factors), factors[0].constant(0))
    shifted = [factors[0], parse('a-2/5',vs), *factors[3:]]
    global_bound = lower_bound_certificate(energy,'1/5',
        terms=[((),squares_certificate(shifted,[1,5,1,1,1]))])
    assert check_lower_bound(global_bound,energy)
    v = parse('v',vs)
    slice_energy = energy.substitute({'v':0})
    scalar_energy = power_coordinates(slice_energy, ('a',), {'a':('a',1)})
    minimum = quadratic_minimum(scalar_energy)
    lower = minimum['bound']['lower']
    (multiplier,), remainder = (energy-slice_energy).divide([v])
    assert not remainder
    slice_bound = lower_bound_certificate(energy,lower,equalities=[v],
        terms=[((),quadratic_certificate(slice_energy-parse(lower,vs)))],ideal=[(0,multiplier)])
    assert check_lower_bound(slice_bound,energy,equalities=[v])
    assert energy.evaluate([0,'44/89',0]) == parse(lower,vs).evaluate([0,0,0])
    write('psg_invariant_energy.json',dict(source_factors=list(expressions),global_bound=global_bound,
        v_zero_slice_bound=slice_bound,slice_minimum=minimum,
        slice_optimizer={'v':'0','a':'44/89','p':'arbitrary real'},
        scope='declared sum of squares of PSG factors; no physical energy identification'))

    metrics = [synthesize_lyapunov([[-1,10],[0,-2]],'1/4'),
               synthesize_lyapunov([[-2,1,0],[-1,-2,1],[0,-1,-3]],'1/2')]
    assert all(check_lyapunov(p) for p in metrics)
    toeplitz = [toeplitz_certificate([1,1,1]),
                toeplitz_certificate(['1','999999999999999999999999999999/1000000000000000000000000000000'])]
    assert all(check_toeplitz(p) for p in toeplitz)
    write('matrix_certificates.json',dict(lyapunov=metrics,toeplitz=toeplitz))

    rows = []
    for a in range(-6,7):
        for b in range(-12,13):
            if not b or a*a == 4*b:
                continue
            p = two_isogeny_rank_bound(a,b)
            assert check_rank_bound(p,a,b)
            rows.append(p)
    write('two_isogeny_corpus.json',rows)
    histogram = dict(sorted(Counter(p['rank_upper_bound'] for p in rows).items()))
    summary = dict(schema='pp-structural-math-release/1',
        species=[dict(bound=p['specification']['bound'],cardinality=p['cardinality'],states=p['states']) for p in species],
        psg_global_lower='1/5',psg_v_zero_minimum=lower,
        two_isogeny_curves=len(rows),rank_upper_bound_histogram=histogram,
        rational_rank_zero_curves=histogram.get(0,0),
        scope='exact Python calculations; classical descent identity; no new Lean compilation',
        formal_verification=False)
    write('summary.json',summary)
    print(json.dumps(summary,indent=2))


if __name__ == '__main__':
    main()
