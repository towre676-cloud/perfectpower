"""Recover the January arithmetic kernels and apply them to the stored census.

Run from any directory using this script's absolute path. Stdlib only. The
optional 50,000-coordinate run records local timings, not historical timings.
"""
import argparse
import hashlib
import json
from fractions import Fraction as Q
from math import factorial, gcd, isclose
from pathlib import Path
from time import perf_counter
from perfectpower.divisor_kernel import (DivisorKernel,divisor_transform,power_kernel,
                                        sigma_kernel,sparse_divisor_counts,sparse_pairing,threshold_solve)
from perfectpower.divisor_kernel_cli import json_exact
from perfectpower.divisor_sum import sigma_sieve
from perfectpower.exact_linear import rank

ROOT=Path(__file__).resolve().parents[1]


def build(output,benchmark=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    source=ROOT/'receipts/divisor_sum/bounded_power_hits.json'
    census=json.loads(source.read_text());lo,hi=census['domain']
    if lo!=1:raise ValueError('this replay expects the stored prefix census')
    sigma,_=sigma_sieve(hi)
    # A million-coordinate identity links the old incidence idea to the new
    # sigma atlas. This pass allocates vectors, never a million-square matrix.
    rebuilt=divisor_transform(range(1,hi+1))
    assert rebuilt==sigma[1:]
    frequencies={};counts={};validation_rows=0
    for degree,rows in census['hits'].items():
        for n,value,root in rows:
            assert lo<=n<=hi and sigma[n]==value==root**int(degree)
        indices=[row[0] for row in rows]
        frequencies[degree]=sparse_divisor_counts(indices,index_limit=hi)
        counts[degree]=len(rows);validation_rows+=len(rows)
    degrees=sorted(frequencies,key=int)
    gram=[[sparse_pairing(frequencies[a],frequencies[b]) for b in degrees] for a in degrees]
    gram_rank=rank(gram);assert gram_rank==len(degrees)
    # Independent pairwise check on actual (not planted) census subsets.
    pair_checks=0
    for a in degrees:
        left=[row[0] for row in census['hits'][a][:32]]
        ca=sparse_divisor_counts(left,index_limit=hi)
        for b in degrees:
            right=[row[0] for row in census['hits'][b][:32]]
            cb=sparse_divisor_counts(right,index_limit=hi)
            brute=sum(sigma[gcd(i,j)] for i in left for j in right)
            assert sparse_pairing(ca,cb)==brute;pair_checks+=1
    k=sigma_kernel(128);square_indices={row[0] for row in census['hits']['2']}
    indicator=[int(i in square_indices) for i in range(1,129)]
    observation=k.apply(indicator);recovered=k.solve(observation,domain='integer')
    assert recovered['particular']==indicator
    normalized=sigma_kernel(12,normalized=True);v=[(i*7)%11-5 for i in range(12)]
    action=normalized.apply(v);energy=normalized.energy(v)
    assert energy==sum(x*y for x,y in zip(v,action))
    bad=DivisorKernel.from_weights([1,Q(1,10)],normalized=True)
    threshold_rhs=[10**30+i*i for i in range(1,13)]
    threshold_lift=threshold_solve(threshold_rhs)
    assert power_kernel(12,0,normalized=True).apply(threshold_lift)==threshold_rhs
    results={
        'scope':'Recovered arithmetic operators and bounded-corpus feature coordinates; no new perfect-power classification or spectral-growth theorem.',
        'arithmetic':'exact; no new Lean compilation claimed',
        'mobius_coefficients':{'gcd':power_kernel(24).g,'gcd_square':power_kernel(24,2).g,'sigma':sigma_kernel(24).g},
        'counterexamples':{
            'positive_weights_indefinite':{'weights':[1,'1/10'],'vector':[1,-2],
                'normalized_action':bad.apply([1,-2]),'energy':bad.energy([1,-2]),'certificate':bad.certificate()},
            'constant_weights':{'raw':power_kernel(12,0).certificate(),
                'normalized':power_kernel(12,0,normalized=True).certificate()},
            'normality':'Both real kernels equal their transpose, so their Euclidean commutator with the adjoint is identically zero.'},
        'normalized_exact_example':{'vector':v,'action':action,'energy':energy,'certificate':normalized.certificate()},
        'constant_normalized_integral_inverse':{'rhs':threshold_rhs,'solution':threshold_lift,
            'determinant':Q(1,factorial(12)**2),'inverse_diagonal':[2*i*i for i in range(1,12)]+[144],
            'inverse_adjacent_entries':[-i*(i+1) for i in range(1,12)]},
        'decoded_actual_census_prefix':{'domain':[1,128],'source_degree':2,'indicator':indicator,
            'gcd_sigma_observation':observation,'solution':recovered},
        'corpus':{'domain':census['domain'],'globally_complete':False,'hit_counts':counts,
            'validated_rows':validation_rows,'sigma_incidence_identity_rows':hi,
            'degrees':list(map(int,degrees)),'sigma_gcd_gram':gram,'gram_rank':gram_rank,
            'divisor_feature_counts':{d:len(c) for d,c in frequencies.items()},
            'top_divisor_frequencies':{d:sorted(c.items(),key=lambda kv:(-kv[1],kv[0]))[:25] for d,c in frequencies.items()},
            'independent_actual_subset_pairings':pair_checks,
            'pairings_represented':sum(counts.values())**2,
            'meaning':'Each entry sums sigma(gcd(n,m)) over two stored hit sets; overlapping degrees are retained as separate vectors, not independent evidence.'},
        'input_sha256':{str(source.relative_to(ROOT)):hashlib.sha256(source.read_bytes()).hexdigest()}}
    (output/'results.json').write_text(json.dumps(json_exact(results),indent=2)+'\n')
    summary={'validated_rows':validation_rows,'sigma_identity_rows':hi,'corpus_gram_rank':gram_rank,
             'independent_pairings':pair_checks,'normalized_energy':str(energy),'benchmark_requested':benchmark}
    if benchmark:
        n=50_000;vector=[(i*17)%31-15 for i in range(1,n+1)]
        start=perf_counter();raw=sigma_kernel(n);rhs=raw.apply(vector);multiply_seconds=perf_counter()-start
        start=perf_counter();solution=raw.solve(rhs,domain='integer');solve_seconds=perf_counter()-start
        assert solution['particular']==vector
        numerical=sigma_kernel(n,normalized=True,exact=False)
        start=perf_counter();answer=numerical.apply(vector);normalized_seconds=perf_counter()-start
        sampled=[]
        for i in (1,2,3,17,127,997,9999,25001,49999,50000):
            direct=sum(sigma[gcd(i,j)]*vector[j-1]/max(i,j) for j in range(1,n+1))
            assert isclose(answer[i-1],direct,rel_tol=2e-10,abs_tol=2e-9)
            sampled.append({'index':i,'matrix_free':answer[i-1],'direct':direct,'absolute_difference':abs(answer[i-1]-direct)})
        bench={'n':n,'dense_entries_avoided':n*n,'dense_float64_bytes_avoided':8*n*n,
               'divisor_visits':raw.visits,'raw_exact_action_seconds':multiply_seconds,
               'raw_complete_integer_solve_seconds':solve_seconds,
               'raw_recovered_coordinates':n,'normalized_float_action_seconds':normalized_seconds,
               'normalized_sampled_dense_rows':sampled,'floating_sample_tolerance':{'relative':2e-10,'absolute':2e-9},
               'scope':'One current-host run; complete raw inverse replay, ten direct normalized rows. Not a proof of floating accuracy in every coordinate or historical benchmark reproduction.'}
        (output/'benchmark.json').write_text(json.dumps(bench,indent=2)+'\n')
        summary['benchmark']=bench
    print(json.dumps(summary,indent=2));return results


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,default=ROOT/'receipts/divisor_kernel')
    parser.add_argument('--benchmark',action='store_true')
    args=parser.parse_args();build(args.output,args.benchmark)
