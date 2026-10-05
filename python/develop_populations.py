"""Build configuration datasets and exact tasks, including sourced Bober domains."""
import argparse
from hashlib import sha256
import json
from pathlib import Path

from perfectpower.populations import ExactPopulation
from perfectpower.gamma_arithmetic import hypergeometric

ROOT=Path(__file__).resolve().parents[1]


def bounded(lo,hi,predicate=True):
    return {'op':'and','args':[{'poly':[-lo,1],'relation':'>='},
                             {'poly':[-hi,1],'relation':'<='},predicate]}


def save(path, data):
    path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')


def develop(output):
    output.mkdir(parents=True,exist_ok=True)
    T=10**40
    curve_spec=dict(kind='curve',left=[0,0,2],right=[0,0,0,3],
                    predicate={'expr':'y-'+str(6*T*T),'relation':'<='})
    curve=ExactPopulation(curve_spec)
    save(output/'coefficient_curve.spec.json',curve_spec)
    curve_export=curve.export(output/'curve_dataset.jsonl',size=256,seed=20261005)
    records=curve.sample(256,seed=20261005)
    tasks=[]
    for record in records:
        x,y=record['values']['x'],record['values']['y']
        assert 2*x*x==3*y**3 and y<=6*T*T
        assert curve.rank(record)==record['rank']
        tasks.extend([
            dict(kind='ranked_point',question=dict(population_id=curve.population_id,rank=record['rank']),answer=record),
            dict(kind='chart_evaluation',question=dict(chart=record['chart'],parameter=record['parameter']),answer=record['values']),
            dict(kind='count_restriction',question=dict(equation='2*x^2=3*y^3',y_upper=6*record['parameter']**2),
                 answer=2*record['parameter']+1)])
    # Count questions have an independent prime-valuation parameter formula.
    assert curve.count()==2*T+1
    save(output/'math_tasks.json',dict(schema='pp-population-tasks/1',population=curve.summary(),tasks=tasks,
                                      task_scope='exact generated arithmetic tasks; not an external AI evaluation'))
    for rank in (0,T,T+1,2*T):
        record=curve.select(rank)
        assert curve.locate(**record['values'])==rank
    H=10**30
    layout_spec=dict(kind='domain',predicate=bounded(1,H,{'op':'or','args':[
        {'poly':[0,1],'modulus':8,'relation':'=','value':0},
        {'poly':[0,1],'modulus':8,'relation':'=','value':3}]}),
        fields=dict(square_side=[0,0,0,1],cube_side=[0,0,1],elements=[0,0,0,0,0,0,1]))
    layouts=ExactPopulation(layout_spec)
    save(output/'compatible_layouts.spec.json',layout_spec)
    layout_export=layouts.export(output/'layout_dataset.jsonl',size=128,seed=617)
    for record in layouts.sample(128,seed=617):
        values=record['values']
        assert values['square_side']**2==values['cube_side']**3==values['elements']
        assert record['parameter']%8 in (0,3)
    target=H-5
    layout_optimum=layouts.optimize([target*target,-2*target,1])
    save(output/'layout_optimum.json',layout_optimum)
    # Sourced factorial-ratio recurrence coefficients: exact unit-index domains.
    source=ROOT/'data/gamma_bober52.json'
    corpus=json.loads(source.read_text())
    N=10**100
    bober=[]
    dataset=[]
    for row in corpus['rows']:
        recurrence=hypergeometric(row['numerator'],row['denominator'])
        for prime in (17,31,47):
            predicate=bounded(0,N,{'op':'and','args':[
                {'poly':recurrence[k],'modulus':prime,'relation':'!=','value':0} for k in ('P','Q')]})
            spec=dict(kind='domain',predicate=predicate,fields={'index':[0,1]})
            population=ExactPopulation(spec)
            # Independent literal affine-factor products, without polynomial evaluation.
            residues=[]
            for n in range(prime):
                good=all((c*n+j)%prime!=0 for slopes in (row['numerator'],row['denominator'])
                         for c in slopes for j in range(1,c+1))
                if good:residues.append(n)
            expected=sum((N-r)//prime+1 for r in residues if r<=N)
            assert population.count()==expected
            sampled=population.sample(min(4,population.count()),seed=prime+row['table_line'])
            for record in sampled:
                n=record['parameter']
                assert n%prime in residues and population.rank(record)==record['rank']
                dataset.append(dict(family=row['table_line'],prime=prime,**record))
            bober.append(dict(family=row['table_line'],prime=prime,residues=residues,
                              cardinality=population.count(),population_id=population.population_id,specification=spec))
    save(output/'bober_unit_domains.json',dict(source=str(source.relative_to(ROOT)),
        source_sha256=sha256(source.read_bytes()).hexdigest(),original_source=corpus['source'],
        meaning='indices where both original recurrence coefficients are units modulo the stated prime',domains=bober))
    (output/'bober_index_dataset.jsonl').write_text(''.join(json.dumps(r,sort_keys=True)+'\n' for r in dataset))
    summary=dict(schema='pp-population-development/1',curve_cardinality=curve.count(),
        curve_sample_records=256,generated_math_tasks=len(tasks),curve_export=curve_export,
        layout_cardinality=layouts.count(),layout_sample_records=128,layout_export=layout_export,
        layout_optimum=dict(value=layout_optimum['value'],parameters=layout_optimum['points']),
        sourced_families=len(corpus['rows']),unit_domains=len(bober),unit_index_records=len(dataset),
        population_enumeration=False,execution_verified=False,
        scope='constructive application examples and sourced mathematical parameters; no industrial performance or mathematical priority claim')
    # Output destinations are operational details, not deterministic corpus content.
    for k in ('curve_export','layout_export'):summary[k].pop('path')
    save(output/'summary.json',summary)
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',type=Path,default=ROOT/'receipts/populations')
    develop(parser.parse_args().output)
