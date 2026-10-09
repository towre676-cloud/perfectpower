"""Reproduce checked original-coordinate population query batches."""
import json
from pathlib import Path
from perfectpower.checked_population import population_certificate, check_population

ROOT=Path(__file__).resolve().parents[1]


def main():
    queries=[{'condition':['or',['eq','x',0],['not',['mod','y',0,2]]],
              'objective':['add',['pow','x',2],['pow','y',2]],'ranks':[0,1,999]},
             {'condition':['le','y',0],'objective':['mul','x','y']},
             {'condition':False}]
    cases=[('signed_square',[0,0,1],2,[-2,2],None),
           ('odd_root',[0,1],3,[-3,3],None),
           ('no_real_square',[-1],2,[-2,2],None),
           ('zero',[0],2,[-2,2],None),
           ('empty_interval',[1],2,[2,1],None),
           ('explicit_mordell',[-2,0,0,1],2,[-2,5],[0,6])]
    rows=[]
    for name,cs,d,x,y in cases:
        packet=population_certificate(cs,d,x,queries,y)
        receipt=check_population(packet)
        if not receipt['accepted']:raise RuntimeError(receipt)
        rows.append(dict(name=name,packet=packet,acceptance=receipt))
    result=dict(schema='pp-population-query-replay/1',complete=True,source_batches=len(rows),
                restricted_queries=sum(len(r['packet']['results']) for r in rows),
                global_completeness=False,execution_verified=False,rows=rows)
    (ROOT/'receipts/polynomial_population_queries.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rows'}))


if __name__=='__main__':main()
