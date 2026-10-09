"""Rebuild globally complete affine Mordell query receipts."""
import json
from pathlib import Path
from perfectpower.checked_global_population import global_population_certificate,check_global_population

def main():
    queries=[{'ranks':[0,1,2],'objective':['pow','y',2]},
             {'condition':['le',0,'y'],'objective':['mul','x','y']}]
    rows=[]
    cases=[{},dict(scale=5,shift=-7),dict(scale=5),dict(scale=-5,shift=13),
           dict(scale=2,shift=5,domain='positive'),dict(scale=1,shift=3-10**30)]
    for spec in cases:
        packet=global_population_certificate(queries,**spec)
        acceptance=check_global_population(packet)
        if not acceptance['accepted']:raise RuntimeError(acceptance)
        rows.append(dict(packet=packet,acceptance=acceptance))
    out=dict(schema='pp-global-population-replay/1',globally_complete=True,
             source_batches=len(rows),queries=sum(len(r['packet']['results']) for r in rows),rows=rows)
    root=Path(__file__).resolve().parents[1]
    (root/'receipts/global_population_queries.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k!='rows'}))

if __name__=='__main__':main()
