"""Generate exact solution charts, queries and all-integer Lean certificates."""
import json
from pathlib import Path
from perfectpower.linear_product import solve,query,compile_lean,close_descent
from perfectpower.euclid_descent import compile_descent


def main():
    out=Path('receipts/linear_product');out.mkdir(parents=True,exist_ok=True)
    cases=[('Adjacent',[0,1],[2,1]),('Six',[0,1],[6,1]),
           ('NegativeSlopes',[0,-1],[6,-1]),('UnequalSlopes',[1,4],[3,9]),
           ('NoSolutions',[1,2],[6,8]),('OddMidpoint',[0,1],[3,1]),
           ('Translated80Digits',[-10**80,1],[6-10**80,1])]
    for name,left,right in cases:
        p=solve(left,right)
        (out/f'{name}.json').write_text(json.dumps(p,indent=2)+'\n')
        proof=compile_lean(p)
        (out/f'{name}.lean').write_text(proof.pop('source'))
        (out/f'{name}-proof.json').write_text(json.dumps(proof,indent=2)+'\n')
    q=query(solve([0,1],[6,1]),{'restrictions':{'n_min':0,'y_min':0},'select':1,'rank':[2,4],'objective':'y','maximize':True})
    (out/'query.json').write_text(json.dumps(q,indent=2)+'\n')
    (out/'closed-descent.json').write_text(json.dumps(close_descent(compile_descent([0,1],[6,1])),indent=2)+'\n')


if __name__=='__main__':main()
