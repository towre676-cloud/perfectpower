"""420 complete quartic commands; every emitted list is kernel checked."""
import json
from pathlib import Path
from perfectpower.linear_perturbation import solve


def generate():
    source=['import PerfectPower.Tactic.LinearPerturbation',
            'namespace PerfectPower.Generated.LinearCatalogue',
            'set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    rows=[]
    for c in range(-10,11):
        if not c:continue
        for d in range(-10,11):
            name=f'case_{len(rows):03}'
            result=solve(1,0,0,c,d)
            source.append(f'native_linear_perturbation {name} for 1, 0, 0, {c}, {d}')
            rows.append({'name':name,'coefficients':[d,c,0,0,1],**result,
                         'instance_theorem':f'PerfectPower.Generated.LinearCatalogue.{name}_complete'})
    source += ['def sets : List (Finset (ℤ × ℤ)) := ['+', '.join(r['name'] for r in rows)+']',
               'theorem total_points : (sets.map Finset.card).sum=850 := by decide +kernel',
               'theorem empty_curves : (sets.filter fun s => decide (s.card=0)).length=132 := by decide +kernel',
               'end PerfectPower.Generated.LinearCatalogue']
    Path('PerfectPower/Generated/LinearCatalogue.lean').write_text('\n'.join(source)+'\n')
    Path('receipts/linear_perturbation').mkdir(exist_ok=True)
    Path('receipts/linear_perturbation/catalogue.json').write_text(json.dumps(rows,indent=2)+'\n')
    print('Emitted',len(rows),'equations;',sum(len(r['points']) for r in rows),'integer points')


if __name__=='__main__':generate()
