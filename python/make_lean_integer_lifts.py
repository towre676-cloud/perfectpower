"""Kernel-replayable unimodular coordinates for five actual Smith instances."""
import json
from pathlib import Path
from perfectpower.integer_lifting import smith_certificate
from perfectpower.exact_linear import inverse


def build(output='receipts/branched_geometry'):
    out=Path(output);cases=[]
    lean=['import PerfectPower.IntegerLiftRecovery','namespace PerfectPower.Generated.IntegerLiftPackets',
          'open Matrix','set_option maxRecDepth 100000','set_option maxHeartbeats 0']
    def literal(a):return '!['+','.join('!['+','.join(map(str,row))+']' for row in a)+']'
    for index,a in enumerate(([[2,3]],[[4,6]],[[2,0,1],[0,3,1]],[[2,4],[6,12]],[[2,0],[0,3]])):
        cert=smith_certificate(a);u,v,d=cert['left'],cert['right'],cert['diagonal_matrix']
        ui,vi=inverse(u),inverse(v)
        if any(x.denominator!=1 for block in (ui,vi) for row in block for x in row):raise AssertionError('inverse not integral')
        ui=[[int(x) for x in row] for row in ui];vi=[[int(x) for x in row] for row in vi]
        m,n=len(a),len(a[0]);prefix=f'case_{index}'
        for name,block,h,w in (('A',a,m,n),('U',u,m,m),('Ui',ui,m,m),('V',v,n,n),('Vi',vi,n,n),('D',d,m,n)):
            lean.append(f'def {prefix}_{name} : Matrix (Fin {h}) (Fin {w}) ℤ := {literal(block)}')
        lean.append(f'''theorem {prefix}_all (x : Fin {n} → ℤ) (b : Fin {m} → ℤ) :
    {prefix}_A *ᵥ x=b ↔ {prefix}_D *ᵥ ({prefix}_Vi *ᵥ x)={prefix}_U *ᵥ b := by
  exact PerfectPower.IntegerLiftRecovery.transformed_fibre {prefix}_A {prefix}_U {prefix}_Ui {prefix}_V {prefix}_Vi {prefix}_D
    (by decide +kernel) (by decide +kernel) (by decide +kernel) x b''')
        lean.append(f'#print axioms {prefix}_all')
        cases.append({'certificate':cert,'left_inverse':ui,'right_inverse':vi,
                      'theorem':f'PerfectPower.Generated.IntegerLiftPackets.{prefix}_all'})
    lean.append('end PerfectPower.Generated.IntegerLiftPackets')
    (out/'IntegerLiftPackets.lean').write_text('\n'.join(lean)+'\n')
    (out/'integer_lift_packets.json').write_text(json.dumps(cases,separators=(',',':'))+'\n')
    return len(cases)
if __name__=='__main__':print(build())
