"""Native signed-cycle-word execution certificates for marked branch braids."""
import hashlib
import json
from .marked_curve_topology import braid_monodromy
from .divisor_square import WorkLimit


def _matrix(rows):
    return '!!['+';'.join(','.join(f'({v})' for v in row) for row in rows)+']'


def braid_certificate(genus, word):
    packet=braid_monodromy(genus,word)
    n=2*genus
    if len(word)>64 or len(word)*n**3>20000:raise WorkLimit('native braid reduction budget')
    J=packet['intersection'];stages=[[[int(i==j) for j in range(n)] for i in range(n)]]
    declarations=[];steps=[];checks=[]
    for k,letter in enumerate(word):
        d=packet['vanishing_cycles'][abs(letter)-1];sign=1 if letter>0 else -1
        vector='!['+','.join(f'({v})' for v in d)+']'
        declarations.append(f'private def cycle_{k} : Fin {n} → ℤ := {vector}')
        declarations.append(f'private def factor_{k} : Matrix (Fin {n}) (Fin {n}) ℤ :=\n'
            f'  1 + Matrix.of (fun i j => ({sign}) * cycle_{k} i * ∑ l, cycle_{k} l * intersection l j)')
        steps.append(f'(cycle_{k}, ({sign}))')
        factor=[[int(i==j)+sign*d[i]*sum(d[l]*J[l][j] for l in range(n)) for j in range(n)] for i in range(n)]
        last=stages[-1]
        stages.append([[sum(last[i][l]*factor[l][j] for l in range(n)) for j in range(n)] for i in range(n)])
        checks.append(f'private theorem step_{k} : stage_{k} * factor_{k} = stage_{k+1} := by decide +kernel')
    if stages[-1]!=packet['matrix']:raise ArithmeticError('native factor reconstruction disagrees with producer')
    tag=hashlib.sha256(json.dumps([genus,word],separators=(',',':')).encode()).hexdigest()[:16]
    namespace='PerfectPower.BraidPacket_'+tag
    stage_defs='\n'.join(f'private def stage_{k} : Matrix (Fin {n}) (Fin {n}) ℤ := {_matrix(m)}' for k,m in enumerate(stages))
    product='stage_0'
    for k in range(len(word)):product=f'({product} * factor_{k})'
    proof=f'''  change {product.replace('stage_0',f'(1 : Matrix (Fin {n}) (Fin {n}) ℤ)')} = stage_{len(word)}
  rw [show (1 : Matrix (Fin {n}) (Fin {n}) ℤ) = stage_0 by decide +kernel]
'''
    if word:proof+='  rw ['+', '.join(f'step_{k}' for k in range(len(word)))+']\n'
    else:proof='  decide +kernel\n'
    source=f'''import PerfectPower.PicardLefschetz
namespace {namespace}
open scoped BigOperators
open PerfectPower.PicardLefschetz
private def intersection : Matrix (Fin {n}) (Fin {n}) ℤ := {_matrix(J)}
{chr(10).join(declarations)}
{stage_defs}
{chr(10).join(checks)}
private def steps : List ((Fin {n} → ℤ) × ℤ) := [{','.join(steps)}]
def action : Matrix (Fin {n}) (Fin {n}) ℤ := wordMatrix intersection steps

theorem word_action_checked : action = {_matrix(packet['matrix'])} := by
{proof}
theorem integral_symplectic : action.transpose * intersection * action = intersection := by
  rw [word_action_checked]
  decide +kernel
end {namespace}
#print axioms {namespace}.word_action_checked
#print axioms {namespace}.integral_symplectic
'''
    return dict(schema='pp-native-braid-certificate/1',genus=genus,word=word,receipt=packet,
        namespace=namespace,lean=source,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        native_step_count=len(word),execution_verified=False,
        scope='compile Lean to check each native rank-one factor product and symplectic identity; supplied branch marking is the geometric premise')
