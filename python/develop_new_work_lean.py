"""Emit kernel proof instances bound to the retained SOE and matrix receipts."""
import json
from fractions import Fraction
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def rat(x):
 q=Fraction(x)
 return f'({q.numerator}:ℚ)' if q.denominator==1 else f'({q.numerator}:ℚ)/{q.denominator}'
def choices(values,var,encode):
 out=encode(values[-1])
 for i in reversed(range(len(values)-1)):out=f'if {var}={i} then {encode(values[i])} else ({out})'
 return out
def opt(x):return 'none' if x is None else f'some {x}'
def main():
 rows=json.loads((ROOT/'receipts/soe_bridge/all_two_state_automata.json').read_text())
 lines=['import PerfectPower.SOESemantics','namespace PerfectPower.SOEModelPackets','set_option linter.unusedVariables false']
 for i,r in enumerate(rows):
  model,p=r['model'],r['packet'];q=p['projection'];n=len(p['blocks']);tag=f'{i:03}'
  obs=choices(model['observations'],'s',str)
  aa=choices(model['actions']['a'],'s',opt);bb=choices(model['actions']['b'],'s',opt)
  qt=[]
  for key in ['a','b']:
   qt.append(choices(p['quotient']['actions'][key],'s',opt))
  word=p['distinguishing_witnesses'][0]['word'] if p['distinguishing_witnesses'] else []
  w='['+','.join(str(0 if a=='a' else 1) for a in word)+']'
  lines.extend([f'def obs{tag} (s : Fin 2) : ℕ := {obs}',
   f'def step{tag} (s : Fin 2) (a : Fin 2) : Option (Fin 2) := if a=0 then ({aa}) else ({bb})',
   f'def q{tag} (s : Fin 2) : Fin {n} := '+choices(q,'s',str),
   f'def out{tag} (s : Fin {n}) : ℕ := '+choices(p['quotient']['observations'],'s',str),
   f'def target{tag} (s : Fin {n}) (a : Fin 2) : Option (Fin {n}) := if a=0 then ({qt[0]}) else ({qt[1]})',
   f'theorem complete{tag} (s t : Fin 2) : SOESemantics.Equivalent step{tag} obs{tag} s t ↔ q{tag} s=q{tag} t := by',
   f'  apply SOESemantics.quotient_complete step{tag} target{tag} obs{tag} out{tag} q{tag}',
   '  · decide','  · decide',
   f'  · have hw : ∀ s t : Fin 2, q{tag} s ≠ q{tag} t → SOESemantics.behavior step{tag} obs{tag} s ({w} : List (Fin 2)) ≠ SOESemantics.behavior step{tag} obs{tag} t {w} := by decide',
   f'    intro s t h; exact ⟨{w}, hw s t h⟩'])
 lines.append('end PerfectPower.SOEModelPackets')
 (ROOT/'PerfectPower/Generated/SOEModelPackets.lean').write_text('\n\n'.join(lines)+'\n')
 matrices=json.loads((ROOT/'receipts/structural_math/matrix_certificates.json').read_text())
 lines=['import PerfectPower.StructuralCertificates','namespace PerfectPower.StructuralPackets']
 for i,packet in enumerate([p['metric'] for p in matrices['lyapunov']]+[p['psd'] for p in matrices['toeplitz']]):
  a,L,D=packet['matrix'],packet['L'],packet['D'];n=len(D);vs=[f'x{j}' for j in range(n)];params=' '.join(vs)
  lhs='+'.join(f'({rat(a[j][k])})*{vs[j]}*{vs[k]}' for j in range(n) for k in range(n))
  zs=['+'.join(f'({rat(L[j][k])})*{vs[j]}' for j in range(n)) for k in range(n)]
  rhs='+'.join(f'({rat(d)})*({z})^2' for d,z in zip(D,zs))
  lines += [f'def form{i} ({params} : ℚ) : ℚ := {lhs}',f'theorem ldl{i} ({params} : ℚ) : form{i} {params}={rhs} := by unfold form{i}; ring',f'theorem nonnegative{i} ({params} : ℚ) : 0 ≤ form{i} {params} := by rw [ldl{i}]; positivity']
  if i<2:
   A=matrices['lyapunov'][i]['operator'];alpha=rat(matrices['lyapunov'][i]['alpha'])
   velocity=['+'.join(f'({rat(A[j][k])})*{vs[k]}' for k in range(n)) for j in range(n)]
   deriv='+'.join(f'2*({rat(a[j][k])})*{vs[j]}*({velocity[k]})' for j in range(n) for k in range(n))
   residual='+'.join(f'{v}^2' for v in vs)
   lines.append(f'theorem dissipation{i} ({params} : ℚ) : ({deriv})+2*({alpha})*form{i} {params}=-({residual}) := by unfold form{i}; ring')
 # The global and constrained PSG energy bounds, with exact attainment on v=0.
 lines += ['def energy (v a p : ℚ) : ℚ := v^2+a^2+(2*a-1)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2',
 'theorem global_energy (v a p : ℚ) : 1/5 ≤ energy v a p := by\n  have hid : energy v a p-1/5=v^2+5*(a-2/5)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2 := by unfold energy; ring\n  have hn : 0 ≤ v^2+5*(a-2/5)^2+(v+4-8*a)^2+(a*v-2*a-2*p*v+1)^2+(2*a*v+4*a-4*p*v-v-2)^2 := by positivity\n  linarith',
 'theorem slice_energy (a p : ℚ) : 22/89 ≤ energy 0 a p := by\n  have hid : energy 0 a p-22/89=89*(a-44/89)^2 := by unfold energy; ring\n  have hn : 0 ≤ 89*(a-44/89)^2 := by positivity\n  linarith',
 'theorem slice_attainment (p : ℚ) : energy 0 (44/89) p=22/89 := by unfold energy; ring',
 'end PerfectPower.StructuralPackets']
 (ROOT/'PerfectPower/Generated/StructuralPackets.lean').write_text('\n\n'.join(lines)+'\n')
 print('Emitted 324 all-future quotient proofs and retained matrix/energy proofs')
if __name__=='__main__':main()
