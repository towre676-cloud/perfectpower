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
 from perfectpower.checked_soe import compile_soe
 rows=json.loads((ROOT/'receipts/soe_bridge/all_two_state_automata.json').read_text())
 lines=['import PerfectPower.SOESemantics']
 for i,r in enumerate(rows):
  compiled=compile_soe(r['model'],r['packet']);ns='PerfectPower.CheckedSOE.P'+compiled['specification_sha256'];tag=f'{i:03}'
  lines.append(compiled['lean'].removeprefix('import PerfectPower.SOESemantics\n').replace('#print axioms complete\n',''))
  lines.append('namespace PerfectPower.SOEModelPackets\n'+
   '\n'.join(f'def {name}{tag} := {ns}.{name}' for name in ('obs','step','q','out','target'))+
   f'\ntheorem complete{tag} (s t : Fin {len(r["model"]["observations"])}) : SOESemantics.Equivalent step{tag} obs{tag} s t ↔ q{tag} s = q{tag} t := {ns}.complete s t\nend PerfectPower.SOEModelPackets\n')
 (ROOT/'PerfectPower/Generated/SOEModelPackets.lean').write_text('\n'.join(lines))
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
