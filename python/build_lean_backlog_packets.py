"""Emit kernel-checkable arithmetic packets from the existing geometry corpus.
This does not formalize analytic normalization or interpret numerical periods.
"""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

root = Path(__file__).resolve().parents[1]
out = root / 'receipts/lean_backlog'
out.mkdir(exist_ok=True)
inputs = [root/'receipts/holomorphic_basis/representative_bases.json',
          root/'receipts/holomorphic_basis/collision_characters.json',
          root/'receipts/positive_geometry/associahedra.json',
          root/'receipts/positive_geometry/polyhedral_metrics.json']
representatives, collisions, faces, metrics = [json.loads(p.read_text()) for p in inputs]
profiles = []
for row in representatives:
    p = row['packet']; g = p['geometry']
    profiles.append((g['power'], g['root_multiplicities'], g['genus_per_component'],
                     [c['holomorphic_dimension'] for c in p['characters']]))
for row in collisions['rows']:
    profiles.append((row['power'], row['multiplicities'], row['genus_per_component'],
                     [c['holomorphic_dimension'] for c in row['characters']]))

head = '''import PerfectPower.HolomorphicArithmetic
import PerfectPower.PositiveGeometry
namespace PerfectPower.LeanBacklogPackets
open PerfectPower.HolomorphicArithmetic
set_option maxRecDepth 100000
set_option maxHeartbeats 0
abbrev Profile := ℕ × List ℕ × ℕ × List ℕ
def checkProfile (p : Profile) : Bool :=
  let c := p.2.1.foldl Nat.gcd p.1
  let n := p.1/c
  let es := p.2.1.map (fun e => e/c)
  decide (basisDimension n es = p.2.2.1 ∧ ramificationGenus n es = p.2.2.1 ∧
    ((List.range (n-1)).map (fun j => characterDimension n es (j+1))) = p.2.2.2)
'''
def natlist(xs): return '['+','.join(map(str,xs))+']'
source = head+'\ndef profiles : List Profile := [\n'+',\n'.join(
    f'({d},{natlist(es)},{g},{natlist(hs)})' for d,es,g,hs in profiles)+']\n'
source += '''theorem all_profiles : profiles.all checkProfile = true := by decide +kernel

def alternating (xs : List ℤ) : ℤ :=
  ((xs.zipIdx).map (fun p => (-1)^p.2*p.1)).sum
'''
for i,row in enumerate(faces):
    xs = row['f_vector']; source += f'theorem association_face_euler_{i} : alternating {natlist(xs)} = 1 := by decide +kernel\n'
    boundary=xs[:-1]
    source += f'theorem association_boundary_euler_{i} : alternating {natlist(boundary)} = {row["euler_boundary"]} := by decide +kernel\n'
for i,row in enumerate(metrics):
    V,E,F=row['vertices'],row['edges'],row['faces']
    source+=f'theorem polyhedral_metric_{i} : (2*({V}:ℚ)-({sum(row["corner_counts"])}:ℚ)/3) = 2*({V}-{E}+{F}) := by norm_num\n'
source += '#print axioms all_profiles\n'
for i in range(len(faces)):
    source += f'#print axioms association_face_euler_{i}\n#print axioms association_boundary_euler_{i}\n'
for i in range(len(metrics)): source+=f'#print axioms polyhedral_metric_{i}\n'
source += 'end PerfectPower.LeanBacklogPackets\n'
(out/'ArithmeticPackets.lean').write_text(source)
receipt={'schema':'pp-lean-backlog-input/1',
         'source_sha256':{str(p.relative_to(root)):hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
         'arithmetic_profiles':len(profiles),'representative_profiles':len(representatives),
         'collision_profiles':len(collisions['rows']),'face_vectors':len(faces),'metric_packets':len(metrics),
         'analytic_geometry_formalized':False}
(out/'packet_inputs.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
