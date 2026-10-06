"""Source-bound nonenumerating Lean counts for finite affine residue domains."""
import hashlib
import json
from .semilinear_domains import semilinear_domain, _normalize
from .native_population_certificate import _predicate
from .divisor_square import WorkLimit


def residue_certificate(predicate, *, period_limit=64, cell_limit=32):
    if type(period_limit) is not int or not 1<=period_limit<=256:
        raise ValueError('period limit 1 through 256 required')
    if type(cell_limit) is not int or not 1<=cell_limit<=64:
        raise ValueError('cell limit 1 through 64 required')
    tree,atoms=_normalize(predicate,atom_limit=32)
    if any(len(a['poly'])>2 for a in atoms):
        raise ValueError('native residue source proof currently requires affine atoms')
    if any(abs(c).bit_length()>256 for a in atoms for c in a['poly']) or any(
        abs(a[k]).bit_length()>256 for a in atoms for k in ('modulus','value') if k in a):
        raise WorkLimit('affine coefficient bit budget')
    domain=semilinear_domain(predicate,period_limit=period_limit,work_limit=100000)
    if domain['cardinality'] is None:
        raise ValueError('finite source domain required; include original bounds')
    cells=[]
    for c in domain['cells']:
        lo,hi=c['interval'];m=c['modulus']
        cells.extend((lo,hi,m,r) for r in c['residues'])
    if len(cells)>cell_limit:raise WorkLimit('native residue cell budget')
    n=len(cells);expr=_predicate(tree,atoms)
    tag=hashlib.sha256(json.dumps(predicate,sort_keys=True,separators=(',',':')).encode()).hexdigest()[:16]
    namespace='PerfectPower.ResiduePacket_'+tag
    vector='!['+','.join(f'⟨({lo}),({hi}),({m}),({r})⟩' for lo,hi,m,r in cells)+']'
    if not cells:vector='fun i => Fin.elim0 i'
    source=f'''import PerfectPower.ResiduePopulation
namespace {namespace}
open PerfectPower.ResiduePopulation
private def original (x : ℤ) : Prop := {expr}
private def cells : Fin {n} → Cell := {vector}

theorem source_complete (x : ℤ) : original x ↔ x ∈ population cells := by
  rw [population_complete]
  simp [original, cells, accepts, Fin.exists_fin_succ] <;> omega

private theorem valid_cells : ∀ i, 0 < (cells i).modulus ∧ 0 ≤ (cells i).residue ∧
    (cells i).residue < (cells i).modulus := by
  intro i
  fin_cases i <;> norm_num [cells]

private theorem disjoint_cells : ∀ i j, i ≠ j →
    Disjoint (values (cells i)) (values (cells j)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rw [mem_values] at hx hy
  fin_cases i <;> fin_cases j <;> simp [cells, accepts] at hx hy hij <;> omega

theorem count_checked : (population cells).card = {domain['cardinality']} := by
  rw [population_count cells valid_cells disjoint_cells]
  norm_num [cells, count, Fin.sum_univ_succ] <;> decide +kernel
end {namespace}
#print axioms {namespace}.source_complete
#print axioms {namespace}.count_checked
'''
    return dict(schema='pp-native-residue-certificate/1',predicate=predicate,domain=domain,
        cells=[dict(lower=a,upper=b,modulus=m,residue=r) for a,b,m,r in cells],
        cardinality=domain['cardinality'],namespace=namespace,lean=source,
        source_sha256=hashlib.sha256(source.encode()).hexdigest(),execution_verified=False,
        scope='compile emitted Lean for original affine-source equivalence and floor count; no interval enumeration')
