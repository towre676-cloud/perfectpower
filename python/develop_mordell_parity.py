"""Generate actual rational-group saturation-at-2 proofs for the retained census."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve, primes, encode_point

ROOT = Path(__file__).resolve().parents[1]


def literal(r):
    r = Fraction(r)
    return f'({r.numerator}/{r.denominator} : ℚ)'


def obstruction(cs):
    for m in primes(197):
        if all(sum(c*pow(z,i,m) for i,c in enumerate(cs)) % m for z in range(m)):
            return m
    raise ArithmeticError('no root-free residue modulus in the declared search')


def root_proof(label, cs, source, q):
    n = len(cs)-1
    m = obstruction(cs)
    return f'''private noncomputable def {label}_source : Polynomial ℚ := {source}
private def {label}_coefficients : List ℤ := {cs}
private noncomputable def {label}_scaled := polynomial {label}_coefficients
private theorem {label}_degree : {label}_source.natDegree={n} := by
  unfold {label}_source
  compute_degree! <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
private theorem {label}_monic : {label}_scaled.Monic := by
  simp [{label}_scaled,{label}_coefficients,polynomial] <;> monicity! <;> norm_num
private theorem {label}_scale : {label}_scaled.map (Int.castRingHom ℚ) = {label}_source.scaleRoots ({q}) := by
  have hg : {label}_scaled.natDegree={n} := by
    simp [{label}_scaled,{label}_coefficients,polynomial] <;> compute_degree! <;> norm_num
  ext i
  rw [Polynomial.coeff_map,Polynomial.coeff_scaleRoots,{label}_degree]
  by_cases hi : i ≤ {n}
  · interval_cases i <;> norm_num [{label}_scaled,{label}_coefficients,polynomial,{label}_source,Polynomial.coeff_one,Polynomial.coeff_X]
  · have hi' : {n} < i := by omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hg]; exact hi'),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [{label}_degree]; exact hi')]
    simp
theorem {label}_root_free (x : ℚ) : {label}_source.eval x ≠ 0 :=
  rational_root_free {label}_source {label}_coefficients ({q}) {label}_monic {label}_scale {m} (by decide +kernel) (by decide +kernel) x
''', m


def curve_source(packet):
    k = packet['k']
    E = EllipticCurve([0,k])
    basis = [E.checked(p) for p in packet['basis_points']]
    label = ('m' if k<0 else 'p')+str(abs(k))
    source = f'namespace Curve_{label}\n'
    proof, m = root_proof('branch', [k,0,0,1], f'X^3+C ({k})', 1)
    source += proof
    source += f'''theorem branch_free (x : ℚ) : EllipticDivision.cubic 0 0 ({k}) x ≠ 0 := by
  simpa [branch_source,EllipticDivision.cubic] using branch_root_free x
theorem double_injective : Function.Injective (fun P : (completed (0:ℚ) 0 ({k})).Point => (2:ℤ) • P) :=
  doubling_injective 0 0 ({k}) branch_free
private theorem smooth : (completed (0:ℚ) 0 ({k})).Δ ≠ 0 := by
  norm_num [completed,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
'''
    points = basis + ([E.add(*basis)] if len(basis)==2 else [])
    moduli=[]
    for j, point in enumerate(points):
        u,v = point
        p,q = u.numerator,u.denominator
        cs=[-4*p*k*q**3,-8*k*q**3,0,-4*p,1]
        proof, modulus = root_proof(f'half{j}',cs,f'X^4-C (4*{literal(u)})*X^3-C ({8*k})*X-C (4*{literal(u)}*({k}))',q)
        source += proof
        moduli.append(modulus)
        source += f'''private theorem on_curve{j} : (completed (0:ℚ) 0 ({k})).Nonsingular {literal(u)} {literal(v)} :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth).mp
    ((equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def P{j} : (completed (0:ℚ) 0 ({k})).Point := WeierstrassCurve.Affine.Point.some on_curve{j}
theorem no_half{j} (Q : (completed (0:ℚ) 0 ({k})).Point) : (2:ℤ) • Q ≠ P{j} := by
  apply no_half_of_quartic_root_free 0 0 ({k}) {literal(u)} {literal(v)} on_curve{j}
  intro x
  have he : half{j}_source.eval x=EllipticDivision.halvingPolynomial (0:ℚ) 0 ({k}) {literal(u)} x := by
    simp only [half{j}_source,EllipticDivision.halvingPolynomial,Polynomial.eval_sub,Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    ring
  rw [← he]
  exact half{j}_root_free x
'''
    if len(basis)==1:
        source += '''theorem two_saturated (Q : (completed (0:ℚ) 0 ('''+str(k)+''')).Point) (m : ℤ)
    (h : (2:ℤ) • Q=m • P0) : ∃ a : ℤ, Q=a • P0 :=
  cyclic_two_saturated P0 double_injective no_half0 Q m h
'''
    else:
        u,v=basis[0];x,y=basis[1]
        if u==x:raise ArithmeticError('separate equal-abscissa addition proof required')
        source += f'''theorem sum_checked : P0+P1=P2 := by
  unfold P0 P1 P2
  rw [WeierstrassCurve.Affine.Point.add_some (by
    norm_num [completed,WeierstrassCurve.Affine.negY] : ¬({literal(u)}={literal(x)} ∧ {literal(v)}=(completed (0:ℚ) 0 ({k})).negY {literal(x)} {literal(y)}))]
  rw [WeierstrassCurve.Affine.Point.some.injEq,
    WeierstrassCurve.Affine.slope_of_X_ne (by norm_num : {literal(u)} ≠ {literal(x)})]
  norm_num [completed,WeierstrassCurve.Affine.addX,WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY]
theorem two_saturated (Q : (completed (0:ℚ) 0 ({k})).Point) (m n : ℤ)
    (h : (2:ℤ) • Q=m • P0+n • P1) : ∃ a b : ℤ, Q=a • P0+b • P1 :=
  pair_two_saturated P0 P1 double_injective no_half0 no_half1 (by rw [sum_checked]; exact no_half2) Q m n h
'''
    source += f'end Curve_{label}\n'
    source += ''.join(f'#print axioms PerfectPower.MordellParityAtlas.Curve_{label}.{t}\n' for t in ['double_injective','two_saturated',*[f'no_half{j}' for j in range(len(points))]])
    return source, dict(k=k,rank=len(basis),basis_points=packet['basis_points'],parity_points=[encode_point(p) for p in points],branch_modulus=m,halving_moduli=moduli)


def main():
    rows=[];sources=[]
    for path in sorted((ROOT/'receipts/mordell_completion').glob('[mp][0-9]*.json')):
        packet=json.loads(path.read_text())
        if packet.get('status')!='complete':continue
        source,row=curve_source(packet)
        row.update(source_receipt=str(path.relative_to(ROOT)),source_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        rows.append(row);sources.append(source)
    folder=ROOT/'PerfectPower/MordellParityAtlas';folder.mkdir(exist_ok=True)
    blocks=[]
    for i,start in enumerate(range(0,len(sources),16)):
        path=folder/f'Block{i:02d}.lean'
        path.write_text('import PerfectPower.MordellParity\nimport Mathlib.Tactic.ComputeDegree\nimport Mathlib.Tactic.IntervalCases\nset_option maxRecDepth 4096\nset_option maxHeartbeats 2000000\nset_option linter.unusedTactic false\nset_option linter.unreachableTactic false\nset_option linter.unnecessarySeqFocus false\nnamespace PerfectPower.MordellParityAtlas\nopen Polynomial PerfectPower.MordellParity PerfectPower\n'+''.join(sources[start:start+16])+'end PerfectPower.MordellParityAtlas\n')
        blocks.append(str(path.relative_to(ROOT)))
    (ROOT/'data/mordell_parity_sources.json').write_text(json.dumps(dict(schema='pp-mordell-parity-sources/1',rows=rows,proof_blocks=blocks),indent=2)+'\n')
    print(json.dumps(dict(curves=len(rows),rank_one=sum(r['rank']==1 for r in rows),rank_two=sum(r['rank']==2 for r in rows),parity_obstructions=sum(len(r['halving_moduli']) for r in rows),blocks=len(blocks))))


if __name__=='__main__':main()
