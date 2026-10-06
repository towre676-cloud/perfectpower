"""Emit actual original-model transport and exact literal coordinate-list proofs."""
from .native_rational_certificate import _literal


def literals(points):
    return '(['+','.join('none' if p is None else f'some ({_literal(p[0])},{_literal(p[1])})' for p in points)+'] : List (Option (ℚ × ℚ)))'


def refine(source,ns,E,points,abc,target,quartic):
    a1,a2,a3,a4,a6=E.a
    original=f'(⟨{_literal(a1)},{_literal(a2)},{_literal(a3)},{_literal(a4)},{_literal(a6)}⟩ : WeierstrassCurve ℚ).toAffine'
    sqlemmas=[];sqnames=[]
    if quartic is not None and quartic['roots']:
        from math import isqrt
        from fractions import Fraction
        from .elliptic_arithmetic import q
        for i,r in enumerate(quartic['roots']):
            x=q(r);v=sum(c*x**j for j,c in enumerate(E.cubic))
            s=Fraction(isqrt(max(0,v.numerator)),isqrt(v.denominator))
            name=f'lift_sqrt_{i}';sqnames.append(name)
            sqlemmas.append(f'private theorem {name} : Rat.sqrt (EllipticDivision.cubic {abc} {_literal(x)}) = {_literal(s)} := by decide +kernel')
    extra=f'''
namespace {ns}
open PerfectPower WeierstrassCurve WeierstrassCurve.Affine
{chr(10).join(sqlemmas)}
/-- The exact literal completed coordinates returned by the packet. -/
theorem completed_json_list_checked :
    halves.map EllipticSquareTransport.coordinates = {literals([E.complete(p) for p in points])} := by
  classical
  norm_num [halves, anchor, EllipticPointDivision.torsionList, EllipticPointDivision.branchPoint,
    EllipticSquareTransport.coordinates, two_zsmul, Point.some.injEq, List.filter_cons, List.filter_nil, Point.add_def, Point.add, negY, addX, addY, negAddY,
    WeierstrassCurve.Affine.slope, EllipticPointDivision.completed, EllipticDivision.cubic]
/-- The original generalized model, before square completion. -/
noncomputable def original : Affine ℚ := {original}
/-- The original model is smooth. -/
theorem original_smooth : original.Δ ≠ 0 := by
  norm_num [original, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
/-- The completed native model agrees coefficient by coefficient. -/
theorem model_checked : EllipticSquareTransport.model original = EllipticPointDivision.completed {abc} := by
  ext <;> norm_num [EllipticSquareTransport.model,original,EllipticPointDivision.completed]
/-- The inverse native point-group transport. -/
noncomputable def originalEquiv : (EllipticPointDivision.completed {abc}).Point ≃+ original.Point :=
  (EllipticSquareTransport.castEquiv model_checked.symm).trans (EllipticSquareTransport.equiv original original_smooth).symm
/-- The native fibre expressed as original-model points. -/
noncomputable def originalHalves : List original.Point := halves.map originalEquiv
/-- The checked target expressed as an original-model point. -/
noncomputable def originalTarget : original.Point := originalEquiv target
/-- Complete halving on the actual original point group. -/
theorem original_halves_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ Q ∈ originalHalves :=
  EllipticSquareTransport.list_transport originalEquiv.symm 2 target halves actual_halves_complete Q
/-- Coordinate transport includes the exact inverse ordinate shift. -/
theorem original_coordinates (P : (EllipticPointDivision.completed {abc}).Point) :
    EllipticSquareTransport.coordinates (originalEquiv P) =
      (EllipticSquareTransport.coordinates P).map
        (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2)) := by
  change EllipticSquareTransport.coordinates
    (EllipticSquareTransport.backward original original_smooth (EllipticSquareTransport.castEquiv model_checked.symm P)) = _
  rw [EllipticSquareTransport.coordinates_backward, EllipticSquareTransport.coordinates_cast]
/-- The literal original coordinates are exactly the native full fibre output. -/
theorem original_json_list_checked :
    originalHalves.map EllipticSquareTransport.coordinates = {literals(points)} := by
  simp only [originalHalves, List.map_map, Function.comp_def, original_coordinates]
  change halves.map ((fun p : Option (ℚ × ℚ) => p.map
    (fun xy => (xy.1,xy.2-(original.a₁*xy.1+original.a₃)/2))) ∘ EllipticSquareTransport.coordinates) = _
  rw [← List.map_map, completed_json_list_checked]
  norm_num [original]
/-- Actual original-model halves are exactly the returned literal coordinates. -/
theorem literal_fibre_complete (Q : original.Point) :
    (2 : ℤ) • Q = originalTarget ↔ EllipticSquareTransport.coordinates Q ∈ {literals(points)} := by
  rw [original_halves_complete, ← original_json_list_checked, List.mem_map]
  constructor
  · intro h
    exact ⟨Q,h,rfl⟩
  · rintro ⟨T,hT,he⟩
    have h := EllipticSquareTransport.coordinates_injective original he
    simpa [← h] using hT
/-- The native original target has exactly the supplied coordinates. -/
theorem original_target_checked : EllipticSquareTransport.coordinates originalTarget =
    {('none' if target is None else f'some ({_literal(target[0])},{_literal(target[1])})')} := by
  unfold originalTarget
  rw [original_coordinates]
  norm_num [target, EllipticSquareTransport.coordinates, original]
end {ns}
#print axioms {ns}.literal_fibre_complete
#print axioms {ns}.original_target_checked
#print axioms {ns}.completed_json_list_checked
#print axioms {ns}.original_halves_complete
#print axioms {ns}.original_json_list_checked
'''
    # Infinity and empty fibres have no anchor declaration.
    if 'noncomputable def anchor ' not in source:extra=extra.replace('halves, anchor,','halves, target,')
    if 'EllipticQuarticLifts.fibreList' in source:
        start="  classical\n  norm_num [halves, target,"
        head="  classical\n  simp only [halves, EllipticQuarticLifts.fibreList, List.flatMap_cons, List.flatMap_nil, EllipticQuarticLifts.lifts]\n"
        if sqnames:head+="  simp only ["+','.join(sqnames)+"]\n"
        head+="  norm_num [target,"
        extra=extra.replace(start,head)
    return source+extra
