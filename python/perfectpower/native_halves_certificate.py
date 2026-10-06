"""Native actual-point certificates for anchored and root-free halving fibres."""
import hashlib
import json
from .elliptic_arithmetic import EllipticCurve, encode_point, rational_literal
from .native_rational_certificate import two_torsion_certificate, rational_certificate, _literal
from .divisor_square import WorkLimit


def halves_certificate(specification, target, *, anchor=None, divisor_work_limit=1024,
                       node_limit=100000):
    """Emit a complete Mathlib fibre, using a checked anchor or a root-free quartic.

    Coordinate literals refer to the completed model. Numeric output coordinates
    are retained as producer evidence; the proved list is the actual group coset.
    Original-model transport and JSON interpreter refinement remain separate.
    """
    E=EllipticCurve(specification);target=E.checked(target)
    base=two_torsion_certificate(E.specification,divisor_work_limit=divisor_work_limit,node_limit=node_limit)
    C,B,A,_=E.cubic;abc=f'({_literal(A)} : ℚ) {_literal(B)} {_literal(C)}'
    if anchor is not None:
        anchor=E.checked(anchor)
        if E.mul(anchor,2)!=target:raise ValueError('anchor does not double to target')
        points=[E.add(anchor,t) for t in [None,*E.two_torsion()]]
        evidence=None
    else:
        evidence=E.rational_halves(target,node_limit=node_limit)
        anchor=E.checked(evidence['anchor']);points=[E.checked(p) for p in evidence['points']]
    for p in [target,anchor,*points]:
        if p is not None and any(max(abs(c.numerator).bit_length(),c.denominator.bit_length())>256 for c in p):
            raise WorkLimit('native point coordinate bit budget')
    tag=hashlib.sha256(json.dumps([E.specification,encode_point(target),encode_point(anchor)],sort_keys=True).encode()).hexdigest()[:16]
    ns='PerfectPower.HalvesPacket_'+tag
    source=base['lean'].replace(base['namespace'],ns)
    roots=base['rational_root_packet']['roots']
    from .elliptic_arithmetic import q
    rootset='({' + ','.join(_literal(q(r)) for r in roots) + '} : Finset ℚ)' if roots else '(∅ : Finset ℚ)'
    defs=[]
    def point_def(name,p):
        if p is None:
            defs.append(f'noncomputable def {name} : (EllipticPointDivision.completed {abc}).Point := 0')
        else:
            x,y=p
            defs.append(f'''private theorem {name}_on_curve : (EllipticPointDivision.completed {abc}).Nonsingular {_literal(x)} {_literal(y)} :=
  (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero smooth_checked).mp
    ((EllipticPointDivision.equation_completed _ _ _ _ _).mpr (by norm_num [EllipticDivision.cubic]))
noncomputable def {name} : (EllipticPointDivision.completed {abc}).Point := WeierstrassCurve.Affine.Point.some {name}_on_curve''')
    point_def('target',E.complete(target))
    quartic=None
    if target is None:
        if anchor is not None:raise ValueError('infinity uses the native kernel list directly')
        method='two_torsion'
        proof=f'''noncomputable def halves : List (EllipticPointDivision.completed {abc}).Point :=
  EllipticPointDivision.torsionList {abc} smooth_checked {rootset}.toList
 theorem actual_halves_complete (Q : (EllipticPointDivision.completed {abc}).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := actual_two_torsion_complete Q'''
    elif anchor is not None:
        method='torsion_coset';point_def('anchor',E.complete(anchor));x,y=E.complete(anchor)
        proof=f'''theorem anchor_checked : (2 : ℤ) • anchor = target := by
  unfold anchor target
  rw [two_zsmul]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne (by
    norm_num [EllipticPointDivision.completed, WeierstrassCurve.Affine.negY] :
      ({_literal(y)} : ℚ) ≠ (EllipticPointDivision.completed {abc}).negY {_literal(x)} {_literal(y)})]
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  norm_num [WeierstrassCurve.Affine.addX, WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY, WeierstrassCurve.Affine.slope,
    EllipticPointDivision.completed, WeierstrassCurve.Affine.negY]
noncomputable def halves : List (EllipticPointDivision.completed {abc}).Point :=
  (EllipticPointDivision.torsionList {abc} smooth_checked {rootset}.toList).map (fun T => anchor + T)
theorem actual_halves_complete (Q : (EllipticPointDivision.completed {abc}).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves :=
  EllipticDivision.fibre_list_complete 2 target anchor anchor_checked _ actual_two_torsion_complete Q'''
    else:
        method='root_free_quartic'
        quartic=rational_certificate(E.division_polynomial(target),divisor_work_limit=divisor_work_limit,node_limit=node_limit)
        if quartic['roots']:
            raise WorkLimit('native empty fibre currently requires a root-free quartic; nonsquare lifts remain separate')
        source+='\n'+'\n'.join(line for line in quartic['lean'].splitlines() if not line.startswith('import '));u,v=E.complete(target)
        proof=f'''theorem quartic_root_free (x : ℚ) : EllipticDivision.halvingPolynomial {abc} {_literal(u)} x ≠ 0 := by
  have hc := {quartic['namespace']}.source_complete x
  have he : {quartic['namespace']}.source.eval x = EllipticDivision.halvingPolynomial {abc} {_literal(u)} x := by
    norm_num [{quartic['namespace']}.source, EllipticDivision.halvingPolynomial] <;> ring
  rw [he] at hc
  simpa using hc
noncomputable def halves : List (EllipticPointDivision.completed {abc}).Point := []
theorem actual_halves_complete (Q : (EllipticPointDivision.completed {abc}).Point) :
    (2 : ℤ) • Q = target ↔ Q ∈ halves := by
  have hn := EllipticPointDivision.no_half_of_quartic_root_free {abc} {_literal(u)} {_literal(v)} target_on_curve quartic_root_free Q
  simpa [target, halves] using hn'''
    source+='\nnamespace '+ns+'\nopen PerfectPower\n'+'\n'.join(defs)+'\n'+proof+'\nend '+ns+'\n'
    source+=f'#print axioms {ns}.actual_halves_complete\n'
    if method=='torsion_coset':source+=f'#print axioms {ns}.anchor_checked\n'
    if method=='root_free_quartic':source+=f'#print axioms {ns}.quartic_root_free\n'
    for name,doc in [('source','The original rational polynomial bound to this packet.'),
                     ('target','The checked actual target on the completed model.'),
                     ('anchor','The checked actual anchor on the completed model.'),
                     ('halves','The complete native halving fibre list.')]:
        source=source.replace('noncomputable def '+name+' ', '/-- '+doc+' -/\nnoncomputable def '+name+' ')
    return dict(schema='pp-native-halves-certificate/1',curve=E.specification,target=encode_point(target),
        anchor=encode_point(anchor),completed_target=encode_point(E.complete(target)),
        completed_anchor=encode_point(E.complete(anchor)),completed_points=[encode_point(E.complete(p)) for p in points],
        method=method,producer_evidence=evidence,torsion_packet=base,quartic_packet=quartic,
        namespace=ns,lean=source,source_sha256=hashlib.sha256(source.encode()).hexdigest(),
        execution_verified=False,scope='compile Lean for complete actual completed-model fibre; numeric producer list and original-model transport are not interpreter-refined')
