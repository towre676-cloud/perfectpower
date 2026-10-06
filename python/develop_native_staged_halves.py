"""Generate checked typed original halving packets and a native composed fibre."""
from pathlib import Path
from perfectpower.elliptic_arithmetic import EllipticCurve
from perfectpower.native_halves_certificate import halves_certificate


def develop(output='receipts/elliptic_bridges'):
    out=Path(output);out.mkdir(parents=True,exist_ok=True)
    fixtures=[('TypedHalvesAnchor',[-1,0],[0,0],{}),
              ('TypedHalvesCoset',[0,-2],['129/100','-383/1000'],dict(anchor=[3,5])),
              ('TypedHalvesNonsquare',[1,0],[0,0],{})]
    for name,spec,target,kw in fixtures:
        (out/(name+'.lean')).write_text(halves_certificate(spec,target,**kw)['lean'])
    E=EllipticCurve([0,-2]);P=E.checked([3,5]);twice=E.mul(P,2)
    outer=halves_certificate(E.specification,E.mul(P,4),anchor=twice)
    inner=halves_certificate(E.specification,twice,anchor=P)
    imports=sorted({l for p in [outer,inner] for l in p['lean'].splitlines() if l.startswith('import ')})
    source='\n'.join(imports)+'\n'+'\n'.join(l for p in [outer,inner] for l in p['lean'].splitlines() if not l.startswith('import '))
    a,b=outer['namespace'],inner['namespace'];ns='PerfectPower.NativeStagedHalvesExample'
    source+=f'''
namespace {ns}
open PerfectPower
private theorem outer_singleton : {a}.typedFibre.points=[{a}.anchor] := by
  simp [{a}.typedFibre, {a}.halves, EllipticPointDivision.torsionList]
noncomputable def innerPacket (H : (EllipticPointDivision.completed (0 : ℚ) 0 (-2)).Point)
    (hH : H ∈ {a}.typedFibre.points) : TypedDivisionPackets.FibrePacket 2 H := by
  have he : H={a}.anchor := by simpa [outer_singleton] using hH
  subst H
  exact {b}.typedFibre
noncomputable def points := TypedDivisionPackets.compose 2 2 {a}.target
  {a}.typedFibre innerPacket
theorem actual_four_fibre_complete
    (Q : (EllipticPointDivision.completed (0 : ℚ) 0 (-2)).Point) :
    (4 : ℤ) • Q={a}.target ↔ Q ∈ points :=
  TypedDivisionPackets.compose_complete 2 2 {a}.target {a}.typedFibre innerPacket Q
end {ns}
#print axioms {ns}.actual_four_fibre_complete
'''
    (out/'NativeStagedHalves.lean').write_text(source)


if __name__=='__main__':develop()
