"""Rebuild the actual PSG recovery and independent arithmetic comparison corpus."""
import hashlib
import json
import random
from pathlib import Path
from fractions import Fraction as Q
from perfectpower.psg_polynomial import Polynomial,parse,power_coordinates
from perfectpower.psg_algebra import *
from perfectpower.psg_jets import pushforward_profile,differential_model_space


ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts/psg_structural'
OUT.mkdir(parents=True,exist_ok=True)


def save(name,value):
    (OUT/name).write_text(json.dumps(value,indent=2,sort_keys=True)+'\n')


def main():
    fixture=json.loads((ROOT/'recovery_sources/psg/exact_sources.json').read_text())
    vs=('x','L','T','Y');P=parse(fixture['source'],vs);D=parse('Y^2-1',vs)
    packet=quadratic_reduce(P,'T',D);check_quadratic(packet,P,'T',D)
    save('source_elimination.json',packet)
    norm=Polynomial.from_packet(packet['norm'])
    compressed=power_coordinates(norm,('U','L','Z'),{'x':('U',2),'L':('L',1),'Y':('Z',2)})
    old=parse((ROOT/'recovery_sources/deep_gems/PSG_Q_U_L_Z.txt').read_text(),('U','L','Z'))
    assert compressed==old
    save('power_chart.json',{'original_norm':norm.packet(),'compressed':compressed.packet(),
         'matches_existing_PSGRecovery_source':True,'source_hashes':fixture['sources']})
    vs=('v','a','p');den=parse(fixture['field_denominator'],vs);num=parse(fixture['field_numerator'],vs)
    field=(den,den*den.variable('p'),num)
    factors=('v','a','2*a-1','v+4-8*a','a*v-2*a-2*p*v+1','2*a*v+4*a-4*p*v-v-2')
    certificates=[]
    for f in factors:
        h=parse(f,vs);c=darboux_certificate(h,field);assert check_darboux(c,h,field)
        certificates.append(c)
    save('six_darboux_identities.json',certificates)

    # Exact finite coefficient reconstruction; b7 first enters at order seven.
    p=Polynomial(('b3','b5','b7'));z=p.constant(0);one=p.constant(1)
    outer=[z,one,z,p.variable('b3'),z,p.variable('b5'),z,p.variable('b7')]
    inner=[z,one/2,one/3]+[z]*5
    profile=pushforward_profile(outer,inner,7)
    assert all(row['b7']['independent'] for row in profile['dependencies'][:7])
    assert Polynomial.from_packet(profile['coefficients'][7]).derivative('b7')==one/128
    save('triangular_jet.json',profile)

    # Differential constraints can be algebraic consequences, not new equations.
    p=Polynomial(('x','y'));x,y=p.variable('x'),p.variable('y')
    F=x*x-y;G=y*y-1;target=(x+y)*F+(x*x+1)*G
    redundant=ideal_certificate(target,[F,G]);assert check_ideal(redundant,target,[F,G])
    save('redundancy.json',redundant)
    save('observable_fibres.json',{
        'determined':observable_fibre([[1,1,0],[0,0,1]],[3,7],[[2,2,1]]),
        'ambiguous':observable_fibre([[1,1,0],[0,0,1]],[3,7],[[1,0,0]]),
        'empty':observable_fibre([[1,1],[2,2]],[1,3],[[1,0]])})
    from math import factorial
    save('differential_model_spaces.json',{
        'exponential_first_order':differential_model_space([Q(1,factorial(k)) for k in range(10)],7,1,1),
        'linear_ansatz_excluded':differential_model_space([1,2,3,7,11,19,31,53],6,1,1),
        'rational_quadratic_ansatz':differential_model_space([1]*14,10,2,1)})

    rng=random.Random(20261009);quadratic_rows=[];fibre_checks=0
    for i in range(200):
        vs=('x','t');s=Polynomial(vs,[(tuple((rng.randrange(4),rng.randrange(9))),rng.randrange(-5,6)) for _ in range(12)])
        d=parse('x^2',vs) if i%2 else parse('x+4',vs)
        c=quadratic_reduce(s,'t',d);assert check_quadratic(c,s,'t',d)
        for value in range(-4,5):
            r=reconstruct_quadratic(c,s,'t',d,{'x':value})
            brute=[str(t) for t in range(-8,9) if Q(t*t)==d.evaluate([value,0]) and not s.evaluate([value,t])]
            assert r['roots']==brute;fibre_checks+=1
        quadratic_rows.append({'index':i,'source':s.packet(),'radicand':d.packet(),
            'certificate_sha256':hashlib.sha256(json.dumps(c,sort_keys=True).encode()).hexdigest()})
    save('quadratic_corpus.json',quadratic_rows)

    norm_rows=[];norm_points=0
    for D in (2,3,5,6,7,10):
        for m in (-4,-1,0,1,4):
            for a in (1,2,3):
                A=parse(f'{a}*x+1',('x','y'));B=parse('y',('x','y'))
                result=affine_norm_population(A,B,D,m,40,work_limit=65536)
                brute=[[x,y] for x in range(-140,141) for y in range(-40,41) if (a*x+1)**2-D*y*y==m]
                assert result['points']==brute
                norm_rows.append({'D':D,'norm':m,'scale':a,'offset':1,'cutoff':40,
                    'points':result['points'],'excluded_nonintegral_preimages':result['excluded_nonintegral_preimages']})
                norm_points+=len(brute)
    save('affine_norm_corpus.json',norm_rows)

    # Keep the original expression structure in literal Lean identities.
    lean=['import PerfectPower.PSGStructural','namespace PerfectPower.PSGStructuralPackets',
          'set_option maxHeartbeats 8000000\nset_option maxRecDepth 100000\nset_option linter.unusedVariables false']
    names=('source','A','B','C','D','norm')
    polynomials=(P,*(Polynomial.from_packet(packet[k]) for k in ('A','B','quotient','radicand','norm')))
    for name,p in zip(names,polynomials):
        lean.append(f'def {name} (x L T Y : ℚ) : ℚ := {p.expression()}')
    lean.append('theorem source_reduction (x L T Y : ℚ) : source x L T Y = A x L T Y + T*B x L T Y + (T^2-D x L T Y)*C x L T Y := by\n  dsimp [source,A,B,C,D]\n  ring')
    lean.append('theorem recovered_norm (x L T Y : ℚ) : norm x L T Y = (A x L T Y)^2-D x L T Y*(B x L T Y)^2 := by\n  dsimp [norm,A,B,D]\n  ring')
    lean.append('theorem original_source_sound (x L T Y : ℚ) (hp : source x L T Y=0) (ht : T^2-D x L T Y=0) : norm x L T Y=0 := by\n  rw [source_reduction] at hp\n  rw [recovered_norm]\n  exact PSGStructural.quadratic_elimination_sound _ _ _ _ _ hp ht')
    for i,(expression,c) in enumerate(zip(factors,certificates)):
        h=parse(expression,('v','a','p'));K=Polynomial.from_packet(c['cofactor'])
        lhs=[h.derivative(v).expression() for v in h.variables]
        lean.append(f'theorem darboux_{i} (v a p : ℚ) : ({lhs[0]})*({den.expression()})+({lhs[1]})*({den.expression()})*p+({lhs[2]})*({num.expression()})=({K.expression()})*({h.expression()}) := by ring')
    lean.append('end PerfectPower.PSGStructuralPackets')
    (ROOT/'PerfectPower/Generated/PSGStructuralPackets.lean').write_text('\n\n'.join(lean)+'\n')
    summary={'actual_source_terms':len(P.terms),'eliminated_norm_terms':len(norm.terms),
             'existing_source_match':True,'exact_Darboux_factors':6,'random_quadratic_sources':200,
             'independent_auxiliary_fibre_checks':fibre_checks,'affine_norm_equations':len(norm_rows),
             'independently_compared_original_norm_points':norm_points,'finite_jet_order':7,
             'b7_first_output_order':7,'b7_output_coefficient':'1/128',
             'Lean_status':'sources emitted; compilation must be recorded separately',
             'excluded_claims':['global transcendence','all-degree Darboux classification',
                                'infinite analytic continuation','generic compiler refinement']}
    save('summary.json',summary);print(json.dumps(summary,indent=2))


if __name__=='__main__':main()
