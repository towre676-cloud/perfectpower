import copy
import json
import random
import unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower.psg_polynomial import Polynomial,parse,power_coordinates
from perfectpower.psg_algebra import *
from perfectpower.psg_jets import compose,curvature_jet,schroder_residual,pushforward_profile,differential_model_space


class PSGStructuralTests(unittest.TestCase):
    def test_safe_parser_and_exact_division(self):
        for expression in ('__import__("os")','x[0]','x.foo','x**x','0.1*x','True','x/0'):
            with self.assertRaises((ValueError,ZeroDivisionError)):parse(expression,('x',))
        p=parse('(x+y)^4/3',('x','y'));q=parse('x+y',('x','y'))
        (quotient,),rem=p.divide([q]);self.assertFalse(rem);self.assertEqual(quotient*q,p)
        self.assertEqual(Polynomial.from_packet(p.packet()),p)
        self.assertEqual(p.evaluate([1,2]),27)

    def test_random_quadratic_source_and_complete_fibres(self):
        rng=random.Random(126)
        for _ in range(50):
            s=Polynomial(('x','t'),[(tuple((rng.randrange(3),rng.randrange(7))),rng.randrange(-4,5)) for j in range(10)])
            D=parse('x^2+1',s.variables);packet=quadratic_reduce(s,'t',D)
            self.assertTrue(check_quadratic(packet,s,'t',D))
            for x in range(-3,4):
                roots=reconstruct_quadratic(packet,s,'t',D,{'x':x})['roots']
                brute=[str(t) for t in range(-10,11) if t*t==x*x+1 and not s.evaluate([x,t])]
                self.assertEqual(roots,brute)

    def test_exceptional_and_divisibility_branches(self):
        vs=('x','y','z','t');s=parse('(t^2-x)*(1+y)+y*t+z',vs);D=parse('x',vs)
        p=quadratic_reduce(s,'t',D)
        for x,expected in ((4,['-2','2']),(0,['0']),(-1,[]),(2,[])):
            self.assertEqual(reconstruct_quadratic(p,s,'t',D,{'x':x,'y':0,'z':0})['roots'],expected)
        s=parse('2*t-1',('t',));D=parse('1/4',('t',));p=quadratic_reduce(s,'t',D)
        self.assertEqual(reconstruct_quadratic(p,s,'t',D,{},domain='rational')['roots'],['1/2'])
        self.assertEqual(reconstruct_quadratic(p,s,'t',D,{})['branch'],'integer_divisibility_obstruction')

    def test_tampering_and_source_binding(self):
        s=parse('x+t',('x','t'));D=parse('x^2',s.variables);p=quadratic_reduce(s,'t',D)
        for key in ('source','A','B','quotient','norm','source_multiplier','chamber_multiplier'):
            bad=copy.deepcopy(p);bad[key]=(Polynomial.from_packet(bad[key])+1).packet()
            with self.assertRaises(ValueError):check_quadratic(bad,s,'t',D)
        with self.assertRaises(ValueError):check_quadratic(p,s+1,'t',D)
        with self.assertRaises(ValueError):quadratic_reduce(s,'t',parse('t',s.variables))

    def test_actual_psg_source_and_six_invariants(self):
        root=Path(__file__).resolve().parents[2]
        source=json.loads((root/'recovery_sources/psg/exact_sources.json').read_text())
        vs=('x','L','T','Y');s=parse(source['source'],vs);D=parse('Y^2-1',vs)
        p=quadratic_reduce(s,'T',D);self.assertTrue(check_quadratic(p,s,'T',D))
        n=Polynomial.from_packet(p['norm']);self.assertEqual(len(n.terms),100)
        compressed=power_coordinates(n,('U','L','Z'),{'x':('U',2),'L':('L',1),'Y':('Z',2)})
        self.assertEqual(compressed,parse((root/'recovery_sources/deep_gems/PSG_Q_U_L_Z.txt').read_text(),('U','L','Z')))
        vs=('v','a','p');D=parse(source['field_denominator'],vs);N=parse(source['field_numerator'],vs)
        field=(D,D*D.variable('p'),N)
        for expression in ('v','a','2*a-1','v+4-8*a','a*v-2*a-2*p*v+1','2*a*v+4*a-4*p*v-v-2'):
            h=parse(expression,vs);packet=darboux_certificate(h,field)
            self.assertTrue(check_darboux(packet,h,field))
            bad=copy.deepcopy(packet);bad['cofactor']=(Polynomial.from_packet(bad['cofactor'])+1).packet()
            with self.assertRaises(ValueError):check_darboux(bad,h,field)

    def test_finite_linear_darboux_search_and_product(self):
        p=Polynomial(('x','y'));x,y=p.variable('x'),p.variable('y');field=(x,2*y)
        scan=linear_darboux_scan(field,1)
        self.assertEqual(scan['candidates'],12);self.assertEqual(len(scan['invariants']),2)
        h=x*x*y;packet=darboux_certificate(h,field)
        self.assertTrue(check_darboux(packet,h,field));self.assertEqual(Polynomial.from_packet(packet['cofactor']),p.constant(4))
        rejected=darboux_certificate(x+y,field);self.assertFalse(check_darboux(rejected,x+y,field))

    def test_ideal_redundancy_and_inconclusive_remainder(self):
        p=Polynomial(('x','y'));x,y=p.variable('x'),p.variable('y');g=(x*x-y,y*y-1)
        target=(x+y)*g[0]+(x*x+1)*g[1];packet=ideal_certificate(target,g)
        self.assertTrue(check_ideal(packet,target,g))
        bad=copy.deepcopy(packet);bad['multipliers'][0]=(Polynomial.from_packet(bad['multipliers'][0])+1).packet()
        with self.assertRaises(ValueError):check_ideal(bad,target,g)
        # Ordered division does not decide nonmembership for a non-Groebner list.
        target=y;g=(x*y-1,x*y-y-1);packet=ideal_certificate(target,g)
        self.assertFalse(packet['redundant']);self.assertFalse(check_ideal(packet,target,g))
        self.assertEqual(g[0]-g[1],target)

    def test_dependency_witnesses_not_samples(self):
        p=parse('(x-1)*(x-2)*(x-3)*(x-4)*y',('x','y','z'))
        profile=dependency_profile([p])[0]
        self.assertTrue(profile['z']['independent'])
        for name in ('x','y'):
            w=profile[name];self.assertNotEqual(w['first_value'],w['second_value'])
            self.assertEqual(p.evaluate(w['first']),Q(w['first_value']))
            self.assertEqual(p.evaluate(w['second']),Q(w['second_value']))
            self.assertEqual({v for v in p.variables if w['first'][v]!=w['second'][v]},{name})

    def test_observable_fibres_with_actual_ambiguity(self):
        A=[[1,1,0],[0,0,1]];values=[3,7]
        determined=observable_fibre(A,values,[[2,2,1]])
        self.assertEqual(determined['status'],'determined');self.assertEqual(determined['target_seed'],['13'])
        result=observable_fibre(A,values,[[1,0,0]])
        self.assertEqual(result['status'],'underdetermined')
        w=result['ambiguity_witness']
        for seed in (w['first'],w['second']):self.assertEqual(E.apply(E.matrix(A),list(map(Q,seed))),tuple(map(Q,values)))
        self.assertNotEqual(w['first_target'],w['second_target'])
        self.assertEqual(result['minimum_additional_scalar_observations'],1)
        result=observable_fibre([[1,1],[2,2]],[1,3],[[1,0]])
        self.assertEqual(result['status'],'empty')

    def test_exact_differential_model_space(self):
        from math import factorial
        exponential=[Q(1,factorial(k)) for k in range(10)]
        result=differential_model_space(exponential,7,1,1)
        self.assertEqual(result['nullity'],1)
        matrix=E.matrix([[Q(c) for c in row] for row in result['matrix']])
        for vector in result['basis']:self.assertFalse(any(E.apply(matrix,list(map(Q,vector)))))
        result=differential_model_space([1,2,3,7,11,19,31,53],6,1,1)
        self.assertEqual(result['status'],'bounded_model_excluded')
        with self.assertRaises(ValueError):differential_model_space([1,2,3],3,1,1)

    def test_finite_jets_and_resonant_free_mode(self):
        p=Polynomial(('b3','b5','b7'));z=p.constant(0);one=p.constant(1)
        outer=[z,one,z,p.variable('b3'),z,p.variable('b5'),z,p.variable('b7')]
        inner=[z,one/2,one/3]+[z]*5
        profile=pushforward_profile(outer,inner,7)
        for row in profile['dependencies'][:7]:self.assertTrue(row['b7']['independent'])
        self.assertFalse(profile['dependencies'][7]['b7']['independent'])
        self.assertEqual(compose(outer,inner,7)[7].derivative('b7'),one/128)
        flip=[z,-one]+[z]*6
        self.assertTrue(all(not q for q in schroder_residual(flip,outer,-1,7)))
        self.assertEqual(curvature_jet([0,1,Q(1,2),Q(1,6),Q(1,24)],2)['coefficients'],['1','0','0'])
        with self.assertRaises(ValueError):curvature_jet([0,1,2],1)
        with self.assertRaises(ValueError):compose(outer[:5],inner,7)

    def test_affine_pell_pullback_against_original_equation(self):
        vs=('x','y')
        for a in (1,2,3):
            A=parse(f'{a}*x+1',vs);B=parse('y',vs)
            result=affine_norm_population(A,B,2,-1,30)
            brute=[[x,y] for x in range(-100,101) for y in range(-30,31) if (a*x+1)**2-2*y*y==-1]
            self.assertEqual(result['points'],brute)
        with self.assertRaises(ValueError):affine_norm_population(parse('x',vs),parse('2*x',vs),2,1,10)


if __name__=='__main__':unittest.main()
