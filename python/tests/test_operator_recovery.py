import random
import unittest
from fractions import Fraction as Q
from perfectpower.exact_linear import (matrix,identity,multiply,apply,rank,kernel,inverse,
 fitting_decomposition,target_factor,task_section,intertwiner_space,context_profile,injective_coordinates)
from perfectpower.recurrence import Recurrence,from_generating_function
from perfectpower.recurrence_identity import companion,compare_recurrences,orbit_identity
from perfectpower.radical_arrows import ArrowElement,ONE,ZERO
from perfectpower.quotient_algebra import QuotientAlgebra

class LinearRecovery(unittest.TestCase):
    def test_fitting_nilpotent_and_stable_are_not_kernel(self):
        a=((0,1,0),(0,0,0),(0,0,2));r=fitting_decomposition(a)
        self.assertEqual((r['stabilization_index'],r['nilpotent_dimension'],r['stable_dimension']),(2,2,1))
        self.assertEqual(len(kernel(a)),1);self.assertFalse(r['kernel_free'])
        self.assertEqual(fitting_decomposition(identity(3))['stabilization_index'],0)
        self.assertEqual(fitting_decomposition(((0,0),(0,0)))['nilpotent_dimension'],2)

    def test_fitting_random_conjugates_replay(self):
        rng=random.Random(372)
        for n in range(2,7):
            for _ in range(8):
                b=[list(row) for row in identity(n)]
                for _ in range(8):
                    i,j=rng.sample(range(n),2);c=rng.choice([-2,-1,1,2]);b[i]=[x+c*y for x,y in zip(b[i],b[j])]
                a=[[Q(0)]*n for _ in range(n)];d=n//2
                for i in range(d-1):a[i][i+1]=Q(1)
                for i in range(d,n):a[i][i]=Q(i+1)
                conjugate=multiply(multiply(b,a),inverse(b));r=fitting_decomposition(conjugate)
                self.assertEqual(r['nilpotent_dimension'],d)
                self.assertEqual(r['stable_dimension'],n-d)
                p=r['nilpotent_projector'];v=identity(n)
                for _ in range(r['stabilization_index']):v=multiply(v,conjugate)
                self.assertFalse(any(x for row in multiply(v,p) for x in row))

    def test_target_factor_and_ambiguity(self):
        g=((1,1,0),(0,0,1));f=((2,2,3),)
        r=target_factor(g,f);self.assertEqual(multiply(r['decoder'],g),matrix(f))
        r=target_factor(g,((1,0,0),));v=r['invisible_vector']
        self.assertEqual(apply(g,v),(0,0));self.assertNotEqual(apply(((1,0,0),),v),(0,))

    def test_injective_sections_and_obstructions(self):
        f=((1,0,0),(0,0,0));g=((1,0,0,0),(0,0,0,0))
        r=task_section(f,g,injective=True);self.assertEqual(rank(r['lift']),3)
        self.assertEqual(multiply(g,r['lift']),matrix(f))
        self.assertEqual(task_section(f,((1,),(0,)),injective=True)['status'],'INJECTIVE_DIMENSION_OBSTRUCTION')
        r=task_section(((0,),(1,)),g);self.assertEqual(r['status'],'IMAGE_OBSTRUCTION')
        self.assertNotEqual(r['nonzero_pairing'],0)
        r=task_section(((1,),),((2,),));self.assertFalse(r['constructed_lift_integral'])
        self.assertEqual(r['lift'],((Q(1,2),),))
        # A rationally integral canonical lift flag is not integer solvability.
        r=task_section(((1,),),((2,3),));self.assertFalse(r['constructed_lift_integral'])

    def test_random_constructed_sections(self):
        rng=random.Random(915)
        for _ in range(35):
            g=tuple(tuple(rng.randrange(-3,4) for _ in range(4)) for _ in range(3))
            t=tuple(tuple(rng.randrange(-3,4) for _ in range(3)) for _ in range(4));f=multiply(g,t)
            r=task_section(f,g);self.assertEqual(multiply(g,r['lift']),f)
            if len(kernel(f))<=len(kernel(g)):
                r=task_section(f,g,injective=True);self.assertEqual(rank(r['lift']),3)

    def test_rank_equivalence_does_not_give_transport(self):
        a=((1,0),(0,2));b=((3,0),(0,4))
        self.assertEqual(context_profile({'one':a}),context_profile({'one':b}))
        self.assertEqual(intertwiner_space([a],[b])['dimension'],0)
        self.assertEqual(intertwiner_space([a],[a])['dimension'],2)
        # Individually each context allows Hom; simultaneous equations forbid it.
        self.assertEqual(intertwiner_space([identity(2),a],[identity(2),b])['dimension'],0)
        with self.assertRaises(ValueError):intertwiner_space([a],[b],variable_limit=3)
        with self.assertRaises(ValueError):context_profile({str(i):a for i in range(5)},subset_limit=30)

    def test_transport_conjugation_and_composition(self):
        a=((1,2),(0,3));s=((1,1),(0,1));b=multiply(multiply(s,a),inverse(s))
        basis=intertwiner_space([a],[b])['basis']
        self.assertEqual(len(basis),2)
        for t in basis:self.assertEqual(multiply(t,a),multiply(b,t))
        c=((2,1),(1,1));d=multiply(multiply(c,b),inverse(c))
        self.assertEqual(multiply(multiply(c,s),a),multiply(d,multiply(c,s)))

    def test_reject_inexact_entries(self):
        with self.assertRaises(ValueError):fitting_decomposition(((0.5,),))
        with self.assertRaises(ValueError):target_factor(((1,2),),((1,),))
        with self.assertRaises(ValueError):intertwiner_space([],[])

class RecurrenceIdentity(unittest.TestCase):
    def test_redundant_order_same_infinite_sequence(self):
        a=Recurrence((1,1),(0,1));b=Recurrence((0,1,1),(0,1,1))
        r=compare_recurrences(a,b);self.assertEqual(r['status'],'ZERO_FOR_ALL_NONNEGATIVE_INDICES')
        self.assertEqual(r['reachable_dimension'],2)
        a=Recurrence((1,1,0),(1,1,1));b=from_generating_function((1,1),(1,0,-1,-1))
        self.assertEqual(compare_recurrences(a,b)['status'],'ZERO_FOR_ALL_NONNEGATIVE_INDICES')

    def test_first_mismatch_and_zero_seed(self):
        a=Recurrence((1,1),(0,1));b=Recurrence((1,2),(0,1))
        r=compare_recurrences(a,b);self.assertEqual(r['first_index'],2)
        self.assertEqual(r['value'],-1)
        self.assertEqual(orbit_identity(identity(2),(0,0),(1,1))['reachable_dimension'],0)

    def test_closure_witness_and_random_independent_outputs(self):
        rng=random.Random(221)
        for n in range(1,6):
            for _ in range(15):
                a=tuple(tuple(rng.randrange(-2,3) for _ in range(n)) for _ in range(n))
                v=tuple(rng.randrange(-2,3) for _ in range(n));h=tuple(rng.randrange(-1,2) for _ in range(n))
                r=orbit_identity(a,v,h);vals=[];w=v
                for _ in range(2*n+5):vals.append(sum(x*y for x,y in zip(h,w)));w=apply(a,w)
                if any(vals):self.assertEqual(r['first_index'],next(i for i,x in enumerate(vals) if x))
                else:self.assertEqual(r['status'],'ZERO_FOR_ALL_NONNEGATIVE_INDICES')
                if r['status']=='ZERO_FOR_ALL_NONNEGATIVE_INDICES' and r['orbit_basis']:
                    basis=r['orbit_basis'];last=apply(a,basis[-1]);coeff=r['closure_coefficients']
                    self.assertEqual(last,tuple(sum(c*v[j] for c,v in zip(coeff,basis)) for j in range(n)))

class RadicalAlgebra(unittest.TestCase):
    def test_associativity_regular_representation_and_inverse(self):
        rng=random.Random(897)
        for _ in range(60):
            elems=[ArrowElement(tuple(rng.choice([-2,-1,1,2]) for _ in range(3)),tuple(rng.randrange(-3,4) for _ in range(5))) for _ in range(3)]
            a,b,c=elems;self.assertEqual((a*b)*c,a*(b*c))
            self.assertEqual(a*a.inverse(),ONE);self.assertEqual(a.inverse()*a,ONE)
            self.assertEqual(multiply(a.regular_matrix(),b.regular_matrix()),(a*b).regular_matrix())
            self.assertEqual(multiply(a.carrier_matrix(),b.carrier_matrix()),(a*b).carrier_matrix())
            x=ArrowElement((0,0,0),a.arrows);y=ArrowElement((0,0,0),b.arrows)
            self.assertEqual(x*y,ZERO)
        with self.assertRaises(ValueError):ArrowElement((1,0,1),(1,)*5).inverse()

    def test_recovered_cubic_models_have_zero_hom(self):
        a=QuotientAlgebra((1,-1,-2,1)).element((0,1)).matrix()
        b=QuotientAlgebra((-1,5,-4,1)).element((0,1)).matrix()
        self.assertEqual(rank(a),3);self.assertEqual(rank(b),3)
        self.assertEqual(intertwiner_space([a],[b])['dimension'],0)
        self.assertEqual(intertwiner_space([a],[a])['dimension'],3)

class NormOperatorIntegration(unittest.TestCase):
    def test_unique_integral_coordinates_and_plane_obstruction(self):
        g=((2,0),(0,3),(0,0))
        self.assertEqual(injective_coordinates(g,(4,9,0))['coordinates'],(2,3))
        self.assertEqual(injective_coordinates(g,(1,9,0))['status'],'NONINTEGRAL_COORDINATES')
        self.assertEqual(injective_coordinates(g,(4,9,1))['status'],'IMAGE_OBSTRUCTION')
        with self.assertRaises(ValueError):injective_coordinates(((1,1),),(2,))

    def test_actual_seven_field_packets_and_signed_box(self):
        import json
        from pathlib import Path
        from perfectpower.norm_operator_replay import field_operator_replay
        packet=json.loads((Path(__file__).resolve().parents[2]/'receipts/field756_bound.json').read_text())
        small=field_operator_replay(packet,radius=1);large=field_operator_replay(packet,radius=3)
        self.assertEqual(len(large['classes']),7)
        self.assertEqual(large['unit_norms'],[-1,-1])
        self.assertEqual(large['simultaneous_unit_centralizer']['dimension'],3)
        self.assertFalse(large['external_height_bound_reproved'])
        for a,b in zip(small['classes'],large['classes']):
            self.assertLessEqual({tuple(x['point']) for x in a['points']},{tuple(x['point']) for x in b['points']})
            self.assertEqual(b['trials'],b['wrong_norm']+b['outside_rational_plane']+b['nonintegral_coordinates']+sum(len(x['witnesses']) for x in b['points']))
            self.assertTrue(all(x['replayed'] for x in b['imported_points_replayed']))
            self.assertFalse(b['complete_thue_solution_set_claimed'])
            for x in b['points']:
                v,w=x['point'];self.assertEqual(sum(c*v**(3-i)*w**i for i,c in enumerate(b['form'])),b['M'])

    def test_corrupt_packet_is_rejected(self):
        import json,copy
        from pathlib import Path
        from perfectpower.norm_operator_replay import field_operator_replay
        packet=json.loads((Path(__file__).resolve().parents[2]/'receipts/field756_bound.json').read_text())
        bad=copy.deepcopy(packet);bad['classes'][0]['phi'][0]+=1
        with self.assertRaises(ValueError):field_operator_replay(bad,radius=0)
        bad=copy.deepcopy(packet);bad['classes'][0]['pari_thue'][0][0]+=1
        with self.assertRaises(ValueError):field_operator_replay(bad,radius=0)
        with self.assertRaises(ValueError):field_operator_replay(packet,radius=21)
        bad=copy.deepcopy(packet);bad['units'][0][0]=float(bad['units'][0][0])
        with self.assertRaises(ValueError):field_operator_replay(bad,radius=0)

if __name__=='__main__':unittest.main()
