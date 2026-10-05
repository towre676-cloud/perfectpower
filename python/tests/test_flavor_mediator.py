import unittest
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import pi, sqrt
import numpy as np
from perfectpower.flavor_mediator import (
    abelian_circuit_audit, mediator_operator_audit, alignment_basis,
    inverse_sqrt, canonical_mediator, full_fermion_mass, mixing_record,
    assignment_certificate, degree_eight_example, golden_squared_relation,
    adjoint_background, matched_adjoint)
from perfectpower.flavor_prediction import ckm_from_depth


class ExactMediator(unittest.TestCase):
    def test_phase_charge_obstruction_at_arbitrary_orders(self):
        r=abelian_circuit_audit(240)
        self.assertEqual(r['constraint_gcd'],2)
        for row in r['cyclic_checks']:
            self.assertEqual(row['allowed_Z1_charges'],[0] if row['order']%2 else [0,row['order']//2])
            self.assertEqual(row['T_charge'],0)

    def test_complete_mediator_operator_types_and_counts(self):
        for n in (0,1,17):
            r=mediator_operator_audit(n)
            actual={tuple(sorted(x['fields'])) for x in r['operators']}
            expected=set()
            for f,H in (('u','H'),('d','H_conjugate')):
                expected.add(tuple(sorted(['X_'+f,'Xc_'+f])))
                expected.add(tuple(sorted(['Q','Xc_'+f,H])))
                for i in range(1,4):expected.add(tuple(sorted(['X_'+f,f+str(i)+'c','F_'+f+str(i)])))
                for k in range(1,min(n,16)+1):
                    for name in ('Z'+str(k),'Z'+str(k)+'_conjugate'):
                        expected.add(tuple(sorted(['X_'+f,'Xc_'+f,name])))
                if n==17:
                    for name in ('T','T_conjugate'):expected.add(tuple(sorted(['X_'+f,'Xc_'+f,name])))
            self.assertEqual(actual,expected)
            self.assertEqual(r['count'],10+4*n)
        self.assertEqual(mediator_operator_audit(adjoint=True)['count'],82)

    def test_gram_invariant_counts_against_permutations(self):
        r=alignment_basis()
        self.assertEqual(r['counts'],{'2':6,'4':36,'6':166})
        # Every balanced product of up to three Gram edges decomposes into cycles.
        # Distinct cycles of length 3 are conjugate under reversal; CP retains Re.
        cycles={tuple(sorted(p)) for p in permutations(range(6),3)}
        self.assertEqual(len(cycles),20)
        self.assertEqual(sum(x['kind']=='real_Gram_triangle' for x in r['operators']),20)
        self.assertEqual(r['first_available_nonlinear_orientation_degree'],8)

    def test_assignment_dual_certificate_exact(self):
        rng=np.random.default_rng(2010)
        for _ in range(80):
            c=[[Q(int(x),7) for x in row] for row in rng.integers(-20,21,(3,3))]
            r=assignment_certificate(c)
            optimum=min(sum(c[i][p[i]] for i in range(3)) for p in permutations(range(3)))
            self.assertEqual(Q(r['optimum']),optimum)
            alpha=list(map(Q,r['row_dual']));beta=list(map(Q,r['column_dual']))
            self.assertEqual(sum(alpha)+sum(beta),optimum)
            for i in range(3):
                for j in range(3):self.assertGreaterEqual(c[i][j]-alpha[i]-beta[j],0)

    def test_degenerate_alignment_does_not_exclude_mixed_flat_directions(self):
        r=assignment_certificate([[1]*3 for _ in range(3)])
        self.assertEqual(len(r['winning_permutations']),6)
        v=np.exp(2j*pi*np.outer(np.arange(3),np.arange(3))/3)/sqrt(3)
        self.assertAlmostEqual(float(np.sum(abs(v)**2)),float(Q(r['optimum'])))

    def test_exact_squared_golden_polynomial(self):
        terms=golden_squared_relation()['coefficients']
        # Compare sparse polynomial with direct expression at exact rational inputs.
        for p,q,r in ((Q(1,20),Q(1,500),Q(1,100000)),(Q(1,3),Q(1,5),Q(1,7))):
            value=sum(Q(t['coefficient'])*p**t['powers'][0]*q**t['powers'][1]*r**t['powers'][2] for t in terms)
            a=r*(1-r)**2
            self.assertEqual(value,a*a-7*p*q*a+p*p*q*q)


class NumericalMediator(unittest.TestCase):
    def setUp(self):
        self.rng=np.random.default_rng(3901)

    def unitary(self):
        z=self.rng.normal(size=(3,3))+1j*self.rng.normal(size=(3,3))
        return np.linalg.qr(z)[0]

    def test_matching_null_frame_and_yukawa_projection(self):
        m=np.diag([1.,1.3,1.7])+.1*self.rng.normal(size=(3,3))
        l=.4*(self.rng.normal(size=(3,3))+1j*self.rng.normal(size=(3,3)))
        r=canonical_mediator(m,l,.7);n=r['light_right_frame']
        np.testing.assert_allclose(n.conj().T@n,np.eye(3),atol=2e-15)
        np.testing.assert_allclose(r['heavy_row']@n,0,atol=2e-15)
        np.testing.assert_allclose(np.hstack((np.zeros((3,3)),.7*np.eye(3)))@n,r['Y'],atol=2e-15)

    def test_effective_yukawas_match_independent_full_mass_singular_values(self):
        m=np.eye(3)+.15*self.rng.normal(size=(3,3));l=self.unitary()@np.diag([.03,.12,.4])
        h=.6;vev=1e-5;r=canonical_mediator(m,l,h)
        full=full_fermion_mass(m,l,vev,h)
        light=np.linalg.svd(full,compute_uv=False)[-3:]/vev
        np.testing.assert_allclose(light,np.linalg.svd(r['Y'],compute_uv=False),rtol=1e-8,atol=1e-10)

    def test_flavor_covariance_with_noncommuting_mediator_mass(self):
        u=self.unitary();m=np.eye(3)+.15*self.rng.normal(size=(3,3))
        l=self.rng.normal(size=(3,3))*.2
        a=canonical_mediator(m,l);b=canonical_mediator(u@m@u.conj().T,u@l)
        np.testing.assert_allclose(b['Y'],u@a['Y'],atol=1e-14)
        np.testing.assert_allclose(b['right_metric'],a['right_metric'],atol=1e-14)

    def test_column_phase_cannot_transmit_cp(self):
        y=self.rng.normal(size=(3,3))+1j*self.rng.normal(size=(3,3))
        yp=y@np.diag(np.exp(1j*np.array([.2,1.1,2.3])))
        np.testing.assert_allclose(y@y.conj().T,yp@yp.conj().T,atol=2e-15)

    def test_universal_mass_preserves_nonorthogonal_column_eigenvectors(self):
        lu=self.rng.normal(size=(3,3))*.2
        ld=.3*(self.rng.normal(size=(3,3))+1j*self.rng.normal(size=(3,3)))
        reference=None
        for mu,md in ((.3,1.),(1+1j,.7-.3j),(3.,2.)):
            row=mixing_record(canonical_mediator(mu*np.eye(3),lu)['Y'],canonical_mediator(md*np.eye(3),ld)['Y'])
            if reference is not None:
                for k in ('Vus','Vcb','Vub','depth','J','delta_degrees'):
                    self.assertAlmostEqual(row[k],reference[k],places=10)
            reference=row

    def test_golden_squared_relation_both_branches(self):
        for c in ((3-sqrt(5))/2,(3+sqrt(5))/2):
            # Direct standard-angle construction avoids the small chart's C<=2 limit.
            s12,s23=.2,.04;w=c*s12*s23;c13=sqrt(1-w*w)
            p=(s12*c13)**2;q=(s23*c13)**2;r=w*w
            a=r*(1-r)**2
            self.assertLess(abs(a*a-7*p*q*a+(p*q)**2)/(p*q)**2,2e-13)

    def test_golden_frame_transfer_is_independent_of_masses_and_universal_phases(self):
        c=(3-sqrt(5))/2;v=ckm_from_depth(c,11*pi/30,.22431,.0411)
        for mu,md in ((.7,1.2),(1+1j,2-.3j),(3.,.4)):
            yu=canonical_mediator(mu*np.eye(3),np.diag([.01,.1,.8]))['Y']
            yd=canonical_mediator(md*np.eye(3),v@np.diag([.02,.2,.6]))['Y']
            r=mixing_record(yu,yd)
            self.assertAlmostEqual(r['depth'],c,places=10)
            self.assertAlmostEqual(r['delta_degrees'],66,places=8)
            self.assertAlmostEqual(r['Vus'],.22431,places=12)
            self.assertAlmostEqual(r['Vcb'],.0411,places=12)

    def test_full_mass_light_charged_current_matches_matching_limit(self):
        v=ckm_from_depth((3-sqrt(5))/2,11*pi/30,.22431,.0411);vev=1e-5
        frames=[]
        for l,m in ((np.diag([.02,.12,.6]),1.),(v@np.diag([.03,.15,.4]),1.5)):
            left,_,_=np.linalg.svd(full_fermion_mass(m*np.eye(3),l,vev))
            frames.append(left[:3,[-1,-2,-3]])
        light=frames[0].conj().T@frames[1]
        np.testing.assert_allclose(abs(light),abs(v),atol=2e-9)
        self.assertLess(float(np.max(abs(light@light.conj().T-np.eye(3)))),1e-8)

    def test_gram_triangles_vanish_on_orthogonal_frames(self):
        f=np.column_stack((np.eye(3),self.unitary()))
        g=f.conj().T@f
        for i,j,k in combinations(range(6),3):
            self.assertLess(abs(g[i,j]*g[j,k]*g[k,i]),1e-14)

    def test_assignment_bound_for_nontrivial_unitaries(self):
        cost=np.array([[0,3,6],[5,0,2],[4,7,0]])
        r=assignment_certificate(cost);opt=float(Q(r['optimum']))
        a=np.array(list(map(float,r['row_dual'])));b=np.array(list(map(float,r['column_dual'])))
        reduced=cost-a[:,None]-b[None,:]
        for _ in range(40):
            prob=abs(self.unitary())**2;energy=float(np.sum(cost*prob))
            self.assertGreaterEqual(energy,opt-1e-12)
            self.assertAlmostEqual(energy,opt+float(np.sum(reduced*prob)),places=11)

    def test_degree_eight_nonzero_cp_capability_example(self):
        r=degree_eight_example();b=np.array(r['B'])
        self.assertAlmostEqual(float(np.sum(b*b)),1,places=13)
        self.assertAlmostEqual(abs(r['J']),1/(6*sqrt(3)),places=13)
        for _ in range(30):self.assertGreaterEqual(float(np.sum(abs(self.unitary())**4)),1-1e-12)

    def test_adjoint_couplings_fail_to_enforce_golden_even_after_anchor_matching(self):
        a=matched_adjoint(0.,.5,.22431,.0411);b=matched_adjoint(.1,.5,.22431,.0411)
        for row in (a,b):
            self.assertLess(max(map(abs,row['anchor_residual'])),1e-9)
            self.assertGreater(abs(row['observables']['depth']-(3-sqrt(5))/2),.1)
        self.assertGreater(abs(a['observables']['depth']-b['observables']['depth']),.1)

    def test_cp_conjugate_adjoint_reverses_j_and_retains_magnitudes(self):
        p=matched_adjoint(.1,1.,.22431,.0411,phase=11*pi/30)
        m=matched_adjoint(.1,1.,.22431,.0411,phase=-11*pi/30)
        for k in ('Vus','Vcb','Vub','depth'):self.assertAlmostEqual(p['observables'][k],m['observables'][k],places=11)
        self.assertAlmostEqual(p['observables']['J'],-m['observables']['J'],places=11)

    def test_reject_singular_mass_and_nonpositive_metric(self):
        with self.assertRaises(ValueError):canonical_mediator(np.zeros((3,3)),np.eye(3))
        with self.assertRaises(ValueError):inverse_sqrt(np.diag([1,1,0]))


if __name__=='__main__':unittest.main()
