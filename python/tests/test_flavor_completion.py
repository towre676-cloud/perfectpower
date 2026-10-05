import unittest
from fractions import Fraction as Q
from math import pi, sqrt
import numpy as np
from perfectpower import polyalg as P
from perfectpower.core import evaluate, mul
from perfectpower.flavor_completion import (
    selected_potential, exact_lock_family, remainder_record, scalar_counterterm,
    angular_curvature_polynomial, cyclic_operator_basis, supersymmetric_circuit,
    circuit_jacobian, circuit_spectrum, holomorphic_coefficient_extension, allowed_circuit_deformation, softened_circuit, soft_circuit_branches,
    angular_derivatives, circuit_field_tensors, real_scalar_mass_matrix, circuit_loop, circuit_full_loop_value, driver_quantum_hessian, circuit_quantum_minimum, scalar_loop, scalar_loop_minimum, joint_tree,
    joint_loop, joint_loop_minimum, yukawa_operator_basis, triangular_yukawas,
    ckm_from_yukawas, physical_chart, matched_texture, sm_one_loop, sm_running_example)
from perfectpower.cyclotomic_vacuum import real_cyclotomic_polynomial, cyclotomic_polynomial, certify_global_minimum


class ExactCompletion(unittest.TestCase):
    def test_lock_global_winner_and_constraints(self):
        for l in (Q(0),Q(1,100),Q(1)):
            self.assertTrue(exact_lock_family(l)['stationarity']['zero'])
        # Independently compare all stationary roots of one extended potential.
        r=certify_global_minimum(selected_potential(Q(1,100)),bits=40)
        self.assertIsNotNone(r['winner_index'])
        a,b=map(Q,r['critical_points'][r['winner_index']]['x_interval'])
        self.assertTrue(Q(4,5)<a<b<Q(9,10))

    def test_scalar_divergence_breaks_at_every_carrier_root(self):
        r=scalar_counterterm()['valley_torque_remainder']
        self.assertFalse(r['zero']); self.assertEqual(r['common_root_degree'],0)
        p=real_cyclotomic_polynomial(60)
        # A Bezout identity independently establishes nonvanishing at all roots.
        witness=scalar_counterterm()['bezout_witness']
        g,a,b=(P.poly(map(Q,witness[k])) for k in ('gcd','carrier_multiplier','remainder_multiplier'))
        self.assertEqual(P.add(mul(a,p),mul(b,P.poly(map(Q,r['coefficients'])))),g)
        self.assertEqual(P.degree(g),0)
        self.assertFalse(scalar_counterterm(kappa=Q(1,10))['valley_torque_remainder']['zero'])

    def test_exact_curvature_matches_trigonometric_derivative(self):
        h=angular_curvature_polynomial(selected_potential())
        for theta in (.2,.8,1.1,2.4):
            x=2*np.cos(theta)
            self.assertAlmostEqual(float(evaluate(h,x)),angular_derivatives(theta)[2],places=8)

    def test_joint_trace_matches_actual_mass_matrix(self):
        r=scalar_counterterm(kappa=Q(1,10),f=Q(2),g=Q(3))
        t=P.poly(map(Q,r['trace_mass_fourth_polynomial']))
        for x in (Q(4,5),Q(1),Q(3,2)):
            theta=np.arccos(float(x)/2)
            c=1-2*np.cos(12*theta)
            h=joint_tree(theta,c,.1)[2]
            metric=np.diag([.5,1/3])
            m=metric@h@metric
            expected=float(np.trace(m@m))
            self.assertLess(abs(float(evaluate(t,x))-expected),1e-8)

    def test_operator_basis_independent_monomial_count(self):
        r=cyclic_operator_basis()
        expected=[(a,b) for a in range(13) for b in range(a+1) if 1<=a+b<=12]
        self.assertEqual({(x['z_power'],x['conjugate_power']) for x in r['rows']},set(expected))
        self.assertEqual(r['dangerous_count'],42)
        for n in range(2,61):
            self.assertFalse(cyclic_operator_basis(rotation_order=n)['target_support_allowed'])

    def test_cubic_circuit_elimination_and_complete_basis(self):
        r=supersymmetric_circuit(); phi=cyclotomic_polynomial(60)
        self.assertEqual(len(r['fields']),32); self.assertEqual(len(r['vacua']),16)
        self.assertEqual(r['chosen_term_count'],37)
        self.assertEqual(r['allowed_superpotential_count'],16*(1+16+136))
        self.assertEqual(len({(x['driver'],tuple(x['neutral_fields'])) for x in r['allowed_superpotential']}),2448)
        allowed={(x['driver'],tuple(x['neutral_fields'])) for x in r['allowed_superpotential']}
        reduced={}
        for term in r['superpotential_terms']:
            driver=term['fields'][0]; variables=term['fields'][1:]
            self.assertIn((driver,tuple(sorted(variables))),{(d,tuple(sorted(v))) for d,v in allowed})
            power=sum(int(z[1:]) for z in variables)
            monomial=P.poly([0]*power+[term['coefficient']])
            reduced[driver]=P.add(reduced.get(driver,P.ZERO),monomial)
            self.assertEqual(term['M_power']+len(term['fields']),3)
        for driver,polynomial in reduced.items():
            self.assertTrue(P.is_zero(polynomial) if driver!='Dstar' else polynomial==phi)
        self.assertTrue(r['simple_roots'])

    def test_circuit_mass_pairing_and_jacobian(self):
        r=circuit_spectrum()
        for row in r['rows']:
            self.assertGreater(min(row['mass_squared_over_M_squared']),0)
            self.assertLess(row['F_residual'],1e-12)
            self.assertAlmostEqual(row['jacobian_determinant_over_Phi_prime'][0],-1,places=10)
            self.assertLess(abs(row['jacobian_determinant_over_Phi_prime'][1]),1e-10)
            self.assertEqual(row['supertrace_M_fourth'],0)
        # Full holomorphic W Hessian has each J singular value twice.
        j=circuit_jacobian(np.exp(11j*pi/30))
        full=np.block([[np.zeros_like(j),j.T],[j,np.zeros_like(j)]])
        np.testing.assert_allclose(np.sort(np.linalg.svd(full,compute_uv=False)),
                                   np.sort(np.repeat(np.linalg.svd(j,compute_uv=False),2)),rtol=1e-11)

    def test_allowed_tadpole_changes_initialized_vacuum(self):
        r=allowed_circuit_deformation(1e-4)
        self.assertNotAlmostEqual(r['phase_degrees'],66,places=7)
        self.assertNotAlmostEqual(r['radius'],1,places=7)
        self.assertAlmostEqual(r['phase_degrees']-66,r['linear_phase_displacement_degrees'],delta=1e-5)

    def test_holomorphic_golden_extension(self):
        r=holomorphic_coefficient_extension()
        self.assertEqual(r['golden_identity_remainder'],['0'])
        self.assertEqual(r['extended_chiral_field_count'],34)
        c=P.poly(map(Q,r['coefficient_polynomial']))
        z=np.exp(11j*pi/30)
        value=sum(float(a)*z**n for n,a in enumerate(c))
        self.assertAlmostEqual(value.real,(3-sqrt(5))/2,places=12)
        self.assertLess(abs(value.imag),1e-12)
        for term in r['additional_superpotential_terms']:
            self.assertEqual(term['M_power']+len(term['fields']),3)


class NumericalCompletion(unittest.TestCase):
    def test_full_circuit_loop_susy_cancellation_and_mass_modes(self):
        z=np.exp(11j*pi/30); q=np.array([z**n for n in range(1,17)])
        q=np.r_[q,2-q[3]-q[5]+q[13]]
        v,g,m,av,bv,mu=circuit_loop(q)
        self.assertEqual(len(av),17); self.assertEqual(len(bv),34)
        self.assertLess(abs(v),1e-12); self.assertLess(max(abs(g)),1e-12)
        np.testing.assert_allclose(np.sort(bv),np.sort(np.repeat(av,2)),rtol=1e-10)

    def test_full_circuit_loop_gradient_independent_energy_differences(self):
        z=np.exp(11j*pi/30)
        _,_,q,_=softened_circuit(z,1e-3)
        q=np.r_[q,2-q[3]-q[5]+q[13]]
        value,g,_,_,_,mu=circuit_loop(q,.3)
        step=2e-5
        for i in (0,3,11,16,17,28):
            d=np.zeros(17,complex); d[i%17]=step if i<17 else 1j*step
            finite=(circuit_loop(q+d,.3,mu)[0]-circuit_loop(q-d,.3,mu)[0])/(2*step)
            self.assertAlmostEqual(g[i],finite,delta=2e-10)

    def test_full_circuit_quantum_local_continuation(self):
        r=circuit_quantum_minimum(1e-4,.3)
        self.assertEqual(r['lowest_leading_branch_root_powers'],[11,49])
        self.assertTrue(r['all_tree_scalar_masses_positive_at_corrected_point'])
        self.assertGreater(r['corrected_Z_sector_hessian_minimum'],0)
        self.assertGreater(r['corrected_driver_hessian_minimum'],0)
        self.assertLess(r['tree_plus_one_loop_stationarity_residual'],1e-8)
        self.assertLess(abs(r['quantum_phase_displacement_degrees']),1e-4)
        self.assertEqual((r['real_scalar_modes'],r['Weyl_fermion_modes']),(68,34))

    def test_full_68_mode_expression_and_driver_hessian(self):
        z=np.exp(11j*pi/30)
        _,_,q,_=softened_circuit(z,1e-4)
        q=np.r_[q,2-q[3]-q[5]+q[13]]
        value,_,_,_,_,mu=circuit_loop(q,.3)
        self.assertAlmostEqual(circuit_full_loop_value(q,np.zeros(17),.3,mu),value,delta=1e-15)
        a,_=driver_quantum_hessian(q,.3,mu,2e-4)
        b,_=driver_quantum_hessian(q,.3,mu,4e-4)
        np.testing.assert_allclose(a,b,rtol=2e-4,atol=2e-7)
        self.assertGreater(np.linalg.eigvalsh(a).min(),0)

    def test_auxiliary_elimination_and_envelope_gradient(self):
        z=np.exp(11j*pi/30)+.001; eps=1e-4; step=1e-6
        energy,g,fields,residual=softened_circuit(z,eps)
        self.assertLess(residual,1e-12)
        for i,direction in enumerate((1,1j)):
            left=softened_circuit(z-step*direction,eps)[0]
            right=softened_circuit(z+step*direction,eps)[0]
            self.assertAlmostEqual(g[i],(right-left)/(2*step),delta=1e-9)

    def test_soft_selector_retains_cp_pairs_but_moves_vacua(self):
        r=soft_circuit_branches(1e-4)
        self.assertEqual(r['lowest_continued_branch_root_powers'],[11,49])
        rows={x['root_power']:x for x in r['branches']}
        for k,row in rows.items():
            self.assertTrue(row['positive_reduced_hessian'])
            self.assertAlmostEqual(row['energy_over_M_fourth'],rows[60-k]['energy_over_M_fourth'],places=11)
        self.assertGreater(abs(rows[11]['phase_displacement_degrees']),1e-7)
        self.assertNotAlmostEqual(rows[11]['radius'],1,places=7)
        self.assertGreater(abs(rows[11]['coefficient_from_auxiliary_operator']-rows[11]['coefficient_from_angle']),1e-6)

    def test_scalar_gradient_and_curvature_against_finite_differences(self):
        theta=11*pi/30+.002; e=2e-6
        a=scalar_loop(theta,.1)
        left=scalar_loop(theta-e,.1); right=scalar_loop(theta+e,.1)
        self.assertAlmostEqual(a[1],(right[0]-left[0])/(2*e),delta=1e-9)
        self.assertAlmostEqual(a[2],(right[1]-left[1])/(2*e),delta=1e-8)

    def test_local_shift_and_small_parameter_scaling(self):
        a=scalar_loop_minimum(.03); b=scalar_loop_minimum(.06)
        self.assertLess(a['phase_degrees'],66)
        self.assertGreater(a['loop_corrected_angular_curvature'],0)
        self.assertAlmostEqual(b['actual_displacement_degrees']/a['actual_displacement_degrees'],16,delta=.01)
        self.assertLess(abs(a['actual_displacement_degrees']-a['linear_displacement_degrees']),1e-8)

    def test_joint_tree_hessian_third_derivatives(self):
        q=np.array([11*pi/30+.001,.38]); e=1e-6
        v,g,h,dh=joint_tree(*q,.01)
        for i in range(2):
            left=joint_tree(*(q-e*np.eye(2)[i]),.01)
            right=joint_tree(*(q+e*np.eye(2)[i]),.01)
            np.testing.assert_allclose(h[:,i],(right[1]-left[1])/(2*e),rtol=1e-7,atol=1e-8)
            np.testing.assert_allclose(dh[i],(right[2]-left[2])/(2*e),rtol=1e-7,atol=1e-7)

    def test_joint_loop_gradient_and_both_field_minimum(self):
        q=np.array([11*pi/30,.381966011250105]); e=1e-6
        value,g,m,mu=joint_loop(*q,.03,.01)
        for i in range(2):
            left=joint_loop(*(q-e*np.eye(2)[i]),.03,.01,mu_squared=mu)[0]
            right=joint_loop(*(q+e*np.eye(2)[i]),.03,.01,mu_squared=mu)[0]
            self.assertAlmostEqual(g[i],(right-left)/(2*e),delta=1e-9)
        r=joint_loop_minimum(.03,.01)
        self.assertTrue(r['positive_local_hessian']); self.assertLess(r['stationarity_residual'],1e-10)
        self.assertGreater(abs(r['departure_from_tree_coefficient_portal']),1e-7)

    def test_complete_yukawa_charges_and_independent_coefficients(self):
        r=yukawa_operator_basis()
        self.assertEqual(r['count'],6460)
        for op in r['operators']:
            qi=np.array(r['charges']['Q'][op['row']-1]); qj=np.array(r['charges']['u_c_and_d_c'][op['column']-1])
            np.testing.assert_array_equal(qi+qj-np.array([op['A_power'],op['B_power']]),[0,0])
            self.assertLessEqual(op['superpotential_field_degree'],6)
        self.assertFalse(r['golden_relation_enforced'])

    def test_yukawa_diagonalization_and_anchor_preserving_counterexample(self):
        yu,yd=triangular_yukawas(.23,.041,.38,11*pi/30)
        v,ss=ckm_from_yukawas(yu,yd)
        self.assertLess(np.max(abs(v@v.conj().T-np.eye(3))),1e-12)
        np.testing.assert_allclose(np.sort(np.linalg.svd(yd,compute_uv=False)),ss[1],rtol=1e-10)
        a=matched_texture(.2,.22431,.0411); b=matched_texture(.6,.22431,.0411)
        for row in (a,b):
            self.assertLess(max(map(abs,row['anchor_residual'])),1e-10)
        self.assertGreater(b['observables']['Vub']/a['observables']['Vub'],2.9)

    def test_physical_chart_is_rephasing_invariant(self):
        from perfectpower.flavor_prediction import ckm_from_depth
        c=(3-sqrt(5))/2; v=ckm_from_depth(c,11*pi/30,.22431,.0411)
        phased=np.diag(np.exp(1j*np.array([.2,.7,1.4])))@v@np.diag(np.exp(1j*np.array([.3,.8,.9])))
        a,b=physical_chart(v),physical_chart(phased)
        for key in a:
            self.assertAlmostEqual(a[key],b[key],places=9)
        self.assertAlmostEqual(a['depth'],c,places=12)
        self.assertAlmostEqual(a['delta_degrees'],66,places=9)

    def test_sm_top_only_limit_and_basis_covariance(self):
        z=np.zeros((3,3),complex); y=z.copy(); y[2,2]=.9
        beta,bg=sm_one_loop(y,z,z,[0,0,1.1])
        self.assertAlmostEqual(beta[0][2,2].real,.9*(4.5*.9**2-8*1.1**2)/(16*pi*pi),places=12)
        yu,yd=triangular_yukawas(.23,.041,.38,1.1)
        q=np.array([[0,1,0],[1,0,0],[0,0,1]],complex)
        a,_=sm_one_loop(yu,yd,z,[.46,.65,1.17])
        b,_=sm_one_loop(q@yu,q@yd,z,[.46,.65,1.17])
        for i in (0,1):
            np.testing.assert_allclose(b[i],q@a[i],rtol=1e-12,atol=1e-14)

    def test_sm_running_initial_condition_and_relation_departure(self):
        r=sm_running_example(.22431,.0411)
        self.assertAlmostEqual(r['rows'][0]['observables']['depth'],(3-sqrt(5))/2,places=10)
        self.assertGreater(abs(r['rows'][-1]['phase_displacement_degrees']),1e-5)
        self.assertGreater(abs(r['rows'][-1]['relative_depth_change']),1e-5)

    def test_invalid_domains(self):
        with self.assertRaises(ValueError): selected_potential(-1)
        with self.assertRaises(ValueError): selected_potential(0,0)
        with self.assertRaises(ValueError): scalar_loop(1,0)
        with self.assertRaises(ValueError): scalar_counterterm(f=0)
        with self.assertRaises(ValueError): joint_loop(1,.4,.1,0)
        with self.assertRaises(ValueError): yukawa_operator_basis(4)


if __name__=='__main__':
    unittest.main()
