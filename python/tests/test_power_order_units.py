import copy,json,unittest
from fractions import Fraction as Q
from pathlib import Path
from perfectpower import polyalg as P
from perfectpower.cubic_norm_transport import algebra_norm
from perfectpower.elliptic_two_descent import solve
from perfectpower.power_order_units import (power_order_unit_lattice,lattice_contains,
    compile_binary_source,encode_binary_source,recover_binary_source,unit_orbit_source)
from perfectpower.divisor_square import WorkLimit

ROOT=Path(__file__).resolve().parents[2]


class PowerOrderUnits(unittest.TestCase):
    @classmethod
    def setUpClass(cls):cls.orders=json.loads((ROOT/'receipts/power_order_units.json').read_text())['orders']

    def test_power_order_units_and_inverses_in_original_polynomial(self):
        for c in self.orders:
            f=P.poly(c['polynomial'])
            for u,v in zip(c['power_order_units'],c['power_order_unit_inverses']):
                self.assertEqual(abs(algebra_norm(f,u)),1)
                self.assertEqual(P.divmod_poly(P.mul(P.poly(u),P.poly(v)),f)[1],P.ONE)
            self.assertEqual(c['bnfcertify'],1);self.assertEqual(c['nfcertify'],[])

    def test_complete_finite_images_using_independent_power_basis_actions(self):
        expected={(39,2):(6,6,1),(48,30):(8,96,12),(195,830):(64,1024,16)}
        for c in self.orders:
            f=P.poly(c['polynomial']);B=[[Q(v)for v in row]for row in c['integral_basis']]
            columns=list(map(list,zip(*B)));actions=[];m=c['power_order_index']
            for u in c['maximal_order_units']:
                cols=[]
                for b in B:
                    v=list(P.divmod_poly(P.mul(P.poly(map(Q,u)),P.poly(b)),f)[1]);v += [Q(0)]*(3-len(v))
                    coords=solve(columns,v);self.assertTrue(all(x.denominator==1 for x in coords))
                    cols.append([int(x)for x in coords])
                actions.append(list(map(list,zip(*cols))))
            states={tuple(s['coordinates']):s for s in c['residue_states']}
            good=0
            for state,record in states.items():
                integral=all(sum(row[j]*state[j]for j in range(3)).denominator==1 for row in columns)
                self.assertEqual(integral,record['belongs_to_power_order'])
                self.assertEqual(integral,lattice_contains(c['exponent_hnf_columns'],record['exponents']))
                good+=integral
                for i,A in enumerate(actions):
                    target=tuple(sum(row[j]*state[j]for j in range(3))%m for row in A)
                    self.assertIn(target,states)
                    r=record['exponents'];s=states[target]['exponents']
                    self.assertTrue(lattice_contains(c['exponent_hnf_columns'],[r[0]+int(i==0)-s[0],r[1]+int(i==1)-s[1]]))
            index,image,count=expected[c['P'],c['Q']]
            self.assertEqual((c['free_unit_index'],len(states),good),(index,image,count))
            self.assertEqual(index*good,len(states))

    def test_six_nonmonic_sources_exact_signed_roundtrips_and_norms(self):
        count=0
        for c in self.orders:
            B=[[Q(v)for v in row]for row in c['integral_basis']];columns=list(zip(*B))
            for source in c['binary_sources']:
                count+=1;a,b,e,d=source['form']
                for r in range(-4,5):
                    for s in range(-4,5):
                        coords=encode_binary_source(source,r,s)
                        self.assertEqual(recover_binary_source(source,coords),[r,s])
                        power=[sum(row[j]*coords[j]for j in range(3))for row in columns]
                        self.assertEqual(algebra_norm(c['polynomial'],power),a*a*(a*r**3+b*r*r*s+e*r*s*s+d*s**3))
                with self.assertRaises(ValueError):recover_binary_source(source,[1,0,0])
        self.assertEqual(count,6)

    def test_signed_unit_orbits_preserve_norm_and_reverse(self):
        for c in self.orders:
            source=c['binary_sources'][0];gamma=encode_binary_source(source,-3,2)
            columns=list(zip(*[[Q(v)for v in row]for row in c['integral_basis']]))
            norm=lambda coords:algebra_norm(c['polynomial'],[sum(row[j]*coords[j]for j in range(3))for row in columns])
            for exponents in ([1,-1],[-2,1],[0,0]):
                result=unit_orbit_source(source,c,gamma,exponents)
                self.assertEqual(abs(norm(result['coordinates'])),abs(norm(gamma)))
                back=unit_orbit_source(source,c,result['coordinates'],[-x for x in exponents])
                self.assertEqual(back['coordinates'],gamma)
                self.assertEqual(back['source_pair'],[-3,2])
                if result['source_pair'] is not None:
                    self.assertEqual(encode_binary_source(source,*result['source_pair']),result['coordinates'])

    def test_nonunit_bad_generator_and_incomplete_image_reject(self):
        c=self.orders[0];args=[c['polynomial'],c['integral_basis'],c['field_discriminant'],c['maximal_order_units']]
        with self.assertRaises(WorkLimit):power_order_unit_lattice(*args,cell_limit=1)
        bad=copy.deepcopy(args);bad[3][0]=['2','0','0']
        with self.assertRaises(ValueError):power_order_unit_lattice(*bad)
        with self.assertRaises(ValueError):compile_binary_source(c,c['binary_sources'][0]['form'],[1,1,0])

    def test_index_one_edge_case(self):
        c=power_order_unit_lattice([-1,-3,0,1],[['1','0','0'],['0','1','0'],['0','0','1']],81,
                                 [['0','1','0'],['1','1','0']])
        self.assertEqual(c['free_unit_index'],1);self.assertEqual(c['residue_image_size'],1)
        self.assertEqual(c['exponent_hnf_columns'],[[1,0],[0,1]])


if __name__=='__main__':unittest.main()
