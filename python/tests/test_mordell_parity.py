"""Check census identity, modular obstructions and retained actual-group proof scope."""
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import unittest
from perfectpower.elliptic_arithmetic import EllipticCurve,encode_point

ROOT=Path(__file__).resolve().parents[2]


class MordellParityTests(unittest.TestCase):
    def test_all_census_bases_and_parity_points(self):
        rows=json.loads((ROOT/'data/mordell_parity_sources.json').read_text())['rows']
        self.assertEqual(len(rows),457)
        self.assertEqual(sum(r['rank']==2 for r in rows),14)
        self.assertEqual(sum(len(r['halving_moduli']) for r in rows),485)
        for row in rows:
            source=ROOT/row['source_receipt'];packet=json.loads(source.read_text())
            self.assertEqual(hashlib.sha256(source.read_bytes()).hexdigest(),row['source_sha256'])
            self.assertEqual(packet['basis_points'],row['basis_points'])
            E=EllipticCurve([0,row['k']]);basis=[E.checked(p) for p in row['basis_points']]
            points=basis+([E.add(*basis)] if len(basis)==2 else [])
            self.assertEqual([encode_point(p) for p in points],row['parity_points'])

    def test_obstructions_exhaust_all_residues(self):
        rows=json.loads((ROOT/'data/mordell_parity_sources.json').read_text())['rows']
        for row in rows:
            k=row['k'];M=row['branch_modulus']
            self.assertTrue(all((z**3+k)%M for z in range(M)))
            for point,M in zip(row['parity_points'],row['halving_moduli']):
                u=Fraction(point[0]);p,q=u.numerator,u.denominator
                cs=[-4*p*k*q**3,-8*k*q**3,0,-4*p,1]
                self.assertTrue(all(sum(c*pow(z,i,M) for i,c in enumerate(cs))%M for z in range(M)))

    def test_receipt_matches_actual_group_sources_without_global_promotion(self):
        path=ROOT/'receipts/mordell_parity_atlas.json'
        if not path.exists():self.skipTest('run actual atlas kernel gate first')
        p=json.loads(path.read_text())
        self.assertEqual(p['proof_status'],'kernel_checked')
        self.assertEqual(p['curves'],457)
        self.assertEqual(len(p['audited_declarations']),1399)
        self.assertEqual(p['formally_completed_curves'],0)
        self.assertFalse(p['execution_verified'])
        for name,h in p['source_sha256'].items():
            self.assertEqual(hashlib.sha256((ROOT/name).read_bytes()).hexdigest(),h)


if __name__=='__main__':unittest.main()
