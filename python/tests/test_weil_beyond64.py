import gzip,json,math,unittest
from pathlib import Path
from perfectpower.weil_commutant import _det_mod,certify_commutant,verify_commutant
from perfectpower.weil_orbit import closed_form

ROOT=Path(__file__).resolve().parents[2]


class Beyond64(unittest.TestCase):
    def test_original_equation_packets_match_closed_form(self):
        summary=json.loads((ROOT/'receipts/weil_beyond64/summary.json').read_text())
        packets={c['level']:c for c in json.loads(gzip.decompress((ROOT/'receipts/weil_beyond64/packets.json.gz').read_bytes()))}
        self.assertEqual(summary['levels'],10);self.assertEqual(summary['maximum_level'],128)
        for row in summary['rows']:
            c=packets[row['level']]
            self.assertEqual(c['dimension'],closed_form(c['level']))
            self.assertEqual(c['rank_lower_bound'],c['allowed_entries']-c['dimension'])
            self.assertEqual(len(c['basis']),c['dimension'])
            self.assertEqual(len(c['minor_rows']),c['rank_lower_bound'])
            self.assertEqual(c['dimension'],row['dimension'])
        c=packets[65]
        self.assertTrue(verify_commutant(c))

    def test_integer_array_determinant_against_known_dense_factorization(self):
        n=96;q=99991
        L=[[1 if i==j else ((i+2*j)%5-2 if i>j else 0)for j in range(n)]for i in range(n)]
        U=[[i+1 if i==j else ((2*i+j)%7-3 if i<j else 0)for j in range(n)]for i in range(n)]
        A=[[sum(L[i][k]*U[k][j]for k in range(n))for j in range(n)]for i in range(n)]
        expected=math.prod(range(1,n+1))%q
        self.assertEqual(_det_mod(A,q),expected)
        A[0],A[1]=A[1],A[0]
        self.assertEqual(_det_mod(A,q),-expected%q)
        A[0]=A[1][:];self.assertEqual(_det_mod(A,q),0)

    def test_extended_scope_still_bounds_allocation(self):
        for n in (True,1,129):
            with self.assertRaises(ValueError):certify_commutant(n)


if __name__=='__main__':unittest.main()
