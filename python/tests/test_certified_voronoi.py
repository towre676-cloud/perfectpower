import unittest
from fractions import Fraction as Q
from perfectpower.certified_voronoi import sqrt_upper,prepare,boundary_enclosure

class CertifiedVoronoiTests(unittest.TestCase):
    def setUp(self):
        self.mesh={'vertices':3,'triangles':[[0,1,2]],'edge_lengths':[[0,1,3],[0,2,4],[1,2,5]]}
    def test_outward_sqrt(self):
        for q in [Q(0),Q(2),Q(1,3),Q(10**40,7)]:
            u=sqrt_upper(q);self.assertGreaterEqual(u*u,q)
            if u:self.assertLess((u-Q(1,1<<48))**2,q)
    def test_scaled_fields_are_lipschitz(self):
        _,grams,fs,_=prepare(self.mesh,[[0,100,100]])
        a,c,b=grams[0];u=fs[0][1]-fs[0][0];v=fs[0][2]-fs[0][0]
        self.assertLessEqual((b*u*u-2*c*u*v+a*v*v)/(a*b-c*c),1)
    def test_partition_and_membership(self):
        p=boundary_enclosure(self.mesh,[0,1],[[0,3,0]],4)
        self.assertEqual(Q(p['proven_face_fraction_sum'])+Q(p['unresolved_face_fraction_sum']),1)
        self.assertTrue(any(x['site'] is not None for x in p['pieces']))
        for x in p['pieces']:
            if x['site'] is None:continue
            i=p['sites'].index(x['site']);j=1-i
            self.assertLess(Q(x['center_upper'][i])+2*Q(x['radius_upper']),Q(x['center_lower'][j]))
    def test_certificate_tampering(self):
        from perfectpower.certified_voronoi import verify_enclosure
        fields=[[0,3,0]];p=boundary_enclosure(self.mesh,[0,1],fields,2)
        self.assertTrue(verify_enclosure(self.mesh,fields,p))
        p['pieces'][0]['radius_upper']='0'
        self.assertFalse(verify_enclosure(self.mesh,fields,p))
    def test_invalid_metric(self):
        self.mesh['edge_lengths'][2][2]=8
        with self.assertRaises(ValueError):prepare(self.mesh,[])
