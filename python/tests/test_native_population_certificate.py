import random
import tempfile
import unittest
from pathlib import Path
from perfectpower.native_population_certificate import population_certificate
from perfectpower.divisor_square import WorkLimit
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch


class NativePopulationCertificateTests(unittest.TestCase):
    def test_original_bounded_semantics_and_nonmonotone_deduplication(self):
        predicate={'op':'or','args':[{'poly':[0,1],'relation':'<','modulus':4,'value':2},
                                    {'poly':[-9,0,1],'relation':'='}]}
        result=population_certificate(-12,12,predicate,[0,0,1],ranks=[0,3,9])
        expected=sorted({x*x for x in range(-12,13) if x%4<2 or x*x==9})
        self.assertEqual(result['cardinality'],len(expected))
        self.assertEqual(result['selections'],[dict(rank=i,value=expected[i]) for i in (0,3,9)])
        self.assertIn('bounded_image_complete',result['lean'])
        self.assertIn('by decide +kernel',result['lean'])
        self.assertFalse(result['execution_verified'])

    def test_boolean_combinations_and_negative_remainders(self):
        rng=random.Random(4817)
        for _ in range(40):
            m=rng.randrange(1,8);v=rng.randrange(-2,m+2);c=rng.randrange(-3,4)
            predicate={'op':'not','args':[{'poly':[c,1],'relation':'>=','modulus':m,'value':v}]}
            expected=sorted({(x-c)**2 for x in range(-8,9) if not (x+c)%m>=v})
            result=population_certificate(-8,8,predicate,[c*c,-2*c,1],ranks=list(range(len(expected))))
            self.assertEqual([r['value'] for r in result['selections']],expected)
        for op,truth in [('and',True),('or',False)]:
            result=population_certificate(-2,2,dict(op=op,args=[]),[5])
            self.assertEqual(result['cardinality'],int(truth))

    def test_empty_reversed_bounds_and_fail_closed_budgets(self):
        self.assertEqual(population_certificate(4,1,True,[0,1])['cardinality'],0)
        for args in [(False,1,True,[1]),(0,100,True,[1])]:
            with self.assertRaises((ValueError,WorkLimit)):
                population_certificate(*args,work_limit=10)
        for ranks in ([True],[-1],[5]):
            with self.assertRaises(ValueError):population_certificate(0,1,True,[0,1],ranks=ranks)
        with self.assertRaises(ValueError):population_certificate(0,1,{'poly':[0,1],'relation':'=','extra':1},[1])
        with self.assertRaises(WorkLimit):population_certificate(0,1,True,[1]*34)

    def test_service_roundtrip_uses_numeric_image_order(self):
        with tempfile.TemporaryDirectory() as folder, Catalogue(Path(folder)/'db') as catalogue:
            result=dispatch(catalogue,dict(op='population_certificate',args=dict(lower=-2,upper=2,
                predicate=True,polynomial=[0,0,1],ranks=[0,1,2])))
        self.assertEqual(result['selections'],[dict(rank=0,value=0),dict(rank=1,value=1),dict(rank=2,value=4)])


if __name__=='__main__':unittest.main()
