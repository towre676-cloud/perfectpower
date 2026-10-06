import tempfile
import unittest
from pathlib import Path
from perfectpower.populations import ExactPopulation
from perfectpower.catalogue import Catalogue
from perfectpower.projected_populations import symbolic_join
from perfectpower.divisor_square import WorkLimit


def domain(lo,hi):
    return dict(kind='domain',predicate={'op':'and','args':[
        {'poly':[-lo,1],'relation':'>='},{'poly':[-hi,1],'relation':'<='}]},
        fields={'square':[0,0,1],'linear':[0,1],'zero':[0]})


class MultiColumnJoinTests(unittest.TestCase):
    def test_tuple_keys_restrict_collisions_without_enumeration(self):
        size=10**30
        left=ExactPopulation(domain(-size,size))
        right=ExactPopulation(domain(-size,size))
        join=symbolic_join(left,right,left_fields=['square','linear'],right_fields=['square','linear'])
        self.assertEqual(join.count(),2*size+1)
        for rank in (0,size,2*size):
            record=join.select(rank)
            self.assertEqual(record['values']['x'],record['values']['y'])
        single=symbolic_join(left,right,'square','square')
        self.assertEqual(single.count(),4*size+1)

    def test_complete_bounded_join_preserves_original_multiplicities(self):
        with tempfile.TemporaryDirectory() as directory, Catalogue(Path(directory)/'objects.db') as catalogue:
            a=catalogue.register('population',domain(-3,3))['id']
            b=catalogue.register('population',domain(-3,3))['id']
            rows=catalogue.join(a,b,mode='value',left_fields=['square','linear'],right_fields=['square','linear'])
            self.assertEqual(len(rows),7)
            self.assertTrue(all(r['left']['parameter']==r['right']['parameter'] for r in rows))
            scalar=catalogue.join(a,b,mode='value',left_field='square',right_field='square')
            self.assertEqual(len(scalar),13)
            with self.assertRaises(WorkLimit):
                catalogue.join(a,b,mode='value',left_field='zero',right_field='zero',row_limit=14)

    def test_invalid_field_lists_fail_explicitly(self):
        p=ExactPopulation(domain(0,3))
        for args in [dict(left_fields=[],right_fields=[]),
                     dict(left_fields=['linear'],right_fields=['square','linear']),
                     dict(left_fields=['missing'],right_fields=['linear']),
                     dict(left_field='linear',right_field='linear',left_fields=['linear'],right_fields=['linear'])]:
            with self.assertRaises(ValueError):symbolic_join(p,p,**args)


if __name__=='__main__':unittest.main()
