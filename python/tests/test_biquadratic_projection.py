import unittest
from perfectpower.collision_geometry import biquadratic_collisions
from perfectpower.projected_populations import ProjectedPopulation
from perfectpower.divisor_square import WorkLimit


class BiquadraticProjectionTests(unittest.TestCase):
    def test_complete_circle_decomposition_against_grid(self):
        for a in (-3,-1,1,2):
            for b in range(-15,16):
                coefficients=[7,0,b,0,a]
                receipt=biquadratic_collisions(coefficients)
                pairs=set(receipt['pairs'])
                for x in range(-8,9):
                    for y in range(x+1,9):
                        equal=a*x**4+b*x*x==a*y**4+b*y*y
                        self.assertEqual(equal,y==-x or (x,y) in pairs)

    def test_disconnected_domains_keep_the_least_original_owner(self):
        for absent in (-5,-2,0,1,5):
            predicate={'op':'and','args':[{'poly':[6,1],'relation':'>='},
                {'poly':[-6,1],'relation':'<='},{'poly':[-absent,1],'relation':'!='}]}
            p=ProjectedPopulation(dict(source=dict(kind='domain',predicate=predicate,fields={'f':[0,0,-25,0,1]}),field='f'))
            owners={}
            for n in range(-6,7):
                if n!=absent:owners.setdefault(n**4-25*n*n,n)
            self.assertEqual(p.count(),len(owners))
            self.assertEqual([r['parameter'] for r in p.page(0,p.count())],sorted(owners.values()))
            for value,owner in owners.items():
                self.assertEqual(p.select(p.locate(value))['parameter'],owner)
                self.assertEqual(p.multiplicity(value),sum(n!=absent and n**4-25*n*n==value for n in range(-6,7)))

    def test_work_bound_fails_without_partial_result(self):
        with self.assertRaises(WorkLimit):biquadratic_collisions([0,0,-10**20,0,1])
        with self.assertRaises(ValueError):biquadratic_collisions([0,1,0,0,1])


if __name__=='__main__':unittest.main()
