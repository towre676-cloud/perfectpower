import copy
import os
import unittest
from perfectpower.checked_global_population import global_population_certificate,check_global_population


class GlobalPopulationTests(unittest.TestCase):
    def test_global_base_and_ties(self):
        p=global_population_certificate([{'ranks':[0,1,2],'objective':['pow','y',2]}])
        self.assertEqual(p['source_points'],[[3,-5],[3,5]])
        self.assertEqual(p['results'][0]['minimum'],dict(value=25,points=[[3,-5],[3,5]]))
        self.assertIn('globally',p['scope'])
        self.assertNotIn('x_bounds',p['specification'])
        self.assertIn('expanded_original',p['lean'])

    def test_affine_input_and_sign_domains(self):
        for a,b,n in [(5,-7,2),(-5,13,2),(2,5,-1),(1,3,0),(1,3-(10**30),10**30)]:
            p=global_population_certificate([{'condition':['le',0,'y'],'objective':'x'}],scale=a,shift=b)
            self.assertEqual(p['results'][0]['points'],[[n,5]])
            self.assertEqual(p['results'][0]['minimum']['value'],n)
            cs=p['original_coefficients']
            self.assertEqual(sum(c*n**i for i,c in enumerate(cs)),25)
        self.assertEqual(global_population_certificate([{}],scale=2,shift=5,domain='positive')['source_count'],0)
        self.assertEqual(global_population_certificate([{}],shift=3,domain='nonnegative')['source_count'],2)
        self.assertEqual(global_population_certificate([{}],shift=3,domain='positive')['source_count'],0)

    def test_no_integer_preimage(self):
        p=global_population_certificate([{'objective':'y','ranks':[0]}],scale=5,shift=0)
        self.assertEqual(p['source_count'],0)
        self.assertEqual(p['results'][0]['selections'],[{'rank':0,'point':None}])

    def test_bad_specs_and_mutations(self):
        for kwargs in [dict(scale=0),dict(scale=True),dict(shift=1.0),dict(domain='natural'),dict(family='unproved')]:
            with self.assertRaises(ValueError):global_population_certificate([{}],**kwargs)
        p=global_population_certificate([{}])
        for k,v in [('source_points',[]),('results',[]),('lean','axiom x : False'),('scope','bounded')]:
            q=copy.deepcopy(p);q[k]=v
            self.assertFalse(check_global_population(q,lean='missing')['accepted'])

    def test_dispatch(self):
        from perfectpower.query_service import dispatch
        args=dict(queries=[{}],scale=5,shift=-7)
        self.assertEqual(dispatch(None,dict(op='checked_global_population',args=args)),global_population_certificate(**args))

    @unittest.skipUnless(os.environ.get('PERFECTPOWER_LEAN') and os.environ.get('LEAN_PATH'),'Lean and Mathlib required')
    def test_actual_global_kernel_checks(self):
        queries=[{'ranks':[0,1,2],'objective':['pow','y',2]},
                 {'condition':['le',0,'y'],'objective':['mul','x','y']}]
        for kwargs in [{},dict(scale=5,shift=-7),dict(scale=5),
                       dict(scale=-5,shift=13),dict(scale=2,shift=5,domain='positive')]:
            p=global_population_certificate(queries,**kwargs)
            r=check_global_population(p)
            self.assertTrue(r['accepted'],r)
            self.assertFalse(r['execution_verified'])
            self.assertIn('MordellMinus2Core',r['library_sha256'])


if __name__=='__main__':unittest.main()
