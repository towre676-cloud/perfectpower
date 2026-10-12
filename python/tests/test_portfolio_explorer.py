import json
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch
from perfectpower import portfolio_explorer as ui

class PortfolioTests(unittest.TestCase):
    def setUp(self):
        self.tmp=tempfile.TemporaryDirectory();self.folder=Path(self.tmp.name);ui._SESSION=None
        self.source=ui.model();self.spec=self.source['specification']
        self.resources=[dict(r,min=0,max=0) for r in self.spec['resources']]
    def tearDown(self):self.tmp.cleanup();ui._SESSION=None
    def run_query(self,**extra):
        return ui.execute(dict(kind='portfolio',resources=self.resources,**extra),self.folder)
    def test_empty_choice_and_reuse(self):
        r=self.run_query(action='build');self.assertEqual(r['summary']['count'],'1');self.assertEqual(r['selection']['profit'],'0')
        r=self.run_query(action='conditional',prefix=[1]);self.assertTrue(r['session_reused']);self.assertEqual(r['conditional']['count'],'0');self.assertNotIn('selection',r)
        r=self.run_query(action='select',rank='0');self.assertEqual(r['selection']['projects'],[])
        self.assertTrue((self.folder/'portfolio-evidence.json').is_file())
        self.assertEqual(self.run_query(action='sample',seed=5)['selection']['point'],['0']*50)
    def test_changed_limits_rebuild_and_partition(self):
        self.run_query(action='build');self.resources=[dict(r,max=1) for r in self.resources]
        r=self.run_query(action='conditional',prefix=[]);self.assertFalse(r['session_reused']);self.assertEqual(sum(int(b['count']) for b in r['branches']),int(r['conditional']['count']))
    def test_validation(self):
        with self.assertRaises(ValueError):self.run_query(action='conditional',prefix=[True])
        with self.assertRaises(ValueError):self.run_query(action='select',rank='9007199254740993')
        self.resources[0]['name']='new'
        with self.assertRaises(ValueError):self.run_query(action='build')
    def test_progress_and_source_identity(self):
        self.run_query(action='build');progress=json.loads((self.folder/'progress.json').read_text());self.assertIsNone(progress['percentage'])
        self.assertEqual(ui.model()['source_sha256'],self.source['source_sha256'])

if __name__=='__main__':unittest.main()
