import copy
import unittest
from industrial_performance.run_replay import validate_checkpoint


class ReplayCheckpointTests(unittest.TestCase):
    def test_bound_resume(self):
        config = {'cap':8, 'code_sha256':{'engine':'a'}}
        entry = {'path':'source', 'sha256':'b'}
        row = {'source':entry, 'full_query_count':1, 'selected_queries':1,
               'command':{'queries':[{'answer':'sat'}], 'errors':[]},
               'batched':{'queries':[{'answer':'sat'}], 'errors':[]}}
        saved = {'complete':False, 'config':config, 'rows':[row]}
        self.assertEqual(validate_checkpoint(saved, config, [entry]), [row])
        for mutation in ('config', 'source', 'count', 'error', 'answer'):
            broken = copy.deepcopy(saved)
            if mutation == 'config':
                broken['config']['code_sha256']['engine'] = 'other'
            elif mutation == 'source':
                broken['rows'][0]['source']['sha256'] = 'other'
            elif mutation == 'count':
                broken['rows'][0]['selected_queries'] = 2
            elif mutation == 'error':
                broken['rows'][0]['batched']['errors'] = ['canceled']
            else:
                broken['rows'][0]['batched']['queries'][0]['answer'] = 'unexpected'
            with self.assertRaises(ValueError):
                validate_checkpoint(broken, config, [entry])


if __name__ == '__main__':
    unittest.main()
