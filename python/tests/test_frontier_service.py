import io
import json
from pathlib import Path
import tempfile
import unittest
from perfectpower.catalogue import Catalogue
from perfectpower.query_service import serve


class FrontierServiceTests(unittest.TestCase):
    def test_cold_jsonl_endpoints_and_error_recovery(self):
        requests=[dict(op='inverse_matrix_ball',args=dict(matrix=[[1,0],[0,1]],row_error_bound='1/10')),
                  dict(op='recognize_integral_matrix',args=dict(matrix=[[1,2],[0,1]],row_error_bound=0,symplectic=True)),
                  dict(op='marked_legendre_monodromy',args=dict(path=['1/2','1/2'])),
                  dict(op='cluster_graph_metric',args=dict(roots=[0,3,1,4,2,5],p=3)),
                  dict(op='factorial_window_obstruction',args=dict(index=10**30,width=10**20,degree=2)),
                  dict(op='inverse_matrix_ball',args=dict(matrix=[[0]],row_error_bound=0)),
                  dict(op='recognize_integral_matrix',args=dict(matrix=[[1]],row_error_bound=0))]
        for i,r in enumerate(requests):r['request_id']=i
        with tempfile.TemporaryDirectory() as directory:
            with Catalogue(Path(directory)/'cold.db') as catalogue:
                output=io.StringIO()
                serve(catalogue,io.StringIO('\n'.join(json.dumps(r) for r in requests)),output)
        rows=[json.loads(line) for line in output.getvalue().splitlines()]
        self.assertEqual([r['request_id'] for r in rows],list(range(len(requests))))
        self.assertEqual([r['ok'] for r in rows],[True]*5+[False,True])
        self.assertEqual(rows[4]['result']['status'],'NOT_POWER')
        self.assertTrue(rows[1]['result']['integrality_premise_required'])


if __name__=='__main__':unittest.main()
