from copy import deepcopy
from fractions import Fraction as Q
import unittest
from perfectpower.cluster_graph_metric import cluster_graph_metric, verify_cluster_graph_metric


class ClusterGraphMetricTests(unittest.TestCase):
    def test_parallel_edges_form_cycles_and_shortest_paths(self):
        r = cluster_graph_metric([0, 3, 1, 4, 2, 5], 3)
        self.assertEqual(len(r['integral_cycle_basis']), 2)
        self.assertGreater(Q(r['cycle_form_determinant']), 0)
        d = [list(map(Q, row)) for row in r['vertex_distances']]
        for i in range(len(d)):
            self.assertEqual(d[i][i], 0)
            for j in range(len(d)):
                self.assertEqual(d[i][j], d[j][i])
                for k in range(len(d)):
                    self.assertLessEqual(d[i][j], d[i][k]+d[k][j])
        for edge in r['graph']['edges']:
            self.assertLessEqual(d[edge['source']][edge['target']], Q(edge['length']))

    def test_one_vertex_and_tree_have_trivial_jacobian(self):
        for roots in ([0, 1, 2], [0, 3, 6, 1, 2]):
            r = cluster_graph_metric(roots, 3)
            self.assertEqual(r['integral_cycle_basis'], [])
            self.assertEqual(r['cycle_form_determinant'], '1')
            self.assertEqual(len(r['spanning_tree_edges']), len(r['graph']['vertices'])-1)

    def test_replay_binds_source_and_rejects_tampering(self):
        roots = [0, 3, 1, 4, 2, 5]
        receipt = cluster_graph_metric(roots, 3)
        self.assertTrue(verify_cluster_graph_metric(roots, 3, receipt))
        for key in ('vertex_distances', 'integral_cycle_basis', 'cycle_length_form'):
            bad = deepcopy(receipt)
            bad[key][0][0] = '100'
            self.assertFalse(verify_cluster_graph_metric(roots, 3, bad))
        self.assertFalse(verify_cluster_graph_metric([0, 9, 1, 4, 2, 5], 3, receipt))
        bad = deepcopy(receipt)
        bad['cycle_boundaries_checked'] = 1
        self.assertFalse(verify_cluster_graph_metric(roots, 3, bad))


if __name__ == '__main__':
    unittest.main()
