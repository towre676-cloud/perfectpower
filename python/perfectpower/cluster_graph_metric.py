"""Global length metric and integral cycle form of the split cluster graph.

This is the finite metric graph of geometric semistable reduction, not a
metric on the complex curve or a claim about arithmetic component twists.
"""
from fractions import Fraction as Q
import json
from .root_cluster_geometry import cluster_geometry


def _determinant(matrix):
    rows = [list(row) for row in matrix]
    result = Q(1)
    for j in range(len(rows)):
        pivot = next((i for i in range(j, len(rows)) if rows[i][j]), None)
        if pivot is None:
            return Q(0)
        if pivot != j:
            rows[pivot], rows[j] = rows[j], rows[pivot]
            result = -result
        value = rows[j][j]
        result *= value
        for i in range(j+1, len(rows)):
            ratio = rows[i][j]/value
            rows[i] = [a-ratio*b for a, b in zip(rows[i], rows[j])]
    return result


def cluster_graph_metric(roots, p):
    graph = cluster_geometry(roots, p)
    n, edges = len(graph['vertices']), graph['edges']
    distance = [[Q(0) if i == j else None for j in range(n)] for i in range(n)]
    parent = list(range(n))
    adjacency = [[] for _ in range(n)]
    chords, tree = [], []
    def find(i):
        while parent[i] != i:
            i = parent[i]
        return i
    for k, edge in enumerate(edges):
        a, b, length = edge['source'], edge['target'], Q(edge['length'])
        if length <= 0:
            raise ValueError('positive edge lengths required')
        if distance[a][b] is None or length < distance[a][b]:
            distance[a][b] = distance[b][a] = length
        if find(a) != find(b):
            parent[find(a)] = find(b)
            adjacency[a].append((b, k, 1))
            adjacency[b].append((a, k, -1))
            tree.append(k)
        else:
            chords.append(k)
    for k in range(n):
        for i in range(n):
            for j in range(n):
                if distance[i][k] is not None and distance[k][j] is not None:
                    value = distance[i][k]+distance[k][j]
                    if distance[i][j] is None or value < distance[i][j]:
                        distance[i][j] = value
    if any(value is None for row in distance for value in row):
        raise ValueError('connected graph required')
    cycles = []
    for chord in chords:
        source, target = edges[chord]['source'], edges[chord]['target']
        # The chord goes source -> target; its tree path returns target -> source.
        paths = [(target, None, [])]
        while paths:
            vertex, previous, path = paths.pop()
            if vertex == source:
                break
            paths.extend((v, vertex, path+[(edge, sign)]) for v, edge, sign in adjacency[vertex] if v != previous)
        else:
            raise ArithmeticError('spanning tree path missing')
        vector = [0]*len(edges)
        vector[chord] = 1
        for edge, sign in path:
            vector[edge] = sign
        boundary = [0]*n
        for value, edge in zip(vector, edges):
            boundary[edge['source']] -= value
            boundary[edge['target']] += value
        if any(boundary):
            raise ArithmeticError('cycle boundary is nonzero')
        cycles.append(vector)
    if len(cycles) != graph['graph_cycle_rank']:
        raise ArithmeticError('cycle rank disagrees with the source graph')
    lengths = list(map(lambda edge: Q(edge['length']), edges))
    form = [[sum((length*a*b for length, a, b in zip(lengths, left, right)), Q(0))
             for right in cycles] for left in cycles]
    volume = _determinant(form)
    if volume <= 0:
        raise ArithmeticError('cycle form is not positive definite')
    return dict(schema='pp-cluster-graph-metric/1', graph=graph,
                vertex_distances=[[str(value) for value in row] for row in distance],
                spanning_tree_edges=tree, chord_edges=chords, integral_cycle_basis=cycles,
                cycle_length_form=[[str(value) for value in row] for row in form],
                cycle_form_determinant=str(volume), cycle_boundaries_checked=True,
                scope='global shortest-path length metric and tropical cycle lattice of the geometric split-root cluster graph; no complex-curve metric or Frobenius marking')


def verify_cluster_graph_metric(roots, p, receipt):
    """Bind a supplied packet to the original branch roots and prime."""
    try:
        expected = cluster_graph_metric(roots, p)
        encode = lambda value: json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False)
        return encode(receipt) == encode(expected)
    except (ValueError, TypeError, KeyError, ArithmeticError):
        return False
