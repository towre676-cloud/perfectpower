"""Exact obstacle visibility and Manhattan-cost routing on a finite vertex graph.

Obstacle interiors are forbidden; boundary contact/travel is allowed. This is
not a claim of global Euclidean shortest paths, positive clearance, or dynamics.
"""
from fractions import Fraction as Q
from heapq import heappush,heappop
from .euclid_geometry import point,encode,sub,segment_intersection
from .belyaev_geometry import _simple,_locate
from .divisor_square import Budget,WorkLimit


def _charge(budget,count):
    for _ in range(count):budget.spend()


def _visible(polygons,a,b,budget):
    direction=sub(b,a)
    for polygon in polygons:
        _charge(budget,4*len(polygon))
        if _locate(polygon,a)=='INSIDE' or _locate(polygon,b)=='INSIDE':return False
        if a==b:continue
        cuts={Q(0),Q(1)}
        axis=0 if direction[0] else 1
        for c,d in zip(polygon,polygon[1:]+polygon[:1]):
            budget.spend();hit=segment_intersection(a,b,c,d)
            for encoded in hit['points']:
                p=point(encoded);cuts.add((p[axis]-a[axis])/direction[axis])
        ordered=sorted(cuts)
        for lo,hi in zip(ordered,ordered[1:]):
            _charge(budget,2*len(polygon));t=(lo+hi)/2
            mid=tuple(x+t*v for x,v in zip(a,direction))
            if _locate(polygon,mid)=='INSIDE':return False
    return True


def segment_visibility(obstacles,a,b,*,work_limit=1000000):
    budget=Budget(work_limit);polygons=[_simple(p,budget) for p in obstacles]
    a,b=map(point,(a,b))
    return {'visible':_visible(polygons,a,b,budget),'work_used':budget.used,
            'scope':'straight segment avoids all supplied polygon interiors; boundary contact allowed'}


def route(obstacles,start,end,*,work_limit=1000000,vertex_limit=200):
    if type(vertex_limit) is not int or vertex_limit<2:raise ValueError('vertex limit must be an integer at least two')
    budget=Budget(work_limit);polygons=[_simple(p,budget) for p in obstacles]
    start,end=map(point,(start,end))
    for p in polygons:
        _charge(budget,4*len(p))
        if _locate(p,start)=='INSIDE' or _locate(p,end)=='INSIDE':
            raise ValueError('route endpoints must avoid obstacle interiors')
    nodes=list(dict.fromkeys([start,end]+[v for p in polygons for v in p]))
    if len(nodes)>vertex_limit:raise WorkLimit('visibility vertex budget exceeded')
    start_index=nodes.index(start);end_index=nodes.index(end);edges=[];adj=[[] for _ in nodes]
    for i,a in enumerate(nodes):
        for j in range(i+1,len(nodes)):
            budget.spend();b=nodes[j]
            if _visible(polygons,a,b,budget):
                weight=sum((abs(x-y) for x,y in zip(a,b)),Q(0))
                edges.append([i,j,str(weight)]);adj[i].append((j,weight));adj[j].append((i,weight))
    first=(Q(0),0,(start_index,));best={start_index:first};heap=[(*first,start_index)]
    while heap:
        distance,links,path,current=heappop(heap)
        if best.get(current)!=(distance,links,path):continue
        if current==end_index:break
        for target,weight in adj[current]:
            budget.spend();candidate=(distance+weight,links+1,path+(target,))
            if target not in best or candidate<best[target]:
                best[target]=candidate;heappush(heap,(*candidate,target))
    optimum=best.get(end_index)
    result={'schema':'pp-polygon-visibility-route/1','obstacles':[[encode(p) for p in poly] for poly in polygons],
            'start':encode(start),'end':encode(end),'vertices':[encode(p) for p in nodes],'edges':edges,
            'complete':True,'kernel_checked':False,'work_used':budget.used,
            'objective':'minimum Manhattan edge-length sum on the full supplied vertex visibility graph; ties prefer fewer edges then lexicographic vertex indices',
            'scope':'rational Euclidean obstacle interiors forbidden, boundary contact allowed; graph optimum only, no clearance or physical grasp guarantee'}
    if optimum is None:result.update(status='UNREACHABLE',path=[],cost=None)
    else:
        distance,links,path=optimum
        result.update(status='ROUTE',path=[encode(nodes[i]) for i in path],cost=str(distance),path_indices=list(path))
    return result


def check_route(packet,*,work_limit=1000000,vertex_limit=200):
    expected=route(packet['obstacles'],packet['start'],packet['end'],work_limit=work_limit,vertex_limit=vertex_limit)
    if expected!=packet:raise ValueError('source-bound route does not replay')
    return True
