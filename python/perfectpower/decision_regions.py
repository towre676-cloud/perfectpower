"""Exact closed decision cells on one/two-dimensional affine target boxes."""
from copy import deepcopy
from fractions import Fraction as Q
from . import exact_linear as E
from .observable_machine import _q
from .weighted_hodge import metric
from .bounded_inverse import closest_in_box
from .divisor_square import WorkLimit


def dot(a,b):return sum((x*y for x,y in zip(a,b)),Q(0))


def clip(vertices,normal,rhs):
    if not vertices:return []
    values=[dot(normal,v)-rhs for v in vertices];out=[]
    for i,end in enumerate(vertices):
        start=vertices[i-1];a,b=values[i-1],values[i]
        if (a>0 and b<0) or (a<0 and b>0):
            t=a/(a-b);out.append(tuple(x+t*(y-x) for x,y in zip(start,end)))
        if b<=0:out.append(end)
    unique=[]
    for v in out:
        if v not in unique:unique.append(v)
    return unique


def rectangle(box,d):
    bounds=tuple(map(_q,box))
    if len(bounds)!=2*d or any(bounds[2*i]>=bounds[2*i+1] for i in range(d)):raise ValueError('positive-width target intervals required')
    if d==1:return [(bounds[0],),(bounds[1],)]
    a,b,c,e=bounds;return [(a,c),(b,c),(b,e),(a,e)]


def cells(settings,mass,origin,basis,box):
    result=[]
    for v in sorted(settings):
        vertices=list(box);inequalities=[]
        mv=E.apply(mass,v);constant=dot(v,mv)
        for w in sorted(settings):
            if v==w:continue
            difference=E.apply(mass,tuple(a-b for a,b in zip(v,w)))
            normal=tuple(-2*dot(difference,column) for column in E.transpose(basis))
            rhs=dot(w,E.apply(mass,w))-constant+2*dot(difference,origin)
            inequalities.append(dict(normal=normal,rhs=rhs,competitor=w))
            vertices=clip(vertices,normal,rhs)
            if not vertices:break
        if vertices:
            dimension=0 if len(vertices)==1 else E.rank(tuple(tuple(a-b for a,b in zip(x,vertices[0])) for x in vertices[1:]))
            result.append(dict(setting=v,vertices=vertices,dimension=dimension,inequalities=inequalities))
    return result


class CalibrationPolicy:
    def __init__(self,specification):
        required={'matrix','observation','lower','upper','target_origin','target_basis','target_box'}
        if not required<=set(specification) or set(specification)-required-{'metric','inequalities','node_limit','query_limit','candidate_limit'}:raise ValueError('exact bounded model and affine target rectangle required')
        self.specification=deepcopy(specification);s=self.specification
        origin=tuple(map(_q,s['target_origin']));basis=E.matrix(tuple(tuple(map(_q,row)) for row in s['target_basis']));n=len(origin);d=len(basis[0])
        if len(basis)!=n or d not in (1,2) or E.rank(basis)!=d:raise ValueError('full-rank affine target basis with one or two parameters required')
        mass=metric(E.identity(n) if s.get('metric') is None else [[_q(x) for x in r] for r in s['metric']],n)
        box=rectangle(s['target_box'],d);nodes=s.get('node_limit',500000);queries=s.get('query_limit',2000);capacity=s.get('candidate_limit',128)
        if any(type(v) is not int or v<1 for v in (nodes,queries,capacity)) or capacity>512 or queries>100000:raise ValueError('positive bounded policy budgets required')
        self.origin,self.basis,self.mass,self.box=origin,basis,mass,box
        known=set();cache={};ledger=[];used=0
        def oracle(point):
            nonlocal used
            point=tuple(point)
            if point in cache:return cache[point]
            if len(cache)>=queries or used>=nodes:raise WorkLimit('decision-region oracle budget; no policy returned')
            target=tuple(x+y for x,y in zip(origin,E.apply(basis,point)))
            r=closest_in_box(s['matrix'],s['observation'],target,s['lower'],s['upper'],mass,s.get('inequalities',()),node_limit=nodes-used)
            used+=r['nodes'];winners=tuple(r['minimizers']);cache[point]=winners
            ledger.append(dict(parameter=point,target=target,minimizers=winners,energy=r['minimum_energy'],nodes=r['nodes']))
            known.update(winners)
            if len(known)>capacity:raise WorkLimit('decision-region candidate budget; no policy returned')
            return winners
        for point in box:oracle(point)
        if not known:
            self.packet=dict(schema='pp-calibration-policy/1',status='NO_FEASIBLE_DESIGN',cells=[],contacts=[],oracle_queries=ledger,complete=True,execution_verified=False);return
        rounds=0
        while True:
            rounds+=1;regions=cells(known,mass,origin,basis,box);before=set(known)
            for region in regions:
                for point in region['vertices']:oracle(point)
            if known==before:break
        contacts=[]
        for i,a in enumerate(regions):
            for b in regions[i+1:]:
                overlap=list(a['vertices'])
                for gap in b['inequalities']:overlap=clip(overlap,gap['normal'],gap['rhs'])
                if overlap:contacts.append(dict(settings=[a['setting'],b['setting']],vertices=overlap))
        self.packet=dict(schema='pp-calibration-policy/1',status='COMPLETE_DECISION_REGIONS',cells=regions,contacts=contacts,
            discovered_settings=len(known),oracle_queries=ledger,oracle_nodes=used,rounds=rounds,complete=True,execution_verified=False,
            target_origin=origin,target_basis=basis,target_box=s['target_box'],metric=mass,
            completeness='every final cell vertex checked against the complete integer optimizer; each competitor cost difference is affine',
            scope='all optimal settings and ties on the supplied closed affine target rectangle; oracle work is bounded; Python execution')

    def summary(self):return dict(status=self.packet['status'],cells=len(self.packet['cells']),contacts=len(self.packet['contacts']),oracle_queries=len(self.packet['oracle_queries']),complete=True)
    def evidence(self):return deepcopy(self.packet)
    def decide(self,parameter):
        point=tuple(map(_q,parameter));d=len(self.basis[0])
        if len(point)!=d:raise ValueError('matching parameter dimension required')
        bounds=tuple(map(_q,self.specification['target_box']))
        if any(not bounds[2*i]<=point[i]<=bounds[2*i+1] for i in range(d)):raise ValueError('parameter outside policy region')
        winners=[cell['setting'] for cell in self.packet['cells'] if all(dot(g['normal'],point)<=g['rhs'] for g in cell['inequalities'])]
        target=tuple(x+y for x,y in zip(self.origin,E.apply(self.basis,point)))
        energies=[dot(tuple(a-b for a,b in zip(v,target)),E.apply(self.mass,tuple(a-b for a,b in zip(v,target)))) for v in winners]
        if energies and len(set(energies))!=1:raise AssertionError('overlapping cells disagree')
        return dict(parameter=point,target=target,minimizers=sorted(winners),minimum_energy=energies[0] if energies else None,complete=True)
