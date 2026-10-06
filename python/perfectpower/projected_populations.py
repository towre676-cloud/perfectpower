"""Distinct polynomial values through exact collision and monotonicity geometry."""
from copy import deepcopy
from .populations import ExactPopulation
from .integer_image_index import IntegerImageIndex
from . import polyalg as P


def _substitute(node,offset):
    if type(node) is bool:return node
    if 'poly' in node:
        return dict(node,poly=[int(c) for c in P.compose_linear(P.poly(node['poly']),offset,-1)])
    return dict(op=node['op'],args=[_substitute(a,offset) for a in node['args']])


class ProjectedPopulation:
    """Uniform distinct values, with the least source parameter as owner.

    Cubic off-diagonal collisions are finite; higher degrees require strict
    discrete monotonicity on the convex hull of the supplied source domain.

    For f(n)=a*n²+b*n+c, the only distinct collision is m=-b/a-n.
    If -b/a is not integral, every integer parameter has a distinct value.
    """
    def __init__(self,specification):
        if set(specification)!={'source','field'}:raise ValueError('source domain and projected field required')
        self.specification=deepcopy(specification);self.source=ExactPopulation(specification['source'])
        spec=self.source.specification;field=specification['field']
        if spec['kind']!='domain' or field not in spec['fields']:raise ValueError('existing domain field required')
        self.field=field;self.polynomial=spec['fields'][field];self.images=IntegerImageIndex()
        f=P.poly(self.polynomial)
        self.collision=None
        predicate=spec['predicate'];reflection=None
        if P.degree(f)==0:
            predicate=False if not self.source.cardinality else {'poly':[-self.source.select(0)['parameter'],1],'relation':'='}
        elif P.degree(f)==2 and int(f[1])%int(f[2])==0:
            reflection=-int(f[1])//int(f[2])
            ownership={'op':'or','args':[{'poly':[-reflection,2],'relation':'<='},
                {'op':'not','args':[_substitute(spec['predicate'],reflection)]}]}
            predicate={'op':'and','args':[predicate,ownership]}
        elif P.degree(f)==3:
            from .collision_geometry import cubic_collisions
            self.collision=cubic_collisions(f)
            removed=sorted({y for x,y in self.collision['pairs'] if self.source.locate(parameter=x) is not None and self.source.locate(parameter=y) is not None})
            predicate={'op':'and','args':[predicate]+[{'poly':[-y,1],'relation':'!='} for y in removed]}
        elif P.degree(f)>3:
            # Strict discrete monotonicity on the convex source hull suffices.
            delta=P.add(P.compose_linear(f,1,1),P.scale(f,-1))
            if self.source.cardinality:
                lo=self.source.select(0)['parameter'];hi=self.source.select(self.source.cardinality-1)['parameter']-1
                hull=[{'poly':[-lo,1],'relation':'>='},{'poly':[-hi,1],'relation':'<='}]
                bad=[]
                for relation in ('<=','>='):
                    bad.append(ExactPopulation(dict(kind='domain',predicate={'op':'and','args':hull+[{'poly':list(map(int,delta)),'relation':relation}]})).count())
                if all(bad):raise ValueError('projection needs a complete collision backend or strict discrete monotonicity')
                self.collision=dict(route='strict_discrete_monotonicity',difference=list(map(int,delta)),hull=[lo,hi],direction='increasing' if not bad[0] else 'decreasing',violating_counts=bad,complete=True)
            else:self.collision=dict(route='empty_source',complete=True)
        self.reflection=reflection
        self.population=ExactPopulation(dict(kind='domain',predicate=predicate,fields={field:self.polynomial}))

    def __getattr__(self,name):
        if name in {'cardinality','population_id','count','select','rank','page','sample','partition'}:return getattr(self.population,name)
        raise AttributeError(name)

    def summary(self):
        return dict(self.population.summary(),schema='pp-distinct-projection/1',specification=deepcopy(self.specification),
            identity='distinct projected value; least original parameter is its canonical owner',
            source_population_id=self.source.population_id,source_cardinality=self.source.cardinality,
            reflection=self.reflection,ordering='increasing canonical original parameter, not numeric value order')

    def _owners(self,value):
        if type(value) is not int:raise ValueError('integer projected value required')
        if len(self.polynomial)==1:
            return [self.source.select(0)['parameter']] if self.source.cardinality and value==self.polynomial[0] else []
        owners=[]
        for n in self.images.points(self.polynomial,value):
            if self.source.locate(parameter=n) is None:continue
            owners.append(n)
        return sorted(owners)

    def locate(self,value):
        owners=self._owners(value)
        if not owners:raise ValueError('value outside projected image')
        return self.population.locate(parameter=owners[0])

    def multiplicity(self,value):
        if len(self.polynomial)==1:return self.source.cardinality if type(value) is int and value==self.polynomial[0] else 0
        return len(self._owners(value))

    def evidence(self):
        return dict(source=self.source.evidence(),representatives=self.population.evidence(),reflection=self.reflection,
            collision_identity=(self.collision.get('identity',self.collision.get('route')) if self.collision else 'f(n)-f(m)=(n-m)*(a*(n+m)+b) for quadratic f'),collision_geometry=deepcopy(self.collision),execution_verified=False)


def _curve_predicate(node,variable):
    if type(node) is bool:return node
    if 'poly' in node:
        expr='0'
        for c in reversed(node['poly']):expr=f'({expr})*{variable}+({c})'
        return {('expr' if k=='poly' else k):(expr if k=='poly' else v) for k,v in node.items()}
    return dict(op=node['op'],args=[_curve_predicate(a,variable) for a in node['args']])


def symbolic_join(left,right,left_field,right_field):
    a,b=left.specification,right.specification
    if a['kind']!='domain' or b['kind']!='domain':raise ValueError('symbolic joins require parameter-domain populations')
    if left_field not in a['fields'] or right_field not in b['fields']:raise ValueError('existing polynomial join fields required')
    spec=dict(kind='curve',left=a['fields'][left_field],right=b['fields'][right_field],
        predicate={'op':'and','args':[_curve_predicate(a['predicate'],'x'),_curve_predicate(b['predicate'],'y')]})
    # Completeness is enforced by ExactPopulation; unsupported relations fail.
    return ExactPopulation(spec)
