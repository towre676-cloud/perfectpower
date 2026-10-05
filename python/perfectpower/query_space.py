"""Compile a curve once; reuse its exact charts for queries and integer fibres."""
import json
from .polynomial_charts import parameterize_relation,evaluate_parameterization
from .curve_queries import _query_prepared_curve
from .integer_image_index import IntegerImageIndex

class CurveSpace:
    def __init__(self,left,right,*,node_limit=100000,period_limit=65536,algebra_limit=2000000,image_capacity=256):
        generator=parameterize_relation(left,right,node_limit=node_limit,period_limit=period_limit,algebra_limit=algebra_limit)
        self._compiled=json.dumps(generator,sort_keys=True)
        self.images=IntegerImageIndex(capacity=image_capacity);self.queries=0

    @property
    def generator(self):
        return json.loads(self._compiled)

    def query(self,predicate=True,*,objective=None,sense='min',point_limit=128,node_limit=100000,
              period_limit=65536,work_limit=1000000,algebra_limit=2000000):
        result=_query_prepared_curve(self.generator,predicate,objective=objective,sense=sense,point_limit=point_limit,
                                     node_limit=node_limit,period_limit=period_limit,work_limit=work_limit,algebra_limit=algebra_limit)
        self.queries+=1
        return result

    def evaluate(self,t,*,node_limit=100000):
        return evaluate_parameterization(self.generator,t,node_limit=node_limit,image_index=self.images)

    def statistics(self):
        return {'compilations':1,'queries':self.queries,'integer_images':self.images.statistics()}
