"""Reusable complete integer fibres, with isolated replayable evidence."""
from copy import deepcopy
from .residue_cover import integer_polynomial
from .sturm_fibres import root_certificate,verify_roots
from .divisor_square import WorkLimit

class IntegerImageIndex:
    def __init__(self, *, capacity=256):
        if type(capacity) is not int or capacity<1: raise ValueError('positive cache capacity required')
        self.capacity=capacity;self._fibres={};self.hits=0;self.misses=0;self.nodes_constructed=0

    def fibre(self,coefficients,*,value=0,node_limit=100000):
        if type(value) is not int or abs(value).bit_length()>16384: raise ValueError('bounded integer target required')
        if type(node_limit) is not int or node_limit<1:raise ValueError('positive node budget required')
        f=list(integer_polynomial(coefficients));f[0]-=value;key=integer_polynomial(f)
        if key in self._fibres:
            certificate=self._fibres[key]
            if certificate['nodes_checked']>node_limit:raise WorkLimit('cached fibre exceeds caller transcript budget')
            self.hits+=1
        else:
            certificate=root_certificate(key,node_limit=node_limit)
            if not verify_roots(certificate,node_limit=node_limit):raise ArithmeticError('invalid complete fibre')
            if len(self._fibres)>=self.capacity:del self._fibres[next(iter(self._fibres))]
            self._fibres[key]=deepcopy(certificate);self.misses+=1;self.nodes_constructed+=certificate['nodes_checked']
        return deepcopy(certificate)

    def points(self,coefficients,value,*,node_limit=100000):
        return self.fibre(coefficients,value=value,node_limit=node_limit)['roots']

    def statistics(self):
        return {'cached_fibres':len(self._fibres),'hits':self.hits,'misses':self.misses,'nodes_constructed':self.nodes_constructed}
