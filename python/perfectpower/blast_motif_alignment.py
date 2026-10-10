"""Exact product-DAG alignment families with required conserved literal motifs."""
from collections import Counter
from functools import lru_cache
from .blast_alignment import AlignmentFamily, ZERO, add, subtract, score, sequence
from .divisor_square import WorkLimit


class MotifAlignmentFamily:
    """Require all motifs to occur in contiguous matched diagonal columns.

    Gaps or mismatches reset motif-prefix memory. Previously found motifs stay
    found. This is a path constraint, not a post-hoc feature-count filter.
    """
    def __init__(self, query, subject, motifs, *, work_limit=2000000, term_limit=250000):
        self.base = AlignmentFamily(query, subject, work_limit=work_limit, term_limit=term_limit)
        self.motifs = tuple(sorted(set(sequence(m, limit=16) for m in motifs)))
        if not 1 <= len(self.motifs) <= 4 or any(not m for m in self.motifs):
            raise ValueError('one through four nonempty literal motifs of length <=16 required')
        if any(type(x) is not int or x < 1 for x in (work_limit, term_limit)):
            raise ValueError('positive product-DAG budgets required')
        self.prefixes = sorted({''} | {m[:i] for m in self.motifs for i in range(1,len(m)+1)}, key=lambda x:(len(x),x))
        self.target_mask = (1<<len(self.motifs))-1
        self.work = self.retained_terms = 0
        self.work_limit, self.term_limit = work_limit, term_limit
        self.suffix = lru_cache(None)(self._build)
        self.terms = dict(self.suffix(0,0,'M','',0))

    def transitions(self, i, j, previous, prefix, mask):
        for operation, u, v, increment in self.base.transitions(i,j,previous):
            next_prefix, next_mask = '', mask
            if operation == 'M' and increment[0]:
                word = prefix+self.base.query[i]
                next_prefix = max((p for p in self.prefixes if word.endswith(p)),key=len)
                for k, motif in enumerate(self.motifs):
                    if word.endswith(motif):
                        next_mask |= 1<<k
            yield operation,u,v,next_prefix,next_mask,increment

    def _build(self,i,j,previous,prefix,mask):
        if i==len(self.base.query) and j==len(self.base.subject):
            return ((ZERO,1),) if mask==self.target_mask else ()
        out=Counter()
        for operation,u,v,next_prefix,next_mask,increment in self.transitions(i,j,previous,prefix,mask):
            for f,c in self.suffix(u,v,operation,next_prefix,next_mask):
                self.work+=1
                if self.work>self.work_limit:
                    raise WorkLimit('conserved-motif product-DAG work budget exhausted')
                out[add(f,increment)]+=c
        self.retained_terms+=len(out)
        if self.retained_terms>self.term_limit:
            raise WorkLimit('conserved-motif product-DAG term budget exhausted')
        return tuple(sorted(out.items()))

    @property
    def count(self):return sum(self.terms.values())

    def select(self,feature,index=0):
        feature=tuple(feature)
        if type(index) is not int or not 0<=index<self.terms.get(feature,0):
            raise ValueError('rank outside motif-constrained fibre')
        i=j=mask=0;previous,prefix,remaining,operations='M','',feature,[]
        while i<len(self.base.query) or j<len(self.base.subject):
            for operation,u,v,next_prefix,next_mask,increment in self.transitions(i,j,previous,prefix,mask):
                child=subtract(remaining,increment)
                count=dict(self.suffix(u,v,operation,next_prefix,next_mask)).get(child,0)
                if index>=count:index-=count
                else:
                    operations.append(operation)
                    i,j,previous,prefix,mask,remaining=u,v,operation,next_prefix,next_mask,child
                    break
            else:raise AssertionError('motif fibre unranking failed')
        return self.base.render(''.join(operations))

    def packet(self):
        return {'schema':'pp-blast-motif-alignment/1','query':self.base.query,'subject':self.base.subject,
                'motifs':list(self.motifs),'terms':[[list(f),c] for f,c in sorted(self.terms.items())],
                'alignment_count':self.count,'work':self.work,'complete':True,'kernel_checked':False,
                'scope':'global affine alignment paths containing every supplied motif in contiguous exact paired columns'}
