"""Exact descriptive statistics for declared Dresden interval corpora.

These are population summaries of supplied model outputs, not inference about
ancient observations or a new astronomical visibility calculation.
"""
from collections import Counter
from fractions import Fraction
from .dresden import _integer


def interval_distribution(days, span, start=0, end=None):
    days=list(days)
    end=len(days) if end is None else end
    for v in (span,start,end):_integer(v)
    if span<1 or start<0 or end>len(days) or end-start<=span:
        raise ValueError('window must contain more appearances than month span')
    if any(not isinstance(d,int) or isinstance(d,bool) for d in days) or any(a>=b for a,b in zip(days,days[1:])):
        raise ValueError('strictly increasing integer day sequence required')
    histogram=Counter(days[i+span]-days[i] for i in range(start,end-span))
    return [{'days':d,'count':c} for d,c in sorted(histogram.items())]


def distribution_summary(rows):
    rows=list(rows)
    if not rows:raise ValueError('nonempty empirical count histogram required')
    for r in rows:
        _integer(r['days']);_integer(r['count'])
        if r['count']<=0:raise ValueError('positive empirical counts required')
    count=sum(r['count'] for r in rows)
    mean=Fraction(sum(r['days']*r['count'] for r in rows),count)
    variance=Fraction(sum(r['days']**2*r['count'] for r in rows),count)-mean**2
    ordered=sorted(rows,key=lambda r:r['days'])
    def quantile(p):
        rank=max(1,(count*p.numerator+p.denominator-1)//p.denominator)
        acc=0
        for r in ordered:
            acc+=r['count']
            if acc>=rank:return r['days']
        raise AssertionError('invalid histogram')
    return {'count':count,'mean':str(mean),'variance':str(variance),
            'median':quantile(Fraction(1,2)),
            'central95':[quantile(Fraction(1,40)),quantile(Fraction(39,40))],
            'scope':'descriptive population summaries; central range is not a confidence interval'}


def total_variation(a,b,a_offset=0,b_offset=0):
    """Exact distance after independently declared integer centering offsets."""
    _integer(a_offset);_integer(b_offset)
    A=Counter();B=Counter()
    for rows,hist,offset in ((a,A,a_offset),(b,B,b_offset)):
        for r in rows:
            _integer(r['days']);_integer(r['count'])
            if r['count']<=0:raise ValueError('positive empirical counts required')
            hist[r['days']-offset]+=r['count']
    na,nb=sum(A.values()),sum(B.values())
    if not na or not nb:raise ValueError('nonempty distributions required')
    return str(sum((abs(Fraction(A[d],na)-Fraction(B[d],nb)) for d in set(A)|set(B)),Fraction(0))/2)
