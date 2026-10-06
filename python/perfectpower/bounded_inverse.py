"""Complete integer quadratic design in a finite box with linear constraints."""
from fractions import Fraction as Q
from . import exact_linear as E
from .weighted_hodge import metric
from .observable_machine import _q
from .divisor_square import WorkLimit


def closest_in_box(matrix, observation, target, lower, upper, mass=None, inequalities=(), *, node_limit=100000):
    a=E.matrix(tuple(tuple(_q(x) for x in row) for row in matrix));n=len(a[0]);rhs=tuple(map(_q,observation));target=tuple(map(_q,target))
    lo,hi=tuple(lower),tuple(upper)
    if not 1<=n<=12 or len(rhs)!=len(a) or any(len(v)!=n for v in (target,lo,hi)):
        raise ValueError('matching dimensions with 1 through 12 design variables required')
    if any(type(x) is not int or abs(x).bit_length()>4096 for x in lo+hi) or any(x>y for x,y in zip(lo,hi)):
        raise ValueError('ordered finite integer bounds required')
    if type(node_limit) is not int or node_limit<1:raise ValueError('positive node budget required')
    m=metric(E.identity(n) if mass is None else [[_q(x) for x in row] for row in mass],n)
    constraints=[(tuple(row),'=',value) for row,value in zip(a,rhs)]
    if len(inequalities)>128:raise ValueError('at most 128 additional linear constraints')
    for item in inequalities:
        if set(item)!={'coefficients','relation','rhs'} or item['relation'] not in ('<=','>=','='):
            raise ValueError('linear coefficients, relation <=/>=/= and rhs required')
        row=tuple(map(_q,item['coefficients']))
        if len(row)!=n:raise ValueError('constraint dimension mismatch')
        constraints.append((row,item['relation'],_q(item['rhs'])))
    # Exact unconstrained free-coordinate minima, via Schur complements.
    schur={}
    for k in range(1,n+1):
        ff=tuple(tuple(m[i][j] for j in range(k)) for i in range(k))
        if k<n:
            fu=tuple(tuple(m[i][j] for j in range(k,n)) for i in range(k))
            uu=tuple(tuple(m[i][j] for j in range(k,n)) for i in range(k,n))
            repair=E.multiply(E.multiply(fu,E.inverse(uu)),E.transpose(fu))
            ff=tuple(tuple(x-y for x,y in zip(r,s)) for r,s in zip(ff,repair))
        schur[k]=ff
    best=None;winners=[];nodes=0;feasibility_prunes=0;energy_prunes=0
    def feasible(prefix):
        k=len(prefix)
        for row,relation,b in constraints:
            fixed=sum(c*v for c,v in zip(row,prefix));lower=fixed;upper=fixed
            for c,l,h in zip(row[k:],lo[k:],hi[k:]):
                lower+=c*(l if c>=0 else h);upper+=c*(h if c>=0 else l)
            if (relation=='=' and not lower<=b<=upper) or (relation=='<=' and lower>b) or (relation=='>=' and upper<b):return False
        return True
    def ordered(l,h,center):
        left=min(h,center.numerator//center.denominator);right=max(l,left+1)
        while left>=l or right<=h:
            if right>h or (left>=l and center-left<=right-center):yield left;left-=1
            else:yield right;right+=1
    def visit(prefix):
        nonlocal best,winners,nodes,feasibility_prunes,energy_prunes
        nodes+=1
        if nodes>node_limit:raise WorkLimit('bounded inverse design exceeds node budget; no optimum returned')
        if not feasible(prefix):feasibility_prunes+=1;return
        k=len(prefix)
        energy=Q(0)
        if k:
            delta=tuple(Q(x)-y for x,y in zip(prefix,target));energy=sum(x*y for x,y in zip(delta,E.apply(schur[k],delta)))
            if best is not None and energy>best:energy_prunes+=1;return
        if k==n:
            if best is None or energy<best:best=energy;winners=[]
            if energy==best:winners.append(tuple(prefix))
            return
        for value in ordered(lo[k],hi[k],target[k]):visit(prefix+(value,))
    visit(())
    return dict(schema='pp-bounded-inverse/1',status='OPTIMAL_BOUNDED_INTEGER_DESIGNS' if winners else 'NO_FEASIBLE_DESIGN',
        matrix=a,observation=rhs,target=target,metric=m,lower=lo,upper=hi,inequalities=list(inequalities),
        minimizers=sorted(winners),minimum_energy=best,nodes=nodes,feasibility_prunes=feasibility_prunes,
        energy_prunes=energy_prunes,complete=True,execution_verified=False,
        scope='all closest integer designs in the supplied finite box satisfying every exact linear constraint')


def verify_bounded_design(receipt,node_limit=100000):
    try:
        rebuilt=closest_in_box(receipt['matrix'],receipt['observation'],receipt['target'],receipt['lower'],receipt['upper'],
            receipt['metric'],receipt['inequalities'],node_limit=node_limit)
        from .catalogue import encoded
        return encoded(rebuilt)==encoded(receipt)
    except (ValueError,TypeError,KeyError,ArithmeticError):return False
