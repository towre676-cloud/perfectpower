"""The complete two-orbit solution of x^2 + 7 = 2 y^2.

Completeness follows by strictly decreasing positive x under the inverse
unit whenever it remains positive. The finite terminal box is y <= 5.
This exact certificate replay is not a new Lean theorem.
"""
from math import isqrt

SEEDS=((1,2),(5,4))


def certificate():
    table=[]
    for y in range(6):
        n=2*y*y-7;x=isqrt(n) if n>=0 else None
        table.append(dict(y=y,rhs=n,floor_root=x,
                          seed=bool(x is not None and x>0 and x*x==n and 3*x-4*y<=0)))
    return dict(schema='pp-pell7-complete/1',D=2,norm=-7,unit=[3,2],
                seeds=[list(s) for s in SEEDS],terminal_y_max=5,terminal_table=table,
                completeness='strict positive-x inverse-unit descent',execution_verified=False)


def verify_certificate(c):
    """Independently replay the terminal square-root table and unit identity."""
    try:
        keys='schema D norm unit seeds terminal_y_max terminal_table completeness execution_verified'.split()
        if type(c) is not dict or set(c)!=set(keys):return False
        if c['schema']!='pp-pell7-complete/1' or c['execution_verified'] is not False:return False
        if c['completeness']!='strict positive-x inverse-unit descent':return False
        for k,v in [('D',2),('norm',-7),('terminal_y_max',5)]:
            if type(c[k]) is not int or c[k]!=v:return False
        if type(c['unit']) is not list or len(c['unit'])!=2 or any(type(x) is not int for x in c['unit']):return False
        u,v=c['unit']
        if [u,v]!=[3,2] or u*u-2*v*v!=1:return False
        if type(c['terminal_table']) is not list or len(c['terminal_table'])!=6:return False
        seeds=[]
        for y,row in enumerate(c['terminal_table']):
            if type(row) is not dict or set(row)!=set(('y','rhs','floor_root','seed')):return False
            n=2*y*y-7
            if type(row['y']) is not int or row['y']!=y or type(row['rhs']) is not int or row['rhs']!=n:return False
            x=row['floor_root']
            if n<0:
                if x is not None:return False
            elif type(x) is not int or x<0 or not x*x<=n<(x+1)*(x+1):return False
            root=bool(x is not None and x>0 and x*x==n and u*x-2*v*y<=0)
            if type(row['seed']) is not bool or row['seed']!=root:return False
            if root:seeds.append([x,y])
        listed=c['seeds']
        return (type(listed) is list and all(type(row) is list and len(row)==2 and
                all(type(x) is int for x in row) for row in listed) and listed==seeds)
    except (TypeError,ValueError,KeyError,IndexError,ArithmeticError):return False


def orbit(seed_index,n):
    if type(seed_index) is not int or seed_index not in (0,1):raise ValueError('seed index is zero or one')
    if type(n) is not int or not 0<=n<=100000:raise ValueError('orbit index must be in 0..100000')
    # Binary powering in Z[sqrt(2)] avoids a linear-size computation.
    def mul(a,b):return (a[0]*b[0]+2*a[1]*b[1],a[0]*b[1]+a[1]*b[0])
    factor=(3,2);power=(1,0)
    while n:
        if n&1:power=mul(power,factor)
        factor=mul(factor,factor);n//=2
    return mul(SEEDS[seed_index],power)


def address(x,y,*,step_limit=100000):
    """Unique signs, seed and nonnegative index, or None for a non-solution.

    Resource exhaustion raises; it is not interpreted as nonmembership.
    """
    if type(x) is not int or type(y) is not int:raise ValueError('integer coordinates required')
    if type(step_limit) is not int or not 0<=step_limit<=100000:raise ValueError('bounded nonnegative step limit required')
    if x*x+7!=2*y*y:return None
    a,b=abs(x),abs(y);n=0
    while 3*a-4*b>0:
        if n==step_limit:raise ValueError('descent step budget exhausted')
        a,b=3*a-4*b,3*b-2*a;n+=1
    if (a,b) not in SEEDS:raise AssertionError('complete terminal box contradicted')
    return dict(seed_index=SEEDS.index((a,b)),n=n,x_sign=1 if x>0 else -1,y_sign=1 if y>0 else -1)


def solutions(x_max):
    """All signed solutions with |x| <= x_max, using the complete family."""
    if type(x_max) is not int or not 0<=x_max<=10**1000:raise ValueError('bounded nonnegative integer x limit required')
    result=[]
    for a,b in SEEDS:
        while a<=x_max:
            result.extend((sx*a,sy*b) for sx in (-1,1) for sy in (-1,1))
            a,b=3*a+4*b,2*a+3*b
    return sorted(result)
