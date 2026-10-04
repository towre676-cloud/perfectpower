"""Exact generated matrix algebras, commutants and double-commutant gaps.

Adapted from the large monograph's DAO switch atlas. Closure is checked by
words and multiplication coordinates, never inferred from matching ranks.
Double-commutant equality is not relabeled semisimplicity or a ring isomorphism.
"""
from fractions import Fraction as Q
from . import exact_linear as E
from .divisor_square import WorkLimit


def _flat(a):return tuple(x for row in a for x in row)


def _matrix(a):
    raw=tuple(tuple(row) for row in a)
    if any(type(x) not in (int,Q,str) for row in raw for x in row):raise ValueError('exact rational entries required')
    m=E.matrix([[Q(x) for x in row] for row in raw]);n=len(m)
    if n>6 or any(len(row)!=n for row in m):raise ValueError('square operators of dimension at most six required')
    if any(max(abs(x.numerator).bit_length(),x.denominator.bit_length())>8192 for row in m for x in row):raise WorkLimit('operator coefficient bit budget exceeded')
    return m


def _family(operators):
    operators=tuple(map(_matrix,operators))
    if not 1<=len(operators)<=36 or any(len(a)!=len(operators[0]) for a in operators):raise ValueError('matching nonempty operator family required')
    return operators


def generated_algebra(operators,*,product_limit=4096):
    operators=_family(operators);n=len(operators[0])
    if type(product_limit) is not int or product_limit<1:raise ValueError('positive product budget required')
    basis=[E.identity(n)];words=[[]];position=0;products=0
    def spend():
        nonlocal products
        products+=1
        if products>product_limit:raise WorkLimit('complete operator closure exceeds product budget')
    while position<len(basis):
        for j,g in enumerate(operators):
            spend();value=_matrix(E.multiply(g,basis[position]))
            if E.solve(E.transpose(tuple(map(_flat,basis))),_flat(value)) is None:
                basis.append(value);words.append([j]+words[position])
        position+=1
    columns=E.transpose(tuple(map(_flat,basis)));closure=[]
    for b in basis:
        row=[]
        for g in operators:
            spend();coordinates=E.solve(columns,_flat(E.multiply(g,b)))
            if coordinates is None:raise AssertionError('generated algebra is not closed')
            row.append(coordinates)
        closure.append(row)
    return {'operators':operators,'basis':basis,'basis_words':words,'left_generator_products':closure,
        'dimension':len(basis),'products_checked':products,'field':'Q','execution_verified':False}


def verify_algebra(receipt,*,product_limit=4096):
    """Check words, independence and all generator products; no closure discovery."""
    try:
        if type(product_limit) is not int or product_limit<1 or receipt['execution_verified'] is not False or receipt['field']!='Q':return False
        operators=_family(receipt['operators']);n=len(operators[0]);basis=tuple(map(_matrix,receipt['basis']));r=len(basis)
        if not 1<=r<=n*n or any(len(b)!=n for b in basis) or receipt['dimension']!=r:return False
        if E.rank(tuple(map(_flat,basis)))!=r or len(receipt['basis_words'])!=r or len(receipt['left_generator_products'])!=r:return False
        if 2*r*len(operators)>product_limit or receipt['products_checked']!=2*r*len(operators):return False
        for b,word in zip(basis,receipt['basis_words']):
            if len(word)>n*n or any(type(i) is not int or not 0<=i<len(operators) for i in word):return False
            value=E.identity(n)
            for j in reversed(word):value=E.multiply(operators[j],value)
            if value!=b:return False
        if basis[0]!=E.identity(n) or receipt['basis_words'][0]!=[]:return False
        for b,row in zip(basis,receipt['left_generator_products']):
            if len(row)!=len(operators):return False
            for g,coordinates in zip(operators,row):
                coordinates=tuple(Q(x) for x in coordinates)
                if len(coordinates)!=r:return False
                rebuilt=tuple(tuple(sum(c*t[i][j] for c,t in zip(coordinates,basis)) for j in range(n)) for i in range(n))
                if rebuilt!=E.multiply(g,b):return False
        return True
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def algebra_membership(receipt,target):
    if not verify_algebra(receipt):raise ValueError('invalid algebra certificate')
    target=_matrix(target);basis=tuple(map(_matrix,receipt['basis']));n=len(basis[0])
    if len(target)!=n:raise ValueError('target dimension mismatch')
    rows=tuple(map(_flat,basis));coefficients=E.solve(E.transpose(rows),_flat(target))
    if coefficients is not None:return {'status':'IN_GENERATED_ALGEBRA','target':target,'coordinates':coefficients}
    v=next(v for v in E.kernel(rows) if sum(x*y for x,y in zip(v,_flat(target))))
    return {'status':'OUTSIDE_GENERATED_ALGEBRA','target':target,'annihilator':v,'nonzero_pairing':sum(x*y for x,y in zip(v,_flat(target)))}


def verify_membership(receipt,result):
    try:
        if not verify_algebra(receipt):return False
        target=_matrix(result['target']);basis=tuple(map(_matrix,receipt['basis']));n=len(basis[0])
        if len(target)!=n:return False
        if result['status']=='IN_GENERATED_ALGEBRA':
            c=tuple(Q(x) for x in result['coordinates'])
            return len(c)==len(basis) and tuple(sum(x*y for x,y in zip(c,column)) for column in zip(*map(_flat,basis)))==_flat(target)
        if result['status']!='OUTSIDE_GENERATED_ALGEBRA':return False
        v=tuple(Q(x) for x in result['annihilator'])
        pairing=sum(x*y for x,y in zip(v,_flat(target)))
        return len(v)==n*n and pairing!=0 and pairing==Q(result['nonzero_pairing']) and all(sum(x*y for x,y in zip(v,_flat(b)))==0 for b in basis)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False


def _commutation_rows(operators):
    n=len(operators[0]);rows=[]
    for a in operators:
        for i in range(n):
            for j in range(n):
                row=[Q(0)]*(n*n)
                for k in range(n):row[i*n+k]+=a[k][j];row[k*n+j]-=a[i][k]
                rows.append(row)
    return rows


def _verify_commutant(operators,result):
    n=len(operators[0]);basis=tuple(map(_matrix,result['basis']));rows=_commutation_rows(operators)
    if any(len(b)!=n for b in basis):return False
    dimension=n*n-E.rank(rows)
    return result['dimension']==dimension and len(basis)==dimension and E.rank(tuple(map(_flat,basis)))==dimension and all(E.multiply(b,a)==E.multiply(a,b) for b in basis for a in operators)


def algebra_profile(operators):
    algebra=generated_algebra(operators);operators=tuple(map(_matrix,algebra['operators']))
    commutant=E.intertwiner_space(operators,operators);double=E.intertwiner_space(commutant['basis'],commutant['basis'])
    gap=None
    if double['dimension']!=algebra['dimension']:
        gap=next(result for b in double['basis'] if (result:=algebra_membership(algebra,b))['status']=='OUTSIDE_GENERATED_ALGEBRA')
    return {'algebra':algebra,'commutant':commutant,'bicommutant':double,'gap_witness':gap,
        'status':'DOUBLE_COMMUTANT_CLOSED' if gap is None else 'STRICT_BICOMMUTANT_ENLARGEMENT',
        'execution_verified':False,'scope':'exact supplied rational matrix algebra; no semisimplicity or ring-isomorphism claim'}


def verify_profile(receipt):
    try:
        algebra=receipt['algebra']
        if receipt['execution_verified'] is not False or not verify_algebra(algebra):return False
        operators=tuple(map(_matrix,algebra['operators']));c=receipt['commutant'];d=receipt['bicommutant']
        if not _verify_commutant(operators,c) or not _verify_commutant(tuple(map(_matrix,c['basis'])),d):return False
        if algebra['dimension']==d['dimension']:return receipt['status']=='DOUBLE_COMMUTANT_CLOSED' and receipt['gap_witness'] is None
        gap=receipt['gap_witness'];target=_matrix(gap['target']);commuters=tuple(map(_matrix,c['basis']))
        return receipt['status']=='STRICT_BICOMMUTANT_ENLARGEMENT' and verify_membership(algebra,gap) and all(E.multiply(target,b)==E.multiply(b,target) for b in commuters)
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError):return False
