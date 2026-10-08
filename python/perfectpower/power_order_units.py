"""Exact free-unit lattice of a cubic power order inside a supplied maximal order.

Completeness is relative to the supplied maximal-order fundamental units.
The optional PARI caller supplies that external number-field theorem.
"""
from collections import deque
from fractions import Fraction as Q
from math import gcd
from .elliptic_two_descent import cubic_order, determinant, solve
from .divisor_square import WorkLimit
from . import polyalg as P
from .cubic_norm_transport import monic_model


def bezout(a,b):
    r,s,t=a,1,0; rr,ss,tt=b,0,1
    while rr:
        q=r//rr;r,rr=rr,r-q*rr;s,ss=ss,s-q*ss;t,tt=tt,t-q*tt
    return (r,s,t) if r>=0 else (-r,-s,-t)


def hermite_two(generators):
    """Column basis [(a,0),(b,g)] with a,g>0 and 0<=b<a."""
    g=0;bx=0
    for x,y in generators:
        d,s,t=bezout(g,y);bx=s*bx+t*x;g=d
    if not g:raise ValueError('full-rank exponent lattice required')
    a=0
    for x,y in generators:a=gcd(a,x-(y//g)*bx)
    if not a:raise ValueError('full-rank exponent lattice required')
    return [[a,0],[bx%a,g]]


def lattice_contains(basis,exponents):
    (a,_),(b,g)=basis;x,y=exponents
    return y%g==0 and (x-(y//g)*b)%a==0


def compile_binary_source(unit_packet,form,phi):
    """F(r,s) -> Norm(a*r-s*(h+k*theta)), in maximal-order coordinates."""
    if not isinstance(form,(list,tuple)) or len(form)!=4 or any(type(x)is not int for x in form):
        raise ValueError('four leading-first integer binary-cubic coefficients required')
    if not isinstance(phi,(list,tuple)) or len(phi)!=3 or any(type(x)is not int for x in phi) or phi[2] or not phi[1]:
        raise ValueError('linear integral generator h+k*theta required')
    a,b,c,d=form;h,k,_=phi;characteristic=monic_model(list(reversed(form)))
    f=unit_packet['polynomial'];basis=unit_packet['integral_basis']
    order=cubic_order(f,basis,unit_packet['field_discriminant']);m=order['power_order_index']
    relation=P.ZERO
    for i,v in enumerate(characteristic):relation=P.add(relation,P.scale(P.power(P.poly(phi),i),v))
    if P.divmod_poly(relation,P.poly(f))[1]!=P.ZERO:
        raise ValueError('linear generator does not satisfy the source norm polynomial')
    columns=[list(row)for row in zip(*[[Q(x)for x in r]for r in basis])]
    lattice=[]
    for element in ([a,0,0],[-h,-k,0]):
        coordinates=solve(columns,element)
        if any(x.denominator!=1 for x in coordinates):raise ArithmeticError('binary source outside maximal order')
        lattice.append([int(x)for x in coordinates])
    rows=[[int(m*x)for x in row]for row in columns]
    return dict(form=list(form),phi=list(phi),polynomial=f,integral_basis=basis,
                field_discriminant=unit_packet['field_discriminant'],index=m,
                source_lattice_columns=lattice,zero_row=rows[2],
                divisibility_rows=[dict(modulus=abs(m*k),row=rows[1]),
                    dict(modulus=abs(m*k*a),row=[k*x-h*y for x,y in zip(rows[0],rows[1])])],
                norm_multiplier=a*a,generator_characteristic_polynomial=characteristic,
                norm_identity='Norm(a*r-s*phi)=a^2*F(r,s)')


def encode_binary_source(packet,r,s):
    if type(r)is not int or type(s)is not int:raise ValueError('integer source pair required')
    first,second=packet['source_lattice_columns']
    return [r*x+s*y for x,y in zip(first,second)]


def recover_binary_source(packet,coordinates):
    if not isinstance(coordinates,(list,tuple))or len(coordinates)!=3 or any(type(x)is not int for x in coordinates):
        raise ValueError('three maximal-order integer coordinates required')
    dot=lambda row:sum(x*y for x,y in zip(row,coordinates))
    if dot(packet['zero_row']) or any(dot(test['row'])%test['modulus'] for test in packet['divisibility_rows']):
        raise ValueError('element outside exact binary source lattice')
    columns=list(zip(*[[Q(x)for x in row]for row in packet['integral_basis']]))
    u,v,w=[dot(row)for row in columns]
    h,k,_=packet['phi'];a=packet['form'][0]
    r=(u-h*v/k)/a;s=-v/k
    if w or r.denominator!=1 or s.denominator!=1:raise ArithmeticError('source lattice reverse domain disagrees')
    return [int(r),int(s)]


def unit_orbit_source(source,unit_packet,representative,exponents):
    """Exact signed unit-orbit extraction; no exponent or representative bound."""
    if source['polynomial']!=unit_packet['polynomial'] or source['integral_basis']!=unit_packet['integral_basis']:
        raise ValueError('source and unit coordinates disagree')
    if not isinstance(representative,(list,tuple))or len(representative)!=3 or any(type(x)is not int for x in representative):
        raise ValueError('three integer representative coordinates required')
    if not isinstance(exponents,(list,tuple))or len(exponents)!=2 or any(type(x)is not int or abs(x)>64 for x in exponents):
        raise ValueError('two signed exponents of absolute value at most 64')
    value=list(representative)
    def apply(A,x):return [sum(a*b for a,b in zip(row,x))for row in A]
    def product(A,B):return [[sum(A[i][j]*B[j][k]for j in range(3))for k in range(3)]for i in range(3)]
    for i,n in enumerate(exponents):
        A=unit_packet['power_order_unit_matrices' if n>=0 else 'power_order_unit_inverse_matrices'][i]
        n=abs(n)
        while n:
            if n&1:value=apply(A,value)
            n//=2
            if n:A=product(A,A)
    try:pair=recover_binary_source(source,value)
    except ValueError:pair=None
    a,b,c,d=source['form']
    return dict(coordinates=value,exponents=list(exponents),source_pair=pair,
                zero_constraint=sum(x*y for x,y in zip(source['zero_row'],value)),
                divisibility_residues=[sum(x*y for x,y in zip(test['row'],value))%test['modulus']for test in source['divisibility_rows']],
                source_value=None if pair is None else a*pair[0]**3+b*pair[0]**2*pair[1]+c*pair[0]*pair[1]**2+d*pair[1]**3)


def power_order_unit_lattice(polynomial,basis,field_discriminant,units,*,cell_limit=500000):
    if type(cell_limit) is not int or not 1<=cell_limit<=500000:
        raise ValueError('finite image cell limit from one through 500000')
    if not isinstance(units,(list,tuple)) or len(units)!=2 or any(len(u)!=3 for u in units):
        raise ValueError('two cubic fundamental units required')
    order=cubic_order(polynomial,basis,field_discriminant)
    m=order['power_order_index'];table=order['multiplication_table']
    if m>10000:raise ValueError('power-order index at most 10000 required')
    rows=[[Q(x)for x in r]for r in basis];columns=list(map(list,zip(*rows)))
    def coordinates(u):
        v=solve(columns,[Q(x)for x in u])
        if any(x.denominator!=1 for x in v):raise ValueError('unit outside integral basis')
        return tuple(int(x)for x in v)
    power_embedding=[coordinates([int(i==j)for i in range(3)])for j in range(3)]
    one=power_embedding[0];unit_coordinates=[coordinates(u)for u in units]
    def mul(a,b,mod=None):
        c=tuple(sum(a[i]*b[j]*table[i][j][k]for i in range(3)for j in range(3))for k in range(3))
        return c if mod is None else tuple(x%mod for x in c)
    def matrix(u):
        return [[sum(u[i]*table[i][j][k]for i in range(3))for j in range(3)]for k in range(3)]
    def inverse(u):
        M=matrix(u)
        if abs(determinant(M))!=1:raise ValueError('supplied generator is not an integral unit')
        v=solve(M,one)
        if any(x.denominator!=1 for x in v):raise ArithmeticError('nonintegral unit inverse')
        v=tuple(int(x)for x in v)
        if mul(u,v)!=one:raise ArithmeticError('unit inverse identity failed')
        return v
    inverses=[inverse(u)for u in unit_coordinates]
    inclusion=[]
    for row in columns:
        v=[m*x for x in row]
        if any(x.denominator!=1 for x in v):raise ArithmeticError('index does not clear integral basis')
        inclusion.append([int(x)for x in v])
    def belongs(state):
        return all(sum(row[j]*state[j]for j in range(3))%m==0 for row in inclusion)
    origin=tuple(x%m for x in one);labels={origin:(0,0)};queue=deque([origin]);relations=set()
    while queue:
        state=queue.popleft();label=labels[state]
        for i,u in enumerate(unit_coordinates):
            target=mul(state,u,m);candidate=(label[0]+int(i==0),label[1]+int(i==1))
            if target not in labels:
                if len(labels)>=cell_limit:raise WorkLimit('power-order unit residue image exceeds cell limit')
                labels[target]=candidate;queue.append(target)
            else:relations.add((candidate[0]-labels[target][0],candidate[1]-labels[target][1]))
    good=[label for state,label in labels.items()if belongs(state)]
    hnf=hermite_two(sorted(relations)+good)
    index=hnf[0][0]*hnf[1][1]
    if len(labels)!=index*len(good):raise ArithmeticError('unit index and residue count disagree')
    for state,label in labels.items():
        if lattice_contains(hnf,label)!=belongs(state):raise ArithmeticError('exponent lattice membership disagrees')
    def power(u,n):
        if n<0:u=inverse(u);n=-n
        value=one
        while n:
            if n&1:value=mul(value,u)
            n//=2
            if n:u=mul(u,u)
        return value
    integral_units=[];integral_inverses=[];action=[];inverse_action=[]
    for x,y in hnf:
        u=mul(power(unit_coordinates[0],x),power(unit_coordinates[1],y));v=inverse(u)
        out=[]
        for element in (u,v):
            c=[sum(row[j]*element[j]for j in range(3))for row in columns]
            if any(x.denominator!=1 for x in c):raise ArithmeticError('compiled unit outside power order')
            out.append([int(x)for x in c])
        integral_units.append(out[0]);integral_inverses.append(out[1])
        action.append(matrix(u));inverse_action.append(matrix(v))
    return dict(schema='pp-cubic-power-order-units/1',polynomial=polynomial,
                integral_basis=basis,field_discriminant=field_discriminant,
                maximal_order_units=units,power_order_index=m,
                multiplication_table=table,inclusion_matrix=inclusion,
                power_basis_embedding_columns=[list(v)for v in power_embedding],
                residue_image_size=len(labels),power_order_residue_units=len(good),
                free_unit_index=index,exponent_hnf_columns=hnf,
                power_order_units=integral_units,power_order_unit_inverses=integral_inverses,
                power_order_unit_matrices=action,power_order_unit_inverse_matrices=inverse_action,
                kernel_relations=[list(v)for v in sorted(relations)],
                residue_states=[dict(coordinates=list(state),exponents=list(label),
                                     belongs_to_power_order=belongs(state))for state,label in labels.items()],
                completeness='relative to supplied complete maximal-order fundamental units',
                lean_unit_generation_proof=False)
