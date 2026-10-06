"""Exact deformation, root-motion and nodal-residue explanations for families."""
from math import comb
from fractions import Fraction as Q
from . import polyalg as P
from .rational_functions import RationalFunction as RF, AlgebraBudget, solve_many
from .curve_families import encode_matrix
from . import field_polynomials as F


def fresh(family):
    budget=AlgebraBudget(**family.limits)
    return [RF.parse(a,budget) for a in family.f],budget


def deformation(family):
    f,budget=fresh(family);m=len(f)-1;zero=f[0].coerce(0)
    dx=F.derivative(f);orbit=[dx,F.add([zero]+dx,F.scale(f,-m))]
    orbit=[r+[zero]*(m-len(r)) for r in orbit];dt=[a.derivative() for a in f[:-1]]
    pivots=next(( (i,j) for i in range(m) for j in range(i+1,m)
        if orbit[0][i]*orbit[1][j]-orbit[0][j]*orbit[1][i]),None)
    if pivots is None:raise AssertionError('smooth polynomial has deficient affine orbit')
    speeds=solve_many([[o[i] for o in orbit] for i in pivots],[[dt[i]] for i in pivots])
    speeds=[r[0] for r in speeds]
    residual=[dt[i]-sum((speeds[j]*orbit[j][i] for j in range(2)),zero) for i in range(m)]
    if any(residual[i] for i in pivots):raise AssertionError('affine quotient projection failed')
    answer=dict(schema='pp-curve-deformation/1',coordinate_only_generic=not any(residual),
        affine_orbit_generators=encode_matrix(orbit),coordinate_flow=[a.packet() for a in speeds],
        essential_tangent=[a.packet() for a in residual],pivot_coefficients=list(pivots),
        pivot_minor=(orbit[0][pivots[0]]*orbit[1][pivots[1]]-orbit[0][pivots[1]]*orbit[1][pivots[0]]).packet(),
        quotient_dimension=m-2,identity='P_t = flow_0 P_x + flow_1 (x P_x-m P) + essential_tangent',
        chart='monic polynomial with distinguished branch point at infinity; affine x changes',
        execution_verified=False,scope='exact generic tangent quotient on the nonzero pivot-minor chart; its chart poles are not curve degenerations; coordinate-only means locally trivial after integrating the affine flow, not a global rational isomorphism or preservation of integer coordinates')
    center=-f[-2]/m;centered=F.shift(f,center);constant=centered[0]
    if not any(centered[1:-1]):
        if not constant:raise AssertionError('singular centered binomial')
        rows=[]
        for i in range(family.dimension):
            row=[zero for _ in range(family.dimension)]
            for j in range(i+1):row[j]=comb(i,j)*F.power([-center],i-j)[0]
            rows.append(row)
        inverse=[]
        for i in range(family.dimension):
            row=[zero for _ in range(family.dimension)]
            for j in range(i+1):row[j]=comb(i,j)*F.power([center],i-j)[0]
            inverse.append(row)
        connection=[[RF.parse(a,budget) for a in row] for row in family.connection]
        derivative=[[a.derivative() for a in row] for row in rows]
        ta=F.matrix_product(rows,connection)
        transformed=F.matrix_product([[a+b for a,b in zip(r,s)] for r,s in zip(derivative,ta)],inverse)
        weights=[Q(i+1,m)-Q(1,2) for i in range(family.dimension)]
        expected=[[w*constant.derivative()/constant if i==j else zero for j in range(family.dimension)] for i,w in enumerate(weights)]
        if transformed!=expected:raise AssertionError('centered scaling connection mismatch')
        answer['scaling_explanation']=dict(center=center.packet(),constant=constant.packet(),
            substitution='x=center(t)+constant(t)^(1/m) u; y=constant(t)^(1/2) v; v^2=u^m+1',
            centered_differential_rows=encode_matrix(rows),weights=list(map(str,weights)),
            centered_connection=encode_matrix(transformed),connection_identity_checked=True,
            branch_scope='local choices of fractional powers away from constant=0; marking can have finite monodromy')
    answer['algebra_work']=budget.work
    return answer


def root_motion(family):
    f,budget=fresh(family);dt=[a.derivative() for a in f];dx=F.derivative(f)
    inverse=F.polynomial_inverse(dx,f)
    velocity=F.divide(F.scale(F.product(dt,inverse),-1),f)[1]
    replay=F.add(dt,F.product(dx,velocity));quotient,remainder=F.divide(replay,f)
    if any(remainder):raise AssertionError('root velocity identity failed')
    return dict(schema='pp-root-motion/1',velocity=[a.packet() for a in velocity],
        bezout_inverse=[a.packet() for a in inverse],identity_quotient=[a.packet() for a in quotient],
        identity='P_t+P_x V = identity_quotient P; r_prime=V(r,t) for every simple root',
        discriminant=list(map(str,family.discriminant)),algebra_work=budget.work,
        execution_verified=False,scope='exact simultaneous root velocities in Q(t)[x]/P; no root ordering, braid or numerical root enclosure claimed')


def _component(family,modulus,budget):
    algebra=F.SquarefreeAlgebra(modulus,budget);tau=algebra.element([0,1])
    original=[RF.parse(a,budget) for a in family.f]
    f=[algebra.rational_function(a) for a in original];dx=F.derivative(f)
    common,_,_=F.extended_gcd(f,dx)
    if len(common)!=2:raise AssertionError('simple discriminant root did not give one double root')
    collision=-common[0]/common[1]
    if F.evaluate(f,collision) or F.evaluate(dx,collision):raise AssertionError('collision root identity failed')
    curvature=F.evaluate(F.derivative(dx),collision)
    transverse=F.evaluate([algebra.rational_function(a.derivative()) for a in original],collision)
    curvature.inverse();transverse.inverse()
    # Multiplying by the component modulus cancels each simple pole in this
    # component. Evaluation divided by its derivative gives the residue.
    polynomial=RF(modulus,budget=budget);dmod=algebra.element(P.derivative(modulus))
    residue=[[algebra.rational_function(RF.parse(a,budget)*polynomial)/dmod for a in row] for row in family.connection]
    rank=F.matrix_rank(residue);square=F.matrix_product(residue,residue)
    u=[algebra.element([1])]
    for _ in range(family.dimension-1):u.append(u[-1]*collision)
    evaluation_image=all(residue[i][j]==u[i]*residue[0][j] for i in range(family.dimension) for j in range(family.dimension))
    return dict(parameter_modulus=list(map(str,modulus)),root_count=P.degree(modulus),
        collision_x=collision.packet(),P_xx_at_collision=curvature.packet(),P_t_at_collision=transverse.packet(),
        residue=encode_matrix(residue),rank=rank,square_zero=not any(v for row in square for v in row),
        evaluation_vector=[a.packet() for a in u],image_is_collision_evaluation_line=evaluation_image,
        local_model='one transverse ordinary node; residue in the supplied de Rham frame',
        monodromy_scope='rank-one nilpotent residue explains local unipotent behavior; no exact integral homology matrix claimed')


def collisions(family):
    budget=AlgebraBudget(**family.limits);disc=P.monic(family.discriminant)
    repeated=P.gcd_poly(disc,P.derivative(disc));squarefree=P.exact_div(disc,repeated)
    simple=P.exact_div(squarefree,P.gcd_poly(squarefree,repeated))
    components=[];pending=[simple] if P.degree(simple)>0 else []
    while pending:
        modulus=pending.pop(0)
        try:components.append(_component(family,modulus,budget))
        except F.NonUnit as error:
            factor=P.gcd_poly(modulus,error.factor)
            if not 0<P.degree(factor)<P.degree(modulus):raise AssertionError('collision algebra cannot be split') from error
            pending[0:0]=[factor,P.exact_div(modulus,factor)]
    omitted=P.exact_div(squarefree,simple)
    if sum(c['root_count'] for c in components)!=P.degree(simple):raise AssertionError('collision coverage mismatch')
    return dict(schema='pp-collision-residues/1',discriminant=list(map(str,family.discriminant)),
        simple_discriminant_part=list(map(str,simple)),components=components,
        omitted_multiple_discriminant_part=list(map(str,omitted)),
        covered_simple_roots=P.degree(simple),algebra_work=budget.work,execution_verified=False,
        scope='all simple finite discriminant roots, represented exactly in split squarefree Q-algebras; multiple discriminant roots and degeneration at infinity need separate local analysis')
