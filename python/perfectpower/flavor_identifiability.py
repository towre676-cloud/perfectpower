"""Exact stationarity codimension and allowed-deformation response.

This analyzes the declared CP-even scalar polynomial space. It does not
derive a UV interaction or identify its scalar coefficient with a CKM observable.
"""
from fractions import Fraction as Q
from . import polyalg as P,exact_linear as E
from .cyclotomic_vacuum import cosine_polynomials,real_cyclotomic_polynomial,cyclotomic_polynomial
from .flavor_completion import selected_potential,yukawa_operator_basis
from .quotient_algebra import QuotientAlgebra
from .cyclotomic_real import real_interval


def _evaluate(polynomial,x):
    value=x.algebra.element(0)
    for c in reversed(polynomial):value=value*x+c
    return value


def stationarity_space(max_harmonic=12):
    if type(max_harmonic) is not int or not 1<=max_harmonic<=24:raise ValueError('harmonic degree 1 through 24 required')
    carrier=real_cyclotomic_polynomial(60);degree=P.degree(carrier)
    basis=[P.ONE]+cosine_polynomials(max_harmonic)[1:]
    columns=[P.divmod_poly(P.derivative(p),carrier)[1] for p in basis]
    matrix=tuple(tuple(col[i] if i<len(col) else Q(0) for col in columns) for i in range(degree))
    kernel=E.kernel(matrix);rank=E.rank(matrix)
    if any(any(E.apply(matrix,v)) for v in kernel):raise AssertionError('stationarity kernel replay')
    return dict(schema='pp-flavor-stationarity-space/1',carrier=list(map(str,carrier)),
        basis=[list(map(str,p)) for p in basis],constraint_matrix=matrix,rank=rank,
        coefficient_dimension=len(basis),stationary_subspace_dimension=len(basis)-rank,kernel_basis=kernel,
        meaning='rational CP-even harmonic coefficients preserve every Psi60 carrier root iff their vector is in this kernel',
        scope='stationarity in a declared finite polynomial space, not global vacuum selection or UV dynamics',execution_verified=False)


def allowed_linear_response(lock=0,embedding=11,bits=80):
    if type(embedding) is not int or __import__('math').gcd(embedding,60)!=1:raise ValueError('primitive embedding index required')
    algebra=QuotientAlgebra(cyclotomic_polynomial(60));z=algebra.element([0,1])**embedding;x=z+z**-1
    potential=selected_potential(lock);derivative=P.derivative(potential)
    force=_evaluate(derivative,x);curvature=_evaluate(P.derivative(derivative),x)
    if force!=algebra.element(0):raise AssertionError('reference is not stationary')
    delta_x=-curvature.inverse()  # V_epsilon(x)=V_0(x)+epsilon*x.
    coefficient=algebra.element(1)-z**12-z**-12
    coefficient_derivative=-_evaluate(P.derivative(cosine_polynomials(12)[12]),x)
    delta_coefficient=coefficient_derivative*delta_x
    closure_response=(coefficient*2-algebra.element(3))*delta_coefficient
    if delta_x==algebra.element(0) or closure_response==algebra.element(0):raise AssertionError('allowed deformation did not break nomination')
    def record(value):return dict(coefficients=list(map(str,value.coefficients)),interval=list(map(str,real_interval(value,60,bits))))
    return dict(schema='pp-flavor-allowed-response/1',embedding=embedding,lock=str(Q(lock)),
        deformation='V_epsilon(x)=V_0(x)+epsilon*x; x=2*cos(theta), CP-even and allowed when target harmonic support has gcd one',
        curvature=record(curvature),dx_d_epsilon=record(delta_x),coefficient=record(coefficient),
        dcoefficient_d_epsilon=record(delta_coefficient),golden_polynomial_response=record(closure_response),
        identities=dict(stationarity_remainder=list(map(str,force.coefficients)),
            golden_remainder=list(map(str,(coefficient*coefficient-coefficient*3+algebra.element(1)).coefficients)),
            response_replay=list(map(str,(curvature*delta_x+algebra.element(1)).coefficients))),
        implication='the declared symmetries alone do not protect the nominated phase or scalar golden coefficient against this permitted deformation',
        physical_CKM_coefficient='not identified by these scalar equations; requires a specified charge-compatible up/down interaction',
        execution_verified=False)


def interaction_obligations():
    operators=yukawa_operator_basis()
    return dict(schema='pp-flavor-interaction-obligations/1',allowed_operator_audit=operators,
        required_inputs=['noncentral charge-compatible interaction and field representations','three-light-family mechanism',
            'correlated up/down breaking operators','canonical normalization and matching map',
            'renormalization protection and vacuum selection'],
        status='UV_DERIVATION_OPEN',reason='existing symmetries permit independent Yukawa coefficients; stationarity and scalar carrier identities do not determine those coefficients')
