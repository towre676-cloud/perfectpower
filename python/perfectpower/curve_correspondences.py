"""Composed covers and explicit Richelot correspondences, not projector guesses."""
from fractions import Fraction as Q
from .rational_functions import RationalFunction as RF, AlgebraBudget, determinant
from . import field_polynomials as F
from .symmetry_quotients import XFunction, PolynomialCurve
from .differential_extensions import matrix_encode, encode


def genus_three_elliptic_tower():
    """Over Q(delta), t=3-delta^4/4: degree-32 three-factor Jacobian isogeny."""
    budget=AlgebraBudget(work_limit=20000000,degree_limit=256,bit_limit=8192);r=RF([0,1],budget=budget);z=r.coerce(0);one=r.coerce(1)
    r2=r*r;t=3-r2*r2/4;x=XFunction([z,one]);u=x+1/x
    p=XFunction([z,one,z,t,z,t,z,one]);source=PolynomialCurve(p.n,budget)
    dpoly=[z,-4*(t-3),z,t-7,z,one];w=(x*x-1)/(x*x*x)
    if p*w*w!=XFunction(dpoly).at(u):raise AssertionError('first quotient identity failed')
    dcurve=PolynomialCurve(dpoly,budget)
    def pull(curve,target,v,scale):
        rows=[];primitives=[]
        for basis in target.basis:
            c,primitive=curve.reduce_form(XFunction(basis).at(v)*v.dx()/scale);rows.append(c);primitives.append(primitive.packet())
        ta=F.matrix_product(rows,curve.connection);bt=F.matrix_product(target.connection,rows)
        if any(rows[i][j].derivative()+ta[i][j]-bt[i][j] for i in range(target.dimension) for j in range(curve.dimension)):raise AssertionError('tower connection intertwining failed')
        return rows,primitives
    drows,dprimitives=pull(source,dcurve,u,w)
    maps=[(u,1/(x*x),[z,t-3,z,one],None,None)]
    U=XFunction([z,one]);DP=XFunction(dpoly)
    for sign in (1,-1):
        Z=U+U.coerce(r2)/U;h=(U+sign*r)/(U*U)
        q=F.product([2*sign*r,one],[t-7-2*r2,z,one])
        if DP*h*h!=XFunction(q).at(Z):raise AssertionError('second quotient identity failed')
        maps.append((Z.at(u),w*h.at(u),q,Z,h))
    rows=[];holomorphic=[];targets=[];packets=[]
    for index,(v,scale,q,Z,h) in enumerate(maps):
        target=PolynomialCurve(q,budget)
        if index==0:
            if p*scale*scale!=XFunction(q).at(v):raise AssertionError('first elliptic quotient identity failed')
            pullback,primitives=pull(source,target,v,scale)
        else:
            second,primitives=pull(dcurve,target,Z,h);pullback=F.matrix_product(second,drows)
        ta=F.matrix_product(pullback,source.connection);bt=F.matrix_product(target.connection,pullback)
        if any(pullback[i][j].derivative()+ta[i][j]-bt[i][j] for i in range(2) for j in range(6)):raise AssertionError('tower connection intertwining failed')
        rows.extend(pullback);holomorphic.append(pullback[0]);targets.append(target.evidence())
        packets.append(dict(x_map=v.packet(),y_multiplier=scale.packet(),target_coefficients=[encode(a) for a in q],map_degree=2 if index==0 else 4,pullback=matrix_encode(pullback),primitives=primitives))
    if F.matrix_rank(rows)!=6 or F.matrix_rank(holomorphic)!=3:raise AssertionError('three elliptic factors do not span')
    return dict(schema='pp-genus-three-elliptic-tower/1',base_change={'t':t.packet(),'relation':'delta^4=-4(t-3)','degree':4},intermediate=dcurve.evidence(),intermediate_pullback=matrix_encode(drows),intermediate_primitives=dprimitives,
        source=source.evidence(),maps=packets,targets=targets,pullback=matrix_encode(rows),cohomology_rank=6,holomorphic_rank=3,
        isogeny_degree=32,kernel_annihilator=4,equations_and_connections_checked=True,
        justification='paired degree-two involution covers in genus three (degree 8), followed by paired covers of the genus-two factor (degree 4); composition degree 32',
        scope='this entire family over the quartic base change; smooth locus t not equal to -1 or 3; not a Q(t) splitting assertion')


def richelot_correspondence(factors):
    """Exact (2,2) isogeny from a nonsingular quadratic splitting."""
    if len(factors)!=3 or any(len(v)!=3 for v in factors):raise ValueError('three quadratic factors required')
    budget=AlgebraBudget();f=[F.trim([RF.parse(v,budget) for v in p]) for p in factors];z=f[0][0].coerce(0)
    if any(len(v)!=3 for v in f):raise ValueError('nonzero quadratic leading coefficients required')
    source=F.product(F.product(f[0],f[1]),f[2]);PolynomialCurve(source,budget)
    delta=determinant(f)
    if not delta:raise ValueError('singular Richelot splitting: determinant zero; product target requires a separate construction')
    g=[F.add(F.product(F.derivative(f[(i+1)%3]),f[(i+2)%3]),F.scale(F.product(f[(i+1)%3],F.derivative(f[(i+2)%3])),-1)) for i in range(3)]
    target=F.scale(F.product(F.product(g[0],g[1]),g[2]),1/delta)
    if PolynomialCurve(target,budget).genus!=2:raise ValueError('smooth genus-two Richelot target required')
    # Work as polynomials in z over Q(t)(x), so reduction is an exact
    # correspondence-ideal test, with no floating point recognition.
    x=XFunction([z,z.coerce(1)]);fx=[XFunction(v) for v in f]
    h=F.add([fx[0]*v for v in g[0]],[fx[1]*v for v in g[1]])
    yz=F.product([fx[0]*v for v in g[0]],[x,x.coerce(-1)])
    residual=F.add([XFunction(source)*v for v in target],F.scale(F.product(yz,yz),-1))
    if any(F.divide(residual,h)[1]):raise AssertionError('Richelot correspondence equation failed')
    return dict(schema='pp-richelot-correspondence/1',source=[encode(v) for v in source],target=[encode(v) for v in target],determinant=delta.packet(),
        bracket_factors=[[encode(v) for v in p] for p in g],correspondence_z_polynomial=[v.packet() for v in h],yv_z_polynomial=[v.packet() for v in yz],
        kernel_generators=[dict(branch_pair=[encode(v) for v in p],divisor='sum of the two branch points minus the two points at infinity') for p in f[:2]],
        kernel_order=4,kernel_invariant_factors=[2,2],isogeny_degree=4,correspondence_ideal_identity_checked=True,
        scope='smooth genus-two source and target, nonzero determinant; explicit algebraic correspondence and Weierstrass divisor kernel, not arbitrary endomorphism discovery')
