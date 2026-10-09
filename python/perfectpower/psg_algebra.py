"""Exact elimination, differential invariants and observable parameter fibres.

Certificates are bound to caller-supplied sources. Identity replay does not
trust discovery, rank labels, sample agreement or stored verdict strings.
"""
from fractions import Fraction as Q
from math import isqrt
from itertools import product
from math import gcd
from .psg_polynomial import Polynomial, rational
from . import exact_linear as E


def quadratic_reduce(source, variable, radicand):
    """P = A + t B + (t²-D) C, with A,B independent of t."""
    D=source.coerce(radicand); t=source.variable(variable)
    if D.degree(variable)>0: raise ValueError('radicand must not depend on eliminated variable')
    i=source.variables.index(variable); A=B=C=source.constant(0)
    for e,c in source._terms:
        m=e[i]; k=m//2
        base=Polynomial(source.variables,[(tuple(a if j!=i else 0 for j,a in enumerate(e)),c)])
        parity=t if m%2 else source.constant(1)
        reduced=base*D**k
        if m%2: B=B+reduced
        else: A=A+reduced
        # t^(2k)-D^k = (t²-D) Σ t^(2(k-1-j)) D^j.
        for j in range(k): C=C+base*parity*t**(2*(k-1-j))*D**j
    norm=A*A-D*B*B
    multiplier=A-t*B
    return {'schema':'pp-psg-quadratic/1','source':source.packet(),'variable':variable,
            'radicand':D.packet(),'A':A.packet(),'B':B.packet(),'quotient':C.packet(),
            'norm':norm.packet(),'source_multiplier':multiplier.packet(),
            'chamber_multiplier':(B*B-multiplier*C).packet()}


def check_quadratic(packet, source, variable, radicand):
    """Independently replay both identities and bind the original equation."""
    required={'schema','source','variable','radicand','A','B','quotient','norm',
              'source_multiplier','chamber_multiplier'}
    if not isinstance(packet,dict) or set(packet)!=required or packet['schema']!='pp-psg-quadratic/1':
        raise ValueError('invalid quadratic certificate')
    D=source.coerce(radicand)
    if packet['variable']!=variable or Polynomial.from_packet(packet['source'])!=source or Polynomial.from_packet(packet['radicand'])!=D:
        raise ValueError('quadratic source mismatch')
    A,B,C,N,M,J=[Polynomial.from_packet(packet[k]) for k in
                 ('A','B','quotient','norm','source_multiplier','chamber_multiplier')]
    if any(p.variables!=source.variables for p in (A,B,C,N,M,J)):
        raise ValueError('certificate variable order mismatch')
    if any(p.degree(variable)>0 for p in (A,B,D)): raise ValueError('eliminated variable survives')
    t=source.variable(variable); chamber=t*t-D
    if source!=A+t*B+chamber*C: raise ValueError('source reduction identity failed')
    if N!=A*A-D*B*B or M!=A-t*B or J!=B*B-M*C:
        raise ValueError('norm witness failed')
    if N!=M*source+J*chamber: raise ValueError('elimination ideal identity failed')
    return True


def square_roots(q, domain='rational'):
    q=rational(q)
    if domain not in ('rational','integer'): raise ValueError('rational or integer domain required')
    if q<0: return ()
    n,d=isqrt(q.numerator),isqrt(q.denominator)
    if n*n!=q.numerator or d*d!=q.denominator: return ()
    r=Q(n,d)
    if domain=='integer' and r.denominator!=1: return ()
    return (r,) if not r else (-r,r)


def reconstruct_quadratic(packet, source, variable, radicand, values, *, domain='integer'):
    """Complete auxiliary fibre over an exact base point, including B=0."""
    check_quadratic(packet,source,variable,radicand)
    if domain not in ('integer','rational'): raise ValueError('unsupported fibre domain')
    if set(values)!=set(source.variables)-{variable}: raise ValueError('exactly the base variables required')
    point={k:rational(v) for k,v in values.items()}; point[variable]=Q(0)
    A,B,D,N=[Polynomial.from_packet(packet[k]).evaluate(point) for k in ('A','B','radicand','norm')]
    if N: candidates=(); branch='norm_obstruction'
    elif B:
        t=-A/B
        candidates=(t,) if domain=='rational' or t.denominator==1 else ()
        branch='regular' if candidates else 'integer_divisibility_obstruction'
    elif A: candidates=(); branch='constant_obstruction'
    else: candidates=square_roots(D,domain); branch='exceptional_square_fibre'
    for t in candidates:
        point[variable]=t
        if t*t!=D or source.evaluate(point): raise ArithmeticError('reconstructed source failed')
    return {'branch':branch,'domain':domain,'norm':str(N),'A':str(A),'B':str(B),
            'radicand':str(D),'roots':[str(t) for t in candidates],
            'scope':'complete auxiliary fibre over the supplied exact base point'}


def lie_derivative(polynomial, field):
    if len(field)!=len(polynomial.variables): raise ValueError('vector-field dimension mismatch')
    return sum((polynomial.derivative(v)*polynomial.coerce(f) for v,f in zip(polynomial.variables,field)),polynomial.constant(0))


def darboux_certificate(polynomial, field):
    if not polynomial or polynomial.degree()<=0: raise ValueError('nonconstant nonzero candidate required')
    derivative=lie_derivative(polynomial,field)
    (K,),remainder=derivative.divide([polynomial])
    return {'schema':'pp-psg-darboux/1','candidate':polynomial.packet(),
            'field':[polynomial.coerce(f).packet() for f in field],'cofactor':K.packet(),
            'remainder':remainder.packet(),'invariant':not remainder}


def check_darboux(packet, polynomial, field):
    required={'schema','candidate','field','cofactor','remainder','invariant'}
    if not isinstance(packet,dict) or set(packet)!=required or packet['schema']!='pp-psg-darboux/1': raise ValueError('invalid Darboux packet')
    if not polynomial or polynomial.degree()<=0: raise ValueError('nonconstant candidate required')
    if Polynomial.from_packet(packet['candidate'])!=polynomial or tuple(Polynomial.from_packet(p) for p in packet['field'])!=tuple(polynomial.coerce(f) for f in field):
        raise ValueError('Darboux source mismatch')
    K=Polynomial.from_packet(packet['cofactor']); remainder=Polynomial.from_packet(packet['remainder'])
    if lie_derivative(polynomial,field)!=K*polynomial+remainder or type(packet['invariant']) is not bool or packet['invariant']!=bool(not remainder):
        raise ValueError('Darboux identity failed')
    # A rejected candidate's remainder must also be reduced by its leading term.
    lead=polynomial._terms[-1][0]
    if any(all(a>=b for a,b in zip(e,lead)) for e,c in remainder._terms): raise ValueError('unreduced Darboux remainder')
    return packet['invariant']


def linear_darboux_scan(field, height=1):
    """Exhaust the declared finite integer coefficient box, up to scalar.

This does not exclude rational candidates of larger height or higher degree.
"""
    if not field: raise ValueError('nonempty vector field required')
    prototype=field[0]
    if len(field)!=len(prototype.variables) or len(field)>4 or type(height) is not int or not 1<=height<=3:
        raise ValueError('at most four variables and height 1..3 required')
    if (2*height+1)**(len(field)+1)>20000: raise ValueError('linear candidate box exceeds 20000')
    seen=set(); invariants=[]; rejected=0
    for coefficients in product(range(-height,height+1),repeat=len(field)+1):
        if not any(coefficients[:-1]):continue
        g=0
        for c in coefficients:g=gcd(g,abs(c))
        sign=1 if next(c for c in coefficients if c)>0 else -1
        coefficients=tuple(sign*c//g for c in coefficients)
        if coefficients in seen:continue
        seen.add(coefficients)
        h=sum((c*prototype.variable(v) for v,c in zip(prototype.variables,coefficients)),prototype.constant(coefficients[-1]))
        packet=darboux_certificate(h,field)
        if check_darboux(packet,h,field):invariants.append(packet)
        else:rejected+=1
    return {'height':height,'candidates':len(seen),'invariants':invariants,'rejected':rejected,
            'scope':'complete finite integer coefficient box up to nonzero rational scalar; no all-height classification'}


def ideal_certificate(target, generators):
    """A zero remainder proves redundancy; a nonzero one is inconclusive."""
    qs,remainder=target.divide(generators)
    return {'schema':'pp-psg-ideal/1','target':target.packet(),
            'generators':[target.coerce(g).packet() for g in generators],
            'multipliers':[q.packet() for q in qs],'remainder':remainder.packet(),
            'redundant':not remainder}


def check_ideal(packet, target, generators):
    required={'schema','target','generators','multipliers','remainder','redundant'}
    if not isinstance(packet,dict) or set(packet)!=required or packet['schema']!='pp-psg-ideal/1': raise ValueError('invalid ideal packet')
    gs=tuple(target.coerce(g) for g in generators)
    if Polynomial.from_packet(packet['target'])!=target or tuple(Polynomial.from_packet(g) for g in packet['generators'])!=gs:
        raise ValueError('ideal source mismatch')
    qs=tuple(Polynomial.from_packet(q) for q in packet['multipliers'])
    if len(qs)!=len(gs): raise ValueError('multiplier count mismatch')
    r=Polynomial.from_packet(packet['remainder'])
    if target!=sum((q*g for q,g in zip(qs,gs)),target.constant(0))+r or type(packet['redundant']) is not bool or packet['redundant']!=bool(not r):
        raise ValueError('ideal identity failed')
    return packet['redundant']


def nonzero_point(polynomial):
    """Construct a rational nonvanishing witness by degree-plus-one choices."""
    if not polynomial: raise ValueError('zero polynomial has no nonvanishing witness')
    p=polynomial; values={}
    for v in p.variables:
        for k in range(max(0,p.degree(v))+1):
            q=p.substitute({v:k})
            if q: values[v]=k; p=q; break
        else: raise ArithmeticError('degree witness construction failed')
    if not polynomial.evaluate(values): raise ArithmeticError('nonvanishing witness failed')
    return values


def dependency_profile(outputs):
    """Exact independence or an actual pair of points differing in one input."""
    outputs=tuple(outputs)
    if not outputs: raise ValueError('at least one output required')
    prototype=outputs[0]
    if any(p.variables!=prototype.variables for p in outputs): raise ValueError('output variables mismatch')
    rows=[]
    for p in outputs:
        dependencies={}
        for v in p.variables:
            delta=p.substitute({v:p.variable(v)+1})-p
            if not delta: dependencies[v]={'independent':True}
            else:
                a=nonzero_point(delta); b=dict(a); b[v]+=1
                dependencies[v]={'independent':False,'first':a,'second':b,
                                 'first_value':str(p.evaluate(a)),'second_value':str(p.evaluate(b))}
        rows.append(dependencies)
    return rows


def observable_fibre(observation, values, target):
    """Complete rational affine fibre and target identifiability, with witnesses."""
    A=E.matrix([[rational(x) for x in row] for row in observation])
    C=E.matrix([[rational(x) for x in row] for row in target]); b=tuple(map(rational,values))
    if len(C[0])!=len(A[0]) or len(b)!=len(A): raise ValueError('observable dimensions mismatch')
    seed=E.solve(A,b)
    if seed is None:
        for w in E.kernel(E.transpose(A)):
            residual=sum(x*y for x,y in zip(w,b))
            if residual:
                return {'status':'empty','left_annihilator':list(map(str,w)),
                        'nonzero_pairing':str(residual)}
        raise ArithmeticError('inconsistent system without obstruction')
    null=E.kernel(A); target_seed=E.apply(C,seed); directions=tuple(E.apply(C,v) for v in null)
    out={'status':'determined' if all(not any(v) for v in directions) else 'underdetermined',
         'seed':list(map(str,seed)),'kernel_basis':[list(map(str,v)) for v in null],
         'target_seed':list(map(str,target_seed)),
         'target_directions':[list(map(str,v)) for v in directions],
         'scope':'complete rational affine fibre; integer lattice interpretation is separate'}
    if out['status']=='underdetermined':
        v=next(v for v,d in zip(null,directions) if any(d)); other=tuple(x+y for x,y in zip(seed,v))
        out['ambiguity_witness']={'first':list(map(str,seed)),'second':list(map(str,other)),
                                  'first_target':list(map(str,target_seed)),
                                  'second_target':list(map(str,E.apply(C,other)))}
        # Select a minimal independent set of target rows restricted to ker A.
        restricted=E.transpose(directions);selected=[];span=[]
        for i,row in enumerate(restricted):
            if len(E.rref(span+[row])[1])>len(span):span.append(row);selected.append(i)
        out['minimum_additional_scalar_observations']=len(selected)
        out['separating_target_rows']=selected
        out['separating_observations']=[list(map(str,C[i])) for i in selected]
    else:
        rows=[]
        for row in C:
            lift=E.solve(E.transpose(A),row)
            if lift is None: raise ArithmeticError('determined target did not factor')
            rows.append(list(map(str,lift)))
        out['readout']=rows
        out['minimum_additional_scalar_observations']=0
    return out


def affine_norm_population(A, B, D, norm, cutoff, *, work_limit=4096):
    """Pull generalized Pell orbits back through a nonsingular integer affine map.

The cutoff is |B|, the second norm coordinate, rather than a box in original
coordinates. Nonunimodular maps retain their exact divisibility image gate.
"""
    A=A.coerce(A); B=A.coerce(B)
    if len(A.variables)!=2 or A.degree()>1 or B.degree()>1: raise ValueError('two-variable affine norm coordinates required')
    if any(c.denominator!=1 for p in (A,B) for e,c in p._terms): raise ValueError('integer affine coefficients required')
    x,y=A.variables; zero={x:0,y:0}
    offsets=(A.evaluate(zero),B.evaluate(zero))
    M=((A.derivative(x).evaluate(zero),A.derivative(y).evaluate(zero)),
       (B.derivative(x).evaluate(zero),B.derivative(y).evaluate(zero)))
    inv=E.inverse(M)
    from .checked_pell_orbits import pell_orbits_certificate
    pell=pell_orbits_certificate(D,norm,cutoff,domain='integer',work_limit=work_limit)
    # Existing Pell packets store [Y,X]; original coordinates solve [A,B]=[X,Y].
    points=[]; excluded=0
    for Y,X in pell['source_points']:
        original=E.apply(inv,(Q(X)-offsets[0],Q(Y)-offsets[1]))
        if any(q.denominator!=1 for q in original): excluded+=1; continue
        point=tuple(int(q) for q in original)
        if A.evaluate(point)**2-D*B.evaluate(point)**2!=norm: raise ArithmeticError('norm transport failed')
        points.append(list(point))
    return {'schema':'pp-psg-affine-norm/1','A':A.packet(),'B':B.packet(),
            'D':D,'norm':norm,'cutoff':cutoff,'cutoff_coordinate':'abs(B)',
            'points':sorted(points),'excluded_nonintegral_preimages':excluded,
            'canonical_pell_packet':pell,
            'scope':'complete integer population within abs(B)<=cutoff, using the existing generalized Pell producer'}


def emit_identity(name, variables, lhs, rhs):
    """Emit literal rational-polynomial equality for Lean's ring tactic."""
    if not name.isidentifier() or any(not v.isidentifier() for v in variables): raise ValueError('invalid Lean identifier')
    if lhs!=rhs: raise ValueError('cannot emit a false identity')
    return f'theorem {name} ('+' '.join(variables)+f' : ℚ) : {lhs.expression()} = {rhs.expression()} := by ring\n'
