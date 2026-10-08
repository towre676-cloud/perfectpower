"""Exact power equations on complete integer-valued residue charts.

For Q=F/L, transport Q(x)+k=y^d to G_r(n)+k=y^d with
x=r+L*n. Every signed source solution survives the factored Hensel/CRT
cover. Bounds are pulled back exactly; no global height claim is made.
"""
import hashlib
import json
from fractions import Fraction
from . import polyalg as P
from .integer_valued_polynomial import normalize
from .bounded_residue_patch import terms_checked, evaluate
from .residue_atlas import atlas_packet, _bounds, _parameter, _canonical_equal
from .residue_atlas_intersection_factored import intersect_atlases
from .residue_atlas_product import _blocks
from .residue_determinant import integer


def _factors(factors):
    if not isinstance(factors,list) or not 1 <= len(factors) <= 8:
        raise ValueError('one through eight [prime,exponent] factors required')
    if any(not isinstance(f,list) or len(f)!=2 for f in factors):
        raise ValueError('factors are [prime,exponent] pairs')
    return factors


def power_charts(coefficients, exponent, bounds, *, offset=0, factors=None,
                 denominator_limit=64, explicit_limit=4096):
    d=_parameter(exponent,'exponent',12)
    if d<2: raise ValueError('power exponent at least two required')
    k=integer(offset,256); bounds=_bounds(bounds)
    cap=_parameter(denominator_limit,'denominator_limit',64)
    F,L,canonical=normalize(coefficients)
    if L>cap or len(F)>13:
        raise ValueError('denominator 64 and polynomial degree twelve budgets exceeded')
    if any(abs(c).bit_length()>256 for c in F): raise ValueError('source coefficient budget exceeded')
    factors=_factors([[2,3],[3,2]] if factors is None else factors)
    limit=_parameter(explicit_limit,'explicit_limit',100000)
    charts=[]
    for r in range(L):
        if P.evaluate(F,r)%L: continue
        shifted=P.compose_linear(P.poly(F),r,L)
        if any(v.denominator!=1 or int(v)%L for v in shifted):
            raise ArithmeticError('residue chart coefficient transport failed')
        G=[int(v)//L for v in shifted]
        source_terms=[[c,i,0] for i,c in enumerate(G) if c]
        source_terms.extend([[k,0,0],[-1,0,d]])
        H=terms_checked(source_terms)
        local=[atlas_packet(H,p,e) for p,e in factors]
        cover=intersect_atlases(local,explicit_limit=limit)
        lo,hi=bounds[0]
        nlo=-((r-lo)//L); nhi=(hi-r)//L
        charts.append({'residue':r,'step':L,'coefficients':G,'terms':H,
                       'parameter_interval':[nlo,nhi], 'active':nlo<=nhi,'cover':cover})
    return {'schema':'pp-integer-valued-power-charts/1','rational_coefficients':canonical,
            'numerator':F,'denominator':L,'exponent':d,'offset':k,'bounds':bounds,
            'factors':json.loads(json.dumps(factors)),'denominator_limit':cap,
            'explicit_limit':limit,'charts':charts,'integral_domain_empty':not charts,
            'global_modular_obstruction':all(c['cover']['global_obstruction'] for c in charts),
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}


def verify_power_charts(packet):
    try:
        expected=power_charts(packet['rational_coefficients'],packet['exponent'],packet['bounds'],
            offset=packet['offset'],factors=packet['factors'],denominator_limit=packet['denominator_limit'],
            explicit_limit=packet['explicit_limit'])
        return _canonical_equal(packet,expected)
    except (ValueError,TypeError,KeyError,IndexError,OverflowError): return False


def _prepared_blocks(packet, work_limit):
    if not verify_power_charts(packet): raise ValueError('complete power-chart packet required')
    budget=_parameter(work_limit,'work_limit',2000000)
    # Budget is a complete traversal budget per chart, with at most 64 charts.
    for i,c in enumerate(packet['charts']):
        if not c['active']: continue
        b=[c['parameter_interval'],packet['bounds'][1]]
        for a,y,nx,ny in _blocks(c['cover'],b,budget):
            yield i,a,y,nx,ny


def chart_population(packet, *, work_limit=200000):
    count=sum(nx*ny for _,_,_,nx,ny in _prepared_blocks(packet,work_limit))
    return {'count':count,'bounds':packet['bounds'],'chart_count':len(packet['charts']),
            'order':'source residue; prime-group roots; parameter then signed y',
            'scope':'complete modular candidates for the original rational power equation',
            'execution_verified':False}


def chart_select(packet,index,*,work_limit=200000):
    index=integer(index,1024)
    if index<0: raise IndexError('negative candidate rank')
    for i,a,b,nx,ny in _prepared_blocks(packet,work_limit):
        if index<nx*ny:
            c=packet['charts'][i];m=c['cover']['modulus'];u,v=divmod(index,ny)
            lo=c['parameter_interval'][0];yl=packet['bounds'][1][0]
            n=lo+(a-lo)%m+u*m; y=yl+(b-yl)%m+v*m
            return [c['residue']+c['step']*n,y]
        index-=nx*ny
    raise IndexError('candidate rank outside population')


def chart_rank(packet,point,*,work_limit=200000):
    if not isinstance(point,list) or len(point)!=2: raise ValueError('two integer coordinates required')
    x,y=[integer(v,256) for v in point];total=0
    if not verify_power_charts(packet): raise ValueError('complete power-chart packet required')
    if not all(lo<=z<=hi for z,(lo,hi) in zip((x,y),packet['bounds'])):
        raise ValueError('point outside source bounds')
    for i,a,b,nx,ny in _prepared_blocks(packet,work_limit):
        c=packet['charts'][i];L=c['step'];m=c['cover']['modulus']
        if x%L==c['residue']:
            n=(x-c['residue'])//L
            if (n%m,y%m)==(a,b):
                lo=c['parameter_interval'][0];yl=packet['bounds'][1][0]
                n0=lo+(a-lo)%m;y0=yl+(b-yl)%m
                return total+(n-n0)//m*ny+(y-y0)//m
        total+=nx*ny
    raise ValueError('point outside simultaneous integral/modular domain')


def chart_scan(packet,*,candidate_limit=100000,work_limit=200000):
    cap=_parameter(candidate_limit,'candidate_limit',1000000)
    blocks=list(_prepared_blocks(packet,work_limit))
    count=sum(nx*ny for _,_,_,nx,ny in blocks)
    if count>cap: raise ValueError('complete candidate scan exceeds budget; no partial result')
    points=[]
    for i,a,b,nx,ny in blocks:
        c=packet['charts'][i];m=c['cover']['modulus'];lo=c['parameter_interval'][0];yl=packet['bounds'][1][0]
        for u in range(nx):
            n=lo+(a-lo)%m+u*m
            for v in range(ny):
                y=yl+(b-yl)%m+v*m
                if evaluate(c['terms'],n,y)==0:
                    points.append([c['residue']+c['step']*n,y])
    return {'points':sorted(points),'candidate_count':count,'complete_in_box':True,
            'source_equation':'F(x)/L + offset = y^exponent on the exact integral domain',
            'global_height_bound':False,'execution_verified':False}


def native_power_charts(packet):
    """Source-bound all-integer chart and denominator-clearing certificates."""
    if not verify_power_charts(packet): raise ValueError('complete power-chart packet required')
    if packet['denominator']>16 or len(packet['charts'])>16:
        raise ValueError('native denominator/chart budget sixteen exceeded')
    from .power_free_local import _poly, _finset
    F,L,d,k=packet['numerator'],packet['denominator'],packet['exponent'],packet['offset']
    tag=hashlib.sha256(json.dumps(packet,sort_keys=True).encode()).hexdigest()[:16]
    ns='PowerCharts_'+tag
    lines=['import PerfectPower.IntegerValuedPowerCharts','set_option maxHeartbeats 0',
           'set_option maxRecDepth 100000',f'namespace {ns}',
           'open Polynomial PerfectPower.IntegerValuedPolynomial PerfectPower.IntegerValuedPowerCharts',
           f'noncomputable def source : Polynomial ℤ := {_poly(F)}',
           f'theorem source_checked : source = PerfectPower.NativePolynomialSquare.polynomial {F} := by',
           '  norm_num [source, PerfectPower.NativePolynomialSquare.polynomial] <;> ring',
           f'theorem denominator_clearing (x y : ℤ) : PowerAt source {L} {k} {d} x y ↔',
           f'    source.eval x + ({L} : ℤ)*({k}) = ({L} : ℤ)*y^{d} :=',
           f'  cleared_power_iff source {L} {k} {d} (by norm_num) x y']
    qparts=[]
    for i,value in enumerate(map(Fraction,packet['rational_coefficients'])):
        if value:
            term=f'C (({value.numerator} : ℚ)/{value.denominator})'
            qparts.append(term if i==0 else term+f'*X^{i}')
    qpoly=' + '.join(qparts) or '0'
    lines += [f'noncomputable def rationalSource : Polynomial ℚ := {qpoly}',
              f'theorem rational_identity : rationalSource*C ({L} : ℚ)=source.map (Int.castRingHom ℚ) := by',
              '  simp only [rationalSource,source,Polynomial.map_add,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_C,Polynomial.map_X,add_mul,mul_assoc,mul_left_comm,← Polynomial.C_mul]',
              '  ring_nf',
              '  norm_num [← Polynomial.C_mul,← Polynomial.C_pow] <;> ring',
              f'theorem rational_equation (x y : ℤ) : rationalSource.eval (x : ℚ)+({k} : ℚ)=(y : ℚ)^{d} ↔ PowerAt source {L} {k} {d} x y :=',
              f'  rational_power_iff source rationalSource {L} {k} {d} (by norm_num) rational_identity x y',
              '#print axioms rational_identity','#print axioms rational_equation']
    roots=[c['residue'] for c in packet['charts']]
    lines+=[f'theorem residues_checked : PerfectPower.PowerFreeLocal.rootResidues {F} {L} = {_finset(roots)} := by decide +kernel',
            f'theorem integral_domain (x : ℤ) : IntegralAt source {L} x ↔',
            f'    ∃ r ∈ {_finset(roots)}, ∃ n : ℤ, x = (r : ℤ)+{L}*n := by',
            '  rw [source_checked]',
            f'  simpa only [residues_checked] using integer_domain_cover {F} {L} (by norm_num) x']
    names=['source_checked','denominator_clearing','residues_checked','integral_domain']
    for i,c in enumerate(packet['charts']):
        r=c['residue'];G=c['coefficients']
        lines += [f'noncomputable def chart{i} : Polynomial ℤ := {_poly(G)}',
                  f'theorem chart{i}_identity : source.comp (C ({r} : ℤ)+C ({L} : ℤ)*X) = C ({L} : ℤ)*chart{i} := by',
                  '  norm_num [source,chart'+str(i)+',Polynomial.add_comp,Polynomial.mul_comp,Polynomial.pow_comp,Polynomial.C_comp,Polynomial.X_comp] <;> ring',
                  f'theorem chart{i}_power (n y : ℤ) : PowerAt source {L} {k} {d} ({r}+{L}*n) y ↔',
                  f'    chart{i}.eval n + ({k}) = y^{d} := chart_power_iff source chart{i} {L} {r} {k} {d} (by norm_num) chart{i}_identity n y']
        names += [f'chart{i}_identity',f'chart{i}_power']
    for name in names:lines.append('#print axioms '+name)
    lines.append('end '+ns)
    return '\n'.join(lines)+'\n'


def branch_power_charts(packet,prime,exponent,*,work_limit=200000):
    """Intersect normalized blowup leaves with the existing Hensel/CRT cover."""
    from math import gcd,lcm
    from .branching_residue_patch import branching_patch
    from .residue_atlas_intersection import generalized_crt
    from .residue_atlas import _axis_count
    if not verify_power_charts(packet):raise ValueError('complete power-chart packet required')
    p=_parameter(prime,'prime',7)
    if p<2 or any(p%v==0 for v in range(2,p)):raise ValueError('prime 2, 3, 5 or 7 required')
    _parameter(exponent,'exponent',4);budget=_parameter(work_limit,'work_limit',2000000)
    branches=[]
    for c in packet['charts']:
        patch=None;cells=[]
        if c['active']:
            bounds=[c['parameter_interval'],packet['bounds'][1]]
            patch=branching_patch(c['terms'],bounds,prime,exponent,work_limit=budget)
            M=p**exponent;N=c['cover']['modulus'];g=gcd(M,N);period=lcm(M,N)
            buckets={}
            for i in patch['leaf_ids']:
                a,b=patch['nodes'][i]['source_residue']
                buckets.setdefault((a%g,b%g),[]).append(i)
            used=0
            for x,y,_,_ in _blocks(c['cover'],bounds,budget):
                used+=1
                if used>budget:raise ValueError('complete cover join exceeds work budget; no partial result')
                for i in buckets.get((x%g,y%g),[]):
                    used+=1
                    if used>budget:raise ValueError('complete cover join exceeds work budget; no partial result')
                    a,b=patch['nodes'][i]['source_residue']
                    aa=generalized_crt(a,x,M,N);bb=generalized_crt(b,y,M,N)
                    nx=_axis_count(*bounds[0],period,aa);ny=_axis_count(*bounds[1],period,bb)
                    if nx and ny:cells.append({'leaf_id':i,'residue':[aa,bb],'modulus':period,'count':nx*ny})
        branches.append({'source_residue':c['residue'],'source_step':c['step'],'patch':patch,'cells':cells})
    return {'schema':'pp-branching-integer-power-charts/1','source_packet':json.loads(json.dumps(packet)),
            'prime':prime,'exponent':exponent,'work_limit':work_limit,'branches':branches,
            'candidate_count':sum(cell['count'] for row in branches for cell in row['cells']),
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}


def verify_branch_power_charts(packet):
    try:
        return _canonical_equal(packet,branch_power_charts(packet['source_packet'],packet['prime'],
                              packet['exponent'],work_limit=packet['work_limit']))
    except (ValueError,TypeError,KeyError,IndexError,OverflowError):return False


def branch_power_scan(packet,*,candidate_limit=100000):
    from .residue_atlas import _axis_count
    if not verify_branch_power_charts(packet):raise ValueError('complete branching power-chart packet required')
    cap=_parameter(candidate_limit,'candidate_limit',1000000)
    if packet['candidate_count']>cap:raise ValueError('complete candidate scan exceeds budget; no partial result')
    points=[]
    for chart,row in zip(packet['source_packet']['charts'],packet['branches']):
        if row['patch'] is None:continue
        nl=chart['parameter_interval'][0];yl=packet['source_packet']['bounds'][1][0]
        for cell in row['cells']:
            a,b=cell['residue'];m=cell['modulus'];n0=nl+(a-nl)%m;y0=yl+(b-yl)%m
            nx=_axis_count(*chart['parameter_interval'],m,a)
            ny=_axis_count(*packet['source_packet']['bounds'][1],m,b)
            node=row['patch']['nodes'][cell['leaf_id']];aa,bb=node['source_residue'];step=node['step']
            for u in range(nx):
                for v in range(ny):
                    n,y=n0+m*u,y0+m*v
                    if evaluate(node['terms'],(n-aa)//step,(y-bb)//step)==0:
                        points.append([row['source_residue']+row['source_step']*n,y])
    return {'points':sorted(points),'candidate_count':packet['candidate_count'],
            'complete_in_box':True,'global_height_bound':False,'execution_verified':False}
