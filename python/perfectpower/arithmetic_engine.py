"""Structural exact integer solver: normalize, quotient, sieve, solve, lift.

Completeness is attached to a checked finite leaf and exact integer image
conditions. Unsupported work is explicit. Caches store canonical leaf data,
not unverified guesses; the checker does not run normal-form discovery.
"""
from collections import OrderedDict
from copy import deepcopy
from dataclasses import asdict
from fractions import Fraction as Q
from math import gcd,lcm
import json
from . import polyalg as P
from .core import rigid_certificate,verify_certificate,RigidCertificate,integer_power_root
from .divisor_square import WorkLimit
from . import linear_perturbation as LP
from .residue_cover import integer_polynomial,evaluate,residue_cover,verify_cover,scan_cover


def _degree(d):
    if type(d) is not int or not 2<=d<=64:raise ValueError('integer power in [2,64] required')


def _same(a,b):return json.dumps(a,sort_keys=True)==json.dumps(b,sort_keys=True)


def _bound(f,d,*,root_node_limit=100000):
    from .sharp_power_gap import sharp_bound
    sharp=sharp_bound(f,d,root_node_limit=root_node_limit)
    if sharp is not None:return sharp
    return _legacy_bound(f,d)


def _legacy_bound(f,d):
    if d==2:
        p=LP.match(f)
        if p:
            l,a,b,c,e=p;return {'kind':'quartic_integral','parameters':p,'bound':abs(a)+abs(b)+abs(c)+abs(e)+1,
                'theorem':'PerfectPower.LinearPerturbation.complete'}
        p=LP.match_square_leading(f)
        if p:
            l,u,v,w,z=p;s=8*l**3;a=4*l*l*u;b=4*l*l*v-u*u;c=s*s*w-2*a*b;e=s*s*z-b*b
            return {'kind':'quartic_rational','parameters':p,'bound':abs(a)+abs(b)+abs(c)+abs(e)+1,
                'theorem':'PerfectPower.SquareLeadingQuartic.complete'}
    cert=rigid_certificate(f,d)
    if cert is not None and not cert.exact_identity:
        if not verify_certificate(cert):raise AssertionError('Runge bound replay failed')
        return {'kind':'rigid_absolute','certificate':asdict(cert),'bound':cert.cutoff-1,
                'theorem':'absolute-value extension of checked rational root-gap inequalities; Python derivation'}
    return None


def affine_power_reductions(coefficients,degree):
    """Find exact reductions (s*y)^d=H((a*x+b)^q), a,s>0.

    The canonical affine map retains rational centering denominators. Root
    images and both divisibility conditions are checked during lifting.
    """
    f=integer_polynomial(coefficients);_degree(degree);n=len(f)-1
    if n<1:return []
    center=Q(-f[-2],n*f[-1]);a,b=center.denominator,-center.numerator
    centered=P.poly(f) if a==1 and b==0 else P.compose_linear(P.poly(f),Q(-b,a),Q(1,a));g=0
    for i,c in enumerate(centered):
        if i and c:g=gcd(g,i)
    powers=[q for q in range(1,g+1) if g%q==0]
    out=[]
    for q in reversed(powers):
        outer=centered[::q];den=lcm(*(c.denominator for c in outer))
        # Denominators divide a^n. Clear them with s^d, not necessarily s:
        # s=a^ceil(n/d) is safe, and an exact d-th root of den is better still.
        scales=[den,a**((n+degree-1)//degree)]
        root=integer_power_root(den,degree)
        if root is not None:scales.append(root)
        s=min(v for v in scales if v**degree%den==0)
        h=integer_polynomial(int(c*s**degree) for c in outer)
        expanded=[0]*(q*(len(h)-1)+1)
        for i,c in enumerate(h):expanded[i*q]=c
        if P.scale(centered,s**degree)!=P.poly(expanded):raise AssertionError('normal-form identity failed')
        out.append({'a':a,'b':b,'power':q,'witness_scale':s,'outer_coefficients':h})
    if a>1:
        floor=center.numerator//center.denominator
        shift=floor if center-floor<=Q(1,2) else floor+1
        integer_center={'a':1,'b':-shift,'power':1,'witness_scale':1,
            'outer_coefficients':integer_polynomial(map(int,P.compose_linear(P.poly(f),shift,1)))}
        # A rational q=1 map changes no degree and can inflate the leaf.
        # Prefer its bijective integer-centered counterpart after compression.
        index=next((i for i,v in enumerate(out) if v['power']==1),len(out))
        out.insert(index,integer_center)
    if not any(p['a']==1 and p['b']==0 and p['power']==1 and p['witness_scale']==1 for p in out):
        out.append({'a':1,'b':0,'power':1,'witness_scale':1,'outer_coefficients':f})
    return out


def _lift(reduction,points,original,d):
    a,b,q,s=(reduction[k] for k in ('a','b','power','witness_scale'));result=set()
    for u,v in points:
        if v%s:continue
        root=u if q==1 else integer_power_root(u,q)
        if root is None:continue
        roots={root,-root} if q%2==0 else {root}
        for t in roots:
            if (t-b)%a:continue
            x,y=(t-b)//a,v//s
            if y**d!=evaluate(original,x):raise AssertionError('lift fails original equation')
            result.add((x,y))
    return sorted(result)


class ArithmeticEngine:
    def __init__(self,*,work_limit=100000,cache_limit=8192):
        if any(type(n) is not int or n<1 for n in (work_limit,cache_limit)):raise ValueError('positive work and cache limits required')
        self.work_limit=work_limit;self.cache_limit=cache_limit;self._cache=OrderedDict();self.hits=0;self.misses=0

    def analyze(self,coefficients,degree=2,*,interval=None):
        """Expose necessary restrictions and bounded completeness independently."""
        from .simplifier import analyze_power
        return analyze_power(coefficients,degree,interval=interval,work_limit=self.work_limit)

    def analyze_gamma(self,spec,degree=2,*,n=None,interval=None,complete=False):
        """Exact special-function input compiler, retaining domains and images."""
        from .gamma_arithmetic import analyze_gamma
        return analyze_gamma(spec,degree,n=n,interval=interval,complete=complete,work_limit=self.work_limit)

    def _leaf(self,f,d):
        key=(f,d)
        if key in self._cache:
            self.hits+=1;self._cache.move_to_end(key);return self._cache[key]
        self.misses+=1;cover=residue_cover(f,d);bound=None
        if cover['global_obstruction']:scan={'points':[],'interval':None,'interval_size':0,'candidates_checked':0}
        else:
            bound=_bound(f,d,root_node_limit=self.work_limit)
            if bound is None:return None
            from .factored_sieve import adaptive_cover
            b=bound['bound'];cover=adaptive_cover(cover,-b,b)
            if cover['global_obstruction']:
                bound=None;scan={'points':[],'interval':None,'interval_size':0,'candidates_checked':0}
            elif bound['kind']=='sharp_horner':
                from .sharp_power_gap import scan_sharp
                scan=scan_sharp(cover,bound,work_limit=self.work_limit)
            else:
                b=bound['bound'];scan=scan_cover(cover,-b,b,work_limit=self.work_limit)
        leaf={'coefficients':f,'degree':d,'cover':cover,'bound_certificate':bound,**scan}
        self._cache[key]=leaf
        if len(self._cache)>self.cache_limit:self._cache.popitem(last=False)
        return leaf

    def solve(self,coefficients,degree=2,*,strict=False,decomposition=True):
        f=integer_polynomial(coefficients);_degree(degree)
        if type(strict) is not bool:raise ValueError('strict must be boolean')
        if type(decomposition) is not bool:raise ValueError('decomposition must be boolean')
        base={'coefficients':f,'degree':degree,'domain':'all integer x and y','execution_verified':False}
        if len(f)==1:
            r=integer_power_root(f[0],degree)
            if r is None:return {**base,'status':'COMPLETE','points':[],'proof':{'kind':'constant'}}
            return {**base,'status':'GENERATOR','points':None,'proof':{'kind':'constant'},'generator':{'x':'any integer','y':sorted({r,-r} if degree%2==0 else {r})}}
        cover=residue_cover(f,degree)
        if cover['global_obstruction']:return {**base,'status':'COMPLETE','points':[],'proof':{'kind':'local_obstruction','cover':cover},'statistics':{'candidates_checked':0}}
        attempts=[];budget_failure=False
        for reduction in affine_power_reductions(f,degree):
            h=reduction['outer_coefficients']
            try:leaf=self._leaf(h,degree)
            except WorkLimit as error:
                budget_failure=True;attempts.append({'degree':len(h)-1,'reason':str(error)});continue
            if leaf is None:
                attempts.append({'degree':len(h)-1,'reason':'no complete finite leaf supported'});continue
            points=_lift(reduction,leaf['points'],f,degree)
            return {**base,'status':'COMPLETE','points':points,'proof':{'kind':'affine_power','reduction':reduction,'leaf':deepcopy(leaf)},
                'statistics':{'original_degree':len(f)-1,'leaf_degree':len(h)-1,'original_coefficient_bits':max(abs(c).bit_length() for c in f),
                    'leaf_coefficient_bits':max(abs(c).bit_length() for c in h),'interval_size':leaf['interval_size'],
                    'candidates_checked':leaf['candidates_checked'],'cache_hits':self.hits,'cache_misses':self.misses,
                    'sieve_candidates_tested':leaf.get('sieve_candidates_tested',leaf['candidates_checked']),
                    'outer_points':len(leaf['points']),'retained_points':len(points)}}
        identity=rigid_certificate(f,degree)
        if identity is not None and identity.exact_identity:
            root=tuple(c//identity.denominator for c in identity.root_numerators)
            return {**base,'status':'GENERATOR','points':None,'proof':{'kind':'exact_power','root_coefficients':root},
                'generator':{'x':'any integer','y':'P(x) and -P(x)' if degree%2==0 else 'P(x)','root_coefficients':root}}
        if decomposition:
            from .polynomial_composition import PolynomialCompiler
            composed=PolynomialCompiler(work_limit=self.work_limit,engine=self).solve(f,degree)
            if composed['status']=='COMPLETE':return composed
        if strict:
            if budget_failure:raise WorkLimit('all supported complete leaves exceeded the candidate budget')
            raise ValueError('no supported complete finite reduction')
        return {**base,'status':'UNRESOLVED','points':None,'attempts':attempts,'complete':False,
                'necessary_restrictions':{'kind':'residue_cover','certificate':cover}}


def verify_result(result,*,work_limit=100000):
    """Check a serialized complete result without discovery or compiler dispatch.

    Replays coefficient identities, leaf inequalities, complete local covers,
    full surviving finite search, and both integral image restrictions.
    """
    try:
        if result['domain']!='all integer x and y' or result['execution_verified'] is not False:return False
        f=integer_polynomial(result['coefficients']);d=result['degree'];_degree(d);proof=result['proof'];kind=proof['kind']
        if kind in ('polynomial_composition','mordell_registry','content_power'):
            from .polynomial_composition import verify_compiled
            return verify_compiled(result,work_limit=work_limit)
        if kind=='constant':
            if len(f)!=1:return False
            r=integer_power_root(f[0],d)
            return (_same(result['points'],[]) and result['status']=='COMPLETE') if r is None else (
                result['status']=='GENERATOR' and result['points'] is None and _same(result['generator'],{'x':'any integer','y':sorted({r,-r} if d%2==0 else {r})}))
        if kind=='exact_power':
            root=integer_polynomial(proof['root_coefficients'])
            return result['status']=='GENERATOR' and result['points'] is None and P.power(P.poly(root),d)==P.poly(f) and _same(result['generator'],{'x':'any integer','y':'P(x) and -P(x)' if d%2==0 else 'P(x)','root_coefficients':root})
        if result['status']!='COMPLETE':return False
        if kind=='local_obstruction':
            c=proof['cover'];return integer_polynomial(c['coefficients'])==f and c['degree']==d and verify_cover(c) and c['global_obstruction'] and _same(result['points'],[])
        if kind!='affine_power':return False
        reduction=proof['reduction'];a,b,q,s=(reduction[k] for k in ('a','b','power','witness_scale'))
        if any(type(v) is not int for v in (a,b,q,s)) or a<1 or s<1 or not 1<=q<=64:return False
        h=integer_polynomial(reduction['outer_coefficients'])
        if q*(len(h)-1)>64:return False
        expanded=[0]*(q*(len(h)-1)+1)
        for i,c in enumerate(h):expanded[i*q]=c
        if P.scale(P.compose_linear(P.poly(f),Q(-b,a),Q(1,a)),s**d)!=P.poly(expanded):return False
        leaf=proof['leaf'];cover=leaf['cover']
        if integer_polynomial(leaf['coefficients'])!=h or leaf['degree']!=d or integer_polynomial(cover['coefficients'])!=h or cover['degree']!=d or not verify_cover(cover):return False
        if cover['global_obstruction']:
            if leaf['bound_certificate'] is not None:return False
            scan={'points':[],'interval':None,'interval_size':0,'candidates_checked':0};points=[]
        else:
            bound=leaf['bound_certificate']
            if bound['kind']=='rigid_absolute':
                c=bound['certificate'];cert=RigidCertificate(**{k:tuple(v) if isinstance(v,list) else v for k,v in c.items()})
                if cert.coefficients!=h or cert.d!=d or not verify_certificate(cert) or cert.exact_identity or bound['bound']!=cert.cutoff-1:return False
                if any(type(v) is not int for v in (cert.denominator,cert.cutoff,*cert.root_numerators,*cert.remainder_numerators)):return False
            elif bound['kind']=='sharp_horner':
                from .sharp_power_gap import verify_bound
                if not verify_bound(bound,h,d,root_node_limit=work_limit):return False
            elif not _same(_legacy_bound(h,d),bound):return False
            bnd=bound['bound']
            if type(bnd) is not int or bnd<0:return False
            if bound['kind']=='sharp_horner':
                from .sharp_power_gap import scan_sharp
                scan=scan_sharp(cover,bound,work_limit=work_limit)
            else:scan=scan_cover(cover,-bnd,bnd,work_limit=work_limit)
            points=scan['points']
        if any(not _same(scan[k],leaf[k]) for k in scan):return False
        return _same(points,leaf['points']) and _same(_lift(reduction,points,f,d),result['points'])
    except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,OverflowError):return False
