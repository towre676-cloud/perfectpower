"""Exact real branches for the chosen Gaussian + radial-Higgs thermal model.

Reuse the repository's rational polynomial/Sturm primitives. This is a complete
classification for this potential, not arbitrary multivariate vacuum discovery.
The thermal action and late bias remain supplied physics inputs.
"""
from fractions import Fraction as Q
from . import polyalg as P
from .core import evaluate, mul


def _q(z):return z if isinstance(z,Q) else Q(str(z))


def _interval_mul(a,b):
    products=[x*y for x in a for y in b]
    return min(products),max(products)


def polynomial_interval(p,root):
    lo=hi=Q(0)
    for c in reversed(p):
        lo,hi=_interval_mul((lo,hi),root);lo+=c;hi+=c
    return lo,hi


def _variations(chain,x):
    signs=[1 if v>0 else -1 for p in chain if (v:=evaluate(p,x))]
    return sum(a!=b for a,b in zip(signs,signs[1:]))


def _count(chain,lo,hi):return _variations(chain,lo)-_variations(chain,hi)


def real_root_intervals(coefficients,*,bits=120):
    """All distinct real roots, with rational endpoints; repeated roots retained.

    Exact dyadic roots are removed before restarting. This prevents an endpoint
    convention from silently dropping a branch. Degrees above three are refused
    here: the wall needs only cubics, not a second generic root implementation.
    """
    p=P.poly(map(_q,coefficients))
    if P.degree(p)<1 or P.degree(p)>3 or bits<10:raise ValueError('nonconstant wall polynomial of degree <=3 and bits>=10 required')
    p=P.exact_div(p,P.gcd_poly(p,P.derivative(p)));points=[];eps=Q(1,2**bits)
    while P.degree(p)>0:
        B=P.cauchy_bound(p)+1;chain=P.sturm_chain(p);pending=[(Q(-B),Q(B))];out=[];restart=False
        while pending:
            lo,hi=pending.pop();count=_count(chain,lo,hi)
            if not count:continue
            if count==1 and hi-lo<=eps:out.append((lo,hi));continue
            mid=(lo+hi)/2
            if evaluate(p,mid)==0:
                points.append((mid,mid));p=P.exact_div(p,(-mid,Q(1)));restart=True;break
            pending.extend([(lo,mid),(mid,hi)])
        if not restart:return sorted(points+out)
    return sorted(points)


def sign_at_root(p,q,root):
    """Gcd recognizes exact zero; rational intervals decide the other signs."""
    lo,hi=root
    if lo==hi:
        z=evaluate(q,lo);return (z>0)-(z<0)
    g=P.gcd_poly(p,q)
    if P.degree(g)>0 and _count(P.sturm_chain(g),lo,hi):return 0
    chain=P.sturm_chain(p)
    for _ in range(2048):
        a,b=polynomial_interval(q,(lo,hi))
        if a>0:return 1
        if b<0:return -1
        mid=(lo+hi)/2
        if evaluate(p,mid)==0:
            z=evaluate(q,mid);return (z>0)-(z<0)
        if _count(chain,lo,mid):hi=mid
        else:lo=mid
    raise ArithmeticError('root sign separation exceeded the explicit wall budget')


def _parameters(model,bath,T,thermal_higgs_c):
    v,lam,c,M,g=map(_q,(model.v_GeV,model.lam,model.thermal_c,model.heavy_mass_GeV,model.current_g_GeV))
    k,lH,vH,cH=map(_q,(bath.portal,bath.lam,bath.v_GeV,thermal_higgs_c));T=_q(T)
    if T<0 or cH<=0:raise ValueError('nonnegative temperature and positive Higgs thermal coefficient required')
    tau2=(T/v)**2;d=(vH/v)**2
    h=_q(model.bias_h0_GeV3)
    if h:
        onset=_q(model.bias_onset_GeV);h*=max(Q(0),1-(T/onset)**2)
    return {'v':v,'lam':lam,'c':c,'k':k,'lH':lH,'cH':cH,'tau2':tau2,'d':d,'b':h/v**3,'alpha':g/v,'mu':M/v,'T':T}


def unbiased_global_vacuum(model,bath,T,*,thermal_higgs_c=.4):
    """Exact active-set solution in x=phi^2/v^2,w=h_radial^2/v^2."""
    z=_parameters(model,bath,T,thermal_higgs_c)
    if z['b']:raise ValueError('use biased_stationary_branches when the late bias is active')
    l,k,H,d,t,c,ch=[z[n] for n in ('lam','k','lH','d','tau2','c','cH')]
    a=l+k*k/H;G=((a,k),(k,H));rhs=(l+k*d+k*k/H-c*t,H*d+k-ch*t)
    determinant=l*H;rows={}
    for active in ((),(0,),(1,),(0,1)):
        if not active:x=w=Q(0)
        elif active==(0,):x=rhs[0]/a;w=Q(0)
        elif active==(1,):x=Q(0);w=rhs[1]/H
        else:x=(H*rhs[0]-k*rhs[1])/determinant;w=(a*rhs[1]-k*rhs[0])/determinant
        if min(x,w)<0:continue
        grad=(a*x+k*w-rhs[0],k*x+H*w-rhs[1])
        if any(grad[j]!=0 for j in active) or any(grad[j]<0 for j in (0,1) if j not in active):continue
        rows[(x,w)]={'active_faces':[('source','Higgs')[j] for j,zv in enumerate((x,w)) if zv>0],
                     'zero_KKT_gradient_faces':[('source','Higgs')[j] for j in (0,1) if grad[j]==0],
                     'squared_source_over_v2':str(x),'squared_radial_Higgs_over_v2':str(w),
                     'KKT_gradient_twice':list(map(str,grad)),
                     'S_over_v':str(-z['alpha']*x/z['mu']**2),
                     'CP_global_components':2 if x else 1}
    if len(rows)!=1:raise ArithmeticError('strictly convex amplitude problem must have one KKT solution')
    row=next(iter(rows.values()))
    row.update({'temperature_GeV':str(z['T']),'exact_amplitude_Hessian_twice':[[str(v) for v in r] for r in G],
                'exact_positive_determinant':str(determinant),
                'global_selection':'Gaussian S minimization is exact. The amplitude quadratic has positive leading minor and determinant lambda*lambda_H, so KKT conditions on x,w>=0 are sufficient for the unique global amplitude minimum.',
                'scope':'Complete global homogeneous vacua of the supplied unbiased mean-field spectator potential, modulo Higgs gauge orientations; not the nonet flavor potential.'})
    return row


def biased_stationary_branches(model,bath,T,*,thermal_higgs_c=.4,bits=140):
    """Retain all real radial-Higgs stationary branches, including spinodals."""
    z=_parameters(model,bath,T,thermal_higgs_c)
    l,k,H,d,t,c,ch,b=[z[n] for n in ('lam','k','lH','d','tau2','c','cH','b')]
    beta=k/H;wstar=P.poly((d+beta-ch*t/H,0,-beta))
    definitions=[('Higgs_boundary',l+k*k/H,l+k*d+k*k/H-c*t),
                 ('Higgs_broken',l,l-(c-k*ch/H)*t)]
    global_even=unbiased_global_vacuum(model,bath,T,thermal_higgs_c=thermal_higgs_c) if not b else None
    rows=[]
    for name,L,a in definitions:
        p=P.poly((-b,-a,0,L));curvature=P.poly((-a,0,3*L))
        for root in real_root_intervals(p,bits=bits):
            ws=sign_at_root(p,wstar,root)
            if name=='Higgs_broken' and ws<0:continue
            if name=='Higgs_broken' and ws==0:continue # Same physical junction retained on boundary face.
            source_sign=sign_at_root(p,P.X,root);curve_sign=sign_at_root(p,curvature,root)
            w=(Q(0),Q(0)) if name=='Higgs_boundary' else polynomial_interval(wstar,root)
            eligible=(name=='Higgs_broken' or ws<=0)
            isglobal=bool(b and source_sign==1 and eligible)
            if global_even:
                targetx=Q(global_even['squared_source_over_v2']);targetw=Q(global_even['squared_radial_Higgs_over_v2'])
                isglobal=eligible and ((targetw>0)==(name=='Higgs_broken')) and sign_at_root(p,(-targetx,0,Q(1)),root)==0
            rows.append({'Higgs_branch':name,'source_interval_over_v':list(map(str,root)),
                         'radial_Higgs_squared_interval_over_v2':list(map(str,w)),
                         'source_sign':source_sign,'reduced_source_curvature_sign':curve_sign,
                         'stationary_polynomial':list(map(str,p)),
                         'stationary_multiplicity_gcd':list(map(str,P.gcd_poly(p,P.derivative(p)))),
                         'positive_physical_Hessian':curve_sign>0 and (ws>0 if name=='Higgs_broken' else ws<0),
                         'global_minimum':isglobal,
                         'radial_Higgs_boundary_sign':ws})
    rows.sort(key=lambda r:Q(r['source_interval_over_v'][0]))
    if b and sum(r['global_minimum'] for r in rows)!=1:raise ArithmeticError('positive bias must select one positive-source global minimum')
    result={'temperature_GeV':str(z['T']),'exact_bias_over_v3':str(b),'branches':rows,
            'real_root_interval_bits':bits,
            'selection_proof':'For b>0, opposite signs at equal source amplitude differ by 2*b*abs(u), selecting u>0. In x=u^2,w>=0 the quadratic is strictly convex and -b*sqrt(x) is convex. Hence the positive-source KKT branch is the unique global amplitude minimum; all negative-source branches remain in the stationary census.',
            'scope':'Exact rational Sturm isolation and signs for this mean-field spectator action. No arbitrary multivariate or flavor-vacuum classification.'}
    if not b:result['unbiased_global_vacuum']=global_even
    return result


def exact_transition_temperatures_squared(model,bath,*,thermal_higgs_c=.4):
    z=_parameters(model,bath,0,thermal_higgs_c);l,k,H,d,c,ch,v=[z[n] for n in ('lam','k','lH','d','c','cH','v')]
    cp=(l+k*d+k*k/H)/c
    higgs=H*d/(ch-k*(c-k*ch/H)/l)
    if not 0<higgs<cp:raise ValueError('this ordered transition formula requires the Higgs transition below the CP transition')
    return {'CP_transition_GeV2':str(v*v*cp),'Higgs_transition_GeV2':str(v*v*higgs),
            'conditions':'Unbiased high-temperature source/Higgs symmetric face, intermediate source-broken/Higgs-symmetric face, and low-temperature both-broken face. Exact squared temperatures of the supplied mean-field action.'}
