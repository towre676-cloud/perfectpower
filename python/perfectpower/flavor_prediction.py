"""Finite B5 monomial priors and unitary CKM forecasts from a training-only API.

Exact rational exponent discovery; numerical transcendental evaluation and inference.
No claim of a UV derivation or blinded prospective experiment.
"""
from fractions import Fraction
from itertools import combinations, product
from math import comb, pi
import hashlib
import json


def exponent_domain(denominators=(1,2,3,5,12), support=3, omit_phi=False):
    if type(support) is not int or not 0 <= support <= 5:
        raise ValueError('support must be an integer in 0..5')
    if not denominators or any(type(d) is not int or d < 1 or d > 120 for d in denominators):
        raise ValueError('integer denominators in 1..120 required')
    a=sorted({Fraction(p,q) for p in (-2,-1,1,2) for q in denominators})
    axes=[i for i in range(5) if not (omit_phi and i==3)]
    count=sum(comb(len(axes),k)*len(a)**k for k in range(min(support,len(axes))+1))
    if count > 1_000_000: raise ValueError('exponent domain budget exceeded')
    out=[]
    for k in range(min(support,len(axes))+1):
        for inds in combinations(axes,k):
            for values in product(a,repeat=k):
                r=[Fraction(0)]*5
                for i,v in zip(inds,values): r[i]=v
                out.append(tuple(r))
    return out


def phase_domain(denominators=(3,4,5,12,18,30)):
    if not denominators or any(type(d) is not int or not 2 <= d <= 120 for d in denominators):
        raise ValueError('phase denominators in 2..120 required')
    return sorted({Fraction(p,q) for q in denominators for p in range(1,q)})


def ckm_from_depth(coefficient, phase, vus, vcb):
    """Standard unitary CKM matrix with s13=C*s12*s23, Vus=u, Vcb=v.

    The physical small branch solves t-t^3=C*u*v. For C in [0,2],
    u in (0,.3), v in (0,.1), t<.061 is unique (derivative positive).
    The model explicitly selects this hierarchical branch; it does not include
    other nonhierarchical branches of the cubic.
    """
    import numpy as np
    c=np.asarray(coefficient,dtype=float); d=np.asarray(phase,dtype=float)
    if np.any(~np.isfinite(c)) or np.any((c<0)|(c>2)) or np.any(~np.isfinite(d)) or not 0<vus<.3 or not 0<vcb<.1:
        raise ValueError('outside declared CKM chart')
    t=c*vus*vcb
    for _ in range(5): t-=(t-t**3-c*vus*vcb)/(1-3*t*t)
    c13=np.sqrt(1-t*t); s12=vus/c13; s23=vcb/c13
    c12=np.sqrt(1-s12*s12); c23=np.sqrt(1-s23*s23)
    t,d=np.broadcast_arrays(t,d); s12=np.broadcast_to(s12,t.shape); s23=np.broadcast_to(s23,t.shape)
    c12=np.broadcast_to(c12,t.shape); c23=np.broadcast_to(c23,t.shape); c13=np.broadcast_to(c13,t.shape)
    e=np.exp(1j*d)
    V=np.empty(t.shape+(3,3),dtype=complex)
    V[...,0,0]=c12*c13; V[...,0,1]=s12*c13; V[...,0,2]=t/e
    V[...,1,0]=-s12*c23-c12*s23*t*e; V[...,1,1]=c12*c23-s12*s23*t*e; V[...,1,2]=s23*c13
    V[...,2,0]=s12*s23-c12*c23*t*e; V[...,2,1]=-c12*s23-s12*c23*t*e; V[...,2,2]=c23*c13
    return V


def observables(V):
    import numpy as np
    gamma=np.angle(-V[...,0,0]*V[...,0,2].conj()/(V[...,1,0]*V[...,1,2].conj()))
    beta=np.angle(-V[...,1,0]*V[...,1,2].conj()/(V[...,2,0]*V[...,2,2].conj()))
    return {'Vub':np.abs(V[...,0,2]),'Rtdts':np.abs(V[...,2,0]/V[...,2,1]),
            'gamma':gamma*180/np.pi,'sin2beta':np.sin(2*beta),
            'J':np.imag(V[...,0,0]*V[...,1,1]*V[...,0,1].conj()*V[...,1,0].conj())}


def weighted_summary(values, weights):
    import numpy as np
    a=np.asarray(values); w=np.asarray(weights)
    if a.ndim != 1 or w.shape != a.shape or not len(a) or np.any(w<0) or not np.all(np.isfinite(a)) or not np.isfinite(w.sum()) or w.sum()<=0:
        raise ValueError('finite one dimensional values and positive weights required')
    order=np.argsort(a,kind='stable'); a=a[order]; w=w[order]/w.sum()
    cw=np.cumsum(w); qs=a[np.searchsorted(cw,[.025,.16,.5,.84,.975]).clip(0,len(a)-1)]
    return {'mean':float(np.sum(a*w)), 'median':float(qs[2]),'credible68':[float(qs[1]),float(qs[3])],
            'credible95':[float(qs[0]),float(qs[4])]}


def fit(training, *, model='b5', support_penalty=.8, denominator_penalty=.15,
        omit_phi=False, fixed_phase=None, fixed_coefficient=None, max_support=3, quadrature_order=3, samples_per_node=4096, seed=5052026,
        continuous_points=2001, phase_denominators=(3,4,5,12,18,30), return_samples=False):
    """Numerical posterior using only required training keys, never holdout values.

    Likelihood is independent Gaussian Rtdts and split-normal gamma. Vus,Vcb,
    alpha_s are independent Gaussian nuisance anchors integrated by Hermite
    quadrature. Returned credible ranges concern latent observables.
    Model evidence is conditional on the stated compact C prior range.
    """
    import numpy as np
    from numpy.polynomial.hermite import hermgauss
    required={'Vus','Vcb','Rtdts','gamma','alpha','alpha_s','mpme'}
    if set(training)!=required: raise ValueError('training schema must contain exactly the declared anchors')
    if model not in ('b5','smooth','legacy','locked'): raise ValueError('unknown model')
    if not 1<=quadrature_order<=7 or not 128<=samples_per_node<=65536: raise ValueError('invalid integration/sample budget')
    if not np.isfinite(support_penalty) or not np.isfinite(denominator_penalty) or min(support_penalty,denominator_penalty)<0: raise ValueError('invalid prior')
    for key in ('Vus','Vcb','Rtdts','alpha_s'):
        if set(training[key])!={'mean','sigma'} or not np.isfinite(training[key]['mean']) or not np.isfinite(training[key]['sigma']) or training[key]['sigma']<=0: raise ValueError('invalid Gaussian anchor')
    ga=training['gamma']
    if set(ga)!={'mean','sigma_minus','sigma_plus'} or not 0<ga['mean']<180 or min(ga['sigma_minus'],ga['sigma_plus'])<=0: raise ValueError('invalid gamma anchor')
    if training['alpha']<=0 or training['mpme']<=0: raise ValueError('positive basis required')
    basis=np.log([training['alpha'],training['alpha_s']['mean'],np.pi,(1+np.sqrt(5))/2,training['mpme']])
    rationals=exponent_domain(support=max_support,omit_phi=omit_phi) if model=='b5' else []
    if model=='b5':
        exp=np.array([[float(v) for v in r] for r in rationals])
        support=np.sum(exp!=0,axis=1)
        den=np.array([sum(np.log(v.denominator) for v in r if v) for r in rationals])
        logprior=-support_penalty*support-denominator_penalty*den
        C=np.exp(exp@basis); valid=(C<=2)
        # Condition the structural prior on the frozen reference-domain range.
        exp=exp[valid]; logprior=logprior[valid]
        rationals=[r for r,ok in zip(rationals,valid) if ok]
        domain_count=len(valid); selected_count=len(exp)
    elif model=='smooth':
        if type(continuous_points) is not int or not 101<=continuous_points<=10001: raise ValueError('invalid continuous quadrature')
        C=(np.arange(continuous_points)+.5)*2/continuous_points
        logprior=np.zeros(len(C)); exp=None; domain_count=selected_count=len(C)
    else:
        C=np.array([5/13 if fixed_coefficient is None else float(fixed_coefficient)]); logprior=np.zeros(1); exp=None; domain_count=selected_count=1
        if fixed_phase is None: fixed_phase=Fraction(2,5)
        if model=='locked' and fixed_coefficient is None: raise ValueError('locked forecast requires an explicit coefficient')
    prior=np.exp(logprior-logprior.max()); prior/=prior.sum()
    phases=phase_domain(phase_denominators) if fixed_phase is None else [Fraction(fixed_phase)]
    if any(not 0<v<1 for v in phases): raise ValueError('physical phase must be between zero and pi')
    delta=np.array([float(v)*pi for v in phases])
    nodes,hw=hermgauss(quadrature_order); hw=hw/np.sqrt(np.pi)
    rng=np.random.default_rng(seed); records=[]; global_weights=np.zeros((len(prior),len(phases)))
    best=None
    for iu,iv,ia in product(range(quadrature_order),repeat=3):
        u=training['Vus']['mean']+np.sqrt(2)*nodes[iu]*training['Vus']['sigma']
        v=training['Vcb']['mean']+np.sqrt(2)*nodes[iv]*training['Vcb']['sigma']
        als=training['alpha_s']['mean']+np.sqrt(2)*nodes[ia]*training['alpha_s']['sigma']
        nw=hw[iu]*hw[iv]*hw[ia]
        if exp is not None:
            xb=basis.copy(); xb[1]=np.log(als); coeff=np.exp(exp@xb)
        else: coeff=C
        # Extreme negligible prior points can leave the chart under anchor variation.
        physical=coeff<=2; safe=np.minimum(coeff,2)
        V=ckm_from_depth(safe[:,None],delta[None,:],u,v)
        obs=observables(V)
        sg=np.where(obs['gamma'] < ga['mean'],ga['sigma_minus'],ga['sigma_plus'])
        chi=((obs['Rtdts']-training['Rtdts']['mean'])/training['Rtdts']['sigma'])**2+((obs['gamma']-ga['mean'])/sg)**2
        likelihood=np.exp(-.5*chi)*physical[:,None]
        mass=likelihood*prior[:,None]/len(phases)
        z=float(mass.sum()); global_weights+=nw*mass
        # MAP at reference nuisance values; do not confuse it with evidence.
        if iu==quadrature_order//2 and iv==quadrature_order//2 and ia==quadrature_order//2:
            idx=np.unravel_index(np.argmax(mass),mass.shape)
            best={'coefficient':float(coeff[idx[0]]),'phase_pi':str(phases[idx[1]]),
                  'chi2':float(chi[idx]),'predictions':{k:float(a[idx]) for k,a in obs.items()}}
            if exp is not None: best['exponents']=[str(v) for v in rationals[idx[0]]]
        if not z>0: raise ValueError('zero quadrature likelihood')
        pick=rng.choice(mass.size,size=samples_per_node,p=(mass/z).ravel())
        records.append({'weight':nw*z,'samples':{k:a.ravel()[pick] for k,a in obs.items()}})
    z=sum(r['weight'] for r in records)
    sampleweights=np.concatenate([np.full(samples_per_node,r['weight']/z/samples_per_node) for r in records])
    summary={k:weighted_summary(np.concatenate([r['samples'][k] for r in records]),sampleweights) for k in records[0]['samples']}
    gw=global_weights/z
    top=np.argsort(gw.sum(axis=1))[::-1][:10]
    coefftop=[]
    for i in top:
        row={'probability':float(gw[i].sum())}
        if exp is not None:
            row.update({'exponents':[str(v) for v in rationals[i]],'coefficient':float(np.exp(exp[i]@basis))})
        else: row['coefficient']=float(C[i])
        coefftop.append(row)
    phasepost=[{'pi':str(p),'degrees':float(p)*180,'probability':float(gw[:,i].sum())} for i,p in enumerate(phases)]
    result={'model':model,'training_hash':hashlib.sha256(json.dumps(training,sort_keys=True).encode()).hexdigest(),
            'exponent_domain_count':domain_count,'reference_physical_count':selected_count,
            'phase_count':len(phases),'structural_candidates':selected_count*len(phases),
            'quadrature_nodes':quadrature_order**3,'quadrature_order':quadrature_order,
            'posterior_samples':len(sampleweights),'seed':seed,
            'conditional_evidence_without_common_density_normalizers':z,'best_reference_MAP':best,
            'predictions':summary,'phase_posterior':sorted(phasepost,key=lambda a:-a['probability']),
            'coefficient_posterior_top10':coefftop,
            'maximum_single_formula_probability':float(gw.sum(axis=1).max()),
            'prior':{'support_penalty':support_penalty,'denominator_penalty':denominator_penalty,'omit_phi':omit_phi},
            'method':'complete finite structural enumeration; Hermite nuisance quadrature; sampled posterior quantiles'}

    if return_samples:
        result['_samples']={k:np.concatenate([r['samples'][k] for r in records]) for k in records[0]['samples']}
        result['_samples']['weights']=sampleweights
    return result


def golden_depth_polynomial(vus,vcb,vub):
    """Exact observable closure for C=phi^-2: h^2-3uvh+(uv)^2.

    h=w-w^3. The smaller positive coefficient branch must be specified.
    Measured decimal inputs generally have nonzero residual, not exact equality.
    """
    from .weyl_scaffold import rational
    u,v,w=map(rational,(vus,vcb,vub)); h=w-w**3
    return h*h-3*u*v*h+(u*v)**2


def cyclotomic_golden_carrier():
    """Exact carrier for the nominated phase/coefficient in Q[z]/Phi60.

    This compresses a training-selected candidate; it is not a UV mechanism.
    """
    from .quotient_algebra import QuotientAlgebra
    from . import polyalg as P
    from .core import mul
    # Construct every divisor's cyclotomic polynomial by exact division.
    divisors=[d for d in range(1,61) if 60%d==0]; phis={}
    for d in divisors:
        q=P.poly([-1]+[0]*(d-1)+[1])
        for e in divisors:
            if e<d and d%e==0:q=P.exact_div(q,phis[e])
        phis[d]=q
    A=QuotientAlgebra(phis[60]);z=A.element([0,1]);C=A.element(1)-z**12-z**-12
    identity=C*C-C*3+A.element(1)
    if identity.coefficients!=P.ZERO or (z**60-A.element(1)).coefficients!=P.ZERO:
        raise AssertionError('cyclotomic carrier identities failed')
    char=C.characteristic_polynomial(); expected=P.ONE
    for _ in range(8):expected=mul(expected,(1,-3,1))
    if char!=expected:raise AssertionError('golden carrier characteristic polynomial failed')
    return {'cyclotomic_modulus':[int(v) for v in phis[60]],
            'coefficient_in_power_basis':[str(v) for v in C.coefficients],
            'coefficient_identity':'C^2-3C+1=0', 'coefficient_identity_remainder':[str(v) for v in identity.coefficients],
            'root_unity_identity_remainder':[str(v) for v in (z**60-A.element(1)).coefficients],
            'proper_power_nonzero_remainders':{str(d):[str(v) for v in (z**d-A.element(1)).coefficients] for d in (12,20,30)},
            'characteristic_polynomial':[str(v) for v in char], 'norm':str(C.norm()),'trace':str(C.trace()),
            'embedding':'z=exp(11*pi*i/30), C=1-z^12-z^-12=(3-sqrt(5))/2',
            'minimal_coefficient_polynomial':[1,-3,1], 'embedding_index':11,
            'positive_small_coefficient_CP_positive_embeddings':[1,11,19,29],
            'observable_polynomial':'(w-w^3)^2-3uv(w-w^3)+(uv)^2=0',
            'scope':'exact quotient-algebra identities; nominated phenomenological candidate; numerical physical inference is separate',
            'new_lean_theorems':0}


def locked_forecast(training, coefficient, phase, *, samples=262144, seed=5052026, return_samples=False):
    """Direct nuisance sampling for a fixed formula, avoiding quadrature-step quantiles."""
    import numpy as np
    from math import pi
    # Shared strict input validation and reference MAP calculation.
    reference=fit(training,model='locked',fixed_coefficient=coefficient,fixed_phase=phase,
                  quadrature_order=1,samples_per_node=128)
    if type(samples) is not int or not 10000<=samples<=2_000_000: raise ValueError('invalid locked Monte Carlo budget')
    rng=np.random.default_rng(seed)
    u=rng.normal(training['Vus']['mean'],training['Vus']['sigma'],samples)
    v=rng.normal(training['Vcb']['mean'],training['Vcb']['sigma'],samples)
    # Vectorized CKM construction with array anchors; the public chart intentionally takes scalar anchors.
    t=float(coefficient)*u*v
    for _ in range(5):t-=(t-t**3-float(coefficient)*u*v)/(1-3*t*t)
    c13=np.sqrt(1-t*t);s12=u/c13;s23=v/c13;c12=np.sqrt(1-s12*s12);c23=np.sqrt(1-s23*s23);e=np.exp(1j*float(Fraction(phase))*pi)
    V=np.empty((samples,3,3),dtype=complex)
    V[:,0,0]=c12*c13;V[:,0,1]=s12*c13;V[:,0,2]=t/e
    V[:,1,0]=-s12*c23-c12*s23*t*e;V[:,1,1]=c12*c23-s12*s23*t*e;V[:,1,2]=s23*c13
    V[:,2,0]=s12*s23-c12*c23*t*e;V[:,2,1]=-c12*s23-s12*c23*t*e;V[:,2,2]=c23*c13
    obs=observables(V);ga=training['gamma'];sg=np.where(obs['gamma']<ga['mean'],ga['sigma_minus'],ga['sigma_plus'])
    chi=((obs['Rtdts']-training['Rtdts']['mean'])/training['Rtdts']['sigma'])**2+((obs['gamma']-ga['mean'])/sg)**2
    w=np.exp(-.5*chi);reference['conditional_evidence_without_common_density_normalizers']=float(w.mean());w/=w.sum()
    reference.update({'predictions':{k:weighted_summary(a,w) for k,a in obs.items()},'quadrature_nodes':0,
                      'posterior_samples':samples,'seed':seed,'method':'direct Gaussian nuisance sampling and training likelihood weighting; fixed nominated formula',
                      'effective_sample_size':float(1/np.sum(w*w))})
    if return_samples: reference['_samples']={**obs,'weights':w}
    return reference
