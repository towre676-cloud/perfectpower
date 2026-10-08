"""Real-time stochastic source-wall formation on a periodic two-dimensional lattice.

An explicitly declared mean-field quench and Model-A bath are inputs. This
reduced-source simulation is not a cosmological network or a measured bath.
"""
from dataclasses import dataclass,asdict
import hashlib
import numpy as np


@dataclass(frozen=True)
class FormationInputs:
    nodes:int=128
    length:float=128.
    replicas:int=12
    dt:float=.1
    damping:float=1.
    noise_temperature:float=.00001
    quench_half_range:float=.5
    equilibration:float=20.
    smoothing_length:float=1.
    source_lambda:float=.0000176188164948
    portal:float=.0000001
    Higgs_lambda:float=.13
    Higgs_ratio:float=.0082
    heavy_alpha:float=.1
    heavy_mu:float=10.
    thermal_c:float=.025
    Higgs_thermal_c:float=.4
    v_GeV:float=30000.

    def __post_init__(self):
        if self.nodes<16 or self.nodes%2 or self.replicas<2:raise ValueError('even grid>=16 and replicas>=2 required')
        if not all(np.isfinite(v) for v in asdict(self).values()):raise ValueError('finite inputs required')
        if min(self.length,self.dt,self.damping,self.source_lambda,self.Higgs_lambda,self.heavy_mu,self.thermal_c,self.v_GeV)<=0:raise ValueError('positive scales required')
        if min(self.noise_temperature,self.equilibration,self.smoothing_length,self.portal,self.Higgs_ratio,self.heavy_alpha,self.Higgs_thermal_c)<0:raise ValueError('nonnegative bath and coupling inputs required')
        if not 0<self.quench_half_range<1:raise ValueError('quench remains inside positive-temperature restored-Higgs regime')

    @property
    def quartic(self):return self.source_lambda+self.portal**2/self.Higgs_lambda


def lattice_modes(nodes,length):
    dx=length/nodes
    a=4*np.sin(np.pi*np.fft.fftfreq(nodes))**2/dx**2
    b=4*np.sin(np.pi*np.fft.rfftfreq(nodes))**2/dx**2
    return a[:,None]+b[None,:]


def linear_bath_factors(k2,mass_squared,dt,damping,theta,cell_area):
    """Exact OU factors for each lattice mode, including unstable modes."""
    r=k2+mass_squared;decay=np.exp(-r*dt/damping)
    variance=np.empty_like(r);nz=abs(r)>1e-12
    variance[nz]=-np.expm1(-2*r[nz]*dt/damping)/r[nz]
    variance[~nz]=2*dt/damping
    return decay,np.sqrt(theta/cell_area*variance)


def nonlinear_flow(u,dt,damping):return u/np.sqrt(1+2*dt*u*u/damping)


def step(u,k2,epsilon,dt,p,rng):
    """Strang split exact local quartic drift / exact linear stochastic bath."""
    u=nonlinear_flow(u,dt/2,p.damping)
    decay,sigma=linear_bath_factors(k2,epsilon,dt,p.damping,p.noise_temperature,(p.length/p.nodes)**2)
    white=rng.standard_normal(u.shape)
    u=np.fft.irfft2(decay*np.fft.rfft2(u,axes=(-2,-1))+sigma*np.fft.rfft2(white,axes=(-2,-1)),s=u.shape[-2:],axes=(-2,-1))
    return nonlinear_flow(u,dt/2,p.damping)


def wall_length(u,dx):
    """Periodic marching-squares length with a bilinear saddle decider."""
    f=[u,np.roll(u,-1,-1),np.roll(np.roll(u,-1,-1),-1,-2),np.roll(u,-1,-2)]
    positive=[q>=0 for q in f];cross=[positive[j]!=positive[(j+1)%4] for j in range(4)]
    points=[]
    for j in range(4):
        denom=f[j]-f[(j+1)%4]
        t=np.divide(f[j],denom,out=np.full_like(u,.5),where=denom!=0)
        if j==0:point=(t,np.zeros_like(t))
        elif j==1:point=(np.ones_like(t),t)
        elif j==2:point=(1-t,np.ones_like(t))
        else:point=(np.zeros_like(t),1-t)
        points.append(point)
    count=sum(c.astype(np.int8) for c in cross)
    denom=f[0]-f[1]+f[2]-f[3];det=f[0]*f[2]-f[1]*f[3]
    saddle=np.divide(det,denom,out=sum(f)/4,where=denom!=0)
    same=(saddle>=0)==positive[0];length=np.zeros_like(u)
    for a in range(4):
        for b in range(a+1,4):
            mask=(count==2)&cross[a]&cross[b]
            if (a,b) in [(0,1),(2,3)]:mask|=(count==4)&same
            if (a,b) in [(0,3),(1,2)]:mask|=(count==4)&(~same)
            distance=np.hypot(points[a][0]-points[b][0],points[a][1]-points[b][1])
            length+=np.where(mask,distance,0)
    return dx*length.sum(axis=(-2,-1))


def observe(u,k2,epsilon,p):
    dx=p.length/p.nodes
    smooth=np.fft.irfft2(np.fft.rfft2(u,axes=(-2,-1))*np.exp(-p.smoothing_length**2*k2/2),s=u.shape[-2:],axes=(-2,-1))
    diffx=np.roll(u,-1,-1)-u;diffy=np.roll(u,-1,-2)-u
    energy=(diffx*diffx+diffy*diffy)/(2*dx*dx)+epsilon*u*u/2+u**4/4
    rms=np.sqrt(np.mean(u*u,axis=(-2,-1)))
    return {'wall_length_density':(wall_length(smooth,dx)/p.length**2).tolist(),
        'raw_zero_contour_length_density':(wall_length(u,dx)/p.length**2).tolist(),
        'rms':rms.tolist(),'positive_area_fraction':np.mean(u>0,axis=(-2,-1)).tolist(),
        'energy_density':np.mean(energy,axis=(-2,-1)).tolist(),
        'rms_to_instantaneous_broken_minimum':(rms/np.sqrt(-epsilon)).tolist() if epsilon<0 else None}


def temperature_bridge(epsilon,p):
    T=p.v_GeV*np.sqrt((p.quartic*(1+epsilon)+p.portal*p.Higgs_ratio**2)/p.thermal_c)
    minimum_Higgs_curvature=p.v_GeV**2*(p.Higgs_thermal_c*(T/p.v_GeV)**2-p.Higgs_lambda*p.Higgs_ratio**2-p.portal)
    return {'declared_temperature_GeV':float(T),'restored_Higgs_minimum_curvature_GeV2':float(minimum_Higgs_curvature)}


def simulate(quench_time, *, inputs=None,seed=20261008,sample_multiples=(0,1,2,3,4,5,6)):
    p=FormationInputs() if inputs is None else inputs
    if not np.isfinite(quench_time) or quench_time<=0:raise ValueError('positive quench time required')
    if min(sample_multiples)<0 or len(set(sample_multiples))!=len(sample_multiples):raise ValueError('distinct nonnegative sampling times required')
    if temperature_bridge(-p.quench_half_range,p)['restored_Higgs_minimum_curvature_GeV2']<=0:raise ValueError('Higgs-restored reduction invalid for declared temperature range')
    rng=np.random.default_rng(seed);k2=lattice_modes(p.nodes,p.length);area=(p.length/p.nodes)**2
    # Linear Gibbs proposal at the same positive mass for every quench, then
    # equilibrate the nonlinear dynamics. No freeze-out scale is seeded.
    u=np.fft.irfft2(np.sqrt(p.noise_temperature/area/(k2+p.quench_half_range))*np.fft.rfft2(rng.standard_normal((p.replicas,p.nodes,p.nodes)),axes=(-2,-1)),s=(p.nodes,p.nodes),axes=(-2,-1))
    eqsteps=max(1,int(np.ceil(p.equilibration/p.dt)))
    for _ in range(eqsteps):u=step(u,k2,p.quench_half_range,p.equilibration/eqsteps,p,rng)
    hat_t=np.sqrt(p.damping*quench_time);hat_xi=(quench_time/p.damping)**.25
    targets=[float(m)*hat_t for m in sorted(sample_multiples)]
    t=-p.quench_half_range*quench_time;observations=[];fields=[]
    for target in targets:
        steps=max(1,int(np.ceil((target-t)/p.dt)));dt=(target-t)/steps
        for _ in range(steps):
            epsilon=np.clip(-(t+dt/2)/quench_time,-p.quench_half_range,p.quench_half_range)
            u=step(u,k2,epsilon,dt,p,rng);t+=dt
        t=target;epsilon=float(np.clip(-t/quench_time,-p.quench_half_range,p.quench_half_range))
        observations.append({'time':t,'time_over_hat':target/hat_t,'epsilon':epsilon,**observe(u,k2,epsilon,p)})
        fields.append(u[0].copy())
    return {'inputs':asdict(p),'quench_time':quench_time,'seed':seed,'mean_field_hat_time':hat_t,'mean_field_hat_length':hat_xi,
        'physical_time_unit_seconds':6.582119569e-25/(p.v_GeV*np.sqrt(p.quartic)),
        'physical_length_unit_GeV_inverse':1/(p.v_GeV*np.sqrt(p.quartic)),
        'critical_temperature_bridge':temperature_bridge(0,p),
        'minimum_temperature_bridge':temperature_bridge(-p.quench_half_range,p),
        'final_maximum_source_magnitude':float(np.max(abs(u))),
        'sampled_heavy_valley_metric_correction_max':float(4*p.heavy_alpha**2*np.max(u*u)/p.heavy_mu**4),
        'final_field_sha256':hashlib.sha256(u.astype('<f8').tobytes()).hexdigest(),
        'observations':observations,'first_replica_snapshots':fields}


def summarize_run(run):
    out={k:v for k,v in run.items() if k!='first_replica_snapshots'}
    out['ensemble_summary']=[{'time_over_hat':t['time_over_hat'],
        'mean_wall_density':float(np.mean(t['wall_length_density'])),
        'standard_error_wall_density':float(np.std(t['wall_length_density'],ddof=1)/np.sqrt(len(t['wall_length_density']))),
        'mean_rms':float(np.mean(t['rms'])),
        'mean_broken_amplitude_ratio':float(np.mean(t['rms_to_instantaneous_broken_minimum'])) if t['epsilon']<0 else None}
        for t in run['observations']]
    return out


def scaling_fit(runs, *,time_over_hat=5.,bootstrap=2000):
    samples=[]
    for r in runs:
        t=next(t for t in r['observations'] if abs(t['time_over_hat']-time_over_hat)<1e-10)
        samples.append(t['wall_length_density'])
    samples=np.asarray(samples);x=np.log([r['quench_time'] for r in runs])
    if np.any(samples.mean(axis=1)<=0):raise ValueError('wall density vanished; finite-size saturation cannot be fit')
    slope,intercept=np.polyfit(x,np.log(samples.mean(axis=1)),1)
    rng=np.random.default_rng(917);slopes=[]
    for _ in range(bootstrap):
        chosen=rng.integers(0,samples.shape[1],samples.shape[1]);y=samples[:,chosen].mean(axis=1)
        if np.all(y>0):slopes.append(np.polyfit(x,np.log(y),1)[0])
    return {'sampling_time_over_hat':time_over_hat,'wall_density_exponent':float(slope),
        'paired_replica_bootstrap_95_interval':np.quantile(slopes,[.025,.975]).tolist(),
        'intercept':float(intercept),'mean_field_overdamped_reference_exponent':-.25,
        'scope':'Fit at a declared scaled time on this low-noise, finite-cutoff mean-field quench. Does not establish equilibrium universality or a cosmological formation law.'}


def coupled_timestep_check(quench_time, *, inputs=None,coarse_dt=.1,seed=20261009,time_over_hat=5.):
    """Coarse/fine OU-noise coupling with exact marginal variances.

    Two half-step OU innovations are composed in Fourier space and normalized
    to the coarse midpoint OU variance. Both marginal split schemes remain
    unchanged. This couples stochastic paths rather than comparing random runs.
    """
    p=FormationInputs() if inputs is None else inputs
    if quench_time<=0 or coarse_dt<=0 or time_over_hat<=0:raise ValueError('positive coupled check scales required')
    rng=np.random.default_rng(seed);k2=lattice_modes(p.nodes,p.length);area=(p.length/p.nodes)**2
    u=np.fft.irfft2(np.sqrt(p.noise_temperature/area/(k2+p.quench_half_range))*np.fft.rfft2(rng.standard_normal((p.replicas,p.nodes,p.nodes)),axes=(-2,-1)),s=(p.nodes,p.nodes),axes=(-2,-1))
    eqsteps=max(1,int(np.ceil(p.equilibration/p.dt)))
    for _ in range(eqsteps):u=step(u,k2,p.quench_half_range,p.equilibration/eqsteps,p,rng)
    fine=u.copy();coarse=u.copy();t=-p.quench_half_range*quench_time;end=time_over_hat*np.sqrt(p.damping*quench_time)
    steps=int(np.ceil((end-t)/coarse_dt));dt=(end-t)/steps
    def epsilon(t):return float(np.clip(-t/quench_time,-p.quench_half_range,p.quench_half_range))
    def drift_and_noise(field,decay,innovation,duration):
        field=nonlinear_flow(field,duration/2,p.damping)
        field=np.fft.irfft2(decay*np.fft.rfft2(field,axes=(-2,-1))+innovation,s=(p.nodes,p.nodes),axes=(-2,-1))
        return nonlinear_flow(field,duration/2,p.damping)
    for _ in range(steps):
        d1,s1=linear_bath_factors(k2,epsilon(t+dt/4),dt/2,p.damping,p.noise_temperature,area)
        d2,s2=linear_bath_factors(k2,epsilon(t+3*dt/4),dt/2,p.damping,p.noise_temperature,area)
        dc,sc=linear_bath_factors(k2,epsilon(t+dt/2),dt,p.damping,p.noise_temperature,area)
        w1=np.fft.rfft2(rng.standard_normal(u.shape),axes=(-2,-1));w2=np.fft.rfft2(rng.standard_normal(u.shape),axes=(-2,-1))
        fine=drift_and_noise(drift_and_noise(fine,d1,s1*w1,dt/2),d2,s2*w2,dt/2)
        combined=np.sqrt((d2*s1)**2+s2**2)
        scale=np.divide(sc,combined,out=np.zeros_like(sc),where=combined>0)
        coarse=drift_and_noise(coarse,dc,scale*(d2*s1*w1+s2*w2),dt)
        t+=dt
    a=observe(coarse,k2,epsilon(end),p);b=observe(fine,k2,epsilon(end),p)
    delta=np.asarray(a['wall_length_density'])-np.asarray(b['wall_length_density'])
    return {'quench_time':quench_time,'inputs':asdict(p),'seed':seed,'time_over_hat':time_over_hat,
        'actual_coarse_dt':dt,'actual_fine_dt':dt/2,
        'coarse_wall_densities':a['wall_length_density'],'fine_wall_densities':b['wall_length_density'],
        'paired_coarse_minus_fine_wall_density':delta.tolist(),
        'paired_mean_difference':float(np.mean(delta)),
        'paired_standard_error_difference':float(np.std(delta,ddof=1)/np.sqrt(p.replicas)),
        'replica_field_RMS_difference':np.sqrt(np.mean((fine-coarse)**2,axis=(-2,-1))).tolist(),
        'scope':'Coupled stochastic timestep sensitivity at one quench, bath and cutoff; not a rigorous continuum error bound.'}
