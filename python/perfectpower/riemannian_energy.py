"""Exact planar constant metrics, timed energy and coordinate first jets.

Source-inspired algebra, not a smooth-manifold or obstacle geodesic solver.
Accepted packets emit kernel-checkable source-bound Lean statements. Hashes
identify the source; they are not a substitute for running Lean.
"""
from fractions import Fraction as Q
from hashlib import sha256
import json
import re
from .divisor_square import WorkLimit
from .euclid_geometry import rational, point, sub


def metric(values):
    if not isinstance(values,(list,tuple)) or len(values)!=3:
        raise ValueError('metric requires symmetric entries [a,b,c]')
    a,b,c=map(rational,values)
    if a<=0 or a*c-b*b<=0:raise ValueError('positive definite metric required')
    return a,b,c


def quadratic(g,v):
    a,b,c=g;x,y=v
    return a*x*x+2*b*x*y+c*y*y


def pullback(g,m):
    a,b,c=g;p,q,r,s=m
    return (a*p*p+2*b*p*r+c*r*r,
            a*p*q+b*(p*s+q*r)+c*r*s,
            a*q*q+2*b*q*s+c*s*s)


def connection_jet(g,derivatives):
    """∂ᵢ gⱼₖ, then Γᵏᵢⱼ. Derivatives are supplied first-jet data."""
    a,b,c=metric(g)
    if len(derivatives)!=2 or any(len(row)!=3 for row in derivatives):
        raise ValueError('two symmetric derivative triples required')
    rows=[tuple(map(rational,row)) for row in derivatives]
    d=[[[row[0],row[1]],[row[1],row[2]]] for row in rows]
    det=a*c-b*b;inv=((c/det,-b/det),(-b/det,a/det))
    lower=[[[ (d[i][j][k]+d[j][i][k]-d[k][i][j])/2
              for k in range(2)] for j in range(2)] for i in range(2)]
    gamma=[[[sum(inv[k][l]*lower[i][j][l] for l in range(2))
              for k in range(2)] for j in range(2)] for i in range(2)]
    return d,lower,gamma


def _q(x):
    x=Q(x)
    return f'(({x.numerator} : ℚ)/({x.denominator} : ℚ))'


def _pair(v):return '('+','.join(map(_q,v))+')'
def _list(values):return '['+','.join(values)+']'
def _metric(g):return '⟨'+','.join(map(_q,g))+'⟩'
def _encode(obj):
    if isinstance(obj,Q):return str(obj)
    if isinstance(obj,(tuple,list)):return [_encode(x) for x in obj]
    return obj


def compile_energy_certificate(packet,*,namespace='EnergyCertificate',step_limit=256):
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9_]*',namespace):raise ValueError('simple Lean namespace required')
    if type(step_limit) is not int or step_limit<1:raise ValueError('positive step limit required')
    g=metric(packet['metric']);raw=packet['vertices'];times=packet['durations']
    if not isinstance(raw,(list,tuple)) or len(raw)<2:raise ValueError('at least two vertices required')
    if len(raw)-1>step_limit:raise WorkLimit('timed path step budget exceeded')
    if len(times)!=len(raw)-1:raise ValueError('one duration per segment required')
    vertices=list(map(point,raw));times=list(map(rational,times))
    if any(t<=0 for t in times):raise ValueError('strictly positive durations required')
    steps=list(zip((sub(b,a) for a,b in zip(vertices,vertices[1:])),times))
    duration=sum(times,Q(0));displacement=sub(vertices[-1],vertices[0])
    velocity=tuple(x/duration for x in displacement)
    action=sum((quadratic(g,v)/t for v,t in steps),Q(0))
    residual=sum((quadratic(g,tuple(x-t*y for x,y in zip(v,velocity)))/t for v,t in steps),Q(0))
    lower=duration*quadratic(g,velocity)/2
    assert action/2==lower+residual/2
    lines=['import PerfectPower.RiemannianEnergy','set_option maxRecDepth 10000',
           'set_option maxHeartbeats 4000000','open PerfectPower.RiemannianEnergy',f'namespace {namespace}',
           f'def g : Metric ℚ := {_metric(g)}',
           f'def vertices : List (ℚ × ℚ) := {_list(map(_pair,vertices))}',
           f'def durations : List ℚ := {_list(map(_q,times))}',
           'def steps : List (Step ℚ) := ((vertices.zip vertices.tail).zip durations).map',
           '  (fun e => ((e.1.2.1-e.1.1.1,e.1.2.2-e.1.1.2),e.2))',
           f'def velocity : ℚ × ℚ := {_pair(velocity)}',
           'theorem source_shape : vertices.length = durations.length+1 := by decide +kernel',
           'theorem source_positive : g.Positive := by decide +kernel',
           'theorem source_times : ∀ e ∈ steps, 0 < e.2 := by decide +kernel',
           f'theorem source_duration : totalTime steps = {_q(duration)} := by decide +kernel',
           'theorem source_total_positive : 0 < totalTime steps := by decide +kernel',
           'theorem source_endpoint_x : totalX steps = vertices.getLast!.1-vertices.head!.1 := by decide +kernel',
           'theorem source_endpoint_y : totalY steps = vertices.getLast!.2-vertices.head!.2 := by decide +kernel',
           'theorem source_dx : totalX steps = totalTime steps*velocity.1 := by decide +kernel',
           'theorem source_dy : totalY steps = totalTime steps*velocity.2 := by decide +kernel',
           f'theorem source_energy : action g steps/2 = {_q(action/2)} := by decide +kernel',
           f'theorem source_gap : gap g velocity steps/2 = {_q(residual/2)} := by decide +kernel',
           'theorem source_excess : action g steps = totalTime steps*g.q velocity+gap g velocity steps :=',
           '  energy_excess g velocity steps source_times source_dx source_dy',
           'theorem all_timed_paths (s : List (Step ℚ))',
           '    (ht : ∀ e ∈ s, 0 < e.2) (hT : totalTime s = totalTime steps)',
           '    (hx : totalX s = totalX steps) (hy : totalY s = totalY steps) :',
           '    totalTime steps*g.q velocity/2 ≤ action g s/2 := by',
           '  have dx : totalX s = totalTime s*velocity.1 := by rw [hx,hT,source_dx]',
           '  have dy : totalY s = totalTime s*velocity.2 := by rw [hy,hT,source_dy]',
           '  have h := energy_lower_bound g source_positive velocity s ht dx dy',
           '  simpa only [hT] using h']
    result={'schema':'pp-riemannian-energy/1','metric':_encode(g),'vertices':_encode(vertices),
            'durations':_encode(times),'duration':str(duration),'velocity':_encode(velocity),
            'energy':str(action/2),'straight_energy':str(lower),'excess':str(residual/2),
            'constant_velocity':residual==0,
            'scope':'constant positive metric; sharp energy lower bound for all finite timed paths with the same displacement and total time; no obstacle admission, integral, geodesic ODE or rope dynamics theorem'}
    if residual==0:
        lines += ['theorem source_attained : action g steps/2 = totalTime steps*g.q velocity/2 := by decide +kernel',
                  'theorem source_minimal (s : List (Step ℚ))',
                  '    (ht : ∀ e ∈ s, 0 < e.2) (hT : totalTime s = totalTime steps)',
                  '    (hx : totalX s = totalX steps) (hy : totalY s = totalY steps) :',
                  '    action g steps/2 ≤ action g s/2 := by',
                  '  rw [source_attained]; exact all_timed_paths s ht hT hx hy']
    if 'transport' in packet:
        tr=packet['transport'];target=metric(tr['metric'])
        if len(tr['linear'])!=4:raise ValueError('four linear coefficients required')
        linear=tuple(map(rational,tr['linear']));p,q,r,s=linear
        translation=point(tr.get('translation',[0,0]))
        if p*s-q*r==0:raise ValueError('invertible affine map required')
        if pullback(target,linear)!=g:raise ValueError('source metric is not target metric pullback')
        lines += [f'def target : Metric ℚ := {_metric(target)}',
                  'theorem target_positive : target.Positive := by decide +kernel',
                  f'def linear : LinearMap2 ℚ := ⟨{",".join(map(_q,linear))}⟩',
                  f'def translation : ℚ × ℚ := {_pair(translation)}',
                  'def imageVertices := vertices.map (fun v =>',
                  '  ((linear.apply v).1+translation.1,(linear.apply v).2+translation.2))',
                  'def imageSteps : List (Step ℚ) := ((imageVertices.zip imageVertices.tail).zip durations).map',
                  '  (fun e => ((e.1.2.1-e.1.1.1,e.1.2.2-e.1.1.2),e.2))',
                  'theorem source_pullback : g = pullback target linear := by decide +kernel',
                  'theorem source_invertible : linear.p*linear.s-linear.q*linear.r ≠ 0 := by decide +kernel',
                  'theorem source_bilinear (u v : ℚ × ℚ) : g.bilinear u v = target.bilinear (linear.apply u) (linear.apply v) := by',
                  '  rw [source_pullback]; exact pullback_bilinear target linear u v',
                  'theorem source_bijective : Function.Bijective linear.apply := linear_bijective linear source_invertible',
                  'theorem source_image : imageSteps = mapSteps linear steps := by decide +kernel',
                  'theorem source_transport : action g steps = action target imageSteps := by',
                  '  rw [source_pullback,source_image]',
                  '  exact action_transport target linear steps']
        result['transport']={'metric':_encode(target),'linear':_encode(linear),'translation':_encode(translation)}
    if 'derivatives' in packet:
        d,lowered,gamma=connection_jet(g,packet['derivatives'])
        def tensor(t):
            return 'fun i j k => ((('+_list(_list(_list(map(_q,row)) for row in plane) for plane in t)+').getD i.val []).getD j.val []).getD k.val 0'
        lines += ['def D : Fin 2 → Fin 2 → Fin 2 → ℚ := '+tensor(d),
                  'def gamma : Fin 2 → Fin 2 → Fin 2 → ℚ := '+tensor(gamma),
                  'def gram : Fin 2 → Fin 2 → ℚ := fun i j =>',
                  '  if i.val = 0 then (if j.val = 0 then g.a else g.b) else (if j.val = 0 then g.b else g.c)',
                  'def lowered (i j k : Fin 2) := gram k 0*gamma i j 0+gram k 1*gamma i j 1',
                  'theorem source_D_symmetric : ∀ i j k, D i j k = D i k j := by decide +kernel',
                  'theorem source_connection : ∀ i j k, lowered i j k = koszul D i j k := by decide +kernel',
                  'theorem source_torsion : ∀ i j k, gamma i j k = gamma j i k := by decide +kernel',
                  'theorem source_compatible (i j k : Fin 2) : lowered i j k+lowered i k j = D i j k := by',
                  '  rw [source_connection,source_connection]',
                  '  exact koszul_compatible D source_D_symmetric i j k',
                  'theorem unique_lowered (A : Fin 2 → Fin 2 → Fin 2 → ℚ)',
                  '    (ht : ∀ i j k, A i j k = A j i k)',
                  '    (hc : ∀ i j k, A i j k+A i k j = D i j k) (i j k : Fin 2) :',
                  '    A i j k = lowered i j k := by',
                  '  rw [source_connection]; exact koszul_unique D A ht hc i j k']
        result['connection_jet']={'derivatives':_encode(d),'lowered':_encode(lowered),'gamma':_encode(gamma)}
    if 'transport' in packet:lines += ['#print axioms source_transport','#print axioms source_bilinear','#print axioms source_bijective']
    if 'derivatives' in packet:lines += ['#print axioms source_compatible','#print axioms unique_lowered']
    if residual==0:lines += ['#print axioms source_minimal']
    lines += ['#print axioms all_timed_paths','#print axioms source_excess',f'end {namespace}']
    source='\n'.join(lines)+'\n'
    normalized={k:v for k,v in result.items() if k!='scope'}
    result['proof']={'source_sha256':sha256(source.encode()).hexdigest(),
                     'packet_sha256':sha256(json.dumps(normalized,sort_keys=True,separators=(',',':')).encode()).hexdigest(),
                     'kernel_checked':False}
    return result,source
