"""Source-bound polynomial identities and continuum chart inequalities for Lean."""
from hashlib import sha256
from fractions import Fraction as Q
from . import bernstein_boxes as B
from .box_lean import rational,matrix,emit_certificate as basic_emit_certificate,emit_leaf
from math import comb
from .michor_geometry import check_metric,check_domain,digest


def expression(poly,x='x',y='y'):
    """Balance sums so large literal packets stay within elaborator depth."""
    terms=['*'.join([rational(c)]+([f'({x})^{i}'] if i else [])+([f'({y})^{j}'] if j else [])) for (i,j),c in sorted(B.poly(poly).items())]
    def tree(rows):
        if not rows:return '(0 : ℝ)'
        if len(rows)==1:return '('+rows[0]+')'
        mid=len(rows)//2;return '('+tree(rows[:mid])+' + '+tree(rows[mid:])+')'
    return tree(terms)


def emit_certificate(name,packet):
    """Row-factor tensor identities to bound elaboration memory."""
    text,names=basic_emit_certificate(name,packet)
    for index,node in enumerate(packet['nodes']):
        if node['kind']!='positive' or max(node['m'],node['n'])<8:continue
        m,n=node['m'],node['n'];rows=node['coefficients'];rowpolys=[];lemmas=[]
        for i,row in enumerate(rows):
            p={}
            for j,c in enumerate(row):
                for k in range(n-j+1):p[(0,j+k)]=p.get((0,j+k),Q(0))+Q(c)*comb(n-j,k)*(-1)**k
            expr=expression(p,y='t');rowpolys.append('fun t : ℝ => '+expr)
            lemmas.append(f"  have row_{i} (t : ℝ) : (∑ j : Fin {n+1}, (coeff ({i} : Fin {m+1}) j : ℝ)*basis {n} j t) = {expr} := by\n    change (∑ j : Fin {n+1}, (({matrix([row])[2:-1]} j : ℚ) : ℝ)*basis {n} j t) = {expr}\n    norm_num [basis,Fin.sum_univ_succ] <;> ring")
        rowfun='!['+', '.join(rowpolys)+']'
        factor='\n'.join(lemmas)+f"\n  let rowPoly : Fin {m+1} → ℝ → ℝ := {rowfun}\n  have hrows (i : Fin {m+1}) (t : ℝ) : (∑ j, (coeff i j : ℝ)*basis {n} j t) = rowPoly i t := by\n    fin_cases i\n"
        factor+=''.join(f'    · exact row_{i} t\n' for i in range(m+1))
        old=emit_leaf(name+'_node_'+str(index),B.poly(packet['polynomial']),node,packet['sign'])
        new=old.replace('  have hid :',factor+'  have hid :')
        new=new.replace('norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring',f'rw [PerfectPower.MichorGeometry.tensor_rows {m} {n} coeff rowPoly hrows]\n    norm_num [basis,rowPoly,Fin.sum_univ_succ] <;> ring')
        if old not in text:raise AssertionError('leaf rewrite missed')
        text=text.replace(old,new)
    return text,names


def deriv(p,axis):
    out={}
    for (i,j),c in B.poly(p).items():
        power=(i,j)[axis]
        if power:out[(i-(axis==0),j-(axis==1))]=c*power
    return out

def compile_point(packet,point):
    """Literal exact packet values at a positive point with rational density."""
    from .michor_geometry import _point_data,_eval,sqrt_interval
    from .divisor_square import WorkLimit
    check_metric(packet);x,y,N,D,g,h=_point_data(packet,point);lo,hi=sqrt_interval(D)
    if lo!=hi:raise WorkLimit('exact point theorem requires rational density')
    p=[str(x),str(y)];name='P'+digest({'metric':packet,'point':p})
    qex=lambda poly:expression(poly,x=rational(x,'ℚ'),y=rational(y,'ℚ')).replace(': ℝ',': ℚ')
    ex=lambda poly:f'(({qex(poly)} : ℚ) : ℝ)'
    qrf=lambda r:f'(({qex(r["numerator"])})/({qex(r["denominator"])}):ℚ)'
    rf=lambda r:f'({qrf(r)} : ℝ)'
    lines=[]
    def value(label,r):
        v=_eval(r,x,y)
        lines.append(f'''theorem {label} : {rf(r)}={rational(v)} := by
  have h : {qrf(r)}={rational(v,'ℚ')} := by decide +kernel
  rw [h]; norm_num''')
    value('curvature_times_density',packet['curvature_times_density'])
    rho=N/lo;K=_eval(packet['curvature_times_density'],x,y)/rho
    lines.append(f'''theorem numerator_at_point : {ex(packet['numerator'])}={rational(N)} := by
  have h : {qex(packet['numerator'])}={rational(N,'ℚ')} := by decide +kernel
  rw [h]; norm_num
theorem denominator_at_point : {ex(packet['denominator_squared'])}={rational(D)} := by
  have h : {qex(packet['denominator_squared'])}={rational(D,'ℚ')} := by decide +kernel
  rw [h]; norm_num
theorem source_sqrt : Real.sqrt {ex(packet['denominator_squared'])}={rational(lo)} := by
  have hd : {rational(D)}={rational(lo)}^2 := by norm_num
  rw [denominator_at_point,hd,Real.sqrt_sq (by norm_num)]
theorem density_at_point : {ex(packet['numerator'])}/Real.sqrt {ex(packet['denominator_squared'])}={rational(rho)} := by
  rw [numerator_at_point,source_sqrt]; norm_num
theorem curvature_at_point : ({rf(packet['curvature_times_density'])})/({ex(packet['numerator'])}/Real.sqrt {ex(packet['denominator_squared'])})={rational(K)} := by
  rw [curvature_times_density,density_at_point]; norm_num
''')
    source='import PerfectPower.MichorGeometry\nset_option maxHeartbeats 5000000\nset_option maxRecDepth 10000\nnamespace PerfectPower.CheckedDifferential.'+name+'\n'+'\n'.join(lines)+'\n'
    source+='#print axioms numerator_at_point\n#print axioms density_at_point\n#print axioms curvature_at_point\nend PerfectPower.CheckedDifferential.'+name+'\n'
    return {'schema':'pp-lean-conformal-point/1','point':p,'source':source,'source_sha256':sha256(source.encode()).hexdigest(),
            'specification_sha256':digest({'metric':packet,'point':p}),'kernel_checked':False,
            'scope':'exact source packet density and curvature formula values at this admitted point; analytic derivative interpretation uses classical calculus'}


def compile_dynamics(packet,*,point=None):
    if point is not None:return compile_point(packet,point)
    from .michor_geometry import _sp,_expr,_encode_expr
    check_metric(packet);name='D'+digest(packet);N=B.poly(packet['numerator']);D=B.poly(packet['denominator_squared']);lines=[]
    s,(x,y)=_sp();identity_cache={}
    def factor(a,b):
        value=s.cancel(_expr(a,s,x,y)/_expr(b,s,x,y))
        return B.poly(_encode_expr(value,s,x,y))
    def identity(label,left,right,left_source,right_source):
        if B.poly(left)!=B.poly(right):raise AssertionError(label+' polynomial identity failed')
        key=(left_source,right_source)
        if key in identity_cache:body=identity_cache[key]+' x y'
        else:
            body='by ring'
            identity_cache[key]=label
        lines.append(f'theorem {label} (x y : ℝ) : {left_source} = {right_source} := {body}\n#print axioms {label}')
    def cleared(label,a,b,n,d,f,a_source,b_source):
        fs,ns,ds=expression(f),expression(n),expression(d)
        identity(label+'_denominator',b,B.mul(d,f),b_source,f'({ds})*({fs})')
        identity(label+'_numerator',a,B.mul(n,f),a_source,f'({ns})*({fs})')
        lines.append(f'''theorem {label} (x y : ℝ) : ({ns})*({b_source})=({ds})*({a_source}) :=
  PerfectPower.MichorGeometry.factor_clears ({a_source}) ({b_source}) ({ns}) ({ds}) ({fs})
    ({label}_denominator x y) ({label}_numerator x y)''')
    for i,g in enumerate(packet['log_gradient']):
        n,d=B.poly(g['numerator']),B.poly(g['denominator'])
        a=B.add(B.scale(B.mul(deriv(N,i),D),2),B.scale(B.mul(N,deriv(D,i)),-1));b=B.scale(B.mul(N,D),2)
        a_source=f'2*({expression(deriv(N,i))})*({expression(D)})-({expression(N)})*({expression(deriv(D,i))})'
        b_source=f'2*({expression(N)})*({expression(D)})'
        cleared('log_gradient_'+str(i),a,b,n,d,factor(b,d),a_source,b_source)
        for j,h in enumerate(packet['log_hessian'][i]):
            hn,hd=B.poly(h['numerator']),B.poly(h['denominator'])
            a=B.add(B.mul(deriv(n,j),d),B.scale(B.mul(n,deriv(d,j)),-1));b=B.power(d,2)
            cleared(f'log_hessian_{i}_{j}',a,b,hn,hd,factor(b,hd),
                    f'({expression(deriv(n,j))})*({expression(d)})-({expression(n)})*({expression(deriv(d,j))})',f'({expression(d)})^2')
    for k,plane in enumerate(packet['connection']):
        for i,row in enumerate(plane):
            for j,c in enumerate(row):
                weights=[0,0]
                for index,sign in [(i,1 if k==j else 0),(j,1 if k==i else 0),(k,-1 if i==j else 0)]:weights[index]+=sign
                index=next(a for a,w in enumerate(weights) if w);sign=weights[index]
                g=packet['log_gradient'][index];n,d=B.poly(g['numerator']),B.poly(g['denominator']);cn,cd=B.poly(c['numerator']),B.poly(c['denominator'])
                a,b=B.scale(n,sign),B.scale(d,2)
                cleared(f'connection_{k}_{i}_{j}',a,b,cn,cd,factor(b,cd),f'{sign}*({expression(n)})',f'2*({expression(d)})')
    hx,hy=packet['log_hessian'][0][0],packet['log_hessian'][1][1]
    nx,dx=B.poly(hx['numerator']),B.poly(hx['denominator']);ny,dy=B.poly(hy['numerator']),B.poly(hy['denominator'])
    T=B.poly(_encode_expr(s.lcm(_expr(dx,s,x,y),_expr(dy,s,x,y)),s,x,y));fx,fy=factor(T,dx),factor(T,dy)
    identity('curvature_x_denominator',T,B.mul(dx,fx),expression(T),f'({expression(dx)})*({expression(fx)})')
    identity('curvature_y_denominator',T,B.mul(dy,fy),expression(T),f'({expression(dy)})*({expression(fy)})')
    k=packet['curvature_times_density'];kn,kd=B.poly(k['numerator']),B.poly(k['denominator']);a=B.scale(B.add(B.mul(nx,fx),B.mul(ny,fy)),-1);b=B.scale(T,2)
    cleared('curvature_times_density',a,b,kn,kd,factor(b,kd),f'-(({expression(nx)})*({expression(fx)})+({expression(ny)})*({expression(fy)}))',f'2*({expression(T)})')
    source='import PerfectPower.MichorGeometry\nset_option maxHeartbeats 5000000\nset_option maxRecDepth 10000\nnamespace PerfectPower.CheckedDifferential.'+name+'\n'+ '\n'.join(lines)+'\n'
    for label in ['log_gradient_0','log_gradient_1','connection_0_0_0','curvature_times_density']:source+='#print axioms '+label+'\n'
    source+='end PerfectPower.CheckedDifferential.'+name+'\n'
    return {'schema':'pp-lean-conformal-coefficients/1','source':source,'source_sha256':sha256(source.encode()).hexdigest(),
            'specification_sha256':digest(packet),'kernel_checked':False,
            'scope':'universal source polynomial cofactor identities for log gradient, Hessian, connection and curvature numerator; generic conservation algebra is formal; analytic derivative interpretation uses classical calculus'}


def norm_rectangle_source(packet,bridge,name):
    """Small independent complex-norm proofs for retained genus-two domains."""
    provenance=packet['provenance'] or {}
    if provenance.get('coefficients')!=['0','-1','0','0','0','1']:return None
    chart=provenance.get('chart');finite=chart=='finite'
    if chart=='branch' and provenance.get('branch')!='0':return None
    box=['2','9/4','0','1/4'] if finite else ['-1/4','1/4','-1/4','1/4']
    if chart not in ('finite','branch','infinity') or bridge['box']!=box:return None
    l,u=('1/4','1') if finite else ('1','3')
    if (bridge['lower_scale'],bridge['upper_scale'])!=(l,u):return None
    N=expression(packet['numerator']);D=expression(packet['denominator_squared'])
    a,b,c,d=map(Q,box);power='z^5-z' if finite else 'z^8-1'
    density='1+‖z‖^2' if finite else '4*(1+‖z‖^4)'
    hn='rw [hz]; ring' if finite else 'rw [show ‖z‖^4=(‖z‖^2)^2 by ring,hz]; ring'
    limits='''  have hxL := mul_nonneg (by linarith : 0 ≤ x-2) (by linarith : 0 ≤ x+2)
  have hxU := mul_nonneg (by linarith : 0 ≤ (9/4:ℝ)-x) (by linarith : 0 ≤ (9/4:ℝ)+x)
  have hyU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-y) (by linarith : 0 ≤ (1/4:ℝ)+y)
  have h0 : 2 ≤ ‖z‖ := by nlinarith [sq_nonneg y,norm_nonneg z]
  have h1 : ‖z‖ ≤ (23/10:ℝ) := by nlinarith [norm_nonneg z]
  simpa only [one_pow] using finite_norm_density z h0 h1
''' if finite else '''  have hxU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-x) (by linarith : 0 ≤ (1/4:ℝ)+x)
  have hyU := mul_nonneg (by linarith : 0 ≤ (1/4:ℝ)-y) (by linarith : 0 ≤ (1/4:ℝ)+y)
  have h1 : ‖z‖ ≤ (1/2:ℝ) := by nlinarith [norm_nonneg z]
  convert branch_norm_density z h1 using 1 <;> norm_num
'''
    return f'''import PerfectPower.MichorGeometry
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PerfectPower.CheckedDifferential.{name}
open PerfectPower.MichorGeometry
theorem density_entire_rectangle (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) :
    {rational(Q(l))}^2 < {N}/Real.sqrt {D} ∧ {N}/Real.sqrt {D} < {rational(Q(u))}^2 := by
  let z : ℂ := ⟨x,y⟩
  have hz : ‖z‖^2=x*x+y*y := complex_chart_norm x y
  have hn : {N}={density} := by {hn}
  have hd : {D}=‖{power}‖^2 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply,z,pow_succ,Complex.mul_re,Complex.mul_im]
    <;> ring
  rw [hd,Real.sqrt_sq (norm_nonneg _),hn]
{limits}#print axioms density_entire_rectangle
end PerfectPower.CheckedDifferential.{name}
'''


def compile_bridge(packet,bridge):
    check_domain(packet,bridge);name='B'+digest({'metric':packet,'bridge':bridge})
    if bridge['schema']=='pp-global-smooth-plane-bridge/1':
        N=expression(packet['numerator']);D=expression(packet['denominator_squared'])
        source=f'''import PerfectPower.MichorGeometry
namespace PerfectPower.CheckedDifferential.{name}
open PerfectPower.MichorGeometry
theorem source_density_equals (x y : ℝ) : {N}/Real.sqrt {D}=planeDensity x y := by
  have hd : 0 ≤ 1+x*x+y*y := by nlinarith [sq_nonneg x,sq_nonneg y]
  have hp : {D}=(1+x*x+y*y)^2 := by ring
  rw [hp,Real.sqrt_sq hd]
  unfold planeDensity
  congr 1 <;> ring
theorem density_all_points (x y : ℝ) :
    (1:ℝ)^2 ≤ {N}/Real.sqrt {D} ∧ {N}/Real.sqrt {D} ≤ (3/2:ℝ)^2 := by
  rw [source_density_equals]
  exact plane_rational_scale_bounds x y
#print axioms source_density_equals
#print axioms density_all_points
end PerfectPower.CheckedDifferential.{name}
'''
    elif norm_rectangle_source(packet,bridge,name) is not None:
        source=norm_rectangle_source(packet,bridge,name)
    else:
        parts=[]
        for key,certificate in sorted(bridge['witnesses'].items()):
            text,_=emit_certificate(name+'_'+key,certificate);parts.append(text)
        N=expression(packet['numerator']);D=expression(packet['denominator_squared']);l,u=map(Q,(bridge['lower_scale'],bridge['upper_scale']));a,b,c,d=map(Q,bridge['box'])
        source=f'''import PerfectPower.MichorGeometry
import PerfectPower.BernsteinBoxes
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
namespace PerfectPower.CheckedDifferential.{name}
open PerfectPower.BernsteinBoxes
open scoped BigOperators
'''+ '\n'.join(parts)+f'''
theorem density_entire_rectangle (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) :
    {rational(l)}^2 < {N}/Real.sqrt {D} ∧ {N}/Real.sqrt {D} < {rational(u)}^2 := by
  have bounds := density_comparison {N} {D} 1 {rational(l)} {rational(u)}
    ({name}_numerator_positive x y hx0 hx1 hy0 hy1)
    ({name}_denominator_positive x y hx0 hx1 hy0 hy1) (by norm_num) (by norm_num) (by norm_num)
    (by convert {name}_lower_gap x y hx0 hx1 hy0 hy1 using 1 <;> ring)
    (by convert {name}_upper_gap x y hx0 hx1 hy0 hy1 using 1 <;> ring)
  simpa only [mul_one] using bounds
#print axioms density_entire_rectangle
end PerfectPower.CheckedDifferential.{name}
'''
    return {'schema':'pp-lean-smooth-domain-bridge/1','source':source,'source_sha256':sha256(source.encode()).hexdigest(),
            'specification_sha256':digest({'metric':packet,'bridge':bridge}),'kernel_checked':False,
            'scope':'continuum pointwise density bounds in the stated domain; generic length integration and common-path infimum transfer in MichorGeometry; no unrestricted compact-curve metric claim'}
