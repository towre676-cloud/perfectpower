"""Literal Lean theorem emission: discovery outputs never become trusted facts."""
from fractions import Fraction as Q
from . import bernstein_boxes as B


def rational(q,typ='ℝ'):
    q=Q(q)
    return f'({q.numerator} : {typ})' if q.denominator==1 else f'(({q.numerator} : {typ})/{q.denominator})'


def expression(p,x='x',y='y'):
    terms=[]
    for (i,j),c in sorted(B.poly(p).items()):
        terms.append('*'.join([rational(c)]+([f'({x})^{i}'] if i else [])+([f'({y})^{j}'] if j else [])))
    return '('+' + '.join(terms)+')' if terms else '(0 : ℝ)'


def matrix(rows):return '!['+', '.join('!['+', '.join(rational(c,'ℚ') for c in row)+']' for row in rows)+']'


def emit_leaf(name,p,node,sign=1):
    if node['kind']!='positive':raise ValueError('only proved positive leaves')
    a,b,c,d=map(Q,node['box']);m,n=node['m'],node['n'];rows=node['coefficients']
    if B.expand_basis(m,n,rows)!=B.normalized(B.scale(p,sign),node['box']):raise ValueError('tensor identity')
    expr=expression(B.scale(p,sign));coeff=matrix(rows)
    return f'''theorem {name} (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) : 0 < {expr} := by
  let coeff : Fin {m+1} → Fin {n+1} → ℚ := {coeff}
  have hc : ∀ i j, 0 < coeff i j := by
    decide +kernel
  have hid : ∀ s t : ℝ,
      (fun x y : ℝ => {expr}) ({rational(a)}+({rational(b-a)})*s)
        ({rational(c)}+({rational(d-c)})*t) = tensor {m} {n} coeff s t := by
    intro s t
    norm_num [tensor,basis,coeff,Fin.sum_univ_succ] <;> ring
  exact rectangle_positive (fun x y : ℝ => {expr})
    {rational(a)} {rational(b)} {rational(c)} {rational(d)} (by norm_num) (by norm_num)
    {m} {n} coeff hc (by intro s t; convert hid s t using 1 <;> ring) x y hx0 hx1 hy0 hy1
'''


def emit_certificate(name,packet):
    if not B.verify(packet) or not packet['complete']:raise ValueError('complete valid certificate required')
    p=B.poly(packet['polynomial']);sign=packet['sign'];lines=[];names={}
    for i,node in enumerate(reversed(packet['nodes'])):
        ident=f'{name}_node_{len(packet["nodes"])-1-i}'
        names[tuple(node['address'])]=ident
        if node['kind']=='positive':lines.append(emit_leaf(ident,p,node,sign))
        elif node['kind']=='split':
            a,b,c,d=map(Q,node['box']);axis=node['axis'];mid=(a+b)/2 if axis==0 else (c+d)/2
            left=names[tuple(node['address']+[0])];right=names[tuple(node['address']+[1])]
            coord='x' if axis==0 else 'y'
            leftargs='hx0 hmid hy0 hy1' if axis==0 else 'hx0 hx1 hy0 hmid'
            rightargs='(by linarith) hx1 hy0 hy1' if axis==0 else 'hx0 hx1 (by linarith) hy1'
            lines.append(f'''theorem {ident} (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) : 0 < {expression(B.scale(p,sign))} := by
  by_cases hmid : {coord} ≤ {rational(mid)}
  · exact {left} x y {leftargs}
  · exact {right} x y {rightargs}
''')
        else:raise ValueError('unresolved leaf')
    lines.append(f'abbrev {name} := {names[()]}\n')
    return '\n'.join(lines),list(names.values())


def emit_metric(name,packet):
    from .metric_boxes import verify
    if not verify(packet) or not packet['complete']:raise ValueError('metric certificate')
    parts=[];allnames=[]
    for key,cert in packet['witnesses'].items():
        text,names=emit_certificate(name+'_'+key,cert);parts.append(text);allnames+=names
    a,b,c,d=map(Q,packet['box']);N=expression(packet['chart_data']['numerator']);D=expression(packet['chart_data']['denominator_modulus_squared'])
    l,u,r=map(Q,[packet['lower_scale'],packet['upper_scale'],packet['reference_density']])
    parts.append(f'''theorem {name}_density (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) :
    {rational(l)}^2*{rational(r)} < {N}/Real.sqrt {D} ∧
      {N}/Real.sqrt {D} < {rational(u)}^2*{rational(r)} := by
  apply density_comparison {N} {D} {rational(r)} {rational(l)} {rational(u)}
    ({name}_numerator_positive x y hx0 hx1 hy0 hy1)
    ({name}_denominator_positive x y hx0 hx1 hy0 hy1) (by norm_num) (by norm_num) (by norm_num)
  · convert {name}_lower_gap x y hx0 hx1 hy0 hy1 using 1 <;> ring
  · convert {name}_upper_gap x y hx0 hx1 hy0 hy1 using 1 <;> ring
''');allnames.append(name+'_density')
    return '\n'.join(parts),allnames


def emit_exclusion(name,packet):
    if not B.verify_exclusion(packet) or not packet['excluded']:raise ValueError('excluded valid system required')
    text,names=emit_certificate(name,packet['certificate'])
    eqs=[expression(p) for p in packet['equations']];weights=[expression(p) for p in packet['weights']]
    a,b,c,d=map(Q,packet['certificate']['box']);sign=packet['certificate']['sign']
    combined=expression(B.scale(packet['certificate']['polynomial'],sign))
    rhs=' + '.join(f'{rational(sign)}*{w}*{f}' for w,f in zip(weights,eqs))
    hypotheses=' ∧ '.join(f'{f}=0' for f in eqs)
    destruct=('intro h0' if len(eqs)==1 else 'rintro ⟨'+','.join(f'h{i}' for i in range(len(eqs)))+'⟩')
    simp=', '.join(f'h{i}' for i in range(len(eqs)))
    text+=f'''\ntheorem {name}_no_common_zero (x y : ℝ) (hx0 : {rational(a)} ≤ x) (hx1 : x ≤ {rational(b)})
    (hy0 : {rational(c)} ≤ y) (hy1 : y ≤ {rational(d)}) : ¬({hypotheses}) := by
  {destruct}
  have hp := {name} x y hx0 hx1 hy0 hy1
  have hid : {combined}=({rhs}) := by ring
  rw [hid] at hp
  rw [{simp}] at hp
  norm_num at hp
'''
    return text,names+[name+'_no_common_zero']
