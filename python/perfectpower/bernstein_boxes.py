"""Exact two-variable positivity and joint arithmetic exclusion certificates.

Discovery is budgeted. Replay checks supplied coefficients and every rectangle,
not the producer's decisions. Lean emission checks literal polynomial identities.
"""
from fractions import Fraction as Q
from math import comb
from .divisor_square import WorkLimit


def poly(terms):
    out={}
    if isinstance(terms,dict): terms=[(i,j,c) for (i,j),c in terms.items()]
    for i,j,c in terms:
        if type(i) is not int or type(j) is not int or not 0<=i<=32 or not 0<=j<=32:
            raise ValueError('degrees must be integers in 0..32')
        c=Q(c)
        if max(c.numerator.bit_length(),c.denominator.bit_length())>4096: raise WorkLimit('coefficient size')
        out[i,j]=out.get((i,j),Q(0))+c
    out={k:v for k,v in out.items() if v}
    if len(out)>4096: raise WorkLimit('monomial budget')
    return out


def encode(p):return [[i,j,str(c)] for (i,j),c in sorted(poly(p).items())]
def add(p,q):return poly(list(encode(p))+list(encode(q)))
def scale(p,c):return poly({k:v*Q(c) for k,v in poly(p).items()})
def mul(p,q):
    out={}
    for (i,j),a in poly(p).items():
        for (k,l),b in poly(q).items():out[i+k,j+l]=out.get((i+k,j+l),Q(0))+a*b
    return poly(out)
def power(p,n):
    if type(n) is not int or not 0<=n<=32:raise ValueError('power budget')
    out={(0,0):Q(1)}
    for _ in range(n):out=mul(out,p)
    return out

def evaluate(p,x,y):return sum((c*Q(x)**i*Q(y)**j for (i,j),c in poly(p).items()),Q(0))

def rectangle(box):
    if len(box)!=4:raise ValueError('four rational endpoints')
    a,b,c,d=map(Q,box)
    if a>=b or c>=d:raise ValueError('nonempty ordered rectangle')
    if any(max(q.numerator.bit_length(),q.denominator.bit_length())>4096 for q in (a,b,c,d)):
        raise WorkLimit('endpoint size')
    return a,b,c,d


def normalized(p,box):
    a,b,c,d=rectangle(box);out={}
    for (i,j),v in poly(p).items():
        for k in range(i+1):
            for l in range(j+1):
                out[k,l]=out.get((k,l),Q(0))+v*comb(i,k)*a**(i-k)*(b-a)**k*comb(j,l)*c**(j-l)*(d-c)**l
    return poly(out)


def bernstein(p,box):
    """Unnormalized tensor basis s^i(1-s)^(m-i)t^j(1-t)^(n-j)."""
    p=normalized(p,box);m=max((i for i,j in p),default=0);n=max((j for i,j in p),default=0)
    rows=[]
    for i in range(m+1):
        row=[]
        for j in range(n+1):
            value=sum((v*Q(comb(i,k),comb(m,k))*Q(comb(j,l),comb(n,l))
                       for (k,l),v in p.items() if k<=i and l<=j),Q(0))
            row.append(str(value*comb(m,i)*comb(n,j)))
        rows.append(row)
    return m,n,rows


def expand_basis(m,n,rows):
    if type(m) is not int or type(n) is not int or not 0<=m<=32 or not 0<=n<=32:
        raise ValueError('tensor degree')
    if len(rows)!=m+1 or any(len(r)!=n+1 for r in rows):raise ValueError('tensor dimensions')
    out={}
    for i,row in enumerate(rows):
        for j,coefficient in enumerate(row):
            coefficient=Q(coefficient)
            for a in range(m-i+1):
                for b in range(n-j+1):
                    k=(i+a,j+b)
                    out[k]=out.get(k,Q(0))+coefficient*comb(m-i,a)*comb(n-j,b)*(-1)**(a+b)
    return poly(out)


def certify(terms,box,*,sign=1,depth=4,node_limit=10000):
    p=poly(terms);box=rectangle(box)
    if sign not in (-1,1) or type(sign) is not int:raise ValueError('sign')
    if type(depth) is not int or not 0<=depth<=12:raise ValueError('depth 0..12')
    if type(node_limit) is not int or node_limit<1:raise ValueError('positive node limit')
    nodes=[];closed=True
    def visit(bounds,address):
        nonlocal closed
        if len(nodes)>=node_limit:raise WorkLimit('box subdivision budget; no complete claim')
        m,n,rows=bernstein(scale(p,sign),bounds)
        good=all(Q(v)>0 for row in rows for v in row)
        node={'address':address,'box':list(map(str,bounds)),'m':m,'n':n,'coefficients':rows,
              'kind':'positive' if good else 'unresolved'}
        nodes.append(node)
        if good:return
        if len(address)>=depth:closed=False;return
        a,b,c,d=bounds;axis=0 if b-a>=d-c else 1;mid=(a+b)/2 if axis==0 else (c+d)/2
        node['kind']='split';node['axis']=axis
        children=((a,mid,c,d),(mid,b,c,d)) if axis==0 else ((a,b,c,mid),(a,b,mid,d))
        for i,child in enumerate(children):visit(child,address+[i])
    visit(box,[])
    return {'schema':'pp-bernstein-box/1','polynomial':encode(p),'box':list(map(str,box)),
            'sign':sign,'nodes':nodes,'complete':closed,'kernel_checked':False}


def verify(packet):
    try:
        if packet['schema']!='pp-bernstein-box/1' or packet['kernel_checked'] is not False:return False
        p=poly(packet['polynomial']);root=rectangle(packet['box']);sign=packet['sign']
        if type(sign) is not int or sign not in (-1,1):return False
        pending=[(root,[])];complete=True
        if len(packet['nodes'])>100000:return False
        for node in packet['nodes']:
            if not pending:return False
            bounds,address=pending.pop()
            if node['address']!=address or list(map(str,bounds))!=node['box']:return False
            if len(address)>12:return False
            rows=node['coefficients']
            if expand_basis(node['m'],node['n'],rows)!=normalized(scale(p,sign),bounds):return False
            if node['kind']=='positive':
                if not all(Q(x)>0 for row in rows for x in row):return False
            elif node['kind']=='unresolved':complete=False
            elif node['kind']=='split':
                axis=node['axis']
                if type(axis) is not int or axis not in (0,1):return False
                a,b,c,d=bounds;mid=(a+b)/2 if axis==0 else (c+d)/2
                children=((a,mid,c,d),(mid,b,c,d)) if axis==0 else ((a,b,c,mid),(a,b,mid,d))
                pending.extend([(children[1],address+[1]),(children[0],address+[0])])
            else:return False
        return not pending and packet['complete'] is complete
    except (KeyError,ValueError,TypeError,IndexError,ZeroDivisionError,WorkLimit):return False


def joint_exclusion(equations,weights,box,**options):
    equations=[poly(p) for p in equations]
    if not equations or len(equations)!=len(weights):raise ValueError('equations and weights')
    weights=[poly(w) if isinstance(w,(dict,list,tuple)) else {(0,0):Q(w)} for w in weights];combined={}
    for p,w in zip(equations,weights):combined=add(combined,mul(p,w))
    certificate=certify(combined,box,**options)
    return {'schema':'pp-joint-box-exclusion/1','equations':[encode(p) for p in equations],
            'weights':[encode(w) for w in weights],'certificate':certificate,
            'excluded':certificate['complete'],'kernel_checked':False}


def verify_exclusion(packet):
    try:
        if packet['schema']!='pp-joint-box-exclusion/1' or packet['kernel_checked'] is not False:return False
        eqs=packet['equations'];weights=packet['weights']
        if not eqs or len(eqs)!=len(weights):return False
        p={}
        for eq,w in zip(eqs,weights):p=add(p,mul(eq,w))
        cert=packet['certificate']
        if 'residual_boxes' in packet and packet['residual_boxes'] != [node['box'] for node in cert['nodes'] if node['kind']=='unresolved']:return False
        return verify(cert) and p==poly(cert['polynomial']) and packet['excluded'] is cert['complete']
    except (KeyError,ValueError,TypeError,IndexError,ZeroDivisionError,WorkLimit):return False


def candidate_boxes(equations,weights,box,**options):
    """Necessary residual boxes for common real or integer zeros; never witnesses."""
    packet=joint_exclusion(equations,weights,box,**options)
    packet['residual_boxes']=[node['box'] for node in packet['certificate']['nodes'] if node['kind']=='unresolved']
    return packet


def affine_remainder(F,G):
    """Exact y-division by a*y+B(x), with nonzero constant a.

    Emits an ideal identity; no integer image is cancelled or forgotten.
    """
    F,G=poly(F),poly(G)
    ys={k:c for k,c in G.items() if k[1]}
    if set(ys)!={(0,1)} or not ys[0,1]:raise ValueError('constant nonzero affine y coefficient required')
    a=ys[0,1];remainder=dict(F);quotient={}
    while any(j for i,j in remainder):
        degree=max(j for i,j in remainder)
        layer={(i,degree-1):c/a for (i,j),c in remainder.items() if j==degree}
        quotient=add(quotient,layer)
        remainder=add(remainder,scale(mul(layer,G),-1))
    assert add(mul(quotient,G),remainder)==F
    return quotient,remainder


def compile_system(equations,box,*,route_limit=16,**options):
    """Find a simple ideal separator, then retain complete necessary box coverage."""
    equations=[poly(p) for p in equations]
    if not equations or len(equations)>16:raise ValueError('system must have 1..16 equations')
    if type(route_limit) is not int or not 1<=route_limit<=256:raise ValueError('route budget 1..256')
    candidates=[]
    for j,G in enumerate(equations):
        if set(k for k in G if k[1])=={(0,1)}:
            for i,F in enumerate(equations):
                if i==j:continue
                quotient,remainder=affine_remainder(F,G)
                if remainder:
                    weights=[{} for _ in equations];weights[i]={(0,0):Q(1)};weights[j]=scale(quotient,-1)
                    candidates.append(('affine_elimination',weights))
    for i in range(len(equations)):
        weights=[{} for _ in equations];weights[i]={(0,0):Q(1)};candidates.append(('individual',weights))
    for i,F in enumerate(equations):
        for j in range(i+1,len(equations)):
            G=equations[j];keys=set(F)&set(G)
            if keys:
                key=max(keys,key=lambda k:(sum(k),k));ratio=F[key]/G[key]
                weights=[{} for _ in equations];weights[i]={(0,0):Q(1)};weights[j]={(0,0):-ratio}
                candidates.append(('leading_cancellation',weights))
    best=None
    tried=0
    for route,weights in candidates:
        if tried>=route_limit:break
        combined={}
        for F,W in zip(equations,weights):combined=add(combined,mul(F,W))
        if not combined:continue
        for sign in (1,-1):
            if tried>=route_limit:break
            tried+=1
            packet=candidate_boxes(equations,weights,box,sign=sign,**options);packet['route']=route;packet['routes_examined']=tried
            if packet['excluded']:return packet
            if best is None or len(packet['residual_boxes'])<len(best['residual_boxes']):best=packet
    if best is None:
        best=candidate_boxes(equations,[1]+[0]*(len(equations)-1),box,**options);best['route']='individual'
    return best


def zero_strata(terms,box):
    """Exact zero locus by coordinate faces when the tensor has one weak sign.

    Open interiors are explicit. A mixed-sign tensor returns unresolved instead
    of mistaking a numerical sample or a weak inequality for a strict exclusion.
    """
    p=poly(terms);bounds=rectangle(box);m,n,rows=bernstein(p,bounds)
    coeff=[[Q(c) for c in row] for row in rows]
    sign=1 if all(c>=0 for row in coeff for c in row) else -1 if all(c<=0 for row in coeff for c in row) else None
    strata=[]
    if sign is not None:
        active=lambda state,d: [0] if state=='lower' else [d] if state=='upper' else list(range(d+1))
        for xstate in ['lower','interior','upper']:
            for ystate in ['lower','interior','upper']:
                if all(coeff[i][j]==0 for i in active(xstate,m) for j in active(ystate,n)):
                    strata.append({'x':xstate,'y':ystate})
    return {'schema':'pp-bernstein-zero-strata/1','polynomial':encode(p),'box':list(map(str,bounds)),
            'm':m,'n':n,'coefficients':rows,'weak_sign':sign,'complete':sign is not None,
            'zero_strata':strata,'kernel_checked':False}


def verify_zero_strata(packet):
    try:
        if packet['schema']!='pp-bernstein-zero-strata/1' or packet['kernel_checked'] is not False:return False
        p=poly(packet['polynomial']);m,n=packet['m'],packet['n'];rows=packet['coefficients']
        if expand_basis(m,n,rows)!=normalized(p,packet['box']):return False
        coeff=[[Q(c) for c in row] for row in rows]
        sign=1 if all(c>=0 for row in coeff for c in row) else -1 if all(c<=0 for row in coeff for c in row) else None
        if packet['weak_sign']!=sign or packet['complete'] is not (sign is not None):return False
        expected=[]
        if sign is not None:
            active=lambda state,d:[0] if state=='lower' else [d] if state=='upper' else list(range(d+1))
            for xstate in ['lower','interior','upper']:
                for ystate in ['lower','interior','upper']:
                    if all(coeff[i][j]==0 for i in active(xstate,m) for j in active(ystate,n)):
                        expected.append({'x':xstate,'y':ystate})
        return packet['zero_strata']==expected
    except (KeyError,ValueError,TypeError,IndexError,ZeroDivisionError,WorkLimit):return False


def solve_affine_faces(equations,box):
    """Complete bounded integer models when an affine elimination has face-only zeros."""
    eqs=[poly(p) for p in equations];a,b,c,d=rectangle(box)
    for j,G in enumerate(eqs):
        if set(k for k in G if k[1])!={(0,1)}:continue
        for i,F in enumerate(eqs):
            if i==j:continue
            quotient,remainder=affine_remainder(F,G);strata=zero_strata(remainder,box)
            if not strata['complete'] or any(s['x']=='interior' for s in strata['zero_strata']):continue
            xs={a if s['x']=='lower' else b for s in strata['zero_strata']};models=[]
            for x in sorted(xs):
                y=-evaluate(G,x,0)/G[0,1]
                if x.denominator==1 and y.denominator==1 and c<=y<=d and all(evaluate(eq,x,y)==0 for eq in eqs):
                    models.append([x.numerator,y.numerator])
            return {'schema':'pp-affine-face-system/1','equations':[encode(eq) for eq in eqs],
                    'eliminated_equation':j,'source_equation':i,'quotient':encode(quotient),'remainder':encode(remainder),
                    'zero_certificate':strata,'models':models,'complete':True,'kernel_checked':False}
    return {'schema':'pp-affine-face-system/1','equations':[encode(eq) for eq in eqs],
            'box':list(map(str,(a,b,c,d))),'models':[],'complete':False,'kernel_checked':False}


def verify_affine_faces(packet):
    try:
        if packet['schema']!='pp-affine-face-system/1' or packet['kernel_checked'] is not False:return False
        eqs=[poly(p) for p in packet['equations']]
        if not packet['complete']:
            rectangle(packet['box']);return packet['complete'] is False and packet['models']==[]
        i,j=packet['source_equation'],packet['eliminated_equation']
        if type(i) is not int or type(j) is not int or i==j or not 0<=i<len(eqs) or not 0<=j<len(eqs):return False
        G=eqs[j]
        if set(k for k in G if k[1])!={(0,1)}:return False
        Qp,R=poly(packet['quotient']),poly(packet['remainder'])
        if add(mul(Qp,G),R)!=eqs[i] or any(y for x,y in R):return False
        cert=packet['zero_certificate']
        if not verify_zero_strata(cert) or not cert['complete'] or poly(cert['polynomial'])!=R:return False
        if any(s['x']=='interior' for s in cert['zero_strata']):return False
        a,b,c,d=rectangle(cert['box']);models=[]
        xs={a if s['x']=='lower' else b for s in cert['zero_strata']}
        for x in sorted(xs):
            y=-evaluate(G,x,0)/G[0,1]
            if x.denominator==1 and y.denominator==1 and c<=y<=d and all(evaluate(eq,x,y)==0 for eq in eqs):
                models.append([x.numerator,y.numerator])
        return packet['complete'] is True and packet['models']==models
    except (KeyError,ValueError,TypeError,IndexError,ZeroDivisionError,WorkLimit):return False
