"""Replayable Brumer--Cremona quadratic-character lower bounds over Q."""
from copy import deepcopy
from .elliptic_arithmetic import EllipticCurve,point,encode_point,primes,rational_roots,q
from . import polyalg as P
from .divisor_square import WorkLimit


def binary_rows(rows):
    basis={};relations=[]
    for i,row in enumerate(rows):
        v=row;mask=1<<i
        while v:
            k=v.bit_length()-1
            if k not in basis:basis[k]=(v,mask);break
            v^=basis[k][0];mask^=basis[k][1]
        if not v:relations.append(mask)
    return len(basis),relations


def local_matrix(E,points,prime_bound=500):
    _,f=E.integral_cubic();df=P.derivative(f);rows=[0]*len(points);packets=[];cols=0;no_root=None
    for p in primes(prime_bound):
        if p<5 or E.discriminant.numerator%p==0 or E.discriminant.denominator%p==0:continue
        roots=[r for r in range(p) if P.evaluate(f,r)%p==0]
        if not roots:
            if no_root is None:no_root=p
            continue
        packets.append({'prime':p,'roots':roots})
        for i,P0 in enumerate(points):
            z=E.integral_point(P0)
            if z is None or z[0].denominator%p==0:continue
            x=z[0].numerator*pow(z[0].denominator,-1,p)%p
            for j,r in enumerate(roots):
                a=(x-r)%p
                if a==0:a=int(P.evaluate(df,r))%p
                if pow(a,(p-1)//2,p)==p-1:rows[i]|=1<<(cols+j)
        cols+=len(roots)
    return rows,packets,no_root,cols


def two_torsion_proof(E,no_root=None):
    _,f=E.integral_cubic()
    if no_root is not None:
        assert all(P.evaluate(f,r)%no_root for r in range(no_root))
        return 0,{'kind':'irreducible_cubic_mod_prime','prime':no_root},()
    roots=rational_roots(f)
    if len(roots) not in (0,1,3):raise AssertionError('separable cubic rational roots')
    return (0 if not roots else 1 if len(roots)==1 else 2),{'kind':'complete_rational_roots','roots':[str(r) for r in roots]},E.two_torsion()


def torsion_closure(E,base,node_limit=100000):
    group={None,*base};front=list(base)
    for _ in range(3):
        new=[]
        for t in front:
            try:hs=E.halves(t,node_limit)
            except WorkLimit:continue
            for h in hs:
                if E.mul(h,16) is None and h not in group:group.add(h);new.append(h)
        front=new
        if not front:break
    # Close the discovered subgroup, retaining an exact order check.
    for a in list(group):
        for b in list(group):
            c=E.add(a,b)
            if E.mul(c,16) is None:group.add(c)
    return sorted(group,key=lambda p:encode_point(p) or [])


def certify_independence(curve,points,prime_bound=500,halving_limit=32,node_limit=100000):
    E=curve if isinstance(curve,EllipticCurve) else EllipticCurve(curve)
    if type(halving_limit) is not int or not 0<=halving_limit<=64:raise ValueError('bounded halving limit required')
    original=[E.checked(p) for p in points]
    if len(original)>64:raise ValueError('at most 64 witnesses')
    work=list(original);rows,packets,no_root,cols=local_matrix(E,work,prime_bound)
    t,tp,two=two_torsion_proof(E,no_root);tors=[None];aux=[];steps=[];seen={tuple(work)}
    if binary_rows(rows)[0]-t<len(work) and t:
        tors=torsion_closure(E,two,node_limit);aux=[p for p in tors if p is not None]
    best=None
    for iteration in range(halving_limit+1):
        rows,packets,_,cols=local_matrix(E,work+aux,prime_bound)
        rank,relations=binary_rows(rows);lower=max(0,min(len(work),rank-t))
        result=dict(schema='pp-elliptic-independence/1',curve=E.specification,original_points=[encode_point(p) for p in original],
            working_points=[encode_point(p) for p in work],auxiliary_torsion=[encode_point(p) for p in aux],two_torsion_dimension=t,
            two_torsion_proof=tp,primes=packets,matrix_rows=[str(v) for v in rows],columns=cols,matrix_rank=rank,
            rank_lower_bound=lower,halving_steps=deepcopy(steps),prime_bound=prime_bound,
            independent=lower==len(original),scope='certified lower bound for the rational witness span modulo torsion; not a complete basis')
        if best is None or lower>=best['rank_lower_bound']:best=result
        if lower==len(original) or iteration==halving_limit:break
        acted=False
        for mask in relations:
            indices=[i for i in range(len(work)) if mask>>i&1]
            if not indices:continue
            total=None
            for i in indices:total=E.add(total,work[i])
            if total is None or E.mul(total,16) is None:continue
            # The mod-2 relation may differ by a torsion point.
            for offset in tors:
                target=E.add(total,offset)
                try:hs=E.halves(target,node_limit)
                except WorkLimit:continue
                for h in hs:
                    choices=sorted(indices,key=lambda i: sum(v.numerator.bit_length()+v.denominator.bit_length() for v in work[i]) if work[i] else 0,reverse=True)
                    for i in choices:
                        candidate=work[:];candidate[i]=h
                        if tuple(candidate) in seen:continue
                        seen.add(tuple(candidate));steps.append({'indices':indices,'offset':encode_point(offset),'replace':i,'half':encode_point(h)})
                        work=candidate;acted=True;break
                    if acted:break
                if acted:break
            if acted:break
        if not acted:break
    if not replay_independence(best):raise AssertionError('new certificate failed independent replay')
    return best


def replay_independence(cert):
    try:
        if cert['schema']!='pp-elliptic-independence/1':return False
        E=EllipticCurve(cert['curve']);work=[E.checked(p) for p in cert['original_points']]
        aux=[E.checked(p) for p in cert['auxiliary_torsion']]
        if any(E.mul(p,16) is not None for p in aux):return False
        tp=cert['two_torsion_proof'];_,f=E.integral_cubic()
        if tp['kind']=='irreducible_cubic_mod_prime':
            p=tp['prime']
            if p not in primes(p) or any(P.evaluate(f,r)%p==0 for r in range(p)):return False
            t=0
        elif tp['kind']=='complete_rational_roots':
            roots=rational_roots(f)
            if [str(r) for r in roots]!=tp['roots'] or len(roots) not in (0,1,3):return False
            t=0 if not roots else 1 if len(roots)==1 else 2
        else:return False
        if t!=cert['two_torsion_dimension']:return False
        for s in cert['halving_steps']:
            ii=s['indices'];i=s['replace'];h=E.checked(s['half']);offset=E.checked(s['offset'])
            if not ii or len(set(ii))!=len(ii) or any(type(j) is not int or not 0<=j<len(work) for j in ii) or i not in ii:return False
            if E.mul(offset,16) is not None:return False
            total=offset
            for j in ii:total=E.add(total,work[j])
            if E.mul(h,2)!=total:return False
            work[i]=h
        if [encode_point(p) for p in work]!=cert['working_points']:return False
        rows,packets,_,cols=local_matrix(E,work+aux,cert['prime_bound']);rank,_=binary_rows(rows)
        lower=max(0,min(len(work),rank-t))
        return packets==cert['primes'] and [str(v) for v in rows]==cert['matrix_rows'] and cols==cert['columns'] and rank==cert['matrix_rank'] and lower==cert['rank_lower_bound'] and cert['independent']==(lower==len(work))
    except (ValueError,KeyError,TypeError,ArithmeticError,WorkLimit,IndexError):return False


def independence_certificate(ainvs,points,**kwargs):return certify_independence(EllipticCurve(ainvs),points,**kwargs)
