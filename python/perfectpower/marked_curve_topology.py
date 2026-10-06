"""Integral Picard-Lefschetz braid actions and a geometrically marked kernel.

Branch braids must be supplied. Matrices are not guessed from numerical
monodromy, and this module does not derive braids from arbitrary polynomials.
"""
from .exact_linear import multiply, transpose, identity, inverse
from .integer_lifting import smith_certificate


def intersection(g):return [[int(j==g+i)-int(i==g+j) for j in range(2*g)] for i in range(2*g)]
def integers(a):
    if any(v.denominator!=1 for row in a for v in row):raise AssertionError('nonintegral cycle map')
    return [[int(v) for v in row] for row in a]


def braid_monodromy(genus,word):
    g=genus
    if type(g) is not int or not 1<=g<=4 or not isinstance(word,list) or len(word)>512 or any(type(i) is not int or not 1<=abs(i)<=2*g+1 for i in word):raise ValueError('genus 1 through 4 and signed bounded branch braid required')
    n=2*g;j=intersection(g);cycles=[]
    for k in range(g):
        a=[0]*n;a[k]=1
        if k:a[k-1]=-1
        b=[0]*n;b[g+k]=1;cycles.extend([a,b])
    a=[0]*n;a[g-1]=-1;cycles.append(a)
    twists=[];inverses=[]
    for d in cycles:
        cov=[sum(d[k]*j[k][l] for k in range(n)) for l in range(n)]
        twists.append([[int(k==l)+d[k]*cov[l] for l in range(n)] for k in range(n)])
        inverses.append([[int(k==l)-d[k]*cov[l] for l in range(n)] for k in range(n)])
    for k,t in enumerate(twists):
        if multiply(multiply(transpose(t),j),t)!=tuple(map(tuple,j)):raise AssertionError('twist does not preserve intersections')
        for l,u in enumerate(twists):
            if abs(k-l)==1 and multiply(multiply(t,u),t)!=multiply(multiply(u,t),u):raise AssertionError('braid relation failed')
            if abs(k-l)>1 and multiply(t,u)!=multiply(u,t):raise AssertionError('disjoint twist commutation failed')
    out=identity(n)
    for i in word:out=multiply(out,twists[i-1] if i>0 else inverses[-i-1])
    return dict(schema='pp-marked-branch-braid/1',genus=g,word=word,intersection=j,vanishing_cycles=cycles,matrix=integers(out),
        braid_relations_checked=True,integral_symplectic_checked=True,
        scope='action of the declared braid on the standard marked double cover; no automatic polynomial-loop braid extraction')


def reflection_kernel(a=1,b=2,c=3):
    """C: y^2=(x^2-a^2)(x^2-b^2)(x^2-c^2), positive real marking."""
    from fractions import Fraction as Q
    a,b,c=map(Q,(a,b,c))
    if not 0<a<b<c:raise ValueError('positive ordered rational branch radii required')
    word=[i for k in range(1,6) for i in range(k,0,-1)]
    receipt=braid_monodromy(2,word);s=receipt['matrix'];j=intersection(2);j2=intersection(1)
    if multiply(s,s)!=identity(4):raise AssertionError('rotation lift not an involution')
    transfers=[];certificates=[]
    for sign in (1,-1):
        cert=smith_certificate([[s[i][k]-sign*int(i==k) for k in range(4)] for i in range(4)]);certificates.append(cert)
        g=[row[cert['rank']:] for row in cert['right']]
        if len(g[0])!=2:raise AssertionError('wrong invariant lattice rank')
        pairing=multiply(multiply(transpose(g),j),g)
        if abs(pairing[0][1])!=2:raise AssertionError('transfer polarization is not twice principal')
        if pairing[0][1]<0:
            for row in g:row[1]=-row[1]
        transfers.append(g)
    g=[transfers[0][i]+transfers[1][i] for i in range(4)]
    product_j=[[j2[i%2][k%2] if i//2==k//2 else 0 for k in range(4)] for i in range(4)]
    f=integers(multiply(multiply([[-v for v in row] for row in product_j],transpose(g)),j))
    twice=[[2*int(i==k) for k in range(4)] for i in range(4)]
    if multiply(f,g)!=tuple(map(tuple,twice)) or multiply(g,f)!=tuple(map(tuple,twice)):raise AssertionError('norm-transfer identities failed')
    cert=smith_certificate(f);u_inv=inverse(cert['left']);f_inv=inverse(f);generators=[]
    for k,d in enumerate(cert['smith_factors']):
        if d==1:continue
        representative=[u_inv[i][k] for i in range(4)]
        torsion=[sum(f_inv[i][l]*representative[l] for l in range(4))%1 for i in range(4)]
        generators.append(dict(order=d,product_lattice_representative=list(map(str,representative)),source_torus_coordinates=list(map(str,torsion))))
    return dict(schema='pp-marked-reflection-isogeny-kernel/1',radii=list(map(str,(a,b,c))),braid=receipt,deck_matrix=s,
        transfer=g,norm=f,invariant_lattice_certificates=certificates,kernel_smith_certificate=cert,kernel_generators=generators,
        kernel_invariant_factors=[v for v in cert['smith_factors'] if v>1],isogeny_degree=4,norm_transfer_identities_checked=True,
        quotient_maps=['u=x^2, v=y','u=x^2, v=xy'],
        scope='marked genus-two real reflection family; the two eigentransfer lattices are geometrically fixed by the half-rotation braid, not an arbitrary integral realization of a de Rham projector')
