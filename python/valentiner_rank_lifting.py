"""Joint bifundamental sources: invariant rank lifting with universal columns."""
from itertools import product
import numpy as np
from scipy.optimize import minimize
from valentiner_joint import link_poly, EPSILON, Jet
from develop_valentiner_susy_vacua import adjugate, holomorphic_down_matching
from perfectpower.flavor_mediator import canonical_mediator, mixing_record


def pack(L,A,B):
    z=np.concatenate([L.ravel(),A.ravel(),B.ravel()]);return np.r_[z.real,z.imag]


def unpack(x):
    z=np.asarray(x[:27])+1j*np.asarray(x[27:]);return [z[i:i+9].reshape(3,3) for i in [0,9,18]]


def determinant_jet(M):
    D=np.linalg.det(M);g=adjugate(M).T.ravel()
    h=np.einsum('ikm,jln,mn->ijkl',EPSILON,EPSILON,M).reshape(9,9)
    return D,g,h


def source_potential(A,t=-34.,c=.2,penalty=300.):
    D,dg,dh=determinant_jet(A);I,ig,ih=link_poly(A)
    wg=ig+2*c*D*dg;wh=ih+2*c*(D*dh+np.outer(dg,dg))
    W=I+c*D*D
    v=np.vdot(wg,wg).real-(180+6*t)*np.vdot(A,A).real+2*t*W.real+penalty*np.vdot(dg,dg).real
    dz=wh.T@wg.conj()-(180+6*t)*A.conj().ravel()+t*wg+penalty*dh.T@dg.conj()
    return v,dz


def base_potential(x,penalties=(300.,300.)):
    L,A,B=unpack(x);D,dg,dh=determinant_jet(L);_,ig,ih=link_poly(L)
    wg=(-32.4+.4*D)*dg+ig;wh=(-32.4+.4*D)*dh+ih+.4*np.outer(dg,dg)
    v=np.vdot(wg,wg).real; dz=np.zeros(27,complex);dz[:9]=wh.T@wg.conj()
    for k,M in enumerate([A,B]):
        value,g=source_potential(M,penalty=penalties[k]);v+=value;dz[9+9*k:18+9*k]=g
    return float(v),np.r_[2*dz.real,-2*dz.imag]


def trace(M):return sum(M[i,i] for i in range(3))


def cross_operators(x,derivatives=False):
    L,A,B=unpack(x)
    if derivatives:
        z=np.concatenate([L.ravel(),A.ravel(),B.ravel()]);j=[]
        for i,v in enumerate(z):
            g=np.zeros(54,complex);g[i]=1;g[i+27]=1j;j.append(Jet(v,g))
        L,A,B=[np.array(j[i:i+9],object).reshape(3,3) for i in [0,9,18]]
    dag=lambda M:M.conj().T
    norm=lambda M:trace(dag(M)@M).real
    P=dag(A)@L@B;w=trace(P)
    rows=[('dressed_norm',norm(P)),('dressed_trace', (w.conjugate()*w).real),
          ('link_up',trace(L@dag(L)@A@dag(A)).real),
          ('link_down',trace(dag(L)@L@B@dag(B)).real),
          ('label_overlap',trace(dag(A)@A@dag(B)@B).real),
          ('up_down_norm',norm(A)*norm(B)),('link_up_norm',norm(L)*norm(A)),('link_down_norm',norm(L)*norm(B))]
    if derivatives:return [n for n,v in rows],np.array([v.v.real for n,v in rows]),np.array([v.g.real for n,v in rows])
    return [n for n,v in rows],np.array([float(v) for n,v in rows])


DEFAULT_CROSS=np.array([-1.,1/3,1/5,3/10,1/10,7/100,1/20,1/25])


def potential(x,epsilon,coefficients=DEFAULT_CROSS,penalties=(300.,300.)):
    v,g=base_potential(x,penalties);_,values,jac=cross_operators(x,True)
    return v+epsilon*(coefficients@values),g+epsilon*(coefficients@jac)


def hessian(x,epsilon=0.,coefficients=DEFAULT_CROSS,penalties=(300.,300.),step=1e-5):
    E=np.eye(54);H=np.column_stack([(potential(x+step*e,epsilon,coefficients,penalties)[1]-potential(x-step*e,epsilon,coefficients,penalties)[1])/(2*step) for e in E])
    return (H+H.T)/2


def solve(x,epsilon,coefficients=DEFAULT_CROSS,penalties=(300.,300.)):
    fun=lambda x:potential(x,epsilon,coefficients,penalties)
    fit=minimize(fun,x,method='BFGS',jac=True,options={'maxiter':350,'gtol':2e-9});z=fit.x
    for _ in range(5):
        v,g=fun(z)
        if max(abs(g))<2e-10:break
        H=hessian(z,epsilon,coefficients,penalties);delta=np.linalg.solve(H,-g)
        if np.linalg.norm(delta)>.1:break
        z=z+delta
    v,g=fun(z);H=hessian(z,epsilon,coefficients,penalties)
    return z,{'energy':float(v),'stationarity_max':float(max(abs(g))),'minimum_real_Hessian_eigenvalue':float(np.linalg.eigvalsh(H)[0]),'iterations':int(fit.nit)}


def quarks(x):
    L,A,B=unpack(x);radius=.1
    yu=canonical_mediator(.9*np.eye(3),radius*A,h=.6)['Y']
    yd=holomorphic_down_matching((radius*L).conj(),(radius*B).conj())['Y']
    return yu,yd,mixing_record(yu,yd)
