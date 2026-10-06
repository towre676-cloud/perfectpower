"""Exact compact radial trial bubbles, with a separate numerical-action adapter.

The radial polynomial integrals are rational. A bounce-action bound additionally
requires an exact metastable false vacuum and the usual mountain-pass hypotheses.
Floating-point vacuum receipts alone do not certify those hypotheses.
"""
from fractions import Fraction as F
from math import comb, pi
import numpy as np


def rat(x):
    if isinstance(x, F):
        return x
    if isinstance(x, (float, np.floating)):
        if not np.isfinite(x):
            raise ValueError("finite coefficients required")
        return F(float(x))
    return F(x)


def trim(p):
    p = list(map(rat, p))
    while len(p) > 1 and p[-1] == 0:
        p.pop()
    return p or [F(0)]


def add(a, b):
    return trim([(a[i] if i < len(a) else F(0)) +
                 (b[i] if i < len(b) else F(0))
                 for i in range(max(len(a), len(b)))])


def scale(p, c):
    return trim([rat(x) * rat(c) for x in p])


def mul(a, b):
    out = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i+j] += rat(x) * rat(y)
    return trim(out)


def evaluate(p, x):
    out = F(0)
    for c in reversed(p):
        out = out * rat(x) + rat(c)
    return out


def derivative(p):
    return trim([rat(c) * i for i, c in enumerate(p) if i])


def integral(p, power=0):
    return sum((rat(c) / (i+power+1) for i, c in enumerate(p)), F(0))


def compose(p, q):
    out = [F(0)]
    for c in reversed(p):
        out = add(mul(out, q), [rat(c)])
    return out


def interpolate(values):
    """Coefficients from values at j/(n-1), by exact Newton differences."""
    n = len(values)
    if n < 2:
        raise ValueError("at least two samples required")
    nodes = [F(j, n-1) for j in range(n)]
    divided = list(map(rat, values))
    coefficients = [divided[0]]
    for order in range(1, n):
        divided = [(divided[i+1]-divided[i]) /
                   (nodes[i+order]-nodes[i]) for i in range(n-order)]
        coefficients.append(divided[0])
    out = [F(0)]
    basis = [F(1)]
    for c, node in zip(coefficients, nodes):
        out = add(out, scale(basis, c))
        basis = mul(basis, [-node, F(1)])
    return out


def compact_bubble_polynomials(excess, path):
    """S4(R,L)/(2*pi^2) = T(L)*R^2 + U(L)*R^4.

    Core q=1 for u=r/R<=L. Shell q=1-3t^2+2t^3, t=u-L in [0,1].
    Outside q=0. Canonical path coordinates are supplied as polynomials in q.
    """
    W = trim(excess)
    if W[0] != 0:
        raise ValueError("potential excess must vanish at the exterior")
    if evaluate(W, 1) >= 0:
        raise ValueError("a strictly lower core energy is required")
    if not path:
        raise ValueError("nonempty canonical path required")
    taper = [F(1), F(0), F(-3), F(2)]
    shell = compose(W, taper)
    speed = [F(0)]
    for coordinate in path:
        tangent = derivative(compose(coordinate, taper))
        speed = add(speed, mul(tangent, tangent))
    if integral(speed) <= 0:
        raise ValueError("nonconstant path required")
    T = [F(comb(3, k), 2)*integral(speed, 3-k) for k in range(4)]
    U = [F(comb(3, k))*integral(shell, 3-k) for k in range(4)]
    U.append(evaluate(W, 1)/4)
    return {"kinetic_polynomial": T, "potential_polynomial": U,
            "core_energy_difference": evaluate(W, 1),
            "shell_potential": shell, "shell_speed_squared": speed,
            "taper": taper, "coordinate_count": len(path),
            "false_endpoint_path_derivative": evaluate(derivative(W), 0),
            "lower_endpoint_path_derivative": evaluate(derivative(W), 1)}


def bubble_at_shape(polynomials, L):
    L = rat(L)
    if L < 0:
        raise ValueError("nonnegative core-to-shell ratio required")
    T = evaluate(polynomials["kinetic_polynomial"], L)
    U = evaluate(polynomials["potential_polynomial"], L)
    if T <= 0 or U >= 0:
        raise ValueError("trial shape must have T>0 and U<0")
    return {"shape": L, "kinetic_integral": T, "potential_integral": U,
            "critical_scale_squared": -T/(2*U),
            "action_divided_by_pi_squared": -T*T/(2*U),
            "dimensionless_action": pi*pi*float(-T*T/(2*U))}


def optimize_shape(polynomials):
    """Find a numerical shape, then evaluate its trial action exactly."""
    from scipy.optimize import minimize_scalar
    T = np.array(list(map(float, polynomials["kinetic_polynomial"])))
    U = np.array(list(map(float, polynomials["potential_polynomial"])))
    roots = np.polynomial.polynomial.polyroots(U)
    positive = [r.real for r in roots if abs(r.imag) < 1e-7 and r.real >= 0]
    boundary = max(positive, default=0.)
    lo = max(1e-6, boundary*(1+1e-6)+1e-6)
    hi = max(10., lo*100.)
    def objective(logL):
        L = np.exp(logL)
        t = np.polynomial.polynomial.polyval(L, T)
        u = np.polynomial.polynomial.polyval(L, U)
        return -t*t/(2*u) if u < 0 else np.inf
    answer = minimize_scalar(objective, bounds=(np.log(lo), np.log(hi)),
                             method="bounded", options={"xatol": 1e-11})
    shape = F(format(float(np.exp(answer.x)), ".10g"))
    result = bubble_at_shape(polynomials, shape)
    result["shape_search_scope"] = "Numerical one-parameter minimization; exact action for the retained rational shape, not a certified globally optimal shape."
    return result


class BinaryRationalNonet:
    """Exact arithmetic realization of the retained numerical tensor arrays.

    The float tensors become exact binary fractions. This is distinct from
    an exact algebraic-number representation of the finite-group action.
    """
    def __init__(self, projectors, coefficients, portals, mu2, lam):
        from .nonet_potential import D_TENSOR
        from valentiner_adjoint_quartics import EMBED
        self.P = [[[rat(v) for v in row] for row in P] for P in projectors]
        self.D = [(i,j,k,rat(D_TENSOR[i,j,k]))
                  for i in range(8) for j in range(8) for k in range(8)
                  if D_TENSOR[i,j,k] != 0]
        self.E = [[(i,j,rat(E[i,j])) for i in range(8) for j in range(8)
                   if E[i,j] != 0] for E in EMBED]
        self.c = list(map(rat, coefficients))
        self.portals = list(map(rat, portals))
        self.mu2, self.lam = rat(mu2), rat(lam)

    def features(self, x):
        e,s = x[:2]
        a = x[2:]
        N = sum((v*v for v in a), F(0))
        A2 = [F(0)]*8
        for i,j,k,v in self.D:
            A2[i] += v*a[j]*a[k]
        trace3 = sum((u*v for u,v in zip(a,A2)), F(0))
        w = [sum((v*a[i]*a[j] for i,j,v in E), F(0)) for E in self.E]
        finite = sum((w[i]*v*w[j] for i,row in enumerate(self.P[2])
                      for j,v in enumerate(row)), F(0))
        self_terms = [e**4,e**3*s,e*e*s*s,e*s**3,s**4,
                      e*e*N,e*s*N,s*s*N,e*trace3,s*trace3,N*N,finite]
        return [e*e,s*s,e*s,N], [[e*v for v in a],[s*v for v in a],A2],w,self_terms

    def value(self, z):
        z = list(map(rat,z))
        if len(z) != 21:
            raise ValueError("21 canonical coordinates required")
        up,down = self.features(z[:10]),self.features(z[10:20])
        uq,uc,uw,uv = up
        dq,dc,dw,dv = down
        values = uq+dq+uv+dv+[u*v for u in uq for v in dq]
        values += [sum((a*b for a,b in zip(u,d)),F(0)) for u in uc for d in dc]
        values += [sum((uw[i]*v*dw[j] for i,row in enumerate(P)
                        for j,v in enumerate(row)), F(0)) for P in self.P[2:]]
        h2 = z[20]**2/2
        return sum((v*c for v,c in zip(values,self.c)),F(0)) - self.mu2*h2 + self.lam*h2*h2 + h2*sum((v*c for v,c in zip(uq+dq,self.portals)),F(0))

    def line_excess(self, false, lower):
        false,lower = list(map(rat,false)),list(map(rat,lower))
        values = [self.value([a+F(j,4)*(b-a) for a,b in zip(false,lower)])
                  for j in range(5)]
        polynomial = interpolate(values)
        polynomial[0] -= values[0]
        return trim(polynomial)

    def lifted_path(self, false, lower, plan):
        """Source line plus S=-J/M^2, using exact binary current tensors."""
        false,lower = list(map(rat,false)),list(map(rat,lower))
        path = [[a,b-a] for a,b in zip(false,lower)]
        groups = plan["groups"]
        if any(g["kind"] != "finite" for g in groups):
            raise ValueError("adapter currently supports the protected finite-only completion")
        mass = rat(plan["mass"])
        samples = []
        for q in [F(0),F(1,2),F(1)]:
            z = [a+q*(b-a) for a,b in zip(false,lower)]
            uw,dw = self.features(z[:10])[2],self.features(z[10:20])[2]
            coordinates = []
            for g in groups:
                E = g["embedding"]
                u,d = rat(g["up"]),rat(g["down"])
                coordinates.extend([-sum((rat(E[i,j])*(u*uw[i]+d*dw[i])
                                          for i in range(36)), F(0))/mass**2
                                    for j in range(E.shape[1])])
            samples.append(coordinates)
        path.extend([interpolate([sample[j] for sample in samples])
                     for j in range(len(samples[0]))])
        return path
