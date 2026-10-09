"""Interval-certified O(3) and O(4) bounce actions (Arb), item N40 part 2.

Bounces of wall_nucleation: radial solutions of phi''+(d-1)phi'/r=V'(phi), phi'(0)=0,
phi -> f (false vacuum) for V(x)=(x^2-1)^2/4-eps x, and of the universal cubic
V(w)=w^2/2-w^3/3 (f=0) behind the near-spinodal constants C_3, C_4.

Validated integrator (no floating step is trusted)
--------------------------------------------------
State (phi, P=r^{d-1}phi', q=1/r) with the polynomial field
    phi'=q^{d-1} P,  P'=r^{d-1} V'(phi),  q'=-q^2
(optionally the variational pair psi=d phi/d phi0, Psi=d P/d phi0). The integrating-factor
variable P removes the friction term from the Jacobian, so interval widths grow at the
true rate sqrt|V''| instead of picking up (d-1)/r. On each step [r0, r0+h] a Taylor
polynomial Pol (degree N, exact dyadic coefficients) is a Taylor model: with the Picard
operator T(Y)(s)=y0+int_0^s F(r0+s', Y(s')) ds' (y0 the whole initial box), Arb gives
res_i >= sup|T(Pol)_i-Pol_i| and J_ij >= sup|dF_i/dy_j| on the tube Pol+[-eps,eps]; if
res+h J eps < eps componentwise, T maps the tube into itself and (Perron-Frobenius) is a
contraction in a weighted sup norm, so every solution from y0 stays in the tube.
The first step [0,h0] uses the regular-singular operator
    T(phi)(r)=phi0+int_0^r s^{1-d} int_0^s t^{d-1} V'(phi(t)) dt ds,
which is exact on polynomials, with contraction constant sup|V''| h0^2/(2d).

Existence (Coleman's overshoot/undershoot argument, made finite)
---------------------------------------------------------------
O = {phi0: phi(r)<f for some r while phi'<0 on (0,r]} and U = {phi0: phi'(r)>0 for some r
while phi>f on [0,r]} are open and disjoint. A certified undershoot at one end of
[lo,hi] and overshoot at the other give phi0* in (lo,hi) in neither set; its solution is
strictly decreasing, and its limit is a zero of V' below phi0*. The barrier top b is
excluded (the linearisation there oscillates, which would make phi'>0), so phi -> f:
a bounce. Its action is S=(2/d)T (Derrick), T=(Omega_d/2) int r^{d-1} phi'^2.

Action enclosure
----------------
The family box [lo,hi] is integrated to R where u=phi-f is small; it contains the bounce.
Tail: with u>0, u'<0 and V'(f+u)>=0 for r>=R,
    int_R^inf r^{d-1}u'^2 = -R^{d-1}u u'(R) - int_R^inf r^{d-1} u V'(f+u) in [0, u(R)|P(R)|],
and, while V' increases on [f, f+u(R)], int_R^inf r^{d-1}(V-V_f) lies in the same interval.
Hence s_d=(Omega_d/d) K with K in [K_R, K_R+u|P|]; the direct S=T+U is a cross-check.

Least action (uniqueness)
-------------------------
The Coleman-Glaser-Martin least-action bounce is radially non-increasing with values in
[f,t], so it is a monotone radial solution with V(phi0)<=V(f), i.e. phi0 in [e,t) (e the
exit point). The certificate excludes every other phi0 in [e,t):
  * [e_lo, phi0*-Delta] and [phi0*+Delta, t-eta] by adaptive classification of phi0-boxes,
    each run as a mean-value family (centre trajectory plus the variational pair over the
    whole box, phi in phi_c+[-w,w]|psi|), bisected in log-distance to phi0* and to t;
  * the box B=[phi0*-Delta, phi0*+Delta] by the variational equation: if psi(R) and Psi(R)
    have one strict sign on B and phi(R)<x_infl (V''>0 beyond), two bounces in B would have
    a difference w with w w'>0 at R and (r^{d-1}w')'=r^{d-1}Q w, Q>0, so |w| could not decay;
  * [t-eta, t) by an energy bound: E=phi'^2/2-(V(phi)-V(f)) decreases by
    D=int (d-1)phi'^2/r; while t-phi<=eta2 the comparison u<=eta g(kappa r) (g=sinh z/z or
    2I_1(z)/z) keeps r>=r1; D(0,r1)<=V(t-eta2)-V(t) and D(r1,.)<=(d-1)A/r1 with
    A>=int_f^t sqrt(2(2V(f)-V(t)-V)); E staying positive forces an overshoot.
For the cubic the positive radial solution of Delta w=w-w^2 is unique (Kwong 1989, p=2
subcritical in d=3,4), so only existence is certified.

Scope: tree potential only. The one-loop/two-loop corrected potentials contain
log|m^2(phi)| (a non-analytic point inside the bounce) and thermal splines; they are not
enclosed here. The near-spinodal law s=C_d (eps_sp-eps)^{(6-d)/4} is an asymptotic
statement; only the constant C_d=(2*3^{1/4})^{(6-d)/2} s_cubic(d)/3 is certified.
"""
from fractions import Fraction
from math import log as _log
from flint import arb, arb_poly, ctx, fmpq

# ---------------------------------------------------------------- arithmetic helpers


class _prec:
    def __init__(self, bits):
        self.bits = bits

    def __enter__(self):
        self.old = ctx.prec
        ctx.prec = self.bits

    def __exit__(self, *a):
        ctx.prec = self.old


def exact(q):
    """Exact arb of a rational / float (floats are dyadic) / decimal string."""
    q = Fraction(q)
    return arb(fmpq(q.numerator, q.denominator))


UNIT = arb(0, 1)


def ball0(e):
    return UNIT*e


def up(x):
    """Upper bound of |x| as an exact arb."""
    return x.abs_upper()


def poly_sup(p, h):
    """sup_{0<=s<=h}|p(s)| <= sum |c_k| h^k."""
    acc = arb(0)
    hk = arb(1)
    for c in p.coeffs():
        acc += up(c)*hk
        hk *= h
    return up(acc)


def poly_range(p, h):
    """Enclosure of p([0,h]): c0+c1[0,h]+sum_{k>=2}|c_k|h^k[-1,1]."""
    c = p.coeffs()
    if not c:
        return arb(0)
    out = c[0]
    if len(c) > 1:
        out += c[1]*arb(h/2, h/2)
    if len(c) > 2:
        out += ball0(poly_sup(arb_poly([0, 0] + c[2:]), h))
    return out


_BERN = {}


def _bern_table(n):
    if n not in _BERN:
        from math import comb
        _BERN[n] = [[fmpq(comb(j, i), comb(n, i)) for i in range(j + 1)] for j in range(n + 1)]
    return _BERN[n]


def bern_range(p, h):
    """Enclosure of p([0,h]) by the convex hull of the Bernstein coefficients."""
    c = p.coeffs()
    if len(c) <= 2:
        return poly_range(p, h)
    n = len(c) - 1
    a = []
    hk = arb(1)
    for ck in c:
        a.append(ck*hk)
        hk *= h
    tab = _bern_table(n)
    out = None
    for j in range(n + 1):
        bj = sum((arb(tab[j][i])*a[i] for i in range(j + 1)), arb(0))
        out = bj if out is None else out.union(bj)
    return out


def horner(coeffs, x):
    acc = coeffs[-1] + 0*x
    for c in reversed(coeffs[:-1]):
        acc = acc*x + c
    return acc


def poly_horner(coeffs, Y, n=None):
    acc = arb_poly([coeffs[-1]])
    for c in reversed(coeffs[:-1]):
        acc = acc*Y
        if n is not None:
            acc = acc.truncate(n)
        acc = acc + c
    return acc


def mid_poly(p):
    return arb_poly([c.mid() for c in p.coeffs()])


def to_float(x):
    return float(x.mid())


# ---------------------------------------------------------------- potentials


class Potential:
    """V(x)=sum v_k x^k with exact rational coefficients and certified stationary points."""

    def __init__(self, coeffs, name, false_vac, barrier, true_vac=None, inflection=None):
        self.q = [Fraction(c) for c in coeffs]
        self.name = name
        self.fv_float, self.b_float, self.t_float = false_vac, barrier, true_vac
        self.infl_float = inflection
        self.prec = None
        self.at(160)

    def at(self, prec):
        """(Re)compute the certified constants at working precision prec."""
        if self.prec != prec:
            with _prec(prec):
                self.refresh()
            self.prec = prec
        return self

    def refresh(self):
        self.v = [exact(c) for c in self.q]
        self.dv = [exact(k*c) for k, c in enumerate(self.q)][1:]
        self.ddv = [exact(k*(k - 1)*c) for k, c in enumerate(self.q)][2:]
        self.dddv = [exact(k*(k - 1)*(k - 2)*c) for k, c in enumerate(self.q)][3:] or [arb(0)]
        self.f = self._root(self.dv, self.fv_float)
        self.b = self._root(self.dv, self.b_float)
        self.t = None if self.t_float is None else self._root(self.dv, self.t_float)
        self.x_infl = self._root(self.ddv, self.infl_float)
        self.Vf = self.V(self.f)

    def _root(self, cs, x0):
        """Certified enclosure of the simple root of sum cs_k x^k near x0 (Newton, then a sign change)."""
        x = arb(x0)
        for _ in range(12):
            fx = horner(cs, x)
            dfx = horner([exact(k)*c for k, c in enumerate(cs)][1:], x)
            x = (x - fx/dfx).mid()
        slope = abs(horner([exact(k)*c for k, c in enumerate(cs)][1:], x).mid())
        r = arb(2)**(-(ctx.prec - 12))*(1 + abs(x.mid()))/(slope if slope < 1 else 1)
        lo, hi = horner(cs, x - r), horner(cs, x + r)
        if not ((lo < 0 and hi > 0) or (lo > 0 and hi < 0)):
            raise ArithmeticError('root enclosure failed')
        return arb(x.mid(), r)

    def V(self, x):
        return horner(self.v, x)

    def dV(self, x):
        return horner(self.dv, x)

    def ddV(self, x):
        return horner(self.ddv, x)

    def dddV(self, x):
        return horner(self.dddv, x)


def quartic(eps):
    """(x^2-1)^2/4-eps x with eps taken exactly (a float is a dyadic rational)."""
    import numpy as np
    e = Fraction(eps)
    r = np.sort(np.roots([1., 0., -1., -float(e)]).real)
    return Potential([Fraction(1, 4) + 0, -e, Fraction(-1, 2), 0, Fraction(1, 4)], 'quartic eps=%r' % float(e),
                     r[0], r[1], r[2], -3**-.5)


def cubic():
    """Universal cubic w^2/2-w^3/3, false vacuum 0, barrier 1."""
    return Potential([0, 0, Fraction(1, 2), Fraction(-1, 3)], 'cubic', 0., 1., None, .5)


# ---------------------------------------------------------------- validated integrator


class Integrator:
    def __init__(self, pot, d, *, prec=160, order=36, tol=1e-32, hmax=64., h0=0.25, variational=False):
        if d not in (3, 4):
            raise ValueError('d=3 or 4')
        self.pot, self.d, self.prec, self.N, self.tol = pot, d, prec, order, tol
        self.hmax, self.h0, self.var = hmax, Fraction(h0), variational

    # --- vector field on polynomials (truncated to n terms if n is given)
    def F(self, Y, Rd, n=None):
        d, pot = self.d, self.pot
        tr = (lambda p: p.truncate(n)) if n is not None else (lambda p: p)
        q = Y[2]
        q2 = tr(q*q)
        qd = q2 if d == 3 else tr(q2*q)
        out = [tr(qd*Y[1]), tr(Rd*poly_horner(pot.dv, Y[0], n)), -q2]
        if self.var:
            out.append(tr(qd*Y[4]))
            out.append(tr(Rd*tr(poly_horner(pot.ddv, Y[0], n)*Y[3])))
        return out

    def jac(self, Yr, rmax_d):
        """Upper bounds of |dF_i/dy_j| on the box Yr (list of arb), r^{d-1}<=rmax_d."""
        d, pot = self.d, self.pot
        z = arb(0)
        aq = up(Yr[2])
        aqd = aq**(d - 1)
        aqd2 = (d - 1)*aq**(d - 2)
        vpp = up(pot.ddV(Yr[0]))
        rows = [[z, aqd, aqd2*up(Yr[1])],
                [rmax_d*vpp, z, z],
                [z, z, 2*aq]]
        if self.var:
            for r in rows:
                r += [z, z]
            rows.append([z, z, aqd2*up(Yr[4]), z, aqd])
            rows.append([rmax_d*up(pot.dddV(Yr[0]))*up(Yr[3]), z, z, rmax_d*vpp, z])
        return rows

    def _tube(self, res, rng, h, rmax_d):
        n = len(res)
        tiny = arb(2)**(-self.prec - 40)
        # untrusted fixed-point iteration eps <- res + h J eps (converges from below) ...
        eps = [up(r) + tiny for r in res]
        J = self.jac([rng[i] + ball0(4*eps[i]) for i in range(n)], rmax_d)
        for k in range(40):
            new = [up(res[i] + h*sum((J[i][j]*eps[j] for j in range(n)), arb(0))) + tiny for i in range(n)]
            done = all(new[i] <= eps[i]*(1 + arb(2)**-30) for i in range(n))
            eps = new
            if k % 8 == 7:
                J = self.jac([rng[i] + ball0(4*eps[i]) for i in range(n)], rmax_d)
            if done:
                break
        # ... then a rigorous check of the strict inclusion on a slightly inflated tube
        cand = [up(e*(1 + arb(2)**-12)) + tiny for e in eps]
        for _ in range(6):
            J = self.jac([rng[i] + ball0(cand[i]) for i in range(n)], rmax_d)
            lhs = [res[i] + h*sum((J[i][j]*cand[j] for j in range(n)), arb(0)) for i in range(n)]
            if all(lhs[i] < cand[i] for i in range(n)):
                return cand, J
            cand = [up(2*c) for c in cand]
        return None, None

    @staticmethod
    def _expm_bound(J, h, terms=24):
        """Entrywise upper bound of exp(hJ) for a nonnegative matrix J (series plus tail)."""
        n = len(J)
        A = [[h*J[i][j] for j in range(n)] for i in range(n)]
        nu = up(max((sum(A[i], arb(0)) for i in range(n)), key=lambda x: x.upper().mid()))
        sq = 0
        while nu.upper() > arb(2)**-3:            # scaling and squaring: exp(A)=exp(A/2^sq)^(2^sq)
            nu = nu/2
            sq += 1
        A = [[a/2**sq for a in row] for row in A]
        S = [[arb(1 if i == j else 0) for j in range(n)] for i in range(n)]
        P = [row[:] for row in S]
        for k in range(1, terms + 1):
            P = [[sum((P[i][l]*A[l][j] for l in range(n)), arb(0))/k for j in range(n)] for i in range(n)]
            S = [[S[i][j] + P[i][j] for j in range(n)] for i in range(n)]
        fact = arb(1)
        for k in range(1, terms + 2):
            fact *= k
        tail = nu**(terms + 1)/fact*nu.exp()
        S = [[up(S[i][j] + tail) for j in range(n)] for i in range(n)]
        for _ in range(sq):                         # nonnegative entries: squaring keeps upper bounds
            S = [[up(sum((S[i][l]*S[l][j] for l in range(n)), arb(0))) for j in range(n)] for i in range(n)]
        return S

    def first_step(self, phi0):
        """Taylor model on [0,h0] from the regular singular point; returns state at h0 and pieces."""
        d, pot, N = self.d, self.pot, self.N

        def K(g):
            c = g.coeffs()
            return arb_poly([0, 0] + [ck/((k + d)*(k + 2)) for k, ck in enumerate(c)])

        def Kp(g):
            c = g.coeffs()
            return arb_poly([0] + [ck/(k + d) for k, ck in enumerate(c)])
        m = phi0.mid()
        Y = arb_poly([m])
        for k in range(N//2 + 1):
            Y = m + K(poly_horner(pot.dv, Y, 2*k + 2).truncate(2*k + 2))
        Pol = mid_poly(Y.truncate(N + 1))
        cs = [abs(to_float(x)) for x in Pol.coeffs()]
        top = max(k for k in range(len(cs)) if cs[k] > 0) if any(cs[1:]) else 0
        hf = float(self.h0)
        if top > 0:
            hf = min(hf, (self.tol*max(cs[0], 1e-300)/cs[top])**(1/top))
        hq = Fraction(int(hf*2**16), 2**16) if hf >= 2**-16 else Fraction(1, 2**16)
        h = exact(hq)
        g = poly_horner(pot.dv, Pol)
        res = poly_sup(phi0 + K(g) - Pol, h)
        Psi_pol = None
        if self.var:
            Z = arb_poly([1])
            for k in range(N//2 + 1):
                Z = 1 + K((poly_horner(pot.ddv, Pol, 2*k + 2)*Z).truncate(2*k + 2))
            Psi_pol = mid_poly(Z.truncate(N + 1))
            gz = poly_horner(pot.ddv, Pol)*Psi_pol
            resz = poly_sup(1 + K(gz) - Psi_pol, h)
        c = h*h/(2*d)
        rng = bern_range(Pol, h)
        tiny = arb(2)**(-self.prec - 40)
        e = up(2*res) + tiny
        ez = arb(0)
        ok = False
        for _ in range(30):
            R = rng + ball0(e)
            L = up(pot.ddV(R))
            if not (c*L < 1):
                break
            e_new = up(res/(1 - c*L)*(1 + arb(2)**-8)) + tiny
            if e_new <= e and res + c*L*e_new < e_new:
                e = e_new
                ok = True
                break
            e = up(e_new*2)
        if not ok:
            return None
        R = rng + ball0(e)
        L = up(pot.ddV(R))
        out = {'h': h, 'h_frac': hq, 'phi_range': R, 'dV_range': pot.dV(R)}
        pp = Kp(g)
        ep = L*e*h/d
        hd1 = h**(d - 1)
        phi_end = Pol(h) + ball0(e)
        P_end = hd1*(pp(h) + ball0(ep))
        state = [phi_end, P_end, 1/h]
        # integrals int_0^h r^{d-1} p^2 and r^{d-1}(V-Vf)
        sh = arb_poly([0]*(d - 1) + [1])
        kin = (sh*pp*pp).integral()(h) + ball0(h**d/d*(2*poly_sup(pp, h) + ep)*ep)
        pot_int = (sh*(poly_horner(pot.v, Pol) - pot.Vf)).integral()(h) + ball0(h**d/d*up(pot.dV(R))*e)
        if self.var:
            ez = up(2*resz) + tiny
            rz = bern_range(Psi_pol, h)
            L3 = up(pot.dddV(R))
            ok = False
            for _ in range(30):
                Zr = rz + ball0(ez)
                rhs = resz + c*(L*ez + L3*up(Zr)*e)
                if rhs < ez:
                    ok = True
                    break
                ez = up(rhs*2)
            if not ok:
                return None
            Zr = rz + ball0(ez)
            pz = Kp(gz)
            epz = (L*ez + L3*up(Zr)*e)*h/d
            state += [Psi_pol(h) + ball0(ez), hd1*(pz(h) + ball0(epz))]
        out.update(state=state, kin=kin, pot=pot_int)
        return out

    def step(self, y0, r0, h_force=None):
        """One Taylor-model step from exact r0>0; returns dict or None."""
        d, N = self.d, self.N
        y0 = list(y0)
        y0[2] = 1/r0                     # q is known exactly: no accumulated error in 1/r
        mids = [y.mid() for y in y0]
        n = len(y0)
        Rpoly = arb_poly([r0, 1])
        Rd = Rpoly**(d - 1)
        Y = [arb_poly([m]) for m in mids]
        for k in range(N):
            Fk = self.F(Y, Rd, k + 1)
            Y = [mids[i] + Fk[i].integral() for i in range(n)]
        Pol = [mid_poly(p) for p in Y]
        # step size from the size of the last coefficients
        hf = self.hmax
        for p in Pol:
            c = p.coeffs()
            if len(c) <= N:
                continue
            cN, c0 = abs(to_float(c[N])), abs(to_float(c[0]))
            scale = max(c0, max(abs(to_float(x)) for x in c[1:4])*1e-3, 1e-300)
            if cN > 0:
                hf = min(hf, (self.tol*scale/cN)**(1/N))
        hf = min(hf, 0.45*to_float(r0))
        hq = Fraction(int(hf*2**12), 2**12) if hf >= 2**-12 else Fraction(1, 2**12)
        if h_force is not None:
            hq = min(hq, h_force)
        for attempt in range(6):
            h = exact(hq)
            Fp = self.F(Pol, Rd)
            res = [poly_sup(y0[i] + Fp[i].integral() - Pol[i], h) for i in range(n)]
            rng = [poly_range(p, h) if i == 2 else bern_range(p, h) for i, p in enumerate(Pol)]
            rmax_d = (r0 + h)**(d - 1)
            eps, J = self._tube(res, rng, h, rmax_d)
            if eps is not None:
                break
            hq /= 2
        else:
            return None
        tube = [rng[i] + ball0(eps[i]) for i in range(n)]
        # endpoint: |y-Pol|(s) <= res + int_0^s J|y-Pol|  =>  |y-Pol|(h) <= exp(hJ) res (vector Gronwall)
        E = self._expm_bound(J, h)
        dev = [up(sum((E[i][j]*res[j] for j in range(n)), arb(0))) for i in range(n)]
        dev = [dev[i] if dev[i] < eps[i] else eps[i] for i in range(n)]
        end = [Pol[i](h) + ball0(dev[i]) for i in range(n)]
        # kinetic int q^{d-1} P^2 ds and potential int R^{d-1}(V-Vf) ds over the step
        Cq, B, A = Pol[2], Pol[1], Pol[0]
        Cqd = Cq**(d - 1)
        kin = (Cqd*B*B).integral()(h)
        aC = up(tube[2]) + 0
        aB = up(rng[1])
        kin += ball0(h*(aC**(d - 1)*eps[1]*(2*aB + eps[1]) + (d - 1)*aC**(d - 2)*eps[2]*aB*aB))
        potint = (Rd*(poly_horner(self.pot.v, A) - self.pot.Vf)).integral()(h)
        potint += ball0(h*rmax_d*up(self.pot.dV(tube[0]))*eps[0])
        return {'h': hq, 'end': end, 'tube': tube, 'eps': eps, 'kin': kin, 'pot': potint, 'Pol': Pol,
                'r0': r0, 'Rd': Rd}

    def var_step(self, v0, cs, w):
        """Variational pair (psi, Psi) over the whole family phi0 in [c-w, c+w] on the step of the
        centre trajectory cs. The coefficient V''(phi) is evaluated on the mean-value enclosure
        phi in phi_c + [-w,w] sup|psi| (phi-phi_c = int_c^phi0 psi), so the family is never boxed.
        Bootstrap: |psi-Pol|(s) <= res + h D + int J|psi-Pol| with strict inequality on the tube."""
        d, N, pot = self.d, self.N, self.pot
        h, r0, Rd = exact(cs['h']), cs['r0'], cs['Rd']
        A, B, Cq = cs['Pol']
        ec, tc = cs['eps'], cs['tube']
        Cqd = Cq**(d - 1)
        W2 = Rd*poly_horner(pot.ddv, A)
        mids = [y.mid() for y in v0]
        Y = [arb_poly([m]) for m in mids]
        for k in range(N):
            Y = [mids[0] + (Cqd*Y[1]).truncate(k + 1).integral(), mids[1] + (W2*Y[0]).truncate(k + 1).integral()]
        Pv = [mid_poly(p) for p in Y]
        res = [poly_sup(v0[0] + (Cqd*Pv[1]).integral() - Pv[0], h),
               poly_sup(v0[1] + (W2*Pv[0]).integral() - Pv[1], h)]
        rng = [bern_range(p, h) for p in Pv]
        rmax_d = (r0 + h)**(d - 1)
        Qm = up(tc[2])
        D0 = (d - 1)*Qm**(d - 2)*ec[2]*up(rng[1])
        tiny = arb(2)**(-self.prec - 40)

        def bounds(ev):
            psit = up(rng[0]) + ev[0]
            phiR = tc[0] + ball0(w*psit)
            L2, L3 = up(pot.ddV(phiR)), up(pot.dddV(phiR))
            D1 = rmax_d*L3*(ec[0] + w*psit)*up(rng[0])
            a = [res[0] + h*D0, res[1] + h*D1]
            J = [[arb(0), Qm**(d - 1)], [rmax_d*L2, arb(0)]]
            return a, J

        ev = [up(r) + tiny for r in res]
        for _ in range(40):
            a, J = bounds([4*e for e in ev])
            new = [up(a[i] + h*(J[i][0]*ev[0] + J[i][1]*ev[1])) + tiny for i in range(2)]
            done = all(new[i] <= ev[i]*(1 + arb(2)**-30) for i in range(2))
            ev = new
            if done:
                break
        cand = [up(e*(1 + arb(2)**-12)) + tiny for e in ev]
        ok = False
        for _ in range(6):
            a, J = bounds(cand)
            lhs = [a[i] + h*(J[i][0]*cand[0] + J[i][1]*cand[1]) for i in range(2)]
            if all(lhs[i] < cand[i] for i in range(2)):
                ok = True
                break
            cand = [up(2*c) for c in cand]
        if not ok:
            return None
        E = self._expm_bound(J, h)
        dev = [up(E[i][0]*a[0] + E[i][1]*a[1]) for i in range(2)]
        dev = [dev[i] if dev[i] < cand[i] else cand[i] for i in range(2)]
        return {'end': [Pv[i](h) + ball0(dev[i]) for i in range(2)],
                'tube': [rng[i] + ball0(cand[i]) for i in range(2)]}

    def run_family(self, c, w, mode, *, rmax=400., width_max=None):
        """Mean-value (first-order Taylor model in phi0) classification of all phi0 in [c-w, c+w].

        Centre trajectory from the point c; family enclosures phi in phi_c + [-w,w]|psi|,
        P in P_c + [-w,w]|Psi|. Modes 'classify' and 'unique' as in run()."""
        pot, d = self.pot, self.d
        pot.at(self.prec)
        if self.var:
            raise ValueError('run_family uses its own variational pair')
        with _prec(self.prec):
            c = c.mid() if isinstance(c, arb) else exact(c)
            w = w if isinstance(w, arb) else exact(w)
            first_c = self.first_step(c)
            self.var = True
            try:
                first_b = self.first_step(arb(c, w))
            finally:
                self.var = False
            if first_c is None or first_b is None or first_c['h_frac'] != first_b['h_frac']:
                return {'status': 'inconclusive', 'why': 'first step', 'r': 0.}
            f = pot.f
            p_neg = bool(first_b['dV_range'] < 0)
            above = bool(first_b['phi_range'] > f)
            state = first_c['state']
            v = first_b['state'][3:5]
            r0 = first_c['h_frac']
            steps = 1
            if width_max is None:
                width_max = 0.2*abs(to_float(pot.b) - to_float(f)) if pot.t is None else 0.2*abs(to_float(pot.t) - to_float(f))
            while True:
                hf = None
                for _ in range(8):
                    cs = self.step(state, exact(r0), h_force=hf)
                    if cs is None:
                        return {'status': 'inconclusive', 'why': 'step failed', 'r': float(r0), 'steps': steps}
                    vs = self.var_step(v, cs, w)
                    if vs is not None:
                        break
                    hf = cs['h']/2
                else:
                    return {'status': 'inconclusive', 'why': 'variational step failed', 'r': float(r0), 'steps': steps}
                steps += 1
                r0 = r0 + cs['h']
                state, v = cs['end'], vs['end']
                tube = [cs['tube'][0] + ball0(w*up(vs['tube'][0])), cs['tube'][1] + ball0(w*up(vs['tube'][1]))]
                end = [state[0] + ball0(w*up(v[0])), state[1] + ball0(w*up(v[1]))]
                p_neg = p_neg and bool(tube[1] < 0)
                above = above and bool(tube[0] > f)
                if mode == 'classify':
                    if p_neg and end[0] < f:
                        return {'status': 'over', 'r': float(r0), 'steps': steps}
                    if above and end[1] > 0:
                        return {'status': 'under', 'r': float(r0), 'steps': steps}
                if mode == 'unique' and above and end[0] < pot.x_infl:
                    s1, s2 = v
                    if (s1 < 0 and s2 < 0) or (s1 > 0 and s2 > 0):
                        return {'status': 'unique', 'r': float(r0), 'steps': steps, 'psi': s1, 'Psi': s2,
                                'phi_R': end[0]}
                if end[0].rad() > width_max or float(r0) > rmax:
                    return {'status': 'inconclusive', 'why': 'width' if end[0].rad() > width_max else 'rmax',
                            'r': float(r0), 'steps': steps, 'rad': float(end[0].rad())}

    def run(self, phi0, mode, *, u_stop=None, rmax=400., width_max=None):
        """Integrate from phi0 (an arb box).

        mode 'classify': stop at a certified overshoot ('over') or undershoot ('under').
        mode 'tail': stop at the first step end with phi-f < u_stop (upper bound).
        mode 'unique': stop when phi<x_infl and psi, Psi have one strict sign.
        """
        pot, d = self.pot, self.d
        pot.at(self.prec)
        with _prec(self.prec):
            first = self.first_step(phi0)
            if first is None:
                return {'status': 'inconclusive', 'why': 'first step', 'r': 0.}
            f = pot.f
            p_neg = bool(first['dV_range'] < 0)
            above = bool(first['phi_range'] > f)
            state = first['state']
            kin, potint = first['kin'], first['pot']
            r0 = first['h_frac']
            steps = 1
            if width_max is None:
                width_max = 0.2*abs(to_float(pot.b) - to_float(f)) if pot.t is None else 0.2*abs(to_float(pot.t) - to_float(f))
            while True:
                st = self.step(state, exact(r0))
                if st is None:
                    return {'status': 'inconclusive', 'why': 'step failed', 'r': float(r0), 'steps': steps}
                steps += 1
                tube, end = st['tube'], st['end']
                r0 = r0 + st['h']
                state = end
                kin += st['kin']
                potint += st['pot']
                p_neg = p_neg and bool(tube[1] < 0)
                above = above and bool(tube[0] > f)
                if mode == 'classify':
                    if p_neg and end[0] < f:
                        return {'status': 'over', 'r': float(r0), 'steps': steps}
                    if above and end[1] > 0:
                        return {'status': 'under', 'r': float(r0), 'steps': steps}
                if mode == 'tail' and p_neg and above and (end[0] - f).upper() < u_stop:
                    return self._tail(end, r0, kin, potint, steps)
                if mode == 'unique' and above and end[0] < pot.x_infl:
                    s1, s2 = end[3], end[4]
                    if (s1 < 0 and s2 < 0) or (s1 > 0 and s2 > 0):
                        return {'status': 'unique', 'r': float(r0), 'steps': steps, 'psi': s1, 'Psi': s2,
                                'phi_R': end[0]}
                if end[0].rad() > width_max or float(r0) > rmax:
                    return {'status': 'inconclusive', 'why': 'width' if end[0].rad() > width_max else 'rmax',
                            'r': float(r0), 'steps': steps, 'rad': float(end[0].rad())}

    def _tail(self, end, R, kin, potint, steps):
        pot, d = self.pot, self.d
        u = end[0] - pot.f
        if not (end[0] < pot.x_infl):
            return {'status': 'inconclusive', 'why': 'tail outside convex region', 'r': float(R)}
        tb = up(u)*up(end[1])
        K = kin + arb(tb/2, tb/2)
        Utot = potint + arb(tb/2, tb/2)
        omega = 4*arb.pi() if d == 3 else 2*arb.pi()**2
        s = omega/d*K
        s_direct = omega*(K/2 + Utot)
        return {'status': 'tail', 'R': float(R), 'steps': steps, 'kinetic_int': K, 'tail_bound': tb,
                's': s, 's_direct': s_direct, 'u_R': u, 'P_R': end[1]}


# ---------------------------------------------------------------- seeds (untrusted)


def seed_phi0(pot, d, *, prec=160, order=36, tol=1e-32, targets=(1e-5, 1e-9, 1e-13, 1e-17)):
    """Untrusted high-precision shooting parameter: float shooting refined by Newton steps
    on the linear stable-manifold condition P+R^{d-1} lam(R) u=0 at radii where u reaches each target."""
    from scipy.special import kve
    import numpy as np
    if pot.t is None:
        from . import wall_nucleation as wn
        phi0 = arb(wn.cubic_bounce(d)['w0'])
    else:
        phi0 = arb(_float_phi0(pot, d))
    m = float(pot.ddV(pot.f).mid())**.5
    nu = (d - 2)/2
    integ = Integrator(pot, d, prec=prec, order=order, tol=tol, variational=True)
    hist = []
    for tgt in targets:
        for _ in range(4):
            with _prec(prec):
                out = _newton_run(integ, phi0, tgt)
            if out is None:
                break
            (R, u, P, psi, Psi) = out
            lam = m*kve(nu + 1, m*R)/kve(nu, m*R) + 0*R
            with _prec(prec):
                Rd = exact(Fraction(R))**(d - 1)
                Fv = P + Rd*arb(lam)*u
                dF = Psi + Rd*arb(lam)*psi
                step = Fv/dF
                phi0 = (phi0 - step).mid()
            hist.append((tgt, R, float(step.mid())))
            if abs(float(step.mid())) < 1e-3*tgt**2*1e-6:
                break
    return phi0, hist


def _newton_run(integ, phi0, tgt):
    pot = integ.pot
    first = integ.first_step(arb(phi0.mid()))
    state = first['state']
    r0 = first['h_frac']
    for _ in range(4000):
        st = integ.step(state, exact(r0))
        if st is None:
            return None
        r0 += st['h']
        state = st['end']
        u = state[0] - pot.f
        if u.mid() < tgt or state[1].mid() > 0 or u.mid() < 0:
            return float(r0), u, state[1], state[3], state[4]
    return None


def _float_phi0(pot, d):
    from . import wall_nucleation as wn
    eps = -float(pot.q[1])
    b = wn.bounce(eps, d)
    return _phi_at_zero(eps, d, b)


def _phi_at_zero(eps, d, b):
    # wall_nucleation starts at a small r0 on the linearised solution; extrapolate to r=0
    import numpy as np
    from . import wall_nucleation as wn
    f, bb, t = wn.reduced_vacua(eps)
    r = np.array(b['profile_r'][:3])
    ph = np.array(b['profile_phi'][:3])
    if r[0] < 1e-3:
        return float(ph[0])
    kap = (3*t*t - 1)**.5
    from scipy.special import iv
    g = (lambda z: np.sinh(z)/z) if d == 3 else (lambda z: 2*iv(1, z)/z)
    delta = (t - ph[0])/g(kap*r[0])
    return float(t - delta)


# ---------------------------------------------------------------- certificates


def certify_bounce(pot, d, *, delta=Fraction(1, 10**20), prec=160, order=36, tol=1e-32, u_stop=1e-9,
                   seed=None, rmax=None):
    """Existence certificate and action enclosure for the bounce near the seed."""
    if rmax is None:
        rmax = default_rmax(pot)
    if seed is None:
        seed, hist = seed_phi0(pot, d, prec=prec, order=order, tol=tol)
    else:
        hist = []
    with _prec(prec):
        dl = exact(delta)
        lo, hi = seed - dl, seed + dl
    integ = Integrator(pot, d, prec=prec, order=order, tol=tol)
    c_lo = integ.run(lo, 'classify', rmax=rmax)
    c_hi = integ.run(hi, 'classify', rmax=rmax)
    exists = {c_lo['status'], c_hi['status']} == {'over', 'under'}
    with _prec(prec):
        fam = integ.run(arb(seed, dl), 'tail', u_stop=u_stop, rmax=rmax)
    return {'potential': pot.name, 'd': d, 'phi0_seed': seed, 'delta': delta, 'seed_history': hist,
            'lo': c_lo, 'hi': c_hi, 'exists': exists, 'family': fam,
            's': fam.get('s'), 'certified': exists and fam['status'] == 'tail'
            and bool(fam['s'].overlaps(fam['s_direct']))}


def default_rmax(pot):
    with _prec(64):
        m = to_float(pot.ddV(pot.f))**.5
    return 100. + 80./m


def certify_unique_box(pot, d, seed, Delta, *, prec=128, order=30, tol=1e-24, rmax=None):
    """At most one bounce with phi0 in [seed-Delta, seed+Delta] (variational sign argument)."""
    if rmax is None:
        rmax = default_rmax(pot)
    integ = Integrator(pot, d, prec=prec, order=order, tol=tol)
    return integ.run_family(seed, Delta, 'unique', rmax=rmax,
                            width_max=0.2*abs(to_float(pot.x_infl) - to_float(pot.f)))


def exit_point_lower(pot):
    """A point e_lo in (b, e] with V(e_lo)>=V(f): phi0<=e_lo cannot give a bounce (E(0)<0)."""
    import numpy as np
    from scipy.optimize import brentq
    Vf = to_float(pot.Vf)
    g = lambda x: float(pot.V(arb(x)).mid()) - Vf
    e = brentq(g, to_float(pot.b), to_float(pot.t), xtol=1e-15)
    e_lo = Fraction(e - 1e-9)
    if not (pot.V(exact(e_lo)) > pot.Vf and exact(e_lo) > pot.b):
        raise ArithmeticError('exit point bracket')
    return e_lo, e


def near_true_vacuum_eta(pot, d, *, eta2=Fraction(1, 20), pieces=400):
    """eta such that every phi0 in [t-eta, t) overshoots (energy argument); returns (eta, data)."""
    f, t = pot.f, pot.t
    e2 = exact(eta2)
    if not (pot.ddV(t - e2) > 0 and t - e2 > 0):      # V''' = 6x > 0: V'' increases on [t-eta2, t]
        raise ArithmeticError('V\'\' not positive near t')
    D1 = (pot.V(t - e2) - pot.V(t)).abs_upper()
    E0 = pot.Vf - pot.V(t - e2)                         # E(0) >= V(f)-V(t-eta2)
    # A >= int_f^t sqrt(2(2V(f)-V(t)-V(phi))) dphi, rigorous Riemann upper sum
    a, b = f.lower(), t.upper()
    w = (b - a)/pieces
    A = arb(0)
    top = 2*pot.Vf - pot.V(t)
    for i in range(pieces):
        xs = arb(a + w*(i + 0.5), w/2) + ball0(w*arb(2)**-40)
        val = 2*(top - pot.V(xs))
        vu = val.upper()
        A += w*(vu.sqrt() if vu > 0 else arb(0))
    A = up(A)
    margin = E0 - D1
    if not (margin > 0):
        raise ArithmeticError('eta2 too large')
    r1 = up((d - 1)*A/margin*(1 + arb(2)**-10))
    kmax = pot.ddV(t).upper().sqrt()
    z = up(kmax*r1)
    g = z.sinh()/z if d == 3 else 2*z.bessel_i(1)/z
    eta = (e2/g).lower()
    return eta, {'eta2': float(eta2), 'r1_required': float(r1.mid()), 'A_upper': float(A.mid()),
                 'E0_lower': float(E0.lower().mid()), 'D1_upper': float(D1.mid()), 'kappa_max': float(kmax.mid()),
                 'eta': float(eta.mid())}


def cover_interval(pot, d, a, b, expect, *, prec=96, order=24, tol=1e-18, rmax=None, max_runs=40000,
                   pivot=None, pivot_hi=None, verbose=False):
    """Adaptive interval classification of every phi0 in [a,b] (Fractions); expect 'over'/'under'.

    Pieces are bisected in z=log(phi-pivot)-log(pivot_hi-phi) (or log|phi-pivot|), i.e.
    geometrically about the bounce seed and about the true vacuum, where the classification
    radius grows logarithmically.
    Returns (ok, runs, leaves)."""
    if rmax is None:
        rmax = default_rmax(pot)
    integ = Integrator(pot, d, prec=prec, order=order, tol=tol)
    stack = [(Fraction(a), Fraction(b))]
    runs, leaves, worst = 0, 0, 0.
    while stack:
        x, y = stack.pop()
        out = integ.run_family((x + y)/2, (y - x)/2, 'classify', rmax=rmax)
        runs += 1
        if verbose:
            pv = pivot if pivot is not None else 0
            print('cover', '%.4g %.4g' % (float(x - pv), float(y - pv)), out['status'], '%.3g' % out['r'],
                  out.get('why', ''), flush=True)
        if out['status'] == expect:
            leaves += 1
            worst = max(worst, out['r'])
            continue
        if out['status'] in ('over', 'under'):
            return False, runs, leaves, 'wrong class %s on [%r,%r]' % (out['status'], float(x), float(y))
        if runs > max_runs or y - x < Fraction(1, 10**30):
            return False, runs, leaves, 'unresolved [%r,%r]' % (float(x), float(y))
        m = _log_split(x, y, pivot, pivot_hi)
        stack.append((x, m))
        stack.append((m, y))
    return True, runs, leaves, 'max classification radius %.3g' % worst


def _log_split(x, y, lo_p, hi_p):
    """Split point of [x,y]: midpoint of z=log(phi-lo_p)-log(hi_p-phi) (terms omitted when None)."""
    from math import log, exp
    if lo_p is not None and hi_p is None and y <= lo_p:     # pivot on the right: mirror
        a, b = float(lo_p - y), float(lo_p - x)
        m = lo_p - Fraction(exp((log(a) + log(b))/2))
    elif lo_p is None and hi_p is None:
        m = (x + y)/2
    else:
        L = float(hi_p - lo_p) if (lo_p is not None and hi_p is not None) else None
        def z(ph):
            out = 0.
            if lo_p is not None:
                out += log(float(ph - lo_p))
            if hi_p is not None:
                out -= log(float(hi_p - ph))
            return out
        zm = (z(x) + z(y))/2
        if lo_p is not None and hi_p is not None:
            if zm > 0:
                m = hi_p - Fraction(L/(1 + exp(zm)))
            else:
                m = lo_p + Fraction(L/(1 + exp(-zm)))
        elif lo_p is not None:
            m = lo_p + Fraction(exp(zm))
        else:
            m = hi_p - Fraction(exp(-zm))
    if not x < m < y:
        m = (x + y)/2
    return m


def spinodal_constants(s_cubic):
    """C_d=(2*3^{1/4})^{(6-d)/2} s_cubic(d)/3 from certified cubic actions (dict d->arb)."""
    out = {}
    for d, s in s_cubic.items():
        out[d] = (2*arb(3).root(4))**(arb(6 - d)/2)*s/3
    return out


def certify_least_action(pot, d, seed, *, Delta0=Fraction(1, 10**8), eta2=Fraction(1, 20), cover_kw=None):
    """Every phi0 in [e,t) other than those in the existence bracket is excluded (quartic only)."""
    out = {}
    Delta = Delta0
    while True:
        ub = certify_unique_box(pot, d, seed, Delta)
        if ub['status'] == 'unique' or Delta < Fraction(1, 10**18):
            break
        Delta /= 100
    out['box'] = {'Delta': Delta, 'status': ub['status'], 'R': ub.get('r'),
                  'psi_R': ub.get('psi'), 'Psi_R': ub.get('Psi')}
    with _prec(160):
        pot.at(160)
        eta, ed = near_true_vacuum_eta(pot, d, eta2=eta2)
        e_lo, e_float = exit_point_lower(pot)
        tu = pot.t.upper()
        c = tu - eta
        c_up = c.upper()
    c_frac = _arb_to_fraction_up(c_up)
    t_frac = _arb_to_fraction_up(tu)
    out['near_true_vacuum'] = ed
    out['exit_point'] = {'e_float': e_float, 'e_lo': float(e_lo)}
    kw = cover_kw or {}
    seedf = _arb_to_fraction_up(seed)
    ok1 = cover_interval(pot, d, e_lo, seedf - Delta, 'under', pivot=seedf, **kw)
    ok2 = cover_interval(pot, d, seedf + Delta, c_frac, 'over', pivot=seedf, pivot_hi=t_frac, **kw)
    out['cover_under'] = {'interval': [float(e_lo), float(seedf - Delta)], 'ok': ok1[0], 'runs': ok1[1],
                          'leaves': ok1[2], 'note': ok1[3]}
    out['cover_over'] = {'interval': [float(seedf + Delta), float(c_frac)], 'ok': ok2[0], 'runs': ok2[1],
                         'leaves': ok2[2], 'note': ok2[3]}
    out['least_action'] = bool(ub['status'] == 'unique' and ok1[0] and ok2[0])
    return out


def _arb_to_fraction_up(x):
    """Exact Fraction of the midpoint of an (exact) arb."""
    m = x.mid()
    mant, expo = m.man_exp()
    return Fraction(int(mant))*Fraction(2)**int(expo)
