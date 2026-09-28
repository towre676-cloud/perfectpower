"""Second-order heat asymptotics for Pell-type hit sets (research notes, Theorem T2).

For a Pell-type quadratic P(n) = A n^2 + B n + C (A > 0 nonsquare, Delta != 0), the hits
n >= 1 with P(n) a square split, apart from finitely many, into subsequences
    n_j = alpha E^j + beta + O(E^-j),   j >= 0,   E = eps^pi,   beta = -B/(2A),
one for each positive Pell orbit O and each good residue class r (mod pi) of the orbit index.
Mellin inversion of sum_j exp(-lam E^j), i.e. of Gamma(s) / (1 - E^-s), gives

    sum_{j>=0} exp(-lam E^j) = (log(1/lam) - gamma)/log E + 1/2 + Phi_E(log lam) + O(lam),
    Phi_E(u) = (2/log E) Re sum_{m>=1} Gamma(2 pi i m / log E) exp(-2 pi i m u / log E),

where Phi_E is continuous and log E-periodic; its Fourier coefficients come from the imaginary
poles s = 2 pi i m / log E of the Dirichlet-type transform.  Summing over classes,

    K(tau) = e^{-tau beta} sum_classes [ (log(1/(tau alpha)) - gamma)/log E + 1/2 + Phi_E(log(tau alpha)) ]
             + (integer boundary correction) + O(tau)

with kappa = sum_classes 1/log E (the Lemma Q constant).  Expanding e^{-tau beta} = 1 - tau beta + ...
gives the two-term form kappa log(1/tau) + C0 + sum Phi_E + O(tau log(1/tau)); the shift term
-beta kappa tau log(1/tau) is the leading correction when B != 0 (the O(tau) remainder of the
unshifted form is false for B != 0).
"""
from __future__ import annotations

import cmath
import math

from .atlas import quadratic_square_data
from .arith import pell_fundamental

EULER_GAMMA = 0.5772156649015329


def lgamma_complex(z: complex) -> complex:
    shift = 0
    while z.real < 20:
        shift += cmath.log(z)
        z += 1
    lg = ((z - 0.5) * cmath.log(z) - z + 0.5 * math.log(2 * math.pi)
          + 1 / (12 * z) - 1 / (360 * z ** 3) + 1 / (1260 * z ** 5))
    return lg - shift


def phi(u: float, logE: float, terms: int | None = None) -> float:
    """Phi_E(u) = (2/log E) Re sum_{m>=1} Gamma(2 pi i m/log E) e^{-2 pi i m u / log E}.

    |Gamma(iy)| ~ sqrt(2 pi / y) e^{-pi y / 2}, so terms with 2 pi m / log E > 25 are < 1e-16."""
    if terms is None:
        terms = int(25 * logE / (2 * math.pi)) + 3
    tot = 0.0
    for m in range(1, terms + 1):
        w = 2j * math.pi * m / logE
        tot += (cmath.exp(lgamma_complex(w) - w * u)).real
    return 2 * tot / logE


def pell_heat_model(A: int, B: int, C: int, match: int = 10 ** 12):
    """Classes (alpha, log E) and the integer boundary correction for the Pell family A n^2+Bn+C."""
    qd = quadratic_square_data(A, B, C)
    if qd.get('case') != 'pell':
        raise ValueError('not an infinite Pell family')
    Dp = 4 * A
    x1, y1 = pell_fundamental(Dp)
    eps = x1 + y1 * math.sqrt(Dp)
    classes, model_small, model_sum = [], 0, 0
    for X0, Y0 in qd['orbits']:
        # period of (X, Y) mod 2A along the orbit
        M = 2 * A
        st0, st, period = (X0 % M, Y0 % M), None, 0
        X, Y = X0, Y0
        states = []
        while True:
            states.append((X, Y))
            period += 1
            X, Y = X * x1 + Dp * Y * y1, X * y1 + Y * x1
            if (X % M, Y % M) == st0:
                break
        logE = period * math.log(eps)
        for r, (Xr, Yr) in enumerate(states):
            if (Xr - B) % M:
                continue
            eta_r = Xr + Yr * math.sqrt(Dp)            # orbit element at index r
            alpha = eta_r / (4 * A)                    # n_j ~ alpha E^j
            # n_j = alpha E^j + beta + delta_j exactly, with delta_j = (Delta / eta_r) E^-j / (4A):
            # the conjugate of eta_r eps^k is (Delta / eta_r) eps^-k
            delta0 = (B * B - 4 * A * C) / eta_r / (4 * A)
            classes.append({'alpha': alpha, 'logE': logE, 'orbit': (X0, Y0), 'r': r, 'delta0': delta0})
            # count exact model terms n_j <= match (each tends to 1 in the Mellin formula)
            X, Y = Xr, Yr
            while True:
                n = (X - B) // M
                if n > match:
                    break
                model_small += 1
                model_sum += n
                for _ in range(period):
                    X, Y = X * x1 + Dp * Y * y1, X * y1 + Y * x1
    return classes, model_small, model_sum


def pell_heat_prediction_first_order(A: int, B: int, tau: float, hits_small: int, hits_sum: int,
                                     classes, model_small: int, model_sum: int):
    """Prediction including every O(tau) term; the remainder is O(tau^2).

    Per class: exp(-tau beta) [ (log(1/lam) - gamma)/log E + 1/2 + Phi_E(log lam) + lam/(E - 1) ]
    - tau * sum_j delta_j, where lam/(E - 1) is the residue of Gamma(s) lam^-s / (1 - E^-s) at
    s = -1 and sum_j delta_j = delta0 E / (E - 1); plus the boundary correction
    (hits_small - model_small) - tau (hits_sum - model_sum)."""
    total = 0.0
    f = math.exp(tau * B / (2 * A))
    for cl in classes:
        E = math.exp(cl['logE'])
        lam = tau * cl['alpha']
        total += f * ((math.log(1 / lam) - EULER_GAMMA) / cl['logE'] + 0.5 + phi(math.log(lam), cl['logE'])
                      + lam / (E - 1))
        total -= tau * cl['delta0'] * E / (E - 1)
    return total + (hits_small - model_small) - tau * (hits_sum - model_sum)


def pell_heat_prediction(A: int, B: int, C: int, tau: float, hits_small: int, classes, model_small,
                         shift: bool = True):
    """Prediction of K(tau) = sum_{hits n} e^{-tau n}.

    hits_small is the number of actual hits n <= match (same match as the model).  With shift=True
    the class sums carry the factor e^{-tau beta}, beta = -B/(2A) (remainder O(tau)); with
    shift=False this is the unshifted two-term form (remainder O(tau log(1/tau)) when B != 0).
    Returns (full prediction, prediction without the periodic term).
    """
    main = 0.0
    periodic = 0.0
    for cl in classes:
        lam = tau * cl['alpha']
        main += (math.log(1 / lam) - EULER_GAMMA) / cl['logE'] + 0.5
        periodic += phi(math.log(lam), cl['logE'])
    f = math.exp(tau * B / (2 * A)) if shift else 1.0
    corr = hits_small - model_small
    return f * (main + periodic) + corr, f * main + corr


def pell_kappa_canonical(A: int, B: int, C: int, u: int, v: int):
    """kappa exactly as in the Lean theorem `PellExact.pell_exact_count`.

    Roots are the solutions of X^2 - 4A Y^2 = Delta with X > 0, Y >= 0 whose inverse-unit
    predecessor leaves that quadrant (they lie in the box 4A Y^2 <= |Delta| u^2); P is the period
    of X mod 2A along the orbit, g the number of good residues (X_r = B mod 2A).  Returns
    (kappa, [(root, P, g)])."""
    from math import isqrt
    D, Delta = 4 * A, B * B - 4 * A * C
    ymax = isqrt(abs(Delta) * u * u // D) + 1
    roots = []
    for Y in range(0, ymax + 1):
        if D * Y * Y > abs(Delta) * u * u:
            break
        X2 = Delta + D * Y * Y
        if X2 <= 0:
            continue
        X = isqrt(X2)
        if X * X != X2:
            continue
        Xp, Yp = X * u - D * Y * v, u * Y - v * X          # predecessor
        if not (Xp > 0 and Yp >= 0):
            roots.append((X, Y))
    data, total = [], 0.0
    for X0, Y0 in roots:
        M = 2 * A
        X, Y, P, good = X0, Y0, 0, 0
        while True:
            if (X - B) % M == 0:
                good += 1
            P += 1
            X, Y = X * u + D * Y * v, X * v + Y * u
            if (X % M, Y % M) == (X0 % M, Y0 % M):
                break
        data.append(((X0, Y0), P, good))
        total += good / P
    return total / math.log(u + v * math.sqrt(D)), data
