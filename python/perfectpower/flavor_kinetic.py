"""CP-even polynomial kinetic covariants and exact fixed-spectrum matching.

The nine-generator spanning proof is algebraic. Multiprecision here evaluates
its constructive metric at a reference vacuum, including hierarchical spectra.
All reference constants are real and stay fixed when the fields change.
"""
from itertools import combinations
import mpmath as mp
import numpy as np


def matrix(a):
    a = np.asarray(a, complex)
    return mp.matrix([[mp.mpc(str(z.real), str(z.imag)) for z in row] for row in a])


def array(M):
    return np.array([[complex(M[i, j]) for j in range(M.cols)] for i in range(M.rows)])


def inner(A, B):
    return mp.re(sum((A*B)[i, i] for i in range(A.rows)))


def hermitian_function(A, function):
    values, U = mp.eighe((A+A.H)/2)
    return U*mp.diag([function(v) for v in values])*U.H


def hermitian_coordinates(A):
    return mp.matrix([mp.re(A[i, i]) for i in range(3)]+[x for i, j in combinations(range(3), 2)
                     for x in [mp.sqrt(2)*mp.re(A[i, j]), mp.sqrt(2)*mp.im(A[i, j])]])


class KineticCovariants:
    """Nine CP-compatible covariants on a right-handed flavor space.

    R=X†X, S=X†ZZ†X, with two left-flavor covariants X,Z. The spectral
    constants in P_i(R) refer to the initial vacuum, not a moving diagonalizer.
    """
    def __init__(self, X, Z, digits=90):
        self.digits = digits
        with mp.workdps(digits):
            X, Z = matrix(X), matrix(Z)
            self.reference_R = X.H*X
            self.reference_S = X.H*(Z*Z.H)*X
            values, U = mp.eighe(self.reference_R)
            self.values = list(values)
            if min(values) <= 0 or min(values[i+1]-values[i] for i in range(2)) <= 0:
                raise ValueError('Full rank and distinct reference singular values required')
            S = U.H*self.reference_S*U
            self.triangle_imaginary = mp.im(S[0, 1]*S[1, 2]*S[2, 0])
            if not self.triangle_imaginary:
                raise ValueError('Nonzero CP triangle required')
            raw = self.raw(self.reference_R, self.reference_S)
            self.recipes = []
            self.basis = raw[:3]
            for k in range(3):
                B, C = raw[3+2*k:5+2*k]
                norm = mp.sqrt(inner(B, B)); alpha = inner(B, C)/inner(B, B)
                remainder = C-alpha*B; second_norm = mp.sqrt(inner(remainder, remainder))
                if second_norm <= 0: raise ValueError('Dependent off-diagonal paths')
                self.recipes.append((norm, alpha, second_norm))
                self.basis.extend([B/norm, remainder/second_norm])
            self.basis = list(self.basis)

    def projectors(self, R):
        I = mp.eye(3); result = []
        for i in range(3):
            P = I.copy()
            for j in range(3):
                if j != i: P = P*(R-self.values[j]*I)/(self.values[i]-self.values[j])
            result.append((P+P.H)/2)
        return result

    def raw(self, R, S):
        P = self.projectors(R); result = list(P)
        for i, j in combinations(range(3), 2):
            B, C = P[i]*S*P[j], P[i]*S*S*P[j]
            result.extend([B+B.H, C+C.H])
        return result

    def evaluate(self, X, Z):
        with mp.workdps(self.digits):
            X, Z = matrix(X), matrix(Z); raw = self.raw(X.H*X, X.H*(Z*Z.H)*X)
            result = raw[:3]
            for k, (norm, alpha, second_norm) in enumerate(self.recipes):
                B, C = raw[3+2*k:5+2*k]
                result.extend([B/norm, (C-alpha*B)/second_norm])
            return result

    def positive_completion(self, target, floor=.5):
        """B(phi)=(I+T(phi))²+floor I; positive for every field value.

        Its coefficients are real. At the reference point B equals target.
        Only the RH block is completed; the full Kahler metric is local near
        zero matter backgrounds, where mixed matter/flavon blocks vanish.
        """
        with mp.workdps(self.digits):
            B = matrix(target); f = mp.mpf(str(floor))
            if f <= 0 or min(mp.eighe((B+B.H)/2)[0]) <= f:
                raise ValueError('Positive floor strictly below the target eigenvalues required')
            if max(abs(B[i, j]-B.H[i, j]) for i in range(3) for j in range(3)) > mp.mpf('1e-14'):
                raise ValueError('Hermitian target metric required')
            B = (B+B.H)/2
            T = hermitian_function(B-f*mp.eye(3), mp.sqrt)-mp.eye(3)
            coeffs = [inner(Q, T) for Q in self.basis]
            reconstructed_T = sum((c*Q for c, Q in zip(coeffs, self.basis)), mp.zeros(3))
            rebuilt = (mp.eye(3)+reconstructed_T)**2+f*mp.eye(3)
            error = max(abs(rebuilt[i, j]-B[i, j]) for i in range(3) for j in range(3))
            return {'real_coefficients': [mp.nstr(c, 80) for c in coeffs],
                    'floor': float(f), 'reconstructed': array(rebuilt), 'error': float(error)}


def fixed_spectrum_bare_metric(Y0, A, target_H, digits=90):
    """Bare RH metric before heavy matching, with the superpotential unchanged.

    Heavy null frame is (I,-A); its metric becomes B+A†A. Choosing
    B=Y0† H_target^-1 Y0-A†A makes the canonically matched YY†=H_target.
    """
    with mp.workdps(digits):
        Y0, A, H = matrix(Y0), matrix(A), matrix(target_H)
        H = (H+H.H)/2
        if min(mp.eighe(H)[0]) <= 0:
            raise ValueError('Positive target mass-squared matrix required')
        B = Y0.H*H**-1*Y0-A.H*A
        B = (B+B.H)/2
        values, _ = mp.eighe(B)
        if min(values) <= 0: raise ValueError('Target requires an indefinite bare metric')
        K = B+A.H*A
        Y = Y0*hermitian_function(K, lambda v: 1/mp.sqrt(v))
        error = max(abs((Y*Y.H-H)[i, j]) for i in range(3) for j in range(3))
        return {'bare_metric': array(B), 'matched_Y': array(Y), 'target_H_error': float(error),
                'minimum_bare_metric_eigenvalue': float(min(values)),
                'metric_operator_distance_from_identity': float(max(abs(v-1) for v in values))}
