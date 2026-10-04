"""Exact finite residue filters for one- and two-unit orbits.

These are search certificates, not Lean theorems. A period is returned only
when the full matrix returns to the identity modulo m; bounded prefixes fail.
"""
from rank_one_sources import Mx, mm

IDENTITY = [[int(i == j) for j in range(3)] for i in range(3)]


def matrix_period(A, modulus, limit=100000):
    if modulus < 2:
        raise ValueError('modulus must be at least 2')
    A = [[x % modulus for x in row] for row in A]
    X = IDENTITY
    powers = []
    for _ in range(limit):
        powers.append(X)
        X = [[x % modulus for x in row] for row in mm(X, A)]
        if X == IDENTITY:
            return powers
    raise ValueError('no certified period within limit')


def apply(A, gamma):
    return tuple(sum(row[j] * gamma[j] for j in range(3)) for row in A)


def allowed(P, Q, units, gamma, modulus, leading, shift=0, plane=(0,0,1), extra_divisibility=()):
    """Necessary exponent residues for w2=0 and a | w0+h*w1.

    modulus must be a positive multiple of |a|. Negative exponents are
    interpreted modulo the certified periods. Supports rank one or two.
    """
    if leading == 0 or modulus % abs(leading):
        raise ValueError('modulus must be a multiple of nonzero |a|')
    if len(units) not in (1, 2):
        raise ValueError('expected one or two units')
    if any(d < 1 or modulus % d for _,d in extra_divisibility):
        raise ValueError('extra divisors must divide the modulus')
    powers = [matrix_period(Mx(P, Q, eta), modulus) for eta in units]
    rows = []
    for i, A in enumerate(powers[0]):
        for j, B in enumerate(powers[1] if len(powers) == 2 else [IDENTITY]):
            w = apply(mm(A, B), gamma)
            if (sum(plane[t]*w[t] for t in range(3)) % modulus == 0
                    and (w[0] + shift*w[1]) % abs(leading) == 0
                    and all(sum(row[t]*w[t] for t in range(3)) % d == 0 for row,d in extra_divisibility)):
                rows.append([i, j] if len(powers) == 2 else [i])
    return {'modulus': modulus, 'periods': [len(xs) for xs in powers],
            'allowed_residues': rows, 'tested_residues': len(powers[0]) * (len(powers[1]) if len(powers)==2 else 1),
            'status': 'exact Python residue filter; not an exponent bound or Lean certificate'}


def information_plan(P, Q, units, gamma, modulus, leading, *, scope,
                     extra_divisibility=(), plane=(0,0,1), shift=0,
                     costs=None, subset_limit=1_000_000, pair_limit=1_000_000):
    """Minimal readouts deciding this modular unit-orbit admissibility test.

    Uses the SAME certified period tables as allowed(). Covers residue classes,
    including signed exponents by reduction, but supplies no global height bound.
    """
    from perfectpower.information import InformationProblem, Observation
    table = allowed(P,Q,units,gamma,modulus,leading,shift,plane,extra_divisibility)
    periods = table['periods']
    states = ([(i,) for i in range(periods[0])] if len(periods)==1 else
              [(i,j) for i in range(periods[0]) for j in range(periods[1])])
    powers = [matrix_period(Mx(P,Q,u),modulus) for u in units]
    vectors = {s:apply(powers[0][s[0]] if len(s)==1 else
                      mm(powers[0][s[0]],powers[1][s[1]]),gamma) for s in states}
    predicates = [('plane',lambda s:sum(plane[t]*vectors[s][t] for t in range(3)) % modulus == 0),
                  ('lattice',lambda s:(vectors[s][0]+shift*vectors[s][1]) % abs(leading)==0)]
    predicates += [(f'extra_{i}',lambda s,row=row,d=d:
                     sum(row[t]*vectors[s][t] for t in range(3)) % d==0)
                   for i,(row,d) in enumerate(extra_divisibility)]
    accepted={tuple(s) for s in table['allowed_residues']}
    observations=[Observation(name,read,(costs or {}).get(name,1)) for name,read in predicates]
    problem=InformationProblem(states,lambda s:s in accepted,observations,
        scope=scope,pair_limit=pair_limit)
    result=problem.compile(subset_limit=subset_limit)
    result.update(modulus=modulus,periods=periods,
                  allowed_residue_count=len(accepted),global_exponent_bound=False,
                  signed_exponents='reduce modulo certified matrix periods')
    return result
