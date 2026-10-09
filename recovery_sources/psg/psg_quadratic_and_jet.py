import sympy as sp
import time
import argparse

v, a, p = sp.symbols('v a p')

D = 2*a*v**2*(2*a - 1)*(v + 4 - 8*a)**2
N = (
    8*p**3*v**4
    + p**2*(512*a**3*v**2 - 96*a**2*v**3 - 576*a**2*v**2 - 8*a*v**4
            + 64*a*v**3 + 192*a*v**2 + 2*v**4 - 8*v**3 - 16*v**2)
    + p*(-256*a**4*v**2 - 256*a**4*v + 48*a**3*v**3 + 384*a**3*v**2
         + 384*a**3*v + 4*a**2*v**4 - 44*a**2*v**3 - 216*a**2*v**2
         - 192*a**2*v - 2*a*v**4 + 16*a*v**3 + 56*a*v**2 + 32*a*v
         - 3*v**3 - 6*v**2)
    + 64*a**5*v**2 + 128*a**5*v - 256*a**5
    - 16*a**4*v**3 - 128*a**4*v**2 - 96*a**4*v + 576*a**4
    + 20*a**3*v**3 + 76*a**3*v**2 - 80*a**3*v - 512*a**3
    - 8*a**2*v**3 - 8*a**2*v**2 + 104*a**2*v + 224*a**2
    + a*v**3 - 5*a*v**2 - 36*a*v - 48*a + v**2 + 4*v + 4
)

KNOWN_LINEAR = [a, 2*a - 1, v, v + 4 - 8*a]
KNOWN_PRODUCT = sp.expand(sp.prod(KNOWN_LINEAR))


def Xtilde(F: sp.Expr) -> sp.Expr:
    return sp.expand(D*sp.diff(F, v) + D*p*sp.diff(F, a) + N*sp.diff(F, p))


def poly(expr: sp.Expr) -> sp.Poly:
    return sp.Poly(sp.expand(expr), v, a, p)


def primitive_poly_expr(expr: sp.Expr) -> sp.Expr:
    P = poly(expr)
    if P.is_zero:
        return sp.Integer(0)
    _, prim = P.primitive()
    return sp.expand(prim.as_expr())


def normalize_linear_form(H: sp.Expr) -> sp.Expr:
    P = poly(H)
    if P.is_zero:
        return sp.Integer(0)
    lead = P.coeffs()[0]
    return sp.expand(P.as_expr() / lead)


def normalize_up_to_scalar(H: sp.Expr) -> sp.Expr:
    P = poly(H)
    if P.is_zero:
        return sp.Integer(0)
    lead = P.coeffs()[0]
    return primitive_poly_expr(P.as_expr() / lead)


def divides(num: sp.Expr, den: sp.Expr):
    q, r = sp.div(poly(num), poly(den))
    return r == 0, (sp.expand(q.as_expr()) if r == 0 else None)


def darboux_status(H: sp.Expr):
    ok, cof = divides(Xtilde(H), H)
    return ok, (sp.factor(cof) if ok else None)


def gcd_with_known_factors(H: sp.Expr) -> sp.Expr:
    return sp.expand(sp.gcd(poly(H), poly(KNOWN_PRODUCT)).as_expr())


def coprime_to_known_linear_factors(H: sp.Expr) -> bool:
    return gcd_with_known_factors(H) == 1


def linear_darboux_search_fast():
    c1, c2, c3, c4 = sp.symbols('c1 c2 c3 c4')
    H = c1*v + c2*a + c3*p + c4
    Y = Xtilde(H)
    sols = []
    for idx, var in enumerate((v, a, p)):
        coeffs = [c1, c2, c3]
        subs_norm = {coeffs[idx]: 1}
        Hn = sp.expand(H.subs(subs_norm))
        Yn = sp.expand(Y.subs(subs_norm))
        if var == v:
            expr = sp.expand(Yn.subs(v, -c2*a - c3*p - c4))
            P = sp.Poly(expr, a, p)
            unknowns = [c2, c3, c4]
        elif var == a:
            expr = sp.expand(Yn.subs(a, -c1*v - c3*p - c4))
            P = sp.Poly(expr, v, p)
            unknowns = [c1, c3, c4]
        else:
            expr = sp.expand(Yn.subs(p, -c1*v - c2*a - c4))
            P = sp.Poly(expr, v, a)
            unknowns = [c1, c2, c4]
        G = sp.groebner(P.coeffs(), *unknowns, order='lex')
        if list(G) == [sp.Integer(1)]:
            continue
        raw = sp.solve([sp.Eq(g, 0) for g in G], unknowns, dict=True)
        for sol in raw:
            Hsol = normalize_linear_form(H.subs({**subs_norm, **sol}))
            if Hsol != 0 and all(sp.expand(Hsol - T) != 0 for T in sols):
                sols.append(Hsol)
    return sols


def reducible_quadratic_scan():
    out = []
    seen = set()
    for i, L1 in enumerate(KNOWN_LINEAR):
        for j in range(i, len(KNOWN_LINEAR)):
            H = normalize_up_to_scalar(sp.expand(L1 * KNOWN_LINEAR[j]))
            key = sp.srepr(H)
            if key in seen:
                continue
            seen.add(key)
            ok, cof = darboux_status(H)
            out.append((H, ok, cof))
    return out


def quadratic_search_case_monic_p2():
    h2, h3, h4, h5, h6, h7, h8, h9, h10 = sp.symbols('h2:11')
    H = p**2 + h2*v*p + h3*a*p + h4*p + h5*v**2 + h6*v*a + h7*a**2 + h8*v + h9*a + h10
    Y = Xtilde(H)
    _, rem = sp.div(sp.Poly(Y, p), sp.Poly(H, p))
    coeffs = sp.Poly(sp.expand(rem.as_expr()), v, a, p).coeffs()
    unknowns = [h2, h3, h4, h5, h6, h7, h8, h9, h10]
    G = sp.groebner(coeffs, *unknowns, order='lex')
    if list(G) == [sp.Integer(1)]:
        return []
    raw = sp.solve([sp.Eq(g, 0) for g in G], unknowns, dict=True)
    sols = []
    seen = set()
    for sol in raw:
        Hsol = normalize_up_to_scalar(H.subs(sol))
        if poly(Hsol).total_degree() == 2 and coprime_to_known_linear_factors(Hsol):
            ok, cof = darboux_status(Hsol)
            if ok:
                key = sp.srepr(Hsol)
                if key not in seen:
                    seen.add(key)
                    sols.append((Hsol, cof))
    return sols


def quadratic_search_case_linear_in_p():
    b1, b2, b3 = sp.symbols('b1 b2 b3')
    c1, c2, c3, c4, c5, c6 = sp.symbols('c1:7')
    B = b1*v + b2*a + b3
    C = c1*v**2 + c2*v*a + c3*a**2 + c4*v + c5*a + c6
    H = sp.expand(B*p + C)
    Y = Xtilde(H)
    sols, seen = [], set()
    for norm in (b1, b2, b3):
        subs_norm = {norm: 1}
        Bn = sp.expand(B.subs(subs_norm))
        Cn = sp.expand(C.subs(subs_norm))
        Yn = sp.expand(Y.subs(subs_norm))
        expr = sp.expand(sp.together(Yn.subs(p, -Cn/Bn)) * Bn**3)
        num = sp.together(expr).as_numer_denom()[0]
        vars_to_solve = [u for u in (b1, b2, b3, c1, c2, c3, c4, c5, c6) if u != norm]
        G = sp.groebner(sp.Poly(sp.expand(num), v, a).coeffs(), *vars_to_solve, order='lex')
        if list(G) == [sp.Integer(1)]:
            continue
        raw = sp.solve([sp.Eq(g, 0) for g in G], vars_to_solve, dict=True)
        for sol in raw:
            Hsol = normalize_up_to_scalar(H.subs({**subs_norm, **sol}))
            if poly(Hsol).total_degree() == 2 and coprime_to_known_linear_factors(Hsol):
                ok, cof = darboux_status(Hsol)
                if ok:
                    key = sp.srepr(Hsol)
                    if key not in seen:
                        seen.add(key)
                        sols.append((Hsol, cof))
    return sols


def derive_second_order_ode_from_squared_first_order():
    q = sp.symbols('q')
    lam = 8*a*(2*a - 1)
    S = (8*a - v - 4)**2 / v**2
    P = 8*p - (4*a - 1)
    Eexpr = sp.simplify(-S*lam / (P**2 - S))
    dE = sp.expand(sp.diff(Eexpr, v) + p*sp.diff(Eexpr, a) + q*sp.diff(Eexpr, p))
    qsol = sp.solve(sp.Eq(sp.simplify(dE), sp.simplify(Eexpr + 1)), q)
    if len(qsol) != 1:
        raise RuntimeError(f"Expected unique q, got {len(qsol)}")
    qexpr = sp.simplify(qsol[0])
    agrees = sp.simplify(sp.cancel(qexpr - N/D)) == 0
    return sp.factor(Eexpr), sp.factor(qexpr), agrees


def prolong_one_more_jet():
    q = sp.simplify(N/D)
    q2 = sp.expand(sp.diff(q, v) + p*sp.diff(q, a) + q*sp.diff(q, p))
    return sp.factor(q), sp.factor(sp.together(q2))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--heavy-quadratic', action='store_true', help='run the expensive new quadratic searches')
    args = ap.parse_args()

    t0 = time.time()
    print('Known linear factors:')
    for H in KNOWN_LINEAR:
        ok, cof = darboux_status(H)
        print(f'  {sp.factor(H)}   Darboux={ok}')
        if ok:
            print(f'    cofactor={cof}')

    print('\nFast linear search:')
    for H in linear_darboux_search_fast():
        print(f'  {sp.factor(H)}')

    print('\nReducible quadratic scan:')
    for H, ok, cof in reducible_quadratic_scan():
        print(f'  {sp.factor(H)}   Darboux={ok}')

    print('\nJet-elimination step:')
    Eexpr, qexpr, agrees = derive_second_order_ode_from_squared_first_order()
    print(f'  E = {Eexpr}')
    print(f'  derived a" = {qexpr}')
    print(f'  matches supplied N/D? {agrees}')

    print('\nOne more prolongation:')
    q1, q2 = prolong_one_more_jet()
    print(f'  p\'  = {q1}')
    print(f"  p'' = {q2}")

    if args.heavy_quadratic:
        print('\nQuadratic search: monic p^2 case')
        sols = quadratic_search_case_monic_p2()
        if sols:
            for H, cof in sols:
                print(f'  new coprime candidate: {sp.factor(H)}')
                print(f'    cofactor={cof}')
        else:
            print('  no coprime monic-p^2 quadratic Darboux factors found')

        print('\nQuadratic search: linear-in-p case')
        sols = quadratic_search_case_linear_in_p()
        if sols:
            for H, cof in sols:
                print(f'  new coprime candidate: {sp.factor(H)}')
                print(f'    cofactor={cof}')
        else:
            print('  no coprime linear-in-p quadratic Darboux factors found')
    else:
        print('\nSkipping heavy quadratic searches. Use --heavy-quadratic to run them.')

    print(f'\nRun completed in {(time.time()-t0)*1000:.1f}ms')

if __name__ == '__main__':
    main()
