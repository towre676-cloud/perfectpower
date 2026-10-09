#!/usr/bin/env python3
"""
PSG source-jet elimination experiment.

Goal:
  Start from the exact Euler-rigid numerator P(x,L,T), impose the algebraic
  chamber relation
      1 + T^2 = e^{2L},
  and eliminate T to derive an obstruction candidate in x, L, Y where Y = e^L.

Important:
  - This script does NOT prove the final theorem.
  - It performs the purely algebraic elimination step that is available from
    the exact source-jet formula.
  - No numerical PSG constants are needed for the symbolic core.
  - Optional numeric checks are included only for sanity-testing.

Usage examples:
  python psg_source_jet_elimination.py
  python psg_source_jet_elimination.py --factor
  python psg_source_jet_elimination.py --numeric-check 1.0638333784865985691510562708330853
"""

import argparse
import math
from pathlib import Path
import sympy as sp


# Symbols
x, L, T, Y = sp.symbols('x L T Y')


def build_P() -> sp.Expr:
    """
    Exact Euler-rigid numerator P(x,L,T) derived in the conversation.
    """
    P = (
        L**7*T**4*x + L**7*T**3 + L**7*T - L**7*x
        - L**6*T**4*x - L**6*T**3 - 3*L**6*T**2*x + 2*L**6*T - 2*L**6*x
        + 2*L**5*T**4*x**3 - 12*L**5*T**2*x - 2*L**5*x**3
        + 2*L**4*T**4*x**3 + 15*L**4*T**3*x**2 - 6*L**4*T*x**2 - 2*L**4*x**3
        + L**3*T**4*x**5 - 8*L**3*T**4*x**3 - L**3*T**3*x**4 + 12*L**3*T**2*x**3
        - L**3*T*x**4 - L**3*x**5
        + 3*L**2*T**4*x**5 - 9*L**2*T**3*x**4 + 3*L**2*T**2*x**5
        - T**3*x**6
    )
    return sp.expand(P)


def eliminate_T(P: sp.Expr) -> sp.Expr:
    """
    Eliminate T from:
        P(x,L,T) = 0
        T^2 - (Y^2 - 1) = 0
    via resultant in T.

    The output is a polynomial obstruction candidate R(x,L,Y).
    """
    chamber = T**2 - (Y**2 - 1)
    R = sp.resultant(sp.expand(P), sp.expand(chamber), T)
    return sp.expand(R)


def summarize_poly(expr: sp.Expr, vars_):
    poly = sp.Poly(expr, *vars_)
    return {
        "total_degree": poly.total_degree(),
        "degrees": {str(v): poly.degree(v) for v in vars_},
        "num_terms": len(poly.terms()),
    }


def save_expr(expr: sp.Expr, path: Path):
    path.write_text(str(expr))


def maybe_factor(expr: sp.Expr) -> sp.Expr:
    # Full symbolic factoring can be expensive; split out content first.
    expr = sp.expand(expr)
    cont, prim = sp.factor_terms(expr).as_coeff_Mul()
    try:
        fac = sp.factor(prim)
        return sp.expand(cont) * fac
    except Exception:
        return expr


def numeric_check(P: sp.Expr, L_value: float):
    """
    Substitute the physical branch relation:
        Y = exp(L), T = sqrt(exp(2L)-1), x = arccos(exp(-L))
    and evaluate P numerically.

    This is only a sanity check, not part of the symbolic elimination proof.
    """
    Yv = math.exp(L_value)
    Tv = math.sqrt(math.exp(2.0 * L_value) - 1.0)
    xv = math.acos(math.exp(-L_value))

    val = sp.N(P.subs({
        L: sp.nsimplify(L_value),
        T: sp.nsimplify(Tv),
        x: sp.nsimplify(xv),
    }), 50)
    return xv, Tv, Yv, val


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--factor", action="store_true",
                    help="attempt to factor the resultant obstruction candidate")
    ap.add_argument("--numeric-check", type=float, default=None,
                    help="optional numeric L-value for sanity check on P")
    ap.add_argument("--outdir", type=str, default=".",
                    help="directory for output text files")
    args = ap.parse_args()

    outdir = Path(args.outdir)
    outdir.mkdir(parents=True, exist_ok=True)

    print("Building exact Euler-rigid numerator P(x,L,T)...")
    P = build_P()
    print("Done.")
    print("P summary:", summarize_poly(P, (x, L, T)))

    print("\nEliminating T using T^2 = Y^2 - 1 with Y = e^L ...")
    R = eliminate_T(P)
    print("Done.")
    print("R(x,L,Y) summary:", summarize_poly(R, (x, L, Y)))

    p_path = outdir / "P_exact.txt"
    r_path = outdir / "R_obstruction_x_L_Y.txt"
    save_expr(P, p_path)
    save_expr(R, r_path)
    print(f"\nSaved exact P to: {p_path}")
    print(f"Saved obstruction candidate R(x,L,Y) to: {r_path}")

    if args.factor:
        print("\nAttempting symbolic factorization of R ...")
        RF = maybe_factor(R)
        rf_path = outdir / "R_obstruction_x_L_Y_factored.txt"
        save_expr(RF, rf_path)
        print(f"Saved factor attempt to: {rf_path}")

    if args.numeric_check is not None:
        print("\nNumeric sanity check on the physical-branch substitution:")
        xv, Tv, Yv, val = numeric_check(P, args.numeric_check)
        print(f"  L = {args.numeric_check}")
        print(f"  x = arccos(e^(-L)) = {xv}")
        print(f"  T = sqrt(e^(2L)-1) = {Tv}")
        print(f"  Y = e^L = {Yv}")
        print(f"  P(x,L,T) ≈ {val}")

    print("\nNotes:")
    print("  * The symbolic elimination step does NOT require the PSG numerical constants.")
    print("  * Those constants are only needed if you also want to impose the special-point")
    print("    chamber law T = (C1/2) v + 2D/v or test at the distinguished PSG point.")
    print("  * The current script derives the first obstruction candidate R(x,L,e^L) by")
    print("    eliminating T only; removing x would require an additional relation.")

if __name__ == "__main__":
    main()
