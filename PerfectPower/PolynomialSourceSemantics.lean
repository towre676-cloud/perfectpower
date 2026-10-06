import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

namespace PerfectPower.PolynomialSourceSemantics

/-- The polynomial source language; division and arbitrary parser text are outside it. -/
inductive Expr where
  | constant : ℚ → Expr
  | variable : Expr
  | add : Expr → Expr → Expr
  | multiply : Expr → Expr → Expr
  | negate : Expr → Expr
  | power : Expr → ℕ → Expr

def evaluate (x : ℚ) : Expr → ℚ
  | .constant c => c
  | .variable => x
  | .add a b => evaluate x a + evaluate x b
  | .multiply a b => evaluate x a * evaluate x b
  | .negate a => -evaluate x a
  | .power a n => evaluate x a ^ n

noncomputable def compile : Expr → Polynomial ℚ
  | .constant c => Polynomial.C c
  | .variable => Polynomial.X
  | .add a b => compile a + compile b
  | .multiply a b => compile a * compile b
  | .negate a => -compile a
  | .power a n => compile a ^ n

/-- Structural compilation preserves the value at every rational input. -/
theorem compile_correct (e : Expr) (x : ℚ) : (compile e).eval x=evaluate x e := by
  induction e <;> simp_all [compile, evaluate]

/-- Source equality and the compiled polynomial's zero set coincide globally. -/
theorem equality_correct (a b : Expr) (x : ℚ) :
    evaluate x a=evaluate x b ↔ (compile (.add a (.negate b))).eval x=0 := by
  rw [compile_correct]
  change evaluate x a=evaluate x b ↔ evaluate x a + -evaluate x b=0
  rw [← sub_eq_add_neg, sub_eq_zero]

end PerfectPower.PolynomialSourceSemantics
