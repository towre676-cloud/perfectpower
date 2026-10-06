"""A consumer bridge: emit a checked replacement as a Why3 proof obligation and let Why3 decide it.

For an SMT-LIB task whose live assertions contain a conjunct certified by `smt_cert` (a source-bound
certificate re-derived by `check_certificate`), this module writes a WhyML module with three parts:
- **`val lemma curve`**: the Lean theorem's statement, as a lemma function called with explicit arguments (`∀ x y : ℤ, y² = x³ + k ↔ (x, y) ∈ L`, or
  `y² ≠ x³ + k`), generated from the statement re-parsed out of the Lean source (`smt_cert._lean_list`).
  Why3's `int` is the mathematical integers, so the statement is the same proposition.
- **`lemma replacement`**: `∀ n m, C(n, m) ↔ ⋁ (n = a ∧ m = b)` for the source conjunct `C`.  Why3
  must **prove** this from the axiom: it is the substitution `x = r n + s`, which until now was
  checked only in Python.
- **`goal vc`**: the query itself, `∀ vars. A₁ ∧ … ∧ A_k → false` (the SMT task asks whether its
  assertions are unsatisfiable, so validity of this goal is the verification condition).

A **control module** states the same goal without the axiom and lemma.

The trust boundary moves.  Why3, with z3 as its prover, now checks the replacement and the VC.
The remaining imported fact is the curve theorem, stated in Why3 exactly as Lean proves it, and its
proof is in Lean, not in Why3.  This is not GNATprove: no SPARK toolchain is available here.  Why3 is
the layer GNATprove discharges its VCs through.

Run: python3 -m perfectpower.why3_bridge TASK.smt2 [--out DIR] [--timeout S]
"""
from __future__ import annotations

import hashlib
import json
import re
import shutil
import subprocess
from pathlib import Path


class Untranslatable(Exception):
    pass


def _name(s: str) -> str:
    out = re.sub(r'[^A-Za-z0-9_]', '_', s)
    if not out or not out[0].isalpha():
        out = 'v_' + out
    out = out.lower() if out[0].isupper() else out
    # x,y are local names in the imported curve lemma; reserve them too.
    reserved = {'x','y','true','false','not','if','then','else','let','in','forall','exists',
                'module','end','use','import','clone','type','val','lemma','goal','axiom',
                'function','predicate','constant','assert','assume','ensures','requires',
                'result','old','at','match','with','do','done','while','for','to','downto',
                'exception','raise','try','rec','and','or','unit','int','bool'}
    return 'v_'+out if out in reserved else out


def _allocate_name(symbol, names):
    if symbol not in names:
        base = _name(symbol)
        candidate, suffix = base, 0
        used = set(names.values())
        while candidate in used:
            suffix += 1
            candidate = f'{base}_{suffix}'
        names[symbol] = candidate
    return names[symbol]


def to_why(e, names: dict) -> str:
    """A z3 Int/Bool term as WhyML (int.Int, int.EuclideanDivision); Untranslatable otherwise."""
    import z3
    if z3.is_int_value(e):
        v = e.as_long()
        return str(v) if v >= 0 else f'({v})'
    if z3.is_rational_value(e):
        if e.denominator_as_long() != 1:
            raise Untranslatable('non-integer numeral')
        v = e.numerator_as_long()
        return str(v) if v >= 0 else f'({v})'
    if z3.is_true(e):
        return 'true'
    if z3.is_false(e):
        return 'false'
    if z3.is_const(e) and e.decl().kind() == z3.Z3_OP_UNINTERPRETED:
        if e.sort() not in (z3.IntSort(), z3.BoolSort()):
            raise Untranslatable(f'sort {e.sort()}')
        return _allocate_name(str(e), names)
    k = e.decl().kind()
    a = [to_why(c, names) for c in e.children()] if k != z3.Z3_OP_POWER else None
    bin_ops = {z3.Z3_OP_LE: '<=', z3.Z3_OP_LT: '<', z3.Z3_OP_GE: '>=', z3.Z3_OP_GT: '>'}
    if k == z3.Z3_OP_AND:
        return '(' + ' /\\ '.join(a) + ')' if a else 'true'
    if k == z3.Z3_OP_OR:
        return '(' + ' \\/ '.join(a) + ')' if a else 'false'
    if k == z3.Z3_OP_NOT:
        return f'(not {a[0]})'
    if k == z3.Z3_OP_IMPLIES:
        return f'({a[0]} -> {a[1]})'
    if k == z3.Z3_OP_EQ:
        if e.arg(0).sort() == z3.BoolSort():
            return f'({a[0]} <-> {a[1]})'
        return f'({a[0]} = {a[1]})'
    if k == z3.Z3_OP_DISTINCT:
        return '(' + ' /\\ '.join(f'{x} <> {y}' for i, x in enumerate(a) for y in a[i + 1:]) + ')'
    if k in bin_ops:
        return f'({a[0]} {bin_ops[k]} {a[1]})'
    if k == z3.Z3_OP_ADD:
        return '(' + ' + '.join(a) + ')'
    if k == z3.Z3_OP_SUB:
        return '(' + ' - '.join(a) + ')'
    if k == z3.Z3_OP_UMINUS:
        return f'(- {a[0]})'
    if k == z3.Z3_OP_MUL:
        return '(' + ' * '.join(a) + ')'
    if k == z3.Z3_OP_IDIV:
        return f'(div {a[0]} {a[1]})'
    if k == z3.Z3_OP_MOD:
        return f'(mod {a[0]} {a[1]})'
    if k == z3.Z3_OP_ITE:
        return f'(if {a[0]} then {a[1]} else {a[2]})'
    if k == z3.Z3_OP_TO_REAL:
        return a[0]
    if k == z3.Z3_OP_POWER:
        base, ex = e.children()
        if not (z3.is_int_value(ex) or z3.is_rational_value(ex)):
            raise Untranslatable('symbolic exponent')
        n = ex.as_long() if z3.is_int_value(ex) else ex.numerator_as_long()
        if n < 0 or (z3.is_rational_value(ex) and ex.denominator_as_long() != 1):
            raise Untranslatable('exponent')
        if n > 4096:
            raise Untranslatable('expanded exponent exceeds translation budget')
        b = to_why(base, names)
        return '(' + ' * '.join([b] * n) + ')' if n else '1'
    raise Untranslatable(str(e.decl()))


def _disj(n, m, W) -> str:
    return ' \\/ '.join(f'({n} = {a if a >= 0 else f"({a})"} /\\ {m} = {b if b >= 0 else f"({b})"})'
                        for a, b in W) if W else 'false'


def emit(task_text: str, query: int = 0):
    """(whyml text, control text, meta) for one query of a task; raises Untranslatable."""
    import z3
    from . import smt_cert as sc
    sha = hashlib.sha256(task_text.encode()).hexdigest()
    cmds = sc.split_commands(task_text)
    queries, ctx = sc.replay(cmds)
    if not queries:
        raise Untranslatable('no check-sat')
    q = queries[query]
    if q.assuming:
        raise Untranslatable('check-sat-assuming')
    defn = sc.defined_names(cmds)
    certs, atoms, names = [], [], {}
    for i in q.live_asserts:
        for r in sc.classify_assert(cmds, i, ctx[i], sha, defn):
            if r.category in ('barrier', 'extension', 'parse_error'):
                raise Untranslatable(f'assertion {i}: {r.category}')
            if r.certificate:
                ok, why = sc.check_certificate(r.certificate, task_text)
                if not ok:
                    raise Untranslatable(f'certificate rejected: {why}')
                certs.append(r.certificate)
        parsed = z3.parse_smt2_string('\n'.join(cmds[d] for d in ctx[i]) + '\n' + cmds[i])
        # The emitted goal quantifies mathematical integers. A free Boolean
        # constant needs a separately typed binder, which this bridge does not
        # implement; reject it instead of silently emitting an integer binder.
        stack = list(parsed)
        while stack:
            term = stack.pop()
            if (z3.is_const(term) and term.decl().kind() == z3.Z3_OP_UNINTERPRETED
                    and term.sort() != z3.IntSort()):
                raise Untranslatable('only integer free variables are supported by the Why3 bridge')
            stack.extend(term.children())
        atoms += [to_why(a, names) for a in parsed]
    if not certs:
        raise Untranslatable('no checked replacement in this query')
    consts = '\n'.join(f'  (* source symbol UTF-8 hex: {orig.encode().hex()} *)' for orig in names)
    vars_ = ' '.join(sorted(names.values()))
    body = ' /\\ '.join(atoms)
    goal = f'  goal vc: forall {vars_}:int. {body} -> false\n'
    parts, meta = [], []
    for j, c in enumerate(certs):
        k = c['affine']['k']
        name, L = sc._lean_list(k)
        if name != c['theorem']:
            raise Untranslatable('theorem changed since certification')
        kk = f'({k})' if k < 0 else str(k)
        rhs = ' \\/ '.join(f'(x = {a} /\\ y = {b if b >= 0 else f"({b})"})' for a, b in L) if L else 'false'
        # the imported theorem as a lemma *function*: calling it with explicit arguments adds exactly
        # that ground instance, with no reliance on quantifier instantiation
        curve = (f'  val lemma curve_{j} (x y: int) : unit\n'
                 f'    ensures {{ y * y = x * x * x + {kk} <-> {rhs} }}\n')
        n, m = names[c['unknowns']['n']], names[c['unknowns']['m']]
        parsed_atom = z3.parse_smt2_string('\n'.join(cmds[d] for d in ctx[c['command_index']]) + '\n'
                                           + cmds[c['command_index']])
        atom = [x for a in parsed_atom for x in sc._conjuncts(a) if x.sexpr() == c['atom']][0]
        r, s_ = c['affine']['r'], c['affine']['s']
        xs = f'({r} * {n} + {s_ if s_ >= 0 else f"({s_})"})'
        # a let-lemma: Why3 must prove it, by instantiating the curve theorem at x = r n + s, y = m
        lemma = (f'  let lemma replacement_{j} ({n} {m}: int)\n'
                 f'    ensures {{ {to_why(atom, dict(names))} <-> {_disj(n, m, [tuple(w) for w in c["witnesses"]])} }}\n'
                 f'  = let x = {xs} in\n'
                 f'    curve_{j} x {m};\n'
                 f'    assert {{ {to_why(atom, dict(names))} <-> {m} * {m} = x * x * x + {kk} }}\n')
        parts.append(f'  (* {name}, re-parsed from the Lean source; proved in Lean, imported here *)\n'
                     + curve + lemma)
        meta.append({'theorem': name, 'k': k, 'r': c['affine']['r'], 's': c['affine']['s'],
                     'witnesses': c['witnesses'], 'command_index': c['command_index']})
    head = '  use int.Int\n  use int.EuclideanDivision\n'
    why = (f'(* generated by perfectpower.why3_bridge from task sha256 {sha}, query {query} *)\n'
           f'module VC\n{head}{consts}\n' + ''.join(parts) + goal + 'end\n')
    control = (f'(* control: the same goal without the imported curve theorem or the replacement *)\n'
               f'module Control\n{head}{goal}end\n')
    return why, control, {'task_sha256': sha, 'query': query, 'replacements': meta}


def run_why3(path: Path, timeout: float) -> dict:
    """Per-goal Why3 results with z3."""
    out = subprocess.run(['why3', 'prove', '-P', 'z3', '-t', str(timeout), str(path)],
                         capture_output=True, text=True, timeout=timeout * 20 + 60)
    res, cur = {}, None
    for line in (out.stdout + out.stderr).splitlines():
        m = re.match(r'\s*Goal (\S+?)(?:\'vc)?\.', line)
        if m:
            cur = m.group(1)
        m = re.search(r'Prover result is: (\w+)', line)
        if m and cur:
            res[cur] = m.group(1)
    return {'goals': res, 'returncode': out.returncode}


def main(argv=None):
    import argparse
    ap = argparse.ArgumentParser()
    ap.add_argument('task')
    ap.add_argument('--out', default='.')
    ap.add_argument('--timeout', type=float, default=10)
    a = ap.parse_args(argv)
    if not shutil.which('why3'):
        raise SystemExit('why3 not found')
    text = Path(a.task).read_text()
    why, control, meta = emit(text)
    out = Path(a.out)
    out.mkdir(parents=True, exist_ok=True)
    stem = Path(a.task).stem
    (out / f'{stem}.mlw').write_text(why)
    (out / f'{stem}_control.mlw').write_text(control)
    meta['why3'] = run_why3(out / f'{stem}.mlw', a.timeout)
    meta['control'] = run_why3(out / f'{stem}_control.mlw', a.timeout)
    goals = meta['why3']['goals']
    meta['accepted'] = bool(goals) and all(v == 'Valid' for v in goals.values()) and \
        any(g.startswith('replacement') for g in goals) and 'vc' in goals
    meta['why3_version'] = subprocess.run(['why3', '--version'], capture_output=True, text=True).stdout.strip()
    print(json.dumps(meta, indent=1))
    return meta


if __name__ == '__main__':
    main()
