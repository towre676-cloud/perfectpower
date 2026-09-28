"""Interval-sandwich Lean certificates for complete hit sets (rigid branch).

Let F be rigid with positive leading coefficient b^d, Q = P/D its truncated d-th root (P in Z[x],
positive leading coefficient).  For each n >= 1 put V(n) = D^d F(n) and t(n) = floor(V(n)^(1/d)) - P(n).
If V(n) > 0 is not a d-th power then

    (P(n) + t)^d < D^d F(n) < (P(n) + t + 1)^d,     P(n) + t >= 0,                         (*)

and `no_hit_of_sandwich` shows F(n) is not a d-th power (F(n) = m^d would make D^d F(n) = (Dm)^d).
Because D V^(1/d) - P -> 0, t(n) is constant on long runs; the cover of [1, oo) is

  * finitely many *intervals* [a, a + w] on which one t works for every integer n;
  * a *tail* [c, oo) on which one t works;
  * isolated *points* (hits, zeros, sign changes, or where no interval certificate was found).

Certificates.  For an interval, write each of the three polynomials in (*), shifted by x = a + k,
as POS(k) - NEG(k) with POS, NEG having nonnegative coefficients.  For 0 <= k <= w we have
NEG(k) <= NEG(w) (monotone, proved by `gcongr`) and POS(k) >= POS(0) (proved by `positivity`), so
POS(0) > NEG(w) certifies positivity on the whole interval.  For the tail, NEG must be empty.
Lean re-proves every identity by `ring` and every numeral by `norm_num`; Python only proposes
the cover, so a compiled certificate does not depend on this module being correct.
"""
from __future__ import annotations

from fractions import Fraction

from .core import floor_nth_root, integer_power_root, normalize, power, rigid_certificate
from .lean_emit import _expr, _ints, _shift
from .polyalg import add, scale, subtract


def _split(p):
    """Positive part (with constant) and negated negative part, as integer coefficient lists."""
    pos = [int(c) if c > 0 else 0 for c in p]
    neg = [int(-c) if c < 0 else 0 for c in p]
    return pos, neg


def _eval(p, x) -> int:
    v = 0
    for c in reversed(p):
        v = v * x + c
    return v


def _interval_ok(polys, a: int, w: int | None) -> bool:
    """Every poly positive on {a + k : 0 <= k <= w} by the POS(0) > NEG(w) test (w=None: tail)."""
    for p in polys:
        pos, neg = _split(_shift(p, a))
        if w is None:
            if any(neg) or pos[0] <= 0:
                return False
        elif pos[0] <= _eval(neg, w):
            return False
    return True


class Cover:
    def __init__(self, coefficients, d: int, tail_max: int = 1 << 22):
        cert = rigid_certificate(coefficients, d)
        if cert is None or cert.exact_identity:
            raise ValueError('needs a rigid F that is not an exact d-th power')
        F = normalize(coefficients)
        if F[-1] <= 0:
            raise ValueError('needs a positive leading coefficient')
        self.F, self.d, self.D = F, d, cert.denominator
        P = normalize(cert.root_numerators)
        self.P = scale(P, -1) if P[-1] < 0 else P
        self.V = scale(F, self.D ** d)
        self.fi = _ints(F)
        self.tail_max = tail_max

    def polys(self, t: int):
        P, d, V = self.P, self.d, self.V
        Pt = add(P, (Fraction(t),))
        return [Pt, subtract(V, power(Pt, d)), subtract(power(add(Pt, (Fraction(1),)), d), V)]

    def t_at(self, n: int):
        """('hit', m) / ('neg',) / ('t', t) at the index n."""
        v = _eval(self.fi, n)
        m = integer_power_root(v, self.d)
        if m is not None:
            return ('hit', m)
        if v < 0:
            return ('neg',) if self.d % 2 == 0 else ('point',)
        V = self.D ** self.d * v
        return ('t', floor_nth_root(V, self.d) - int(_eval(_ints(self.P), n)))

    def tail(self):
        """Least power of two c (and its t) such that the tail [c, oo) is certified."""
        c = 1
        while c <= self.tail_max:
            kind = self.t_at(c)
            if kind[0] == 't' and _interval_ok(self.polys(kind[1]), c, None):
                return c, kind[1]
            c *= 2
        raise ValueError('no tail certificate below tail_max')

    def build(self):
        c, tc = self.tail()
        # shrink the tail start by bisection on [c/2, c] while the same t still certifies it
        lo, hi = max(1, c // 2), c
        while lo < hi:
            mid = (lo + hi) // 2
            k = self.t_at(mid)
            if k == ('t', tc) and _interval_ok(self.polys(tc), mid, None):
                hi = mid
            else:
                lo = mid + 1
        c = hi
        pieces = []                     # ('point', n, info) | ('interval', a, b, t)
        runs = []
        n = 1
        while n < c:
            k = self.t_at(n)
            if k[0] != 't':
                pieces.append(('point', n, k))
                n += 1
                continue
            m = n
            while m + 1 < c and self.t_at(m + 1) == k:
                m += 1
            runs.append((n, m, k[1]))
            n = m + 1
        for a, b, t in runs:
            pieces.extend(self._cover_run(a, b, t))
        pieces.sort(key=lambda p: p[1])
        return pieces, (c, tc)

    def _cover_run(self, a: int, b: int, t: int):
        out, stack = [], [(a, b)]
        polys = self.polys(t)
        while stack:
            lo, hi = stack.pop()
            if lo == hi:
                out.append(('point', lo, ('t', t)))
            elif _interval_ok(polys, lo, hi - lo):
                out.append(('interval', lo, hi, t))
            else:
                mid = (lo + hi) // 2
                stack += [(lo, mid), (mid + 1, hi)]
        return out


def _cert_block(cov: Cover, name: str, a: int, w: int | None, t: int) -> list[str]:
    """Lean lines proving the three inequalities for x = a + k (0 <= k <= w, or k >= 0)."""
    d, D = cov.d, cov.D
    kk = '(k : ℤ)'
    Fz = _expr(cov.fi, 'z')
    Pz = _expr(_ints(cov.P), 'z')
    lhs = [f'({Pz}) + ({t})',
           f'{D} ^ {d} * ({Fz}) - (({Pz}) + ({t})) ^ {d}',
           f'(({Pz}) + ({t}) + 1) ^ {d} - {D} ^ {d} * ({Fz})']
    goals = ['0 ≤', '0 <', '0 <']
    lines = []
    for i, (p, L, g) in enumerate(zip(cov.polys(t), lhs, goals)):
        pos, neg = _split(_shift(p, a))
        c0, rest = pos[0], [0] + pos[1:]
        rest_e = _expr(rest, kk) if any(rest) else '0'
        neg_e = _expr(neg, kk) if any(neg) else '0'
        lines.append(f'  have e{i} : {L} = {c0} + ({rest_e}) - ({neg_e}) := by rw [hz]; ring')
        lines.append(f'  have r{i} : (0 : ℤ) ≤ {rest_e} := by positivity')
        if w is None or not any(neg):
            lines.append(f'  have b{i} : {neg_e} ≤ (0 : ℤ) := by norm_num')
        else:
            bound = _eval(neg, w)
            lines.append(f'  have b{i} : {neg_e} ≤ ({bound} : ℤ) := by')
            lines.append(f'    calc {neg_e} ≤ {_expr(neg, f"({w} : ℤ)")} := by gcongr')
            lines.append(f'      _ = {bound} := by norm_num')
        lines.append(f'  have g{i} : {g} {L} := by rw [e{i}]; linarith')
    lines.append(f'  exact no_hit_of_sandwich (D := {D}) (a := ({Pz}) + ({t})) g0 (by linarith [g1]) (by linarith [g2])')
    return lines


def emit_sandwich(name: str, coefficients, d: int, tail_max: int = 1 << 22):
    """Lean source (lemmas + main theorem) and statistics for the complete hit set of F(n) = m^d."""
    cov = Cover(coefficients, d, tail_max)
    pieces, (c, tc) = cov.build()
    fi = cov.fi
    Fz = _expr(fi, 'z')
    stmt = f'IsHit {d} (let z : ℤ := n; {Fz})'
    out, dispatch, hits = [], [], []
    header = f'/-- `{name}`: piece of the sandwich certificate; see `{name}`. -/'
    for idx, pc in enumerate(pieces):
        if pc[0] == 'point':
            n, info = pc[1], pc[2]
            v = _eval(fi, n)
            if info[0] == 'hit':
                hits.append((n, info[1]))
                dispatch.append(('hit', n))
                continue
            lem = f'{name}_p{idx}'
            if info[0] == 'neg':
                proof = '(not_isHit_neg (by decide) (by norm_num))'
            else:
                r = floor_nth_root(abs(v), d)
                proof = f'(not_isHit_between (a := {r}) (by norm_num) (by norm_num) (by norm_num))'
            out.append(header.replace('piece', 'point'))
            out.append(f'lemma {lem} : ¬ IsHit {d} (let z : ℤ := ({n} : ℕ); {Fz}) := by')
            out.append(f'  simp only; exact {proof}')
            dispatch.append(('point', n, lem))
        else:
            _, a, b, t = pc
            lem = f'{name}_i{idx}'
            out.append('set_option maxHeartbeats 1000000 in')
            out.append(header.replace('piece', 'interval'))
            out.append(f'lemma {lem} (n : ℕ) (h1 : {a} ≤ n) (h2 : n ≤ {b}) : ¬ {stmt} := by')
            out.append('  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1')
            out.append(f'  have hk : (k : ℤ) ≤ {b - a} := by exact_mod_cast (show k ≤ {b - a} by omega)')
            out.append(f'  have hz : ((({a} + k : ℕ)) : ℤ) = {a} + (k : ℤ) := by push_cast; ring')
            out.append(f'  generalize ((({a} + k : ℕ)) : ℤ) = z at hz ⊢')
            out.append('  simp only')
            out.extend(_cert_block(cov, name, a, b - a, t))
            dispatch.append(('interval', a, b, lem))
    lem = f'{name}_tail'
    out.append('set_option maxHeartbeats 1000000 in')
    out.append(header.replace('piece', 'tail'))
    out.append(f'lemma {lem} (n : ℕ) (h1 : {c} ≤ n) : ¬ {stmt} := by')
    out.append('  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h1')
    out.append(f'  have hz : ((({c} + k : ℕ)) : ℤ) = {c} + (k : ℤ) := by push_cast; ring')
    out.append(f'  generalize ((({c} + k : ℕ)) : ℤ) = z at hz ⊢')
    out.append('  simp only')
    out.extend(_cert_block(cov, name, c, None, tc))
    hitset = '{' + ', '.join(str(n) for n, _ in hits) + '}' if hits else '∅'
    main = [f'/-- Complete hit set, certified by interval sandwiches: for `n ≥ 1`, '
            f'`{_expr(fi, "n")} = m ^ {d}` is solvable in integers iff `n ∈ {hitset}`. '
            f'Tail certificate from `n = {c}`; {len(dispatch)} pieces below it. -/',
            f'theorem {name} (n : ℕ) (hn : 1 ≤ n) : {stmt} ↔ n ∈ ({hitset} : Finset ℕ) := by',
            '  constructor',
            '  · intro h']
    for dp in dispatch:
        hi = dp[1] if dp[0] in ('hit', 'point') else dp[2]
        main.append(f'    rcases Nat.lt_or_ge n {hi + 1} with hb | hb')
        if dp[0] == 'hit':
            main.append(f'    · obtain rfl : n = {dp[1]} := by omega')
            main.append('      simp')
        elif dp[0] == 'point':
            main.append(f'    · obtain rfl : n = {dp[1]} := by omega')
            main.append(f'      exact absurd h {dp[2]}')
        else:
            main.append(f'    · exact absurd h ({dp[3]} n (by omega) (by omega))')
    main.append(f'    exact absurd h ({lem} n (by omega))')
    main.append('  · intro h')
    if hits:
        main.append('    simp only [Finset.mem_insert, Finset.mem_singleton] at h')
        main.append('    rcases h with ' + ' | '.join('rfl' for _ in hits))
        for n, m in hits:
            main.append(f'    · exact ⟨{m}, by norm_num⟩')
    else:
        main.append('    simp at h')
    stats = {'tail_start': c, 'tail_t': tc, 'pieces': len(dispatch),
             'intervals': sum(1 for p in dispatch if p[0] == 'interval'),
             'points': sum(1 for p in dispatch if p[0] != 'interval'), 'hits': hits}
    return '\n'.join(out + main) + '\n', stats
