"""The PerfectPower certificate format, version `pp-cert/1` (docs/CERTIFICATE_FORMAT.md).

A certificate is a JSON object that binds a *statement* (polynomial F, exponent d, complete hit list
among n >= 1) to *data* that the verified Lean checkers accept:

    {"format": "pp-cert/1",
     "kind": "sandwich" | "runge",
     "name": "<Lean identifier>",
     "statement": {"F": [c0, c1, ...], "d": d, "hits": [n1, n2, ...]},
     "statement_sha256": sha256 of the canonical JSON of "statement",
     "data": {...kind-specific...},
     "producer": {"name": ..., "version": ...}}

Segments (both kinds) cover an initial range [1, c) contiguously and in order:
    {"k": "hit",  "n": n, "m": m}       F(n) = m^d
    {"k": "gap",  "n": n, "a": a}       a^d < |F(n)| < (a+1)^d, a >= 0
    {"k": "neg",  "n": n}               F(n) < 0 and d even
    {"k": "ival", "lo": lo, "hi": hi, "t": t}   sandwich on [lo, hi] with offset t (sandwich only)
sandwich data: {"D", "P", "segments", "tail_start", "tail_t"}
runge data:    {"D", "P", "x0", "T", "segments", "signs"}   (signs of G_t for t = -T..T)

The Lean kernel is the authority: `Reflect.check_sound` / `Reflect.rungeCheck_sound` make any
accepted certificate a proof.  `validate` is a fast structural pre-check that rejects malformed
certificates before Lean sees them (it never makes a certificate valid).  `to_lean` is the
importer; `from_lean` parses the generated Lean data back, for round-trip tests.
"""
from __future__ import annotations

import hashlib
import json
import re

from .lean_emit import _expr

FORMAT = 'pp-cert/1'
PRODUCER = {'name': 'perfectpower', 'version': '0.6'}


def canonical(obj) -> str:
    return json.dumps(obj, sort_keys=True, separators=(',', ':'))


def statement_hash(statement) -> str:
    return hashlib.sha256(canonical(statement).encode()).hexdigest()


def _ev(f, n):
    r = 0
    for c in reversed(f):
        r = r * n + c
    return r


def make(kind, name, F, d, hits, data):
    st = {'F': [int(c) for c in F], 'd': int(d), 'hits': [int(n) for n in hits]}
    return {'format': FORMAT, 'kind': kind, 'name': name, 'statement': st,
            'statement_sha256': statement_hash(st), 'data': data, 'producer': PRODUCER}


def produce_sandwich(name, F, d, tail_max=1 << 22):
    from .core import floor_nth_root
    from .lean_emit import _ints
    from .lean_sandwich import Cover
    cov = Cover(F, d, tail_max)
    pieces, (c, tc) = cov.build()
    fi = cov.fi
    segs, hits = [], []
    for pc in pieces:
        if pc[0] == 'point':
            n, info = pc[1], pc[2]
            if info[0] == 'hit':
                segs.append({'k': 'hit', 'n': n, 'm': int(info[1])})
                hits.append(n)
            elif info[0] == 'neg':
                segs.append({'k': 'neg', 'n': n})
            else:
                segs.append({'k': 'gap', 'n': n, 'a': floor_nth_root(abs(_ev(fi, n)), d)})
        else:
            segs.append({'k': 'ival', 'lo': pc[1], 'hi': pc[2], 't': int(pc[3])})
    data = {'D': int(cov.D), 'P': _ints(cov.P), 'segments': segs, 'tail_start': c, 'tail_t': int(tc)}
    return make('sandwich', name, fi, d, hits, data)


def produce_runge(name, F, d, **kw):
    from .core import floor_nth_root, integer_power_root
    from .lean_emit import _ints, plan
    pl = plan(F, d, **kw)
    if pl is None:
        raise ValueError(f'no Runge plan for {name}')
    fi, x0, T = _ints(pl['F']), pl['x0'], pl['T']
    segs, hits = [], []
    for n in range(1, x0):
        v = _ev(fi, n)
        m = integer_power_root(v, d)
        if m is not None:
            segs.append({'k': 'hit', 'n': n, 'm': int(m)})
            hits.append(n)
        elif v < 0 and d % 2 == 0:
            segs.append({'k': 'neg', 'n': n})
        else:
            segs.append({'k': 'gap', 'n': n, 'a': floor_nth_root(abs(v), d)})
    data = {'D': int(pl['D']), 'P': _ints(pl['P']), 'x0': x0, 'T': T, 'segments': segs,
            'signs': [int(pl['Gs'][t][2]) for t in range(-T, T + 1)]}
    return make('runge', name, fi, d, hits, data)


class CertError(ValueError):
    pass


def validate(cert):
    """Structural checks; raises CertError.  Acceptance here is necessary, not sufficient."""
    def need(cond, msg):
        if not cond:
            raise CertError(msg)
    need(cert.get('format') == FORMAT, 'unknown format')
    need(cert.get('kind') in ('sandwich', 'runge'), 'unknown kind')
    need(isinstance(cert.get('name'), str) and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', cert['name']),
         'bad name')
    st, data = cert['statement'], cert['data']
    need(cert.get('statement_sha256') == statement_hash(st), 'statement hash mismatch')
    F, d, hits = st['F'], st['d'], st['hits']
    need(all(isinstance(c, int) for c in F) and any(F), 'F must be a nonzero integer list')
    need(isinstance(d, int) and d >= 2, 'exponent must be an integer >= 2')
    need(hits == sorted(set(hits)) and all(isinstance(n, int) and n >= 1 for n in hits), 'bad hit list')
    end = data['tail_start'] if cert['kind'] == 'sandwich' else data['x0']
    cur, seen = 1, []
    for s in data['segments']:
        k = s.get('k')
        lo = s['lo'] if k == 'ival' else s.get('n')
        hi = s['hi'] if k == 'ival' else s.get('n')
        need(k in ('hit', 'gap', 'neg') or (k == 'ival' and cert['kind'] == 'sandwich'),
             f'segment kind {k!r} not allowed')
        need(isinstance(lo, int) and isinstance(hi, int), 'segment endpoints must be integers')
        need(lo == cur, f'segments must be contiguous: expected {cur}, got {lo}')
        need(lo <= hi, 'empty segment')
        if k == 'hit':
            need(_ev(F, lo) == s['m'] ** d, f'hit witness wrong at n = {lo}')
            seen.append(lo)
        elif k == 'gap':
            v = abs(_ev(F, lo))
            need(s['a'] >= 0 and s['a'] ** d < v < (s['a'] + 1) ** d, f'gap witness wrong at n = {lo}')
        elif k == 'neg':
            need(d % 2 == 0 and _ev(F, lo) < 0, f'neg segment wrong at n = {lo}')
        cur = hi + 1
    need(cur == end, f'segments end at {cur}, the tail starts at {end}')
    need(seen == hits, 'statement hit list differs from the hit segments')
    if cert['kind'] == 'runge':
        need(len(data['signs']) == 2 * data['T'] + 1 and all(s in (1, -1) for s in data['signs']),
             'signs must be +-1, one for each t in [-T, T]')
    return True


def _lst(xs):
    return '[' + ', '.join(f'({x})' if x < 0 else str(x) for x in xs) + ']'


def _seg_lean(s):
    k = s['k']
    if k == 'hit':
        return f".hit {s['n']} ({s['m']})"
    if k == 'gap':
        return f".gap {s['n']} {s['a']}"
    if k == 'neg':
        return f".neg {s['n']}"
    return f".ival {s['lo']} {s['hi']} ({s['t']})"


def to_lean(cert) -> str:
    """Importer: the Lean text (data literal, kernel check, hit-set theorem) for a certificate."""
    validate(cert)
    st, data, name = cert['statement'], cert['data'], cert['name']
    fi, d, hits = st['F'], st['d'], st['hits']
    cid = f'cert_{name}'
    Fz = _expr(fi, 'z')
    stmt = f'IsHit {d} (let z : ℤ := n; {Fz})'
    hitset = '{' + ', '.join(map(str, hits)) + '}' if hits else '∅'
    hdr = f'-- pp-cert/1 statement_sha256 {cert["statement_sha256"]}\n'
    if cert['kind'] == 'sandwich':
        segs = ',\n    '.join(_seg_lean(s) for s in data['segments'])
        body = f'''/-- Sandwich certificate data for `{name}` ({len(data['segments'])} segments, tail from `n = {data['tail_start']}`). -/
def {cid} : Reflect.Cert where
  F := {_lst(fi)}
  d := {d}
  D := {data['D']}
  P := {_lst(data['P'])}
  segs := [
    {segs}]
  c := {data['tail_start']}
  tc := {data['tail_t']}

/-- The verified checker accepts `{cid}` (kernel evaluation, no `Lean.ofReduceBool`). -/
theorem {cid}_ok : Reflect.check {cid} = true := by decide +kernel
'''
        sound, kindname = 'Reflect.check_sound', 'the reflective sandwich checker'
    else:
        segs = ', '.join(_seg_lean(s) for s in data['segments'])
        body = f'''/-- Runge certificate data for `{name}`: `D = {data['D']}`, `P = {_expr(data['P'], "x")}`, `x₀ = {data['x0']}`, `T = {data['T']}`. -/
def {cid} : Reflect.RungeCert where
  F := {_lst(fi)}
  d := {d}
  D := {data['D']}
  P := {_lst(data['P'])}
  x₀ := {data['x0']}
  T := {data['T']}
  segs := [{segs}]
  signs := {_lst(data['signs'])}

/-- The verified Runge checker accepts `{cid}` (kernel evaluation). -/
theorem {cid}_ok : Reflect.rungeCheck {cid} = true := by decide +kernel
'''
        sound, kindname = 'Reflect.rungeCheck_sound', 'a reflective Runge certificate'
    thm = f'''
/-- Complete hit set, certified by {kindname}: for `n ≥ 1`,
`{_expr(fi, "n")} = m ^ {d}` is solvable in integers iff `n ∈ {hitset}`. -/
theorem {name} (n : ℕ) (hn : 1 ≤ n) : {stmt} ↔ n ∈ ({hitset} : Finset ℕ) := by
  have h := {sound} {cid}_ok n hn
  have hF : {cid}.F = {_lst(fi)} := rfl
  have e : Reflect.ev {cid}.F n = (let z : ℤ := n; {Fz}) := by
    rw [hF]; simp only [Reflect.ev]; ring
  have hh : Reflect.hitsOf {cid}.segs = {_lst(hits)} := by decide +kernel
  have hd : {cid}.d = {d} := rfl
  rw [e, hh, hd] at h
  rw [h]
  simp
'''
    return hdr + body + thm


_INT = r'\(?(-?\d+)\)?'


def from_lean(text: str):
    """Parse the data of one generated certificate back into (kind, name, statement, data)."""
    m = re.search(r'def cert_(\w+) : Reflect\.(Cert|RungeCert) where', text)
    if not m:
        raise CertError('no certificate definition found')
    name, lk = m.group(1), m.group(2)
    block = text[m.end():text.index('theorem', m.end())]

    def field(f):
        mm = re.search(rf'^\s*{f} := (\[.*?\]|\(?-?\d+\)?)', block, re.S | re.M)
        return mm.group(1).strip()

    def ints(s):
        return [int(x) for x in re.findall(r'-?\d+', s)]
    segs = []
    for k, rest in re.findall(r'\.(hit|gap|neg|ival) ([^,\]]*)', field('segs')):
        v = ints(rest)
        segs.append({'hit': lambda: {'k': 'hit', 'n': v[0], 'm': v[1]},
                     'gap': lambda: {'k': 'gap', 'n': v[0], 'a': v[1]},
                     'neg': lambda: {'k': 'neg', 'n': v[0]},
                     'ival': lambda: {'k': 'ival', 'lo': v[0], 'hi': v[1], 't': v[2]}}[k]())
    F, d = ints(field('F')), ints(field('d'))[0]
    hits = [s['n'] for s in segs if s['k'] == 'hit']
    if lk == 'Cert':
        data = {'D': ints(field('D'))[0], 'P': ints(field('P')), 'segments': segs,
                'tail_start': ints(field('c'))[0], 'tail_t': ints(field('tc'))[0]}
        kind = 'sandwich'
    else:
        data = {'D': ints(field('D'))[0], 'P': ints(field('P')), 'x0': ints(field('x₀'))[0],
                'T': ints(field('T'))[0], 'segments': segs, 'signs': ints(field('signs'))}
        kind = 'runge'
    return make(kind, name, F, d, hits, data)
