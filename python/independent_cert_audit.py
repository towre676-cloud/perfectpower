"""Independent integer-arithmetic audit of pp-cert/1 files.

This deliberately does not import the certificate producer or the Lean checker.
The Lean kernel remains the authority for the generated theorems; this script
checks the serialized arithmetic and fails closed if any file is malformed.
"""

import glob
import hashlib
import json
import sys
from pathlib import Path


def require(ok, message):
    if not ok:
        raise ValueError(message)


def add(a, b):
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)
            for i in range(max(len(a), len(b)))]


def mul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def power(a, d):
    out = [1]
    for _ in range(d):
        out = mul(out, a)
    return out


def neg(a):
    return [-x for x in a]


def shifted(a, n):
    """Coefficients of a(x+n), calculated by Horner composition."""
    out = [0]
    for c in reversed(a):
        out = add(mul(out, [n, 1]), [c])
    return out


def value(a, n):
    out = 0
    for c in reversed(a):
        out = out * n + c
    return out


def positive_on_tail(a, start):
    coefficients = shifted(a, start)
    return all(c >= 0 for c in coefficients) and any(c > 0 for c in coefficients)


def check(cert):
    require(cert['format'] == 'pp-cert/1', 'format')
    statement, data = cert['statement'], cert['data']
    digest = hashlib.sha256(json.dumps(statement, sort_keys=True,
                                       separators=(',', ':')).encode()).hexdigest()
    require(digest == cert['statement_sha256'], 'statement hash')
    F, d = statement['F'], statement['d']
    D, P = data['D'], data['P']
    require(isinstance(d, int) and d >= 2 and isinstance(D, int) and D > 0,
            'exponent or denominator')
    require(F and P and all(type(c) is int for c in F + P), 'polynomial coefficients')
    limit = data['tail_start'] if cert['kind'] == 'sandwich' else data['x0']
    require(type(limit) is int and limit >= 1, 'tail start')

    current, hits = 1, []
    for segment in data['segments']:
        kind = segment['k']
        if kind in ('hit', 'gap', 'neg'):
            n = segment['n']
            require(n == current, f'prefix coverage at {current}')
            v = value(F, n)
            if kind == 'hit':
                require(v == segment['m'] ** d, f'hit witness at {n}')
                hits.append(n)
            elif kind == 'gap':
                a = segment['a']
                require(type(a) is int and a >= 0 and a ** d < abs(v) < (a + 1) ** d,
                        f'gap at {n}')
            else:
                require(d % 2 == 0 and v < 0, f'negative value at {n}')
            current += 1
        elif kind == 'ival':
            require(cert['kind'] == 'sandwich', 'interval in Runge certificate')
            lo, hi, t = segment['lo'], segment['hi'], segment['t']
            require(lo == current and hi >= lo, f'interval coverage at {current}')
            for n in range(lo, hi + 1):
                p, scaled = value(P, n) + t, D ** d * value(F, n)
                require(p > 0 and p ** d < scaled < (p + 1) ** d,
                        f'interval inequality at {n}')
            current = hi + 1
        else:
            raise ValueError(f'unknown segment kind {kind!r}')
    require(current == limit, 'tail coverage')
    require(hits == statement['hits'], 'declared hit list')

    scaled_F = [D ** d * c for c in F]
    if cert['kind'] == 'sandwich':
        t = data['tail_t']
        lower = add(P, [t])
        upper = add(P, [t + 1])
        for q in (lower, add(scaled_F, neg(power(lower, d))),
                  add(power(upper, d), neg(scaled_F))):
            require(positive_on_tail(q, limit), 'sandwich tail')
    elif cert['kind'] == 'runge':
        T, signs = data['T'], data['signs']
        require(type(T) is int and T >= 0 and len(signs) == 2 * T + 1,
                'Runge window')
        require(all(s in (-1, 1) for s in signs), 'Runge signs')
        remainder = add(scaled_F, neg(power(P, d)))
        p_at_start = shifted(P, limit)
        r_at_start = shifted(remainder, limit)
        p_power = power(p_at_start, d - 1)
        bound = [(T + 1) * c for c in p_power]
        for q in (p_at_start, add(bound, r_at_start),
                  add(bound, neg(r_at_start))):
            require(all(c >= 0 for c in q) and any(c > 0 for c in q),
                    'Runge tail bound')
        if d % 2:
            for q in (add(power(p_at_start, d), r_at_start),
                      add(power(p_at_start, d), neg(r_at_start))):
                require(all(c >= 0 for c in q) and any(c > 0 for c in q),
                        'odd Runge sign bound')
        for t, sign in zip(range(-T, T + 1), signs):
            q = add(scaled_F, neg(power(add(P, [t]), d)))
            require(positive_on_tail([sign * c for c in q], limit),
                    f'Runge sign at {t}')
    else:
        raise ValueError(f'unknown certificate kind {cert["kind"]!r}')


def main(paths):
    if not paths:
        paths = sorted(glob.glob('certs/*/*.json'))
    require(paths, 'no certificates found')
    failures = 0
    for path in paths:
        try:
            check(json.loads(Path(path).read_text()))
            print('OK', path)
        except (ValueError, KeyError, TypeError, OverflowError) as exc:
            print('FAIL', path, exc, file=sys.stderr)
            failures += 1
    print(f'{len(paths) - failures}/{len(paths)} certificates passed')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
