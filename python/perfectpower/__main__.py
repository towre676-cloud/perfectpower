"""python -m perfectpower scan|certificate|verify|surgery|classify|enumerate|count ..."""
import argparse
import json
from pathlib import Path
from .core import (RigidCertificate, count, hit_indices, rigid_certificate,
                   verify_certificate, windows, integer_power_root)


def coefficients(raw):
    return [int(s.strip()) for s in raw.split(',')]


def main():
    parser = argparse.ArgumentParser(description='Exact polynomial perfect-power research console')
    sub = parser.add_subparsers(dest='command', required=True)
    for name in ('scan', 'certificate', 'surgery', 'classify', 'enumerate', 'count'):
        p = sub.add_parser(name)
        p.add_argument('--coeff', required=True, type=coefficients,
                       help='S coefficients low to high, comma separated')
        p.add_argument('--d', type=int, required=True)
        p.add_argument('--k', type=int, default=0)
        if name in ('scan', 'surgery', 'count'):
            p.add_argument('--N', type=int, required=True)
        if name == 'surgery':
            p.add_argument('--override', action='append', default=[],
                           help='n:value; replace S(n) at finitely many prefix indices')
            p.add_argument('--N0', type=int, required=True)
    p = sub.add_parser('verify')
    p.add_argument('certificate', type=Path)
    args = parser.parse_args()
    if args.command == 'verify':
        obj = RigidCertificate(**json.loads(args.certificate.read_text()))
        result = verify_certificate(obj)
        print(json.dumps({'valid': result}))
        raise SystemExit(0 if result else 1)
    if args.d < 2:
        parser.error('d >= 2 required')
    f = args.coeff.copy()
    f[0] += args.k
    if args.command == 'classify':
        from dataclasses import asdict
        from .atlas import classify
        out = asdict(classify(f, args.d))
        out['exponent'] = str(out['exponent'])
        print(json.dumps(out, indent=2, default=str))
        return
    if args.command == 'enumerate':
        from dataclasses import asdict
        from .runge import runge_enumerate
        e = runge_enumerate(f, args.d)
        if e is None:
            print(json.dumps({'classification': 'nonrigid', 'enumeration': None}))
            raise SystemExit(1)
        print(json.dumps({'classification': 'perfect_polynomial_power' if e.exact_identity
                          else 'complete_finite_hit_list', 'enumeration': asdict(e)}, indent=2))
        return
    if args.command == 'count':
        from .atlas import classify, structural_count
        cl = classify(f, args.d)
        print(json.dumps({'kind': cl.kind, 'growth': cl.growth, 'N': args.N,
                          'count': structural_count(f, args.d, args.N),
                          'kappa': cl.details.get('kappa')}, indent=2))
        return
    if args.command == 'certificate':
        cert = rigid_certificate(f, args.d)
        print(json.dumps({'classification': 'nonrigid' if cert is None else
                          ('perfect_polynomial_power' if cert.exact_identity else 'finite_hit_cutoff'),
                          'certificate': None if cert is None else cert.to_json()}, indent=2))
    elif args.command == 'scan':
        hits = list(hit_indices(args.coeff, args.d, args.k, args.N))
        print(json.dumps({'coefficients': args.coeff, 'd': args.d, 'k': args.k,
                          'N': args.N, 'count': len(hits), 'hits': hits,
                          'dyadic_windows': windows(args.coeff, args.d, args.k, args.N)}, indent=2))
    else:
        if args.N0 < 1 or args.N < args.N0:
            parser.error('requires 1 <= N0 <= N')
        overrides = {}
        for item in args.override:
            try:
                index, value = map(int, item.split(':'))
            except ValueError:
                parser.error('override must be n:value')
            if not 1 <= index < args.N0 or index in overrides:
                parser.error('override indices must be distinct and in [1,N0)')
            overrides[index] = value
        # The two sequences agree beyond N0 by their construction, not a finite scan.
        D = 0
        for n, replacement in overrides.items():
            v = 0
            for c in reversed(args.coeff):
                v = v * n + c
            v += args.k
            D += (integer_power_root(v, args.d) is not None)
            D -= (integer_power_root(replacement + args.k, args.d) is not None)
        at_N = count(args.coeff, args.d, args.k, args.N)
        other_at_N = at_N - D
        if not 0 <= other_at_N <= args.N:
            raise AssertionError('count identity inconsistent')
        print(json.dumps({'tested_N0': args.N0, 'tested_N': args.N,
                          'fixed_difference': D, 'density_gap_at_N': D / args.N,
                          'count_base': at_N, 'count_modified': other_at_N,
                          'status': 'exact finite-surgery identity; density conclusion by D/N -> 0'}))

if __name__ == '__main__':
    main()
