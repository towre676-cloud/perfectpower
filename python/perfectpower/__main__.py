"""python -m perfectpower scan|certificate|verify|surgery|classify|enumerate|count|shifts|solve ..."""
import argparse
import sys
import json
from pathlib import Path
from .core import (RigidCertificate, count, hit_indices, rigid_certificate,
                   verify_certificate, windows, integer_power_root)


def coefficients(raw):
    from fractions import Fraction
    out = [Fraction(s.strip()) for s in raw.split(',')]
    return [int(c) if c.denominator == 1 else c for c in out]


def main():
    parser = argparse.ArgumentParser(description='Exact polynomial perfect-power research console')
    sub = parser.add_subparsers(dest='command', required=True)
    from .psg_console import add_commands as add_psg_commands
    add_psg_commands(sub)
    from .checked_box import add_commands as add_checked_commands
    add_checked_commands(sub)
    from .checked_population import add_commands as add_population_commands
    add_population_commands(sub)
    from .checked_global_population import add_commands as add_global_commands
    add_global_commands(sub)
    from .checked_nonlinear_population import add_commands as add_nonlinear_commands
    add_nonlinear_commands(sub)
    from .checked_pell_population import add_commands as add_pell_commands
    add_pell_commands(sub)
    from .checked_family_population import add_commands as add_family_commands
    add_family_commands(sub)
    from .checked_pell_family import add_commands as add_pell_family_commands
    add_pell_family_commands(sub)
    from .checked_pell_orbits import add_commands as add_orbit_commands
    add_orbit_commands(sub)
    from .automatic_population import add_commands as add_auto_commands
    add_auto_commands(sub)
    from .checked_factorial_unit import add_commands as add_unit_commands
    add_unit_commands(sub)
    from .checked_landau import add_commands as add_landau_commands
    add_landau_commands(sub)
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
    p = sub.add_parser('lean', help='emit a Lean theorem pinning down the complete hit set')
    p.add_argument('--coeff', required=True, type=coefficients)
    p.add_argument('--d', type=int, required=True)
    p.add_argument('--name', default='generated_hits')
    p.add_argument('--method', choices=('runge', 'sandwich'), default='runge',
                   help='runge: Taylor-shift plan (small thresholds); sandwich: interval cover')
    p = sub.add_parser('shifts', help='type of S + k for every integer shift k')
    p.add_argument('--coeff', required=True, type=coefficients)
    p.add_argument('--d', type=int, required=True)
    p = sub.add_parser('solve', help='compile an integer constraint into a plan (constraint compiler)')
    p.add_argument('--expr', required=True, help="integer polynomial in n, e.g. '(5*n - 7)**3 - 2'")
    p.add_argument('--form', choices=('power', 'triangular', 'root'), default='power',
                   help='power: expr = m^d; triangular: expr = y(y+1)/2; root: a y^2 + b y + c = expr')
    p.add_argument('--d', type=int, default=2)
    p.add_argument('--a', type=int, default=1)
    p.add_argument('--b', type=int, default=0)
    p.add_argument('--c', type=int, default=0)
    p.add_argument('--domain', choices=('int', 'nonneg', 'pos'), default='int')
    p.add_argument('--N', type=int, default=10 ** 6)
    p.add_argument('--program', action='store_true', help='print the specialized program instead')
    p = sub.add_parser('prove', help='emit a standalone Lean theorem for a descent-certified plan')
    p.add_argument('--expr', required=True, help="cubic in n, e.g. '(2*n + 1)**3 - 74'")
    p.add_argument('--name', default='emitted_hits')
    p = sub.add_parser('oeis', help='compare PerfectPower coordinates with a local OEIS snapshot')
    p.add_argument('--stripped', type=Path, required=True, help='local stripped(.gz) from oeis.org')
    p.add_argument('--names', type=Path, help='local names(.gz), for reading leads only')
    p.add_argument('--reviewed', type=Path, help='JSON {A-number: review note} of checked definitions')
    p.add_argument('--retrieved', help='date the snapshot was downloaded (recorded in the atlas)')
    p = sub.add_parser('information', help='minimal residue decoder on an explicit finite interval')
    p.add_argument('--coeff', required=True, type=coefficients)
    p.add_argument('--d', type=int, required=True)
    p.add_argument('--lo', type=int, required=True)
    p.add_argument('--hi', type=int, required=True)
    p.add_argument('--moduli', required=True, help='comma-separated integer moduli')
    p.add_argument('--pair-limit', type=int, default=1_000_000)
    p.add_argument('--subset-limit', type=int, default=1_000_000)
    sub.add_parser('covering-replay', help='recompute source-backed Fisher 571a1 obstruction')
    p = sub.add_parser('lattice', help='integer presentation invariants and optional image membership')
    p.add_argument('--matrix', required=True, type=json.loads, help='JSON integer matrix; columns generate image')
    p.add_argument('--vector', type=json.loads, help='JSON integer vector to pull back')
    p.add_argument('--prime', type=int, help='optional prime-power torsion profile')
    p.add_argument('--minor-limit', type=int, default=100_000)
    p = sub.add_parser('integer-lift', help='complete integral fibre with a replayable Smith certificate')
    p.add_argument('--matrix', required=True, type=json.loads)
    p.add_argument('--vector', required=True, type=json.loads)
    p.add_argument('--operation-limit', type=int, default=100_000)
    p = sub.add_parser('integral-task-section', help='construct every integral target lift through a carrier')
    p.add_argument('--target', required=True, type=json.loads)
    p.add_argument('--carrier', required=True, type=json.loads)
    p.add_argument('--operation-limit', type=int, default=100_000)
    p = sub.add_parser('integer-project', help='eliminate affine equalities with exact integer parameters')
    p.add_argument('source', type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--certificate-output', type=Path)
    p.add_argument('--operation-limit', type=int, default=100_000)
    p = sub.add_parser('recurrence', help='execute an exact supplied recurrence')
    p.add_argument('--coeff', required=True, type=coefficients)
    p.add_argument('--initial', required=True, type=coefficients)
    p.add_argument('--index', type=int, required=True)
    p.add_argument('--modulus', type=int, help='also count modular zeros before --stop')
    p.add_argument('--stop', type=int, default=0)
    p = sub.add_parser('sequence-atlas', help='discover prefix recurrences in actual staged .seq files')
    p.add_argument('--seq-dir', required=True, type=Path)
    p = sub.add_parser('primary-module', help='phase-sensitive cyclic subgroup counts')
    p.add_argument('--prime', type=int, required=True)
    p.add_argument('--exponents', required=True, help='comma-separated positive exponents')
    p.add_argument('--census', action='store_true', help='enumerate all subgroups within small-module budgets')
    sub.add_parser('operator-replay', help='exact recovered hypergeometric/Weyl prefix replay')
    p = sub.add_parser('operator-atlas', help='exact operator recovery on staged recurrence models')
    p.add_argument('--seq-dir', required=True, type=Path)
    p = sub.add_parser('fitting', help='construct rational nilpotent/stable decomposition')
    p.add_argument('--matrix', required=True, type=json.loads)
    p = sub.add_parser('task-section', help='construct a rational target lift through a carrier')
    p.add_argument('--target', required=True, type=json.loads)
    p.add_argument('--carrier', required=True, type=json.loads)
    p.add_argument('--injective', action='store_true')
    p = sub.add_parser('recurrence-identity', help='all-future equality of supplied recurrence definitions')
    p.add_argument('--left-coeff', required=True, type=coefficients)
    p.add_argument('--left-initial', required=True, type=coefficients)
    p.add_argument('--right-coeff', required=True, type=coefficients)
    p.add_argument('--right-initial', required=True, type=coefficients)
    p = sub.add_parser('norm-operator-replay', help='exact unit operators and task planes from a source packet')
    p.add_argument('--packet', required=True, type=Path)
    p.add_argument('--radius', type=int, default=3)
    p = sub.add_parser('linear-perturbation', help='complete integer points on a quadratic square plus a linear perturbation')
    p.add_argument('--parameters', required=True, type=coefficients, help='L,a,b,c,d')
    p.add_argument('--work-limit', type=int, default=100_000)
    p.add_argument('--emit-lean', action='store_true')
    p.add_argument('--name', default='quartic_points')
    p = sub.add_parser('centered-divisor', help='complete square-plus-constant solve after integer centering')
    p.add_argument('--coeff', required=True, type=coefficients)
    p.add_argument('--k', required=True, type=int)
    p.add_argument('--work-limit', type=int, default=1_000_000)
    p = sub.add_parser('square-triangular-query', help='exact count with residue filters and a monotone boundary')
    bound=p.add_mutually_exclusive_group(required=True)
    bound.add_argument('--bound', type=int)
    bound.add_argument('--power-ten', type=int, help='bound=10**exponent')
    p.add_argument('--filter', action='append', default=[], help='index:modulus:residue or root:modulus:residue')
    p.add_argument('--state-limit', type=int, default=100_000)
    p = sub.add_parser('showcase', help='build the three complete-family demonstration packets')
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--benchmark', action='store_true')
    p.add_argument('--timeout-ms', type=int, default=2000)
    p.add_argument('--repeats', type=int, default=3)
    p = sub.add_parser('finite-project', help='eliminate a supported complete finite relation from an SMT query')
    p.add_argument('source', type=Path)
    p.add_argument('--output', required=True, type=Path)
    p.add_argument('--lean-output', type=Path)
    p = sub.add_parser('divisor-sum', help='exact sum of divisors from validated prime factorization')
    p.add_argument('--factors', required=True, type=json.loads, help='JSON list [[prime,exponent],...]')
    p = sub.add_parser('sigma-quartic', help='complete prime and integer inputs for sigma(p^4)+shift square')
    p.add_argument('--shift', type=int, default=0)
    p.add_argument('--emit-lean', action='store_true')
    p.add_argument('--name', default='sigma_quartic_points')
    p = sub.add_parser('branched-geometry', help='exact normalized-cover topology and faithful connection')
    p.add_argument('--coeff',required=True,type=coefficients)
    p.add_argument('--d',required=True,type=int)
    p.add_argument('--k',default=0,type=int)
    p.add_argument('--connection',action='store_true')
    p.add_argument('--cells',action='store_true')
    p.add_argument('--differentials',action='store_true')
    p = sub.add_parser('legendre-period-bounds', help='exact rational enclosures of normalized Legendre periods')
    p.add_argument('--lambda', dest='lam', required=True)
    p.add_argument('--terms',type=int,default=64)
    from .enhanced_cli import add_commands as add_enhanced_commands
    add_enhanced_commands(sub)
    from .deep_recovery_cli import add_commands as add_deep_commands
    add_deep_commands(sub)
    from .divisor_kernel_cli import add_commands as add_divisor_kernel_commands
    add_divisor_kernel_commands(sub)
    from .analytic_geometry_cli import add_commands as add_analytic_commands
    add_analytic_commands(sub)
    from .monomial_cli import add_commands as add_monomial_commands
    add_monomial_commands(sub)
    from .positive_geometry_cli import add_commands
    add_commands(sub)
    from .population_cli import add_commands as add_population_commands
    add_population_commands(sub)
    from .query_service import add_commands as add_service_commands
    add_service_commands(sub)
    p = sub.add_parser('verify')
    p.add_argument('certificate', type=Path)
    args = parser.parse_args()
    from .psg_console import cli as psg_cli
    if psg_cli(args):
        return
    from .checked_box import cli as checked_cli
    from .checked_population import cli as population_cli
    from .checked_global_population import cli as global_cli
    from .checked_nonlinear_population import cli as nonlinear_cli
    from .checked_pell_population import cli as pell_cli
    from .checked_family_population import cli as family_cli
    from .checked_pell_family import cli as pell_family_cli
    from .checked_pell_orbits import cli as orbit_cli
    from .automatic_population import cli as auto_cli
    if orbit_cli(args) or auto_cli(args):
        return
    if family_cli(args) or pell_family_cli(args):
        return
    if nonlinear_cli(args) or pell_cli(args):
        return
    if global_cli(args):
        return
    if population_cli(args):
        return
    if checked_cli(args):
        return
    from .checked_factorial_unit import cli as unit_cli
    if unit_cli(args):
        return
    from .checked_landau import cli as landau_cli
    if landau_cli(args):
        return
    from .query_service import cli as service_cli
    if service_cli(args):
        return
    from .population_cli import dispatch as dispatch_population
    if dispatch_population(args):
        return
    from .enhanced_cli import dispatch as dispatch_enhanced
    if dispatch_enhanced(args):
        return
    from .deep_recovery_cli import dispatch as dispatch_deep
    if dispatch_deep(args):
        return
    from .divisor_kernel_cli import dispatch as dispatch_divisor_kernel
    if dispatch_divisor_kernel(args):
        return
    from .analytic_geometry_cli import dispatch as dispatch_analytic
    if dispatch_analytic(args):
        return
    from .monomial_cli import dispatch as dispatch_monomial
    if dispatch_monomial(args):
        return
    from .positive_geometry_cli import dispatch
    if dispatch(args):
        return
    if args.command == 'legendre-period-bounds':
        from .legendre_period_bounds import legendre_period_packet
        print(json.dumps(legendre_period_packet(args.lam,args.terms),indent=2))
        return
    if args.command == 'branched-geometry':
        from .branched_geometry import profile,faithful_laplacian,cell_surface
        coeff=list(args.coeff);coeff[0]+=args.k
        result=profile(coeff,args.d)
        if args.connection:result['connection']=faithful_laplacian(result['root_multiplicities'],args.d)
        if args.cells:result['cell_model_per_component']=cell_surface(result['genus_per_component'])
        if args.differentials:
            from .holomorphic_basis import differential_basis
            result['holomorphic_basis']=differential_basis(coeff,args.d)
        print(json.dumps(result,indent=2,default=str))
        return
    if args.command == 'divisor-sum':
        from .divisor_sum import sigma_from_factorization,exact_root
        result=sigma_from_factorization(args.factors)
        result['power_roots']={str(d):exact_root(result['sigma'],d) for d in range(2,9)}
        print(json.dumps(result,indent=2))
        return
    if args.command == 'sigma-quartic':
        from .divisor_sum import repunit_quartic
        from .linear_perturbation import emit_square_leading
        if args.emit_lean:
            print(emit_square_leading(1,1,1,1,1+args.shift,name=args.name),end='')
        else:
            print(json.dumps(repunit_quartic(args.shift),indent=2))
        return
    if args.command == 'linear-perturbation':
        from .linear_perturbation import solve,emit_lean
        if len(args.parameters)!=5:parser.error('five parameters L,a,b,c,d required')
        if args.emit_lean:
            print(emit_lean(*args.parameters,name=args.name),end='')
        else:
            print(json.dumps(solve(*args.parameters,work_limit=args.work_limit),indent=2))
        return
    if args.command == 'information':
        from .information import polynomial_information
        plan = polynomial_information(args.coeff,args.d,args.lo,args.hi,
            [int(m) for m in args.moduli.split(',')],pair_limit=args.pair_limit)
        print(json.dumps(plan.compile(subset_limit=args.subset_limit),indent=2))
        return
    if args.command == 'covering-replay':
        from .covering import fisher_571_replay
        print(json.dumps(fisher_571_replay(),indent=2))
        return
    if args.command in ('integer-lift','integral-task-section','integer-project'):
        from .integer_lifting import solve_integer,integral_task_section
        if args.command=='integer-lift':
            out=solve_integer(args.matrix,args.vector,operation_limit=args.operation_limit)
        elif args.command=='integral-task-section':
            out=integral_task_section(args.target,args.carrier,operation_limit=args.operation_limit)
        else:
            from .integer_projection import project_integer_query
            projection=project_integer_query(args.source.read_text(),operation_limit=args.operation_limit)
            args.output.write_text(projection.smt)
            out={'symbols':projection.symbols,'parameters':projection.parameters,
                 'bindings':projection.bindings,'linear':projection.linear,'solution':projection.solution}
            if args.certificate_output: args.certificate_output.write_text(json.dumps(out,indent=2)+'\n')
        print(json.dumps(out,indent=2))
        return
    if args.command == 'lattice':
        from .integral_lattice import smith_invariants,lattice_membership,local_torsion_profile
        out = smith_invariants(args.matrix,minor_limit=args.minor_limit)
        if args.vector is not None:
            out['membership'] = lattice_membership(args.matrix,args.vector,minor_limit=args.minor_limit)
        if args.prime is not None:
            out['local_profile'] = local_torsion_profile(args.matrix,args.prime,minor_limit=args.minor_limit)
        print(json.dumps(out,indent=2))
        return
    if args.command == 'recurrence':
        from .recurrence import Recurrence,filter_count
        rec=Recurrence(tuple(args.coeff),tuple(args.initial))
        num,den=rec.generating_function()
        out={'value':str(rec.nth(args.index)),'index':args.index,
             'numerator':list(map(str,num)),'denominator':list(map(str,den)),
             'execution_verified':False,'scope':'supplied recurrence'}
        if args.modulus is not None:
            cert=rec.residue_filter(args.modulus,lambda s:s[0]==0)
            out['modular_zero_count']=filter_count(cert,args.stop)
            out['period']=cert['period'];out['preperiod']=cert['preperiod']
        print(json.dumps(out,indent=2))
        return
    if args.command == 'sequence-atlas':
        from .recurrence import scan_seq_directory
        print(json.dumps(scan_seq_directory(args.seq_dir),indent=2))
        return
    if args.command == 'primary-module':
        from .primary_modules import primary_cyclic_counts,subgroup_census
        exponents=tuple(int(x) for x in args.exponents.split(','))
        print(json.dumps((subgroup_census if args.census else primary_cyclic_counts)(args.prime,exponents),indent=2))
        return
    if args.command == 'operator-replay':
        from .exact_operators import hypergeometric_replay
        print(json.dumps(hypergeometric_replay(),indent=2))
        return
    if args.command in ('operator-atlas','fitting','task-section','recurrence-identity'):
        if args.command == 'operator-atlas':
            from .operator_recovery import recovery_receipt
            out=recovery_receipt(args.seq_dir)
        elif args.command == 'fitting':
            from .exact_linear import fitting_decomposition
            out=fitting_decomposition(args.matrix)
        elif args.command == 'task-section':
            from .exact_linear import task_section
            out=task_section(args.target,args.carrier,injective=args.injective)
        else:
            from .recurrence import Recurrence
            from .recurrence_identity import compare_recurrences
            out=compare_recurrences(Recurrence(tuple(args.left_coeff),tuple(args.left_initial)),
                                    Recurrence(tuple(args.right_coeff),tuple(args.right_initial)))
        print(json.dumps(out,indent=2,default=str))
        return
    if args.command == 'norm-operator-replay':
        from .norm_operator_replay import field_operator_replay
        out=field_operator_replay(json.loads(args.packet.read_text()),radius=args.radius)
        print(json.dumps(out,indent=2,default=str))
        return
    if args.command == 'centered-divisor':
        from .centered_divisor import solve_centered
        print(json.dumps(solve_centered(args.coeff,args.k,work_limit=args.work_limit),indent=2))
        return
    if args.command == 'square-triangular-query':
        from .square_triangular_queries import query
        if args.power_ten is not None and not 0 <= args.power_ten <= 2000:
            raise ValueError('power-ten exponent must be from zero to 2000')
        filters=[]
        for raw in args.filter:
            coordinate,modulus,residue=raw.split(':')
            filters.append((coordinate,int(modulus),int(residue)))
        bound=args.bound if args.bound is not None else 10**args.power_ten
        print(json.dumps(query(bound,filters,state_limit=args.state_limit),indent=2))
        return
    if args.command == 'showcase':
        from .showcase import build_examples,benchmark_queries
        r=build_examples(args.output)
        summary={'finite_points':len(r['hidden_needle']['complete_points']),
                 'square_triangular_count':r['square_triangular']['query']['unfiltered_count'],
                 'filtered_count':r['square_triangular']['query']['filtered_count'],
                 'queries':len(r['whole_queries'])}
        if args.benchmark:summary['timings']=benchmark_queries(args.output,timeout_ms=args.timeout_ms,repeats=args.repeats)['summary']
        print(json.dumps(summary,indent=2))
        return
    if args.command == 'finite-project':
        from .finite_projection import project_finite_query
        p=project_finite_query(args.source.read_text())
        args.output.write_text(p.smt)
        if args.lean_output:args.lean_output.write_text(p.emission.lean)
        print(json.dumps({'eliminated':p.emission.eliminated_symbols,'remaining':p.emission.remaining_symbols,
                          'finite_choices':len(p.emission.points),'linear':p.linear,'execution_verified':False},indent=2))
        return
    if args.command == 'verify':
        obj = RigidCertificate(**json.loads(args.certificate.read_text()))
        result = verify_certificate(obj)
        print(json.dumps({'valid': result}))
        raise SystemExit(0 if result else 1)
    if args.command == 'oeis':
        from .oeis import atlas, load_names, load_stripped, premise_candidates
        reviewed = json.loads(args.reviewed.read_text()) if args.reviewed else {}
        out = {'retrieved': args.retrieved,
               'atlas': atlas(load_stripped(args.stripped), reviewed, retrieved=args.retrieved)}
        if args.names:
            out['premise_candidates'] = premise_candidates(load_names(args.names))
        print(json.dumps(out, indent=1, default=str))
        return
    if args.command == 'prove':
        from .compiler import PowerConstraint, compile_constraint, match_affine_cube
        from .descent import standalone_file
        from .specialize import parse_poly
        plan = compile_constraint(PowerConstraint(parse_poly(args.expr), 2))
        cert = plan.data.get('descent')
        if cert is None:
            print(f'no descent certificate: {plan.mechanism}', file=sys.stderr)
            raise SystemExit(1)
        r, s, _ = match_affine_cube(plan.reduced.F)
        print(standalone_file(args.name, r, s, cert['D']))
        return
    if args.command == 'solve':
        from .compiler import NotEnumerable
        from .specialize import LoopProgram, specialize
        test = {'power': ('power', args.d), 'triangular': ('triangular', args.domain),
                'root': ('root', args.a, args.b, args.c, args.domain)}[args.form]
        sp = specialize(LoopProgram(args.expr, test))
        if args.program:
            print(sp.source if sp.source is not None else f'# no specialized program: {sp.plan.status}')
            return
        out = sp.plan.explain(galois=True)
        try:
            out['hits'] = [[n, w] for n, w in sp.plan.iter_hits(args.N)]
            out['N'] = args.N
        except NotEnumerable as exc:
            out['hits'] = None
            out['not_enumerated'] = str(exc)
        if sp.plan.status == 'COMPLETE_FINITE':
            out['all_hits'] = [[n, w] for n, w in sp.plan.all_hits()]
        print(json.dumps(out, indent=2, default=str))
        return
    if args.d < 2:
        parser.error('d >= 2 required')
    if args.command == 'lean':
        from .lean_emit import emit
        if args.d == 2:
            from .linear_perturbation import match,match_square_leading,emit_lean,emit_square_leading
            direct,raw = match(args.coeff),match_square_leading(args.coeff)
            if direct is not None:
                print(emit_lean(*direct,name=args.name),end='')
                return
            if raw is not None:
                print(emit_square_leading(*raw,name=args.name),end='')
                return
        if args.method == 'sandwich':
            from .lean_sandwich import emit_sandwich
            try:
                text, _ = emit_sandwich(args.name, args.coeff, args.d)
            except ValueError as exc:
                print(exc, file=sys.stderr)
                raise SystemExit(1)
        else:
            text = emit(args.name, args.coeff, args.d, T_max=6, x0_max=300)
        if text is None:
            print('no Runge plan (needs rigid F with positive leading coefficient)', file=sys.stderr)
            raise SystemExit(1)
        print('import PerfectPower.Certificates\nopen PerfectPower\n\n' + text)
        return
    if args.command == 'shifts':
        from .atlas import shift_spectrum
        print(json.dumps(shift_spectrum(args.coeff, args.d), indent=2))
        return
    f = args.coeff.copy()
    f[0] += args.k
    if any(not isinstance(c, int) for c in f):
        from .atlas import integerize
        f = list(integerize(f, args.d))   # same hit set; see atlas.integerize
        args.coeff = f.copy()
        args.coeff[0] -= args.k
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
        out = {'kind': cl.kind, 'growth': cl.growth, 'N': args.N,
               'count': structural_count(f, args.d, args.N),
               'kappa': cl.details.get('kappa')}
        if cl.details.get('kappa_exact') is not None:
            out['kappa_exact'] = cl.details['kappa_exact']
        print(json.dumps(out, indent=2))
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
