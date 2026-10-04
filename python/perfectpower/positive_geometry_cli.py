"""Console registration for degeneration and positive-geometry computations."""
import json


def add_commands(sub):
    from .__main__ import coefficients
    p = sub.add_parser('collision-atlas', help='exact normalized topology of labelled root collisions')
    p.add_argument('--multiplicities', required=True, type=json.loads)
    p.add_argument('--d', required=True, type=int)
    p = sub.add_parser('associahedron', help='face poset of a fixed-order real branch chamber')
    p.add_argument('--marks', required=True, type=int)
    p = sub.add_parser('legendre', help='exact degeneration and Picard-Fuchs packet')
    p.add_argument('--parameter', required=True)
    p.add_argument('--series-terms', type=int, default=16)
    p = sub.add_parser('connection-polytope', help='exact cyclic graph determinant and full-rank witness bases')
    p.add_argument('--vertices', type=int, required=True)
    p.add_argument('--edges', type=json.loads, required=True, help='JSON [[source,target,voltage],...]')
    p.add_argument('--d', type=int, required=True)
    p.add_argument('--weights', type=json.loads)
    p.add_argument('--costs', type=json.loads, help='minimum-cost basis route, without subset enumeration')
    p.add_argument('--subset-limit', type=int, default=100_000)
    p = sub.add_parser('descartes-orbit', help='integral circle reflections and bounded polynomial power hits')
    p.add_argument('--seed', type=json.loads, default=[-1, 2, 2, 3])
    p.add_argument('--fixed', type=json.loads, default=[0, 1])
    p.add_argument('--stop', type=int, default=1000)
    p.add_argument('--powers', type=json.loads, default=[2, 3, 4])
    p = sub.add_parser('period-normalize', help='resolve supplied finite holomorphic ambiguity by period conditions')
    p.add_argument('--matrix', type=json.loads, required=True)
    p.add_argument('--periods', type=json.loads, required=True)
    p.add_argument('--target', type=json.loads)
    p = sub.add_parser('branch-signs', help='Descartes real-root bound on a rational open interval')
    p.add_argument('--coeff', type=coefficients, required=True)
    p.add_argument('--left', required=True)
    p.add_argument('--right', required=True)
    p = sub.add_parser('branch-form', help='canonical ordered-branch form or explicit pentagon collision chart')
    mode = p.add_mutually_exclusive_group(required=True)
    mode.add_argument('--coordinates', type=json.loads)
    mode.add_argument('--collision-chart', type=json.loads, help='JSON [u,t] for x=t*u,y=t')


def dispatch(args):
    if args.command == 'branch-form':
        from .degeneration_atlas import ordered_branch_form, pentagon_collision_chart
        result = ordered_branch_form(args.coordinates) if args.coordinates is not None else pentagon_collision_chart(*args.collision_chart)
        print(json.dumps(result, indent=2))
        return True
    if args.command in ('collision-atlas', 'associahedron', 'legendre', 'branch-signs'):
        from .degeneration_atlas import collision_atlas, associahedron, legendre, descartes_variations
        if args.command == 'collision-atlas':
            result = collision_atlas(args.multiplicities, args.d)
        elif args.command == 'associahedron':
            result = associahedron(args.marks)
        elif args.command == 'legendre':
            result = legendre(args.parameter, args.series_terms)
        else:
            result = descartes_variations(args.coeff, args.left, args.right)
        print(json.dumps(result, indent=2))
        return True
    if args.command == 'connection-polytope':
        from .connection_polytope import ConnectionGraph
        graph = ConnectionGraph(args.vertices, tuple(map(tuple, args.edges)), args.d)
        result = graph.minimum_cost_basis(args.costs) if args.costs is not None else graph.packet(args.weights, args.subset_limit)
        print(json.dumps(result, indent=2))
        return True
    if args.command == 'descartes-orbit':
        from .descartes_orbits import orbit_packet
        print(json.dumps(orbit_packet(args.seed, args.fixed, args.stop, args.powers), indent=2))
        return True
    if args.command == 'period-normalize':
        from .period_boundary import normalize_periods
        print(json.dumps(normalize_periods(args.matrix, args.periods, args.target), indent=2))
        return True
    return False
