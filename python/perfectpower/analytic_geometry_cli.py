"""Public entry points for intrinsic cells, conformal metrics and periods."""
import json
from fractions import Fraction


def add_commands(sub):
    p=sub.add_parser('intrinsic-voronoi',help='Legendre conformal torus and continuous intrinsic cells')
    p.add_argument('--lambda',dest='lam',required=True);p.add_argument('--terms',type=int,default=256)
    p.add_argument('--sites',type=json.loads,help='JSON sites in actual normalized torus coordinates')
    p=sub.add_parser('analytic-periods',help='continued-sheet closed periods on a cyclic component')
    p.add_argument('--coeff',required=True);p.add_argument('--d',required=True,type=int)
    p.add_argument('--word',type=json.loads,help='signed one-based root-loop word')
    p.add_argument('--center',type=json.loads,help='[real,imag] of circular contour center')
    p.add_argument('--radius',type=float);p.add_argument('--tolerance',type=float,default=1e-10)
    p=sub.add_parser('conformal-metric',help='smooth differential metric and curvature in original curve charts')
    p.add_argument('--coeff',required=True);p.add_argument('--d',required=True,type=int)
    p.add_argument('--point',type=json.loads,default=[.3,.7])
    p=sub.add_parser('conformal-voronoi',help='curve-derived hyperelliptic mesh and intrinsic heat Voronoi approximation')
    p.add_argument('--coeff',required=True);p.add_argument('--resolution',type=int,default=6)
    p.add_argument('--sites',type=int,default=8)


def dispatch(args):
    if args.command not in ('intrinsic-voronoi','analytic-periods','conformal-metric','conformal-voronoi'):return False
    if args.command=='intrinsic-voronoi':
        from .intrinsic_torus import legendre_torus,legendre_point
        p=legendre_torus(args.lam,args.sites,args.terms)
        p['curve_sites']=[legendre_point(Fraction(args.lam),complex(*s),p['height']) for s in p['sites']]
    else:
        coeff=[int(a) for a in args.coeff.split(',')]
        if args.command=='conformal-voronoi':
            from .conformal_mesh import hyperelliptic_mesh,heat_voronoi
            mesh=hyperelliptic_mesh(coeff,args.resolution);p={'mesh':mesh,'voronoi':heat_voronoi(mesh,args.sites)}
        else:
            from .analytic_surface import AnalyticSurface
            s=AnalyticSurface(coeff,args.d)
            if args.command=='conformal-metric':
                p={'finite_chart':s.metric(complex(*args.point)),
                   'branch_charts':[s.branch_metric(i) for i in range(len(s.roots))],
                   'infinity_chart':s.infinity_metric()}
            elif args.word is not None:p=s.word_period(args.word,args.tolerance)
            elif args.center is not None and args.radius is not None:
                p=s.circle_period(complex(*args.center),args.radius,tolerance=args.tolerance)
            else:p={'circle_periods':s.pair_periods(args.tolerance)}
    print(json.dumps(p,indent=2));return True
