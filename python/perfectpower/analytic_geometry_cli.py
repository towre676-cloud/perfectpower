"""Public entry points for intrinsic cells, conformal metrics and periods."""
import json
from fractions import Fraction


def add_commands(sub):
    p=sub.add_parser('voronoi-witness',help='explicit rational Voronoi witnesses from a supplied closed mesh')
    p.add_argument('--mesh',required=True);p.add_argument('--fields',required=True)
    p.add_argument('--sites',required=True,type=json.loads);p.add_argument('--depth',type=int,default=2)
    p.add_argument('--verify',action='store_true')
    p=sub.add_parser('voronoi-check',help='producer-independent replay of a Voronoi witness packet')
    p.add_argument('--mesh',required=True);p.add_argument('--certificate',required=True)
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
    p=sub.add_parser('certified-voronoi',help='exact rational polyhedral Voronoi boundary enclosure')
    p.add_argument('--coeff',required=True);p.add_argument('--resolution',type=int,default=6)
    p.add_argument('--sites',type=int,default=4);p.add_argument('--depth',type=int,default=2)
    p=sub.add_parser('symplectic-periods',help='actual continued-sheet integrals over mesh symplectic cycles')
    p.add_argument('--coeff',required=True);p.add_argument('--resolution',type=int,default=6)
    p.add_argument('--tolerance',type=float,default=1e-10)
    p=sub.add_parser('integrate-path',help='continued-sheet finite path on a cyclic component')
    p.add_argument('--coeff',required=True);p.add_argument('--d',required=True,type=int)
    p.add_argument('--points',required=True,type=json.loads);p.add_argument('--charts',type=json.loads)
    p.add_argument('--sheet',type=int,default=0);p.add_argument('--tolerance',type=float,default=1e-10)
    p=sub.add_parser('surface-homology',help='integral symplectic basis on a curve-derived surface mesh')
    p.add_argument('--coeff',required=True);p.add_argument('--resolution',type=int,default=6)
    p=sub.add_parser('conformal-voronoi',help='curve-derived hyperelliptic mesh and intrinsic heat Voronoi approximation')
    p.add_argument('--coeff',required=True);p.add_argument('--resolution',type=int,default=6)
    p.add_argument('--sites',type=int,default=8)


def dispatch(args):
    if args.command in ('voronoi-witness','voronoi-check'):
        from pathlib import Path
        from .voronoi_certificate import produce,verify
        mesh=json.loads(Path(args.mesh).read_text())
        if args.command=='voronoi-check':
            certificate=json.loads(Path(args.certificate).read_text())
            ok=verify(mesh,certificate)
            print(json.dumps({'verified':ok,'kernel_checked':False,'smooth_curve_metric_certified':False}))
            if not ok: raise SystemExit(1)
        else:
            fields=json.loads(Path(args.fields).read_text())
            certificate=produce(mesh,args.sites,fields,args.depth)
            if args.verify and not verify(mesh,certificate): raise ValueError('witness verification failed')
            print(json.dumps(certificate,indent=2))
        return True
    if args.command not in ('intrinsic-voronoi','analytic-periods','conformal-metric','conformal-voronoi','certified-voronoi','surface-homology','symplectic-periods','integrate-path'):return False
    if args.command=='intrinsic-voronoi':
        from .intrinsic_torus import legendre_torus,legendre_point
        p=legendre_torus(args.lam,args.sites,args.terms)
        p['curve_sites']=[legendre_point(Fraction(args.lam),complex(*s),p['height']) for s in p['sites']]
    else:
        coeff=[int(a) for a in args.coeff.split(',')]
        if args.command=='integrate-path':
            from .surface_periods import integrate_path
            p=integrate_path(coeff,args.d,args.points,args.charts,args.sheet,args.tolerance)
        elif args.command in ('conformal-voronoi','certified-voronoi','surface-homology','symplectic-periods'):
            from .conformal_mesh import hyperelliptic_mesh,heat_voronoi
            mesh=hyperelliptic_mesh(coeff,args.resolution)
            if args.command=='symplectic-periods':
                from .surface_periods import symplectic_period_matrix
                p=symplectic_period_matrix(mesh,args.tolerance)
            elif args.command=='surface-homology':
                from .symplectic_surface import surface_basis
                p=surface_basis(mesh)
            else:
                heat=heat_voronoi(mesh,args.sites)
                if args.command=='certified-voronoi':
                    from .certified_voronoi import boundary_enclosure
                    p=boundary_enclosure(mesh,heat['sites'],heat['distance_fields'],args.depth)
                else:p={'mesh':mesh,'voronoi':heat}
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
