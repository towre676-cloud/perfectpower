"""Exact Euclidean arithmetic, contact geometry and exhaustion JSON commands."""
import json
from .euclid_descent import compile_descent
from .euclid_geometry import voronoi_cells,segment_intersection,string_disk_contacts,string_geometry
from .euclid_exact import euclidean_gcd,QuadraticSurd,sqrt_continued_fraction,pell_from_cf,sqrt_exhaustion,isolate_root
from .linear_product import solve as solve_linear_product, query as query_linear_product, close_descent

OPERATIONS=('descent','solve-descent','solve-linear-product','query-linear-product','voronoi','segments','contacts','string','gcd','surd','continued-fraction','pell','sqrt-bounds','root-bounds')


def dispatch(operation,spec):
    if operation=='solve-descent':
        limit=spec.get('work_limit',1000000)
        descent=compile_descent(spec['left'],spec['right'],spec.get('degree',2),work_limit=limit,branch_limit=spec.get('branch_limit',10000))
        return close_descent(descent,work_limit=limit)
    if operation in ('solve-linear-product','query-linear-product'):
        packet=solve_linear_product(spec['left'],spec['right'],work_limit=spec.get('work_limit',1000000))
        return packet if operation=='solve-linear-product' else query_linear_product(packet,spec)
    if operation=='descent':return compile_descent(spec['left'],spec['right'],spec.get('degree',2),work_limit=spec.get('work_limit',100000),branch_limit=spec.get('branch_limit',10000))
    if operation=='voronoi':return voronoi_cells(spec['sites'],spec['box'])
    if operation=='segments':return segment_intersection(*spec['segments'][0],*spec['segments'][1])
    if operation=='contacts':return string_disk_contacts(spec['path'],spec['objects'])
    if operation=='string':return string_geometry(spec['path'],spec['objects'])
    if operation=='gcd':return euclidean_gcd(spec['a'],spec['b'])
    if operation=='surd':return QuadraticSurd(spec['D'],spec.get('a',0),spec.get('b',1)).receipt()
    if operation=='continued-fraction':return sqrt_continued_fraction(spec['D'])
    if operation=='pell':return pell_from_cf(spec['D'])
    if operation=='sqrt-bounds':return sqrt_exhaustion(spec['radicand'],spec['epsilon'])
    if operation=='root-bounds':return isolate_root(spec['coefficients'],spec['lower'],spec['upper'],spec['epsilon'])
    raise ValueError('unknown Euclidean operation')


def add_commands(sub):
    p=sub.add_parser('euclid',help='resultant power descent and exact Euclidean geometry')
    p.add_argument('operation',choices=OPERATIONS);p.add_argument('input',help='JSON specification file')


def cli(args):
    if args.command!='euclid':return False
    with open(args.input) as f:result=dispatch(args.operation,json.load(f))
    print(json.dumps(result,sort_keys=True,indent=2));return True
