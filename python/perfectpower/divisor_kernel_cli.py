"""Console routes for the recovered arithmetic kernels."""
import json
from fractions import Fraction


def add_commands(sub):
    p=sub.add_parser('divisor-kernel', help='exact GCD kernel action, Gram energy or complete raw linear fibre')
    p.add_argument('--weights', type=json.loads, help='JSON weights w[1..N], exact integers/fraction strings')
    p.add_argument('--family', choices=('power','sigma'), default='power')
    p.add_argument('--N', type=int, default=8)
    p.add_argument('--degree', type=int, default=1)
    p.add_argument('--normalized', action='store_true', help='divide by max(i,j)')
    p.add_argument('--vector', type=json.loads)
    p.add_argument('--rhs', type=json.loads)
    p.add_argument('--domain', choices=('integer','rational'), default='rational')
    p.add_argument('--work-limit', type=int, default=30_000_000)


def _exact(values):
    if not isinstance(values,list) or any(type(v) not in (int,str) for v in values):
        raise ValueError('JSON integer/fraction-string list required')
    return [Fraction(v) for v in values]


def json_exact(value):
    if isinstance(value,Fraction):return int(value) if value.denominator==1 else str(value)
    if isinstance(value,dict):return {str(k):json_exact(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):return list(map(json_exact,value))
    return value


def dispatch(args):
    if args.command!='divisor-kernel':return False
    from .divisor_kernel import DivisorKernel,power_kernel,sigma_kernel
    opts={'normalized':args.normalized,'work_limit':args.work_limit}
    if args.weights is not None:kernel=DivisorKernel.from_weights(_exact(args.weights),**opts)
    elif args.family=='sigma':kernel=sigma_kernel(args.N,**opts)
    else:kernel=power_kernel(args.N,args.degree,**opts)
    result={'certificate':kernel.certificate()}
    if kernel.n<=256:result['mobius_coefficients']=kernel.g
    if args.vector is not None:
        vector=_exact(args.vector)
        result.update(action=kernel.apply(vector),energy=kernel.energy(vector))
    if args.rhs is not None:result['solution']=kernel.solve(_exact(args.rhs),domain=args.domain)
    print(json.dumps(json_exact(result),indent=2));return True
