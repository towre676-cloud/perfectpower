"""Public standard-library console for exact PSG structural algebra."""
import json
from pathlib import Path
from .psg_polynomial import parse
from .psg_algebra import (quadratic_reduce,reconstruct_quadratic,darboux_certificate,
                         check_darboux,dependency_profile,observable_fibre,
                         ideal_certificate,affine_norm_population)


def add_commands(sub):
    p=sub.add_parser('psg-model-space',help='exact finite differential-model coefficient space')
    p.add_argument('--coefficients',required=True,type=json.loads)
    p.add_argument('--order',required=True,type=int);p.add_argument('--degree',required=True,type=int)
    p.add_argument('--derivatives',type=int,default=1);p.add_argument('--out',type=Path)
    for name in ('psg-reduce','psg-darboux','psg-dependencies','psg-ideal','psg-norm'):
        p=sub.add_parser(name,help='exact PSG structural algebra')
        p.add_argument('--variables',required=True,help='ordered comma-separated variable names')
        if name=='psg-reduce':
            p.add_argument('--source',required=True);p.add_argument('--variable',required=True)
            p.add_argument('--radicand',required=True);p.add_argument('--base-values',type=json.loads)
            p.add_argument('--domain',choices=('integer','rational'),default='integer')
        elif name=='psg-darboux':
            p.add_argument('--candidate',required=True);p.add_argument('--field',required=True,type=json.loads)
        elif name=='psg-dependencies':p.add_argument('--outputs',required=True,type=json.loads)
        elif name=='psg-ideal':
            p.add_argument('--target',required=True);p.add_argument('--generators',required=True,type=json.loads)
        else:
            p.add_argument('--A',required=True);p.add_argument('--B',required=True)
            p.add_argument('--D',type=int,required=True);p.add_argument('--norm',type=int,required=True)
            p.add_argument('--cutoff',type=int,required=True)
        p.add_argument('--out',type=Path)
    p=sub.add_parser('psg-fibre',help='complete rational observation fibre and target ambiguity')
    p.add_argument('--observation',required=True,type=json.loads);p.add_argument('--values',required=True,type=json.loads)
    p.add_argument('--target',required=True,type=json.loads);p.add_argument('--out',type=Path)


def cli(args):
    if not args.command.startswith('psg-'): return False
    if args.command=='psg-model-space':
        from .psg_jets import differential_model_space
        result=differential_model_space(args.coefficients,args.order,args.degree,args.derivatives)
    elif args.command=='psg-fibre':result=observable_fibre(args.observation,args.values,args.target)
    else:
        variables=tuple(v.strip() for v in args.variables.split(','))
        def read(s):return parse(s,variables)
        if args.command=='psg-reduce':
            source,D=read(args.source),read(args.radicand)
            result=quadratic_reduce(source,args.variable,D)
            if args.base_values is not None:
                result={'certificate':result,'fibre':reconstruct_quadratic(result,source,args.variable,D,args.base_values,domain=args.domain)}
        elif args.command=='psg-darboux':
            h=read(args.candidate);field=list(map(read,args.field));result=darboux_certificate(h,field)
            check_darboux(result,h,field)
        elif args.command=='psg-dependencies':result=dependency_profile(list(map(read,args.outputs)))
        elif args.command=='psg-ideal':result=ideal_certificate(read(args.target),list(map(read,args.generators)))
        elif args.command=='psg-norm':result=affine_norm_population(read(args.A),read(args.B),args.D,args.norm,args.cutoff)
        else:raise ValueError('unknown PSG command')
    encoded=json.dumps(result,indent=2)+'\n'
    if args.out:args.out.write_text(encoded)
    else:print(encoded,end='')
    return True
