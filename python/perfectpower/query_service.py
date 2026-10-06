"""Versioned JSONL service: one isolated response per request, no code eval."""
import argparse
import json
import sys
from .catalogue import Catalogue, encoded
from .divisor_square import WorkLimit

METHODS = dict(
    projected={'summary','count','select','rank','page','sample','partition','locate','multiplicity','evidence'},
    factorial={'summary','terms','residues'},
    population={'summary', 'count', 'select', 'rank', 'locate', 'page', 'next', 'sample', 'partition', 'optimize', 'evidence'},
    sequence={'summary', 'terms', 'subsequence', 'experiment', 'witness_experiment'}, inverse={'solve', 'solve_box'},
    graph={'event', 'sample'}, geometry={'point', 'segment', 'grid', 'transition', 'transport'},
    combinatorial={'gamma', 'sizes', 'select_size'})


def dispatch(catalogue, request):
    if not isinstance(request, dict) or set(request)-{'request_id', 'op', 'kind', 'specification', 'name', 'replace', 'object', 'method', 'args', 'other', 'predicate'}:
        raise ValueError('unsupported request fields')
    op = request.get('op'); args = request.get('args', {})
    if not isinstance(args, dict):
        raise ValueError('args must be a JSON object')
    if op == 'register':
        return catalogue.register(request['kind'], request['specification'], request.get('name'), replace=request.get('replace', False))
    if op == 'list':
        return catalogue.list(**args)
    if op == 'definition':
        return catalogue.definition(request['object'])
    if op == 'join':
        return catalogue.join(request['object'], request['other'], **args)
    if op == 'symbolic_join':
        from .projected_populations import symbolic_join
        if any(catalogue.definition(r)['kind']!='population' for r in (request['object'],request['other'])):raise ValueError('symbolic join requires population objects')
        derived=symbolic_join(catalogue.get(request['object']),catalogue.get(request['other']),**args)
        return catalogue.register('population',derived.specification,request.get('name'))
    definition = catalogue.definition(request['object'])
    obj = catalogue.get(request['object'])
    if op == 'restrict' and definition['kind'] == 'population':
        derived = obj.restrict(request['predicate'])
        return catalogue.register('population', derived.specification, request.get('name'))
    if op == 'compare' and definition['kind'] == 'sequence':
        if catalogue.definition(request['other'])['kind'] != 'sequence':
            raise ValueError('comparison requires sequences')
        return obj.compare(catalogue.get(request['other']), **args)
    if op == 'reweight' and definition['kind'] == 'graph':
        derived, proof = obj.with_weights(args['weights'])
        specification = dict(definition['specification'], weights=[str(w) for w in derived.measure.weights])
        return dict(object=catalogue.register('graph', specification, request.get('name')), proof=proof)
    if op != 'call' or request.get('method') not in METHODS[definition['kind']]:
        raise ValueError('unsupported operation for object kind')
    return getattr(obj, request['method'])(**args)


def serve(catalogue, source, destination, *, request_byte_limit=1000000):
    """Read bounded lines, drain overlong ones, continue after invalid requests."""
    if type(request_byte_limit) is not int or not 1 <= request_byte_limit <= 1000000:
        raise ValueError('request byte limit 1 through 1000000 required')
    while True:
        line = source.readline(request_byte_limit+1)
        if not line:
            return
        request_id = None
        try:
            overlong = len(line.encode('utf-8')) > request_byte_limit
            if len(line) > request_byte_limit and not line.endswith('\n'):
                while line and not line.endswith('\n'):
                    line = source.readline(request_byte_limit+1)
            if overlong:
                raise WorkLimit('request exceeds byte budget')
            request = json.loads(line)
            if isinstance(request, dict):
                request_id = request.get('request_id')
            answer = dispatch(catalogue, request)
            result = dict(schema='pp-query-response/1', request_id=request_id, ok=True, result=answer)
        except (ValueError, TypeError, KeyError, IndexError, ArithmeticError, WorkLimit, RecursionError) as error:
            result = dict(schema='pp-query-response/1', request_id=request_id, ok=False,
                          error=dict(type=type(error).__name__, message=str(error)))
        destination.write(encoded(result)+'\n'); destination.flush()


def add_commands(sub):
    p = sub.add_parser('service', help='persistent exact object catalogue over JSONL stdin/stdout')
    p.add_argument('--database', required=True)
    p.add_argument('--http-port',type=int,help='serve the local HTTP console on this port (0 selects a free port)')


def cli(args):
    if args.command != 'service':
        return False
    if args.http_port is not None:
        if not 0<=args.http_port<=65535:raise ValueError('HTTP port 0 through 65535 required')
        from .http_service import run
        run(args.database,args.http_port)
        return True
    with Catalogue(args.database) as catalogue:
        serve(catalogue, sys.stdin, sys.stdout)
    return True


if __name__ == '__main__':
    parser = argparse.ArgumentParser(); parser.add_argument('--database', required=True)
    with Catalogue(parser.parse_args().database) as catalogue:
        serve(catalogue, sys.stdin, sys.stdout)
