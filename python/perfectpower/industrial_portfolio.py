"""Experimental incremental portfolio with a fixed total per-query budget."""
import time
import z3
from .industrial_router import route_lia
from .smt_cert import split_commands, head


def solve_stream(script, query_ms=250, portfolio=False):
    if query_ms < 2:
        raise ValueError('query_ms must be at least 2')
    started = time.perf_counter()
    routed, eligible = route_lia(script) if portfolio else (script, False)
    contexts = [z3.Context() for _ in range(2 if eligible else 1)]
    streams = [split_commands(script)]
    if eligible:
        streams.append(split_commands(routed))
    if len({len(s) for s in streams}) != 1:
        raise ValueError('Routing changed command count')
    rows, errors = [], []

    def evaluate(context, command):
        result = z3.z3core.Z3_eval_smtlib2_string(context.ref(), command)
        if isinstance(result, bytes):
            result = result.decode()
        if '(error' in result:
            raise ValueError(result)
        return result.strip()

    try:
        for commands in zip(*streams):
            op = head(commands[0])
            if op in ('get-model', 'get-value', 'get-info', 'get-proof', 'get-unsat-core', 'exit'):
                continue
            if op not in ('check-sat', 'check-sat-assuming'):
                for context, command in zip(contexts, commands):
                    evaluate(context, command)
                continue
            t = time.perf_counter()
            budget = query_ms // 2 if eligible else query_ms
            evaluate(contexts[0], f'(set-option :timeout {budget})')
            answer = evaluate(contexts[0], commands[0])
            evaluate(contexts[0], '(set-option :timeout 0)')
            path = 'original'
            if answer == 'unknown' and eligible:
                evaluate(contexts[1], f'(set-option :timeout {query_ms - budget})')
                answer = evaluate(contexts[1], commands[1])
                evaluate(contexts[1], '(set-option :timeout 0)')
                path = 'fallback'
            if answer not in ('sat', 'unsat', 'unknown'):
                raise ValueError(f'Unexpected query output: {answer!r}')
            rows.append(dict(answer=answer, seconds=time.perf_counter()-t, path=path))
    except (ValueError, z3.Z3Exception) as e:
        errors.append(str(e))
    return dict(queries=rows, errors=errors, wall_seconds=time.perf_counter()-started,
                eligible=eligible, fallback_queries=sum(r['path']=='fallback' for r in rows))
