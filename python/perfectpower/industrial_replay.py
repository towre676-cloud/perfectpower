"""Bounded native-command batching, with exact incremental query barriers.

This changes transport granularity, not the logic, assertions, or solver strategy.
Observer commands are omitted just as in the existing industrial benchmark.
"""
import time
import z3
from .smt_cert import split_commands, head

OBSERVERS = frozenset(('get-model', 'get-value', 'get-info', 'get-proof', 'get-unsat-core', 'exit'))
QUERIES = frozenset(('check-sat', 'check-sat-assuming'))


def solve_replay(script, query_ms=250, batch_chars=262144, fast_split=False):
    """Use batch_chars=0 for the per-command control, or a positive batch bound.

    A single source command may exceed the bound and is sent alone. Failed
    batches stop the stream. No later query is reported after a native error.
    """
    if query_ms < 2 or batch_chars < 0:
        raise ValueError('Invalid query budget or batch bound')
    started = time.perf_counter()
    if fast_split:
        from .smt_stream import split_commands_fast
        commands = split_commands_fast(script)
    else:
        commands = split_commands(script)
    parsed = time.perf_counter()
    context = z3.Context()
    rows, errors, pending = [], [], []
    pending_chars = 0
    calls = ingestion_calls = peak_batch_chars = 0
    ingestion_seconds = 0.0

    def evaluate(command, ingestion=False):
        nonlocal calls, ingestion_calls, ingestion_seconds, peak_batch_chars
        t = time.perf_counter()
        calls += 1
        if ingestion:
            ingestion_calls += 1
            peak_batch_chars = max(peak_batch_chars, len(command))
        try:
            result = z3.z3core.Z3_eval_smtlib2_string(context.ref(), command)
        finally:
            if ingestion:
                ingestion_seconds += time.perf_counter() - t
        if isinstance(result, bytes):
            result = result.decode()
        if '(error' in result:
            raise ValueError(result)
        return result.strip()

    def flush():
        nonlocal pending_chars
        if pending:
            evaluate('\n'.join(pending), ingestion=True)
            pending.clear()
            pending_chars = 0

    try:
        for command in commands:
            op = head(command)
            if op in OBSERVERS:
                continue
            if op not in QUERIES:
                if batch_chars == 0:
                    evaluate(command, ingestion=True)
                else:
                    added = len(command) + bool(pending)
                    if pending and pending_chars + added > batch_chars:
                        flush()
                        added = len(command)
                    pending.append(command)
                    pending_chars += added
                    if pending_chars >= batch_chars:
                        flush()
                continue
            flush()
            t = time.perf_counter()
            evaluate(f'(set-option :timeout {query_ms})')
            answer = evaluate(command)
            evaluate('(set-option :timeout 0)')
            if answer not in ('sat', 'unsat', 'unknown'):
                raise ValueError(f'Unexpected query output: {answer!r}')
            rows.append(dict(answer=answer, seconds=time.perf_counter()-t))
        flush()
    except (ValueError, z3.Z3Exception) as e:
        errors.append(str(e))
    return dict(queries=rows, errors=errors, wall_seconds=time.perf_counter()-started,
                parse_seconds=parsed-started, ingestion_seconds=ingestion_seconds,
                query_seconds=sum(q['seconds'] for q in rows), native_calls=calls,
                ingestion_calls=ingestion_calls, peak_batch_chars=peak_batch_chars,
                batch_chars=batch_chars, fast_split=fast_split, source_commands=len(commands))
