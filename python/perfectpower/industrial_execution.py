"""Explicit industrial execution policy; experimental portfolios are opt-in."""


def execute(script, *, mode='transport', query_ms=250, experimental=False):
    """Original-assertion, answer-only replay; no universal speedup claim."""
    if not isinstance(script,str):raise TypeError('SMT-LIB source must be text')
    if mode not in {'baseline','transport','portfolio'}:raise ValueError('unknown execution mode')
    if type(query_ms) is not int or not 2<=query_ms<=600000:
        raise ValueError('query_ms must be an integer between 2 and 600000')
    if type(experimental) is not bool:raise ValueError('experimental must be Boolean')
    if mode=='portfolio':
        if not experimental:raise ValueError('portfolio requires explicit experimental=True')
        from .industrial_portfolio import solve_stream
        result=solve_stream(script,query_ms=query_ms,portfolio=True)
    else:
        from .industrial_replay import solve_replay
        result=solve_replay(script,query_ms=query_ms,
            batch_chars=262144 if mode=='transport' else 0,fast_split=mode=='transport')
    result.update(mode=mode,arithmetic_speedup_claimed=False,
                  evidence_scope='answer-only replay; workload-specific timings',
                  experimental=mode=='portfolio')
    return result
