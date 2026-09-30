from __future__ import annotations

def pareto_front(rows, objectives):
    """objectives maps key -> +1 maximize or -1 minimize."""
    out=[]
    for i,a in enumerate(rows):
        dominated=False
        for j,b in enumerate(rows):
            if i==j: continue
            weak=all(objectives[k]*b[k] >= objectives[k]*a[k] for k in objectives)
            strict=any(objectives[k]*b[k] > objectives[k]*a[k] for k in objectives)
            if weak and strict: dominated=True; break
        if not dominated: out.append(a)
    return out
