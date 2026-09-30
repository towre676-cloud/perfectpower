Q192_ROUTE_DEGREES={49:30,12:60,125:60,48:60,116:60,59:60,95:60}
N=7392

def schedule_cost(routes):
    routes=tuple(routes); d=sum(Q192_ROUTE_DEGREES[r] for r in routes)
    return {'route_passes':len(routes),'degree':d,'directed_edge_visits':N*d}

def fano_line_costs(lines, route_order=(49,12,125,48,116,59,95)):
    return [schedule_cost([route_order[i] for i in line]) for line in lines]
