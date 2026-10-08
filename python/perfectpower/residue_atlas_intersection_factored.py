"""Complete intersections of prime-power atlases and factored atlas products.

Different source polynomials are allowed. Shared primes are joined by projection
at their largest exponent; distinct prime groups retain a full factored CRT
product. Every modular candidate and every exact source equation is retained.
"""
from math import prod
import json
from .residue_atlas import verify_atlas, _parameter, _canonical_equal, _bounds
from .residue_atlas_product import verify_product, _all_roots, _blocks
from .bounded_residue_patch import evaluate
from .residue_determinant import integer


def _flatten(atlases):
    if not isinstance(atlases, list) or not 1 <= len(atlases) <= 8:
        raise ValueError('one through eight complete atlases or products required')
    flattened = []
    for packet in atlases:
        if not isinstance(packet, dict):
            raise ValueError('complete atlas evidence required')
        if packet.get('schema') == 'pp-residue-atlas/1' and verify_atlas(packet):
            flattened.append(packet)
        elif packet.get('schema') == 'pp-residue-atlas-product/1' and verify_product(packet):
            flattened.extend(packet['locals'])
        else:
            raise ValueError('invalid atlas evidence')
    if len(flattened) > 64:
        raise ValueError('at most 64 local constraints required')
    unique = {json.dumps(a, sort_keys=True, separators=(',', ':')): a for a in flattened}
    return json.loads(json.dumps([unique[k] for k in sorted(unique)]))


def _groups(constraints):
    groups = []
    for p in sorted({a['prime'] for a in constraints}):
        ids = [i for i, a in enumerate(constraints) if a['prime'] == p]
        m = max(constraints[i]['modulus'] for i in ids)
        seed = min((i for i in ids if constraints[i]['modulus'] == m),
                   key=lambda i: (len(constraints[i]['roots']), i))
        allowed = [(constraints[i]['modulus'], {tuple(z) for z in constraints[i]['roots']}) for i in ids]
        roots = [z for z in constraints[seed]['roots']
                 if all((z[0] % n, z[1] % n) in table for n, table in allowed)]
        groups.append({'prime': p, 'modulus': m, 'constraint_ids': ids, 'roots': roots})
    return groups


def intersect_atlases(atlases, *, explicit_limit=4096):
    limit = _parameter(explicit_limit, 'explicit_limit', 100000)
    constraints = _flatten(atlases)
    local = _groups(constraints)
    count = prod(len(a['roots']) for a in local)
    period = prod(a['modulus'] for a in local)
    roots = _all_roots(local) if count <= limit else None
    return {'schema': 'pp-residue-atlas-intersection-factored/1', 'constraints': constraints,
            'locals': local, 'modulus': period, 'combination_count': count,
            'roots': roots, 'representation': 'explicit' if roots is not None else 'factored',
            'explicit_limit': limit, 'complete_modular_cover': True,
            'global_obstruction': count == 0, 'execution_verified': False,
            'global_height_bound': False}


def verify_intersection(packet):
    """Replay input evidence and independently census each maximal local square."""
    try:
        fields = {'schema','constraints','locals','modulus','combination_count','roots',
                  'representation','explicit_limit','complete_modular_cover','global_obstruction',
                  'execution_verified','global_height_bound'}
        if not isinstance(packet, dict) or set(packet) != fields:
            return False
        if packet['schema'] != 'pp-residue-atlas-intersection-factored/1':
            return False
        constraints = packet['constraints']
        if not isinstance(constraints, list) or not 1 <= len(constraints) <= 64:
            return False
        if any(not verify_atlas(a) for a in constraints):
            return False
        canonical = sorted({json.dumps(a, sort_keys=True, separators=(',', ':')) for a in constraints})
        if not _canonical_equal(constraints, [json.loads(a) for a in canonical]):
            return False
        local = []
        for p in sorted({a['prime'] for a in constraints}):
            ids = [i for i, a in enumerate(constraints) if a['prime'] == p]
            m = max(constraints[i]['modulus'] for i in ids)
            roots = [[x, y] for x in range(m) for y in range(m)
                     if all(evaluate(constraints[i]['terms'], x, y) % constraints[i]['modulus'] == 0 for i in ids)]
            local.append({'prime': p, 'modulus': m, 'constraint_ids': ids, 'roots': roots})
        if not _canonical_equal(packet['locals'], local):
            return False
        limit = _parameter(packet['explicit_limit'], 'explicit_limit', 100000)
        count = prod(len(a['roots']) for a in local)
        period = prod(a['modulus'] for a in local)
        roots = _all_roots(local) if count <= limit else None
        return (integer(packet['modulus']) == period and integer(packet['combination_count']) == count
                and _canonical_equal(packet['roots'], roots)
                and packet['representation'] == ('explicit' if roots is not None else 'factored')
                and packet['complete_modular_cover'] is True
                and packet['global_obstruction'] is (count == 0)
                and packet['execution_verified'] is False and packet['global_height_bound'] is False)
    except (KeyError, TypeError, ValueError, IndexError, OverflowError):
        return False


def intersection_contains(packet, point):
    if not verify_intersection(packet):
        raise ValueError('complete atlas intersection required')
    if not isinstance(point, list) or len(point) != 2:
        raise ValueError('two integer coordinates required')
    x, y = [integer(v, 256) for v in point]
    return all(evaluate(a['terms'], x, y) % a['modulus'] == 0 for a in packet['constraints'])


def _prepare(packet, bounds, work_limit):
    if not verify_intersection(packet):
        raise ValueError('complete atlas intersection required')
    return _bounds(bounds), _parameter(work_limit, 'work_limit', 2000000)


def intersection_population(packet, bounds, *, work_limit=200000):
    bounds, budget = _prepare(packet, bounds, work_limit)
    count = sum(nx*ny for _, _, nx, ny in _blocks(packet, bounds, budget))
    return {'bounds': bounds, 'modulus': packet['modulus'], 'count': count,
            'combination_count': packet['combination_count'], 'representation': packet['representation'],
            'order': 'sorted prime-group root tuples; within each CRT cell x then y ascending',
            'scope': 'complete simultaneous modular candidates; each source equality still required',
            'execution_verified': False}


def intersection_select(packet, bounds, index, *, work_limit=200000):
    bounds, budget = _prepare(packet, bounds, work_limit)
    index = integer(index, 1024)
    if index < 0:
        raise IndexError('negative candidate rank')
    m = packet['modulus']
    for a, b, nx, ny in _blocks(packet, bounds, budget):
        if index < nx*ny:
            u, v = divmod(index, ny)
            return [bounds[0][0]+(a-bounds[0][0]) % m+u*m,
                    bounds[1][0]+(b-bounds[1][0]) % m+v*m]
        index -= nx*ny
    raise IndexError('candidate rank outside population')


def intersection_rank(packet, bounds, point, *, work_limit=200000):
    bounds, budget = _prepare(packet, bounds, work_limit)
    if not isinstance(point, list) or len(point) != 2:
        raise ValueError('two integer coordinates required')
    x, y = [integer(v, 256) for v in point]
    if not bounds[0][0] <= x <= bounds[0][1] or not bounds[1][0] <= y <= bounds[1][1]:
        raise ValueError('point outside rectangle')
    m = packet['modulus']; offset = 0
    for a, b, nx, ny in _blocks(packet, bounds, budget):
        if x % m == a and y % m == b:
            xf = bounds[0][0]+(a-bounds[0][0]) % m
            yf = bounds[1][0]+(b-bounds[1][0]) % m
            return offset+((x-xf)//m)*ny+(y-yf)//m
        offset += nx*ny
    raise ValueError('point fails simultaneous modular conditions')


def intersection_scan(packet, bounds, *, candidate_limit=4096, work_limit=200000):
    bounds, budget = _prepare(packet, bounds, work_limit)
    limit = _parameter(candidate_limit, 'candidate_limit', 100000)
    count = sum(nx*ny for _, _, nx, ny in _blocks(packet, bounds, budget))
    if count > limit:
        raise ValueError('complete candidate population exceeds scan budget; no partial solution list')
    sources = {json.dumps(a['terms'], separators=(',', ':')) for a in packet['constraints']}
    terms = [json.loads(s) for s in sorted(sources)]
    m = packet['modulus']; points = []
    for a, b, nx, ny in _blocks(packet, bounds, budget):
        xf = bounds[0][0]+(a-bounds[0][0]) % m
        yf = bounds[1][0]+(b-bounds[1][0]) % m
        for i in range(nx):
            for j in range(ny):
                z = [xf+i*m, yf+j*m]
                if all(evaluate(t, *z) == 0 for t in terms):
                    points.append(z)
    return {'points': sorted(points), 'bounds': bounds, 'candidates_checked': count,
            'source_count': len(terms), 'complete_in_box': True,
            'global_height_bound': False, 'execution_verified': False}


def native_intersection(packet, bounds):
    """Emit source-bound nested/divisor and coprime CoverPackets for Lean replay."""
    import hashlib
    import re
    from .residue_atlas import native_atlas
    from .bounded_residue_patch import _finset
    if not verify_intersection(packet):
        raise ValueError('complete atlas intersection required')
    bounds = _bounds(bounds)
    prefix = 1
    for group in packet['locals']:
        prefix *= len(group['roots'])
        if prefix > 2048:
            raise ValueError('native intersection root budget exceeded')
    sources = []; imports = {'import PerfectPower.ResidueAtlasIntersectionFactored'}; names = []
    for atlas in packet['constraints']:
        source = native_atlas(atlas, bounds)
        names.append(re.search(r'^namespace (Atlas_\w+)$', source, re.M).group(1))
        imports.update(line for line in source.splitlines() if line.startswith('import '))
        sources.append('\n'.join(line for line in source.splitlines() if not line.startswith('import ')))
    tag = hashlib.sha256(json.dumps([packet, bounds], sort_keys=True).encode()).hexdigest()[:16]
    namespace = 'Intersection_'+tag
    lines = sorted(imports)+sources+[f'namespace {namespace}',
        'open PerfectPower.ResidueAtlasIntersectionFactored',
        'open PerfectPower.ResidueAtlas (Bounds)']
    predicates = {}
    for i, (atlas, ns) in enumerate(zip(packet['constraints'], names)):
        predicate = f'{ns}.F x y % {atlas["modulus"]} = 0'
        predicates[i] = predicate
        lines += [f'def local{i} : CoverPacket (fun x y => {predicate}) {atlas["modulus"]} := ofAtlas {ns}.atlas{atlas["exponent"]}']
    group_names = []; group_predicates = []
    for j, group in enumerate(packet['locals']):
        ids = sorted(group['constraint_ids'], key=lambda i: (-packet['constraints'][i]['modulus'], i))
        m = group['modulus']; predicate = predicates[ids[0]]; previous = f'group{j}_0'
        lines += [f'def {previous} : CoverPacket (fun x y => {predicate}) {m} := local{ids[0]}']
        for k, i in enumerate(ids[1:], 1):
            predicate = f'({predicate}) ∧ ({predicates[i]})'; name = f'group{j}_{k}'
            lines += [f'def {name} : CoverPacket (fun x y => {predicate}) {m} := nested {previous} local{i} (by norm_num)']
            previous = name
        group_names.append(previous); group_predicates.append(predicate)
        lines += [f'theorem group_roots{j} : {previous}.roots = {_finset(group["roots"])} := by decide +kernel',
                  f'#print axioms group_roots{j}']
    predicate = group_predicates[0]; previous = 'stage0'; m = packet['locals'][0]['modulus']
    lines += [f'def stage0 : CoverPacket (fun x y => {predicate}) {m} := {group_names[0]}']
    for j in range(1, len(group_names)):
        n = packet['locals'][j]['modulus']; u = pow(m, -1, n); v = (1-u*m)//n
        predicate = f'({predicate}) ∧ ({group_predicates[j]})'
        lines += [f'theorem coprime{j} : ({m} : ℤ).natAbs.Coprime ({n} : ℤ).natAbs := by decide +kernel',
                  f'theorem bezout{j} : ({u} : ℤ)*{m}+({v})*{n}=1 := by decide +kernel',
                  f'def stage{j} : CoverPacket (fun x y => {predicate}) {m*n} := merge {previous} {group_names[j]} {u} ({v}) coprime{j} bezout{j}',
                  f'#print axioms coprime{j}', f'#print axioms bezout{j}']
        previous = f'stage{j}'; m *= n
    (x0, x1), (y0, y1) = bounds
    count = intersection_population(packet, bounds)['count']
    source_predicate = ' ∧ '.join(f'{ns}.F x y = 0' for ns in names)
    lines += [f'def bounds : Bounds := (({x0},{x1}),({y0},{y1}))',
              f'def S (x y : ℤ) : Prop := {source_predicate}',
              'instance : DecidablePred (fun z : ℤ × ℤ => S z.1 z.2) := fun z => by unfold S; infer_instance',
              f'theorem complete (x y : ℤ) : (x % {m},y % {m}) ∈ {previous}.roots ↔ {predicate} := {previous}.complete x y',
              f'theorem roots_count : {previous}.roots.card = {packet["combination_count"]} := by decide +kernel',
              f'theorem count_checked : (candidates {previous} bounds).card = {count} := by rw [card_candidates]; decide +kernel',
              f'theorem source_implies (x y : ℤ) (h : S x y) : {predicate} := by',
              '  simp only [S] at h',
              '  rcases h with '+('⟨'+','.join(f'h{i}' for i in range(len(names)))+'⟩' if len(names)>1 else 'h0'),
              '  simp only ['+', '.join(f'h{i}' for i in range(len(names)))+', Int.zero_emod, and_self]',
              f'theorem source_survives (x y : ℤ) (h : S x y) : (x % {m},y % {m}) ∈ {previous}.roots := ({previous}.complete x y).mpr (source_implies x y h)',
              '#print axioms complete', '#print axioms roots_count', '#print axioms count_checked',
              '#print axioms source_implies', '#print axioms source_survives']
    if packet['global_obstruction']:
        lines += [f'theorem no_integer_solution (x y : ℤ) : ¬ S x y := fun h => {previous}.empty_obstruction (by decide +kernel) x y (source_implies x y h)',
                  '#print axioms no_integer_solution']
    if (x1-x0+1)*(y1-y0+1) <= 1024 and count <= 512:
        points = intersection_scan(packet, bounds)['points']
        lines += [f'def points : Finset (ℤ × ℤ) := {_finset(points)}',
                  f'theorem points_checked : solutions {previous} bounds S = points := by decide +kernel',
                  f'theorem points_complete (x y : ℤ) : (x,y) ∈ points ↔ {x0}≤x ∧ x≤{x1} ∧ {y0}≤y ∧ y≤{y1} ∧ S x y := by',
                  f'  rw [← points_checked]; exact solutions_complete {previous} bounds S source_implies x y',
                  '#print axioms points_checked', '#print axioms points_complete']
    lines += [f'end {namespace}']
    return '\n'.join(lines)+'\n'
