#!/usr/bin/env python3
"""Dependency-free structural triage, not an SMT solver or proof checker."""
import argparse
import collections
import json
import pathlib
import re

ROOT = pathlib.Path(__file__).resolve().parents[1]
TOKEN = re.compile(r';[^\r\n]*|"(?:[^"\n]|""|\n)*"|\|[^|]*\||[()]|[^\s();]+')
INTEGER = re.compile(r'-?[0-9]+\Z')

def parse(text):
    roots, stack = [], []
    for match in TOKEN.finditer(text):
        token = match.group()
        if token.startswith(';'):
            continue
        if token == '(':
            new = []
            (stack[-1] if stack else roots).append(new)
            stack.append(new)
        elif token == ')':
            if not stack:
                raise ValueError('unmatched closing parenthesis')
            stack.pop()
        else:
            if not stack:
                raise ValueError('atom outside command')
            stack[-1].append(token)
    if stack:
        raise ValueError('unclosed parenthesis')
    return roots

def head(node):
    if not isinstance(node, list) or not node:
        return ''
    if isinstance(node[0], str):
        return node[0]
    inner = node[0]
    return 'indexed:' + str(inner[1]) if len(inner) > 1 and inner[0] == '_' else 'compound-head'

def walk(nodes):
    pending = list(nodes)
    while pending:
        node = pending.pop()
        if isinstance(node, list):
            yield node
            pending.extend(node[1:])

def symbolic(node):
    if isinstance(node, str):
        return not bool(INTEGER.fullmatch(node))
    return any(symbolic(x) for x in node[1:])

def add(a, b, scale=1):
    result = dict(a)
    for m, c in b.items():
        result[m] = result.get(m, 0) + scale*c
        if not result[m]:
            del result[m]
    return result

def mul(a, b):
    result = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            powers = collections.Counter(dict(ma))
            powers.update(dict(mb))
            if sum(powers.values()) > 12:
                raise ValueError('degree cap')
            m = tuple(sorted(powers.items()))
            result[m] = result.get(m, 0) + ca*cb
    if len(result) > 256:
        raise ValueError('term cap')
    return {m:c for m,c in result.items() if c}

def polynomial(node, ints):
    if isinstance(node, str):
        if INTEGER.fullmatch(node):
            n = int(node)
            return {(): n} if n else {}
        if node in ints:
            return {((node, 1),): 1}
        raise ValueError('not an integer polynomial atom')
    op = head(node)
    if op not in ('+', '-', '*') or len(node) < 2:
        raise ValueError('unsupported polynomial operator')
    args = [polynomial(x, ints) for x in node[1:]]
    if op == '+':
        result = {}
        for a in args:
            result = add(result, a)
        return result
    if op == '-':
        if len(args) == 1:
            return {m:-c for m,c in args[0].items()}
        result = args[0]
        for a in args[1:]:
            result = add(result, a, -1)
        return result
    result = {():1}
    for a in args:
        result = mul(result, a)
    return result

def positive_atoms(node):
    # Do not descend through not, or, implies, ite, let, or quantifiers.
    pending = [node]
    while pending:
        item = pending.pop()
        if head(item) == 'and':
            pending.extend(item[1:])
        else:
            yield item

def render(node):
    return '(' + ' '.join(render(x) for x in node) + ')' if isinstance(node, list) else node

def candidates(forms, ints):
    found = []
    for i, form in enumerate(forms):
        if head(form) != 'assert' or len(form) != 2:
            continue
        for atom in positive_atoms(form[1]):
            if head(atom) != '=' or len(atom) != 3:
                continue
            for left, right in ((atom[1], atom[2]), (atom[2], atom[1])):
                try:
                    power, rhs = polynomial(left, ints), polynomial(right, ints)
                except (ValueError, RecursionError):
                    continue
                if len(power) != 1:
                    continue
                (m, c), = power.items()
                if c != 1 or len(m) != 1 or m[0][1] not in (2,3):
                    continue
                output, exponent = m[0]
                variables = sorted({v for mon in rhs for v,d in mon})
                if len(variables) > 1 or output in variables:
                    continue
                coefficients = {}
                for mon, coeff in rhs.items():
                    degree = sum(d for v,d in mon)
                    coefficients[str(degree)] = coefficients.get(str(degree),0)+coeff
                found.append({'command_index':i, 'power':exponent, 'output_variable':output,
                              'input_variable':variables[0] if variables else None,
                              'coefficients_by_degree':coefficients,
                              'atom':render(atom)[:1000], 'classification':'syntactic_candidate_only'})
    return found

def inspect(row):
    text = (ROOT / row['local_path']).read_text(encoding='utf-8')
    forms = parse(text)
    ops = collections.Counter(head(n) for n in walk(forms))
    declared, ints = {}, set()
    for form in forms:
        if head(form) == 'declare-const' and len(form) == 3:
            declared[form[1]] = form[2]
        elif head(form) == 'declare-fun' and len(form) == 4 and form[2] == []:
            declared[form[1]] = form[3]
    ints = {x for x,s in declared.items() if s == 'Int'}
    checks, expected, current_status = [], [], None
    for i, form in enumerate(forms):
        if head(form) == 'set-info' and len(form) > 2 and form[1] == ':status':
            current_status = form[2]
        if head(form) in ('check-sat','check-sat-assuming'):
            checks.append({'command_index':i, 'command':head(form), 'last_status_annotation':current_status})
    expected = re.findall(r'^\s*;\s*EXPECT:\s*(sat|unsat|unknown)\s*$', text, re.MULTILINE)
    flags = re.findall(r'^\s*;\s*COMMAND-LINE:\s*(.*)$',text,re.MULTILINE)
    directives = collections.defaultdict(list)
    for key, value in re.findall(r'^\s*;\s*([A-Z][A-Z-]*):\s*(.*)$',text,re.MULTILINE):
        directives[key].append(value.strip())
    products = sum(head(n) == '*' and sum(symbolic(x) for x in n[1:]) >= 2 for n in walk(forms))
    return {'local_path':row['local_path'],'repository':row['repository'],'bytes':row['upstream_bytes'],
            'logic':[f[1] for f in forms if head(f)=='set-logic' and len(f)>1],
            'commands':len(forms),'declared_integer_constants':len(ints),'operators':dict(sorted(ops.items())),
            'check_sat_queries':checks, 'harness_expectations':expected,'harness_command_lines':flags,
            'harness_directives':dict(directives),
            'expected_harness_failure':bool(directives.get('EXPECT-ERROR')) or any(x != '0' for x in directives.get('EXIT',[])),
            'symbolic_product_sites_heuristic':products,
            'direct_power_candidates':candidates(forms,ints),
            'notes':'Syntactic triage only; does not expand let/define-fun or replay push/pop. No solving or proof.'}

def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output-dir',type=pathlib.Path, default=ROOT/'reports')
    args = p.parse_args()
    manifest = json.loads((ROOT/'provenance/upstream.json').read_text())
    rows = []
    for row in manifest:
        try:
            rows.append(inspect(row))
        except Exception as e:
            rows.append({'local_path':row['local_path'],'repository':row['repository'],'error':str(e)})
    errors = [x for x in rows if 'error' in x]
    cohorts = {}
    for repo in sorted({x['repository'] for x in rows}):
        sub = [x for x in rows if x['repository']==repo and 'error' not in x]
        cohorts[repo] = {'files':len(sub), 'bytes':sum(x['bytes'] for x in sub),
                         'queries':sum(len(x['check_sat_queries']) for x in sub),
                         'files_with_symbolic_products_heuristic':sum(x['symbolic_product_sites_heuristic']>0 for x in sub),
                         'files_with_direct_power_candidates':sum(bool(x['direct_power_candidates']) for x in sub),
                         'files_with_expected_harness_failure':sum(x['expected_harness_failure'] for x in sub),
                         'files_with_integer_bitwise_or_power_extensions':sum(any(k in x['operators'] for k in ('piand','int.pow2','indexed:iand','iand')) for x in sub),
                         'direct_power_candidate_occurrences':sum(len(x['direct_power_candidates']) for x in sub)}
    summary = {'files':len(rows), 'parse_errors':len(errors),'cohorts':cohorts,
               'solving_performed':False,'proof_checking_performed':False,
               'coverage_claim':'No measured PerfectPower coverage or speedup. Candidate counts are syntax only.'}
    args.output_dir.mkdir(parents=True,exist_ok=True)
    (args.output_dir/'structural_inventory.json').write_text(json.dumps(rows,indent=2)+'\n')
    (args.output_dir/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))
    if errors:
        raise SystemExit(1)

if __name__ == '__main__':
    main()
