"""Source-bound, guarded unsigned subtraction lemma injection for SMT-LIB.

Each added fact follows from a ground premise already in the same single-query
task and the unconditional Lean theorem BVWorkflow.sub_le_self/sub_le_bound.
Unsupported scopes/queries are rejected. Other operations keep BV semantics.
No file-name-based matching, result table, or host arithmetic oracle is used.
"""
from __future__ import annotations
import hashlib,json,pathlib,re
import z3

SCHEMA='pp-unsigned-sub/1'

def digest(text):return hashlib.sha256(text.encode()).hexdigest()

def commands(text):
    """Split outer SMT commands while respecting comments, strings and symbols."""
    out=[];depth=0;start=None;mode=None;i=0
    while i<len(text):
        c=text[i]
        if mode=='comment':
            if c=='\n':mode=None
        elif mode=='symbol':
            if c=='|':mode=None
        elif mode=='string':
            if c=='"':
                if i+1<len(text) and text[i+1]=='"':i+=1
                else:mode=None
        elif c==';':mode='comment'
        elif c=='|':mode='symbol'
        elif c=='"':mode='string'
        elif c=='(':
            if depth==0:start=i
            depth+=1
        elif c==')':
            depth-=1
            if depth<0:raise ValueError('unbalanced command')
            if depth==0:
                command=text[start:i+1]
                match=re.match(r'\(\s*([A-Za-z0-9_-]+)',command)
                if not match:raise ValueError('invalid command')
                out.append((match.group(1),start,i+1))
        elif depth==0 and not c.isspace():raise ValueError('text outside command')
        i+=1
    if depth or mode in ('string','symbol'):raise ValueError('incomplete command')
    return out

def assertions(text):
    # Source restrictions are conservative. Do not combine incremental frames.
    cc=commands(text);names=[c[0] for c in cc]
    if names.count('check-sat')!=1:
        raise ValueError('requires exactly one check-sat')
    allowed={'set-logic','set-option','set-info','declare-sort','declare-fun','declare-const',
             'define-fun','define-sort','assert','check-sat','exit'}
    if any(n not in allowed for n in names):raise ValueError('unsupported command or scope')
    q=names.index('check-sat')
    if any(n!='exit' for n in names[q+1:]) or 'exit' in names[:q]:
        raise ValueError('assertions must precede query')
    return list(z3.parse_smt2_string(text))

def terms(e):
    yield e
    if z3.is_quantifier(e):return
    for a in e.children():yield from terms(a)

def bounds(e):
    if z3.is_quantifier(e):return []
    if z3.is_and(e):return [x for a in e.children() for x in bounds(a)]
    k=e.decl().kind()
    if k==z3.Z3_OP_ULEQ:return [(e.arg(0),e.arg(1))]
    if k==z3.Z3_OP_UGEQ:return [(e.arg(1),e.arg(0))]
    return []

def derive(text):
    aa=assertions(text);bb=[]
    for i,e in enumerate(aa):
        for a,b in bounds(e):bb.append((i,a,b))
    steps=[];seen=set()
    for i,e in enumerate(aa):
        if z3.is_quantifier(e):continue
        for t in terms(e):
            if not z3.is_app(t) or t.decl().kind()!=z3.Z3_OP_BSUB:continue
            n,b=t.children()
            for premise,lo,hi in bb:
                if not(z3.eq(lo,b) and z3.eq(hi,n)):continue
                targets=[(None,n)]+[(j,x) for j,v,x in bb if z3.eq(v,n)]
                for upper,x in targets:
                    fact=z3.ULE(t,x).sexpr()
                    if fact in seen:continue
                    seen.add(fact)
                    steps.append(dict(term_assertion=i,guard_assertion=premise,upper_assertion=upper,
                                      n=n.sexpr(),b=b.sexpr(),x=x.sexpr(),width=n.size(),fact=fact))
    return dict(schema=SCHEMA,task_sha256=digest(text),steps=steps)

def check(text,cert):
    if cert.get('schema')!=SCHEMA or cert.get('task_sha256')!=digest(text):return False
    try:
        expected=derive(text)
        # A proposed certificate may select any subset, but cannot forge a step.
        valid={json.dumps(s,sort_keys=True) for s in expected['steps']}
        return bool(cert['steps']) and all(json.dumps(s,sort_keys=True) in valid for s in cert['steps'])
    except (ValueError,z3.Z3Exception,KeyError,TypeError):return False

def select_for_goal(text,cert):
    """A syntactic policy: only unsigned-order goals sharing the derived upper bound.

    Policy changes performance, never the proof rule. No task names, measurements,
    or solver answer is used. Other tasks retain their original assertions.
    """
    aa=assertions(text);goal=aa[-1] if aa else None
    selected=[]
    if goal is not None and z3.is_not(goal):
        g=goal.arg(0)
        if z3.is_app(g) and g.decl().kind()==z3.Z3_OP_ULEQ:
            selected=[s for s in cert['steps'] if s['x']==g.arg(1).sexpr()]
    return dict(schema=cert['schema'],task_sha256=cert['task_sha256'],steps=selected)

def accelerate(text,cert=None,policy='goal'):
    if policy not in ('goal','all'):raise ValueError('unsupported policy')
    cert=derive(text) if cert is None else cert
    if policy=='goal':cert=select_for_goal(text,cert)
    if not check(text,cert):return text,cert
    # Insert before the last (and only) query; source-bound guards are already active.
    position=next(start for name,start,end in commands(text) if name=='check-sat')
    injected='\n; checked instances of PerfectPower.BVWorkflow.sub_le_bound\n'+''.join(
        '(assert '+s['fact']+')\n' for s in cert['steps'])
    return text[:position]+injected+text[position:],cert

if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser();ap.add_argument('task');ap.add_argument('--output',required=True)
    ap.add_argument('--policy',choices=['goal','all'],default='goal')
    a=ap.parse_args();p=pathlib.Path(a.task);out,cert=accelerate(p.read_text(),policy=a.policy);pathlib.Path(a.output).write_text(out)
    pathlib.Path(a.output+'.certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    print(json.dumps(dict(accepted=check(p.read_text(),cert),steps=len(cert['steps']))))
