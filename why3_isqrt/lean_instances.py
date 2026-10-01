"""Emit kernel-checkable ground theorem instances for source-bound SMT facts."""
import argparse,json,pathlib
import z3
import sys as _sys
_sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "python"))
from perfectpower.unsigned_adapter import assertions,derive,terms,check

def emit_task(text,cert,prefix):
    if not check(text,cert):return ''
    aa=assertions(text);index={e.sexpr():e for a in aa for e in terms(a)}
    out=[]
    for i,s in enumerate(cert['steps']):
        es=[index[s[k]] for k in ('n','b','x')]
        names={e.sexpr():e for a in es for e in terms(a) if z3.is_const(e) and e.decl().kind()==z3.Z3_OP_UNINTERPRETED}
        mapping={k:'v'+str(j) for j,k in enumerate(sorted(names))}
        def tr(e):
            if z3.is_bv_value(e):return f'({e.as_long()} : BitVec {e.size()})'
            if e.sexpr() in mapping:return mapping[e.sexpr()]
            k=e.decl().kind();args=[tr(a) for a in e.children()]
            ops={z3.Z3_OP_BADD:'+',z3.Z3_OP_BSUB:'-',z3.Z3_OP_BMUL:'*',z3.Z3_OP_BOR:'|||',
                 z3.Z3_OP_BAND:'&&&',z3.Z3_OP_BXOR:'^^^'}
            if k in ops:return '('+(' '+ops[k]+' ').join(args)+')'
            if k==z3.Z3_OP_BNOT:return '(~~~'+args[0]+')'
            if k==z3.Z3_OP_BSHL:return '('+args[0]+' <<< '+args[1]+'.toNat)'
            if k==z3.Z3_OP_BLSHR:return '('+args[0]+' >>> '+args[1]+'.toNat)'
            raise ValueError('unsupported Lean term: '+e.sexpr())
        pars=' '.join(f'({mapping[k]} : BitVec {names[k].size()})' for k in sorted(names))
        n,b,x=map(tr,es)
        out.append(f'-- Source SHA256 {cert["task_sha256"]}, step {i}\n'
                   f'theorem {prefix}_{i} {pars} (hb : {b} ≤ {n}) (hx : {n} ≤ {x}) :\n'
                   f'    {n} - {b} ≤ {x} :=\n'
                   f'  PerfectPower.BVWorkflow.sub_le_bound {n} {b} {x} hb hx\n')
    return '\n'.join(out)

def emit(root):
    head='import PerfectPower.BVWorkflow\nnamespace PerfectPower.WorkflowInstances\n\n'
    count=0
    for j,p in enumerate(sorted((root/'raw_bv_vcs').glob('*.smt2'))):
        text=p.read_text();cert=derive(text)
        if cert['steps']:
            head+=emit_task(text,cert,'task'+str(j));count+=len(cert['steps'])
    head+='\nend PerfectPower.WorkflowInstances\n'
    (root.parent/'PerfectPower'/'Generated'/'WorkflowInstances.lean').write_text(head)
    print('instances',count)

if __name__=='__main__':emit(pathlib.Path(__file__).resolve().parent)
