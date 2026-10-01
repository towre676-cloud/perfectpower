"""Translate selected *complete ground contexts* from independent Why3 tasks.

Quantified assertions are omitted, strengthening the theorem. Uninterpreted
functions remain arbitrary Lean functions. No identities about squaring are
assumed. The translator is an explicit, reviewable trust boundary, not verified.
"""
import pathlib,json,z3
import sys as _sys
_sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1] / "python"))
from perfectpower.unsigned_adapter import assertions,derive,terms

ROOT=pathlib.Path(__file__).resolve().parent

def emit(text,cert,name):
    aa=assertions(text);ground=[(i,e) for i,e in enumerate(aa[:-1]) if not z3.is_quantifier(e)]
    goal=aa[-1]
    if not z3.is_not(goal):return ''
    goal=goal.arg(0)
    dd={}
    for _,e in ground+[(len(aa)-1,goal)]:
        for t in terms(e):
            if z3.is_app(t) and t.decl().kind()==z3.Z3_OP_UNINTERPRETED:dd[t.decl().name()]=t.decl()
    names={k:'v'+str(j) for j,k in enumerate(sorted(dd))}
    def sort(s):
        if z3.is_bv_sort(s):return f'BitVec {s.size()}'
        if s.kind()==z3.Z3_BOOL_SORT:return 'Prop'
        raise ValueError('unsupported sort '+str(s))
    def tr(e):
        if z3.is_bv_value(e):return f'({e.as_long()} : BitVec {e.size()})'
        k=e.decl().kind()
        if k==z3.Z3_OP_UNINTERPRETED:
            return '('+' '.join([names[e.decl().name()]]+[tr(x) for x in e.children()])+')'
        args=[tr(x) for x in e.children()]
        ops={z3.Z3_OP_BADD:'+',z3.Z3_OP_BSUB:'-',z3.Z3_OP_BMUL:'*',z3.Z3_OP_BOR:'|||',
             z3.Z3_OP_BAND:'&&&',z3.Z3_OP_BXOR:'^^^',z3.Z3_OP_ULEQ:'≤',z3.Z3_OP_ULT:'<',
             z3.Z3_OP_EQ:'=',z3.Z3_OP_AND:'∧',z3.Z3_OP_OR:'∨',z3.Z3_OP_IMPLIES:'→'}
        if k in ops:return '('+(' '+ops[k]+' ').join(args)+')'
        if k==z3.Z3_OP_NOT:return '(¬ '+args[0]+')'
        if k==z3.Z3_OP_ITE:return '(if '+args[0]+' then '+args[1]+' else '+args[2]+')'
        if k==z3.Z3_OP_UGEQ:return '('+args[1]+' ≤ '+args[0]+')'
        if k==z3.Z3_OP_UGT:return '('+args[1]+' < '+args[0]+')'
        if k==z3.Z3_OP_BSHL:return '('+args[0]+' <<< '+args[1]+'.toNat)'
        if k==z3.Z3_OP_BLSHR:return '('+args[0]+' >>> '+args[1]+'.toNat)'
        if k==z3.Z3_OP_TRUE:return 'True'
        if k==z3.Z3_OP_FALSE:return 'False'
        raise ValueError('unsupported term '+e.sexpr())
    out=f'-- Original task SHA256 {cert["task_sha256"]}\ntheorem {name}\n'
    for k,d in sorted(dd.items()):
        types=[sort(d.domain(j)) for j in range(d.arity())]+[sort(d.range())]
        out+=f'    ({names[k]} : '+(' → '.join(types))+')\n'
    for i,e in ground:out+=f'    (h{i} : {tr(e)})\n'
    out+='    : '+tr(goal)+' := by\n'
    index={t.sexpr():t for i,e in ground+[(len(aa)-1,goal)] for t in terms(e)}
    for j,s in enumerate(cert['steps']):
        n,b,x=[tr(index[s[k]]) for k in ('n','b','x')]
        hu=f'h{s["upper_assertion"]}' if s['upper_assertion'] is not None else f'(show {n} ≤ {n} from by simp [BitVec.le_def])'
        out+=f'  have d{j} := PerfectPower.BVWorkflow.sub_le_bound {n} {b} {x} h{s["guard_assertion"]} {hu}\n'
    if name in ('vc0','vc1','vc2'):
        out+='  rw [h37]\n  exact d3\n\n'
    else:
        out+='  have hr : v4 = v5 := by simpa [h26] using h20\n  rw [hr, ← h22]\n  exact d0\n\n'
    return out

def main():
    out='import PerfectPower.BVWorkflow\nset_option linter.unusedVariables false\nnamespace PerfectPower.WorkflowContexts\n\n'
    selected=[]
    # Pin these source obligations explicitly, without altering their programs.
    for w in [16,32,64]:
        selected.append(f'isqrt_von_neumann-VonNeumann{w}-isqrt{w}qtvc26.smt2')
    selected.append('isqrt_von_neumann-VonNeumann64-isqrt64qtvc43.smt2')
    for i,name in enumerate(selected):
        text=(ROOT/'raw_bv_vcs'/name).read_text();cert=derive(text)
        out+=emit(text,cert,'vc'+str(i))
        out+='\n'  # axioms are audited in audit/Axioms.lean
    out+='end PerfectPower.WorkflowContexts\n'
    (ROOT.parent/'PerfectPower'/'Generated'/'WorkflowContexts.lean').write_text(out)
    print('complete ground contexts',len(selected))

if __name__=='__main__':main()
