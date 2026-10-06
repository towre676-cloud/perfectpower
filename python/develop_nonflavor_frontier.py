"""Reproduce the new source-bound witnesses without modifying historic counts."""
import argparse
import hashlib
import json
from pathlib import Path
import tempfile
import time
import tracemalloc

from perfectpower.catalogue import Catalogue
from perfectpower.query_service import dispatch
from perfectpower.smt_cert import split_commands
from perfectpower.smt_stream import iter_commands, file_chunks
from perfectpower.industrial_replay import solve_replay, solve_replay_stream
from perfectpower.gamma_arithmetic import factorial_window_obstruction,factorial_window_lean
from perfectpower.period_matrix_balls import marked_legendre_monodromy

ROOT=Path(__file__).resolve().parents[1]
LOOP=['1/2',['1/2','1/4'],['-1/4','1/4'],['-1/4','-1/4'],['1/2','-1/4'],'1/2']


def develop(output,monodromy=False):
    output=Path(output);output.mkdir(parents=True,exist_ok=True)
    def save(name,data):
        (output/name).write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
    requests=[dict(op='inverse_matrix_ball',args=dict(matrix=[[1,0],[0,1]],row_error_bound='1/10')),
              dict(op='recognize_integral_matrix',args=dict(matrix=[[1,2],[0,1]],row_error_bound=0,symplectic=True)),
              dict(op='marked_legendre_monodromy',args=dict(path=['1/2','1/2'])),
              dict(op='cluster_graph_metric',args=dict(roots=[0,3,1,4,2,5],p=3)),
              dict(op='factorial_window_obstruction',args=dict(index=10**30,width=10**20,degree=2))]
    with tempfile.TemporaryDirectory() as directory, Catalogue(Path(directory)/'cold.db') as catalogue:
        rows=[dict(request=request,result=dispatch(catalogue,request)) for request in requests]
    save('service-replay.json',rows)
    witness=factorial_window_obstruction(10**30,10**20,2)
    save('factorial_window.json',witness)
    (output/'factorial-window.lean').write_text(factorial_window_lean(witness))
    parser=[]
    for path in sorted(ROOT.rglob('*.smt2')):
        if '.lake' in path.parts:continue
        raw=path.read_bytes();control=split_commands(raw.decode())
        with path.open() as handle:
            candidate=list(iter_commands(file_chunks(handle,127),max_command_chars=10000000))
        if candidate!=control:raise ValueError('Parser mismatch: '+str(path))
        parser.append(dict(path=str(path.relative_to(ROOT)),sha256=hashlib.sha256(raw).hexdigest(),commands=len(control)))
    save('parser-corpus.json',dict(files=len(parser),commands=sum(r['commands'] for r in parser),chunk_chars=127,exact_slices_equal=True,rows=parser))
    replay=[]
    paths=sorted((ROOT/'examples/smt').glob('*.smt2'))+sorted((ROOT/'why3_isqrt/raw_vcs').glob('*.smt2'))[:12]
    for path in paths:
        raw=path.read_bytes();control=solve_replay(raw.decode(),query_ms=50,batch_chars=0)
        with path.open() as handle:
            candidate=solve_replay_stream(file_chunks(handle,127),query_ms=50,batch_chars=4096)
        answers=[[q['answer'] for q in r['queries']] for r in (control,candidate)]
        if control['errors'] or candidate['errors'] or len(answers[0])!=len(answers[1]):raise ValueError('Invalid replay: '+str(path))
        conflicts=sum({a,b}=={'sat','unsat'} for a,b in zip(*answers))
        if conflicts:raise ValueError('Contradictory solver answers: '+str(path))
        replay.append(dict(path=str(path.relative_to(ROOT)),sha256=hashlib.sha256(raw).hexdigest(),control=control,streaming=candidate,answer_conflicts=conflicts))
    save('stream-replay.json',dict(files=len(replay),query_count=sum(r['control']['query_count'] for r in replay),answer_conflicts=0,query_ms=50,rows=replay,
        scope='repo fixtures and twelve original Why3 VC tasks; this does not replicate the external 181-file industrial performance cohort'))
    memory=[]
    for count in (1000,100000):
        chunk='(assert true)\n'*100
        tracemalloc.start();started=time.perf_counter()
        commands=sum(1 for _ in iter_commands((chunk for _ in range(count//100))))
        _,peak=tracemalloc.get_traced_memory();tracemalloc.stop()
        memory.append(dict(source_commands=count,parsed_commands=commands,peak_traced_bytes=peak,seconds=time.perf_counter()-started))
    save('scanner-memory.json',dict(rows=memory,scope='Python scanner allocations only; input chunks generated on demand; no solver state or retained result list'))
    if monodromy:
        save('legendre-monodromy.json',dict(path=LOOP,order=24,rounding_bits=128,step_limit=256,
             result=marked_legendre_monodromy(LOOP,order=24)))
    print(json.dumps(dict(parser_files=len(parser),parser_commands=sum(r['commands'] for r in parser),replay_files=len(replay),memory=memory)))


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,default=ROOT/'receipts/nonflavor_frontier')
    parser.add_argument('--monodromy',action='store_true');args=parser.parse_args()
    develop(args.output,args.monodromy)
