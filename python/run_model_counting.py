#!/usr/bin/env python3
"""Source-bound exact-count competition replication. Run solvers serially."""
import fcntl
import argparse,hashlib,json,math,os,platform,re,resource,signal,subprocess,sys,time
from pathlib import Path
from datetime import datetime,timezone
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.model_counting import CNF,CNFCounter,native_library
from perfectpower.divisor_square import WorkLimit

def worker(path,timeout):
    try:
        formula=CNF.read(path)
        with CNFCounter(formula,timeout=timeout) as counter:result=counter.result()
    except WorkLimit as e:result={'status':'WORK_LIMIT','reason':str(e)}
    except (ValueError,UnicodeError) as e:result={'status':'INVALID_INPUT','reason':str(e)}
    print(json.dumps(result),flush=True)

def run(command,limit,memory,log):
    def limits():
        resource.setrlimit(resource.RLIMIT_AS,(memory,memory));resource.setrlimit(resource.RLIMIT_CPU,(math.ceil(limit)+2,math.ceil(limit)+3))
    started=time.perf_counter()
    process=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True,preexec_fn=limits)
    timed=False
    try:out,err=process.communicate(timeout=limit)
    except subprocess.TimeoutExpired:
        timed=True;os.killpg(process.pid,signal.SIGKILL);out,err=process.communicate()
    elapsed=time.perf_counter()-started
    stdout=out.decode('utf8',errors='replace');stderr=err.decode('utf8',errors='replace')
    log.write_text(stdout+'\n--- STDERR ---\n'+stderr)
    status='TIMEOUT' if timed else 'ERROR' if process.returncode else 'NO_COUNT';count=None;reason=None
    if not timed and process.returncode==0:
        # Ganak with --prob 0 reports deterministic arbitrary-precision integers.
        counts=re.findall(r'^c s exact arb int ([0-9]+)\s*$',stdout,re.M)
        if not counts:counts=re.findall(r'^s (?:mc )?([0-9]+)\s*$',stdout,re.M)
        if counts:count=counts[-1];status='EXACT'
        else:
            try:
                r=json.loads(stdout.strip());status=r['status'];count=r.get('count');reason=r.get('reason')
            except (ValueError,KeyError):pass
    return {'status':status,'count':count,'reason':reason,'seconds':elapsed,'exit_code':process.returncode,'command':command,'log':os.path.relpath(log,ROOT)}

def acquire_output_lock(output):
    handle=Path(str(output)+'.lock').open('a')
    try:fcntl.flock(handle.fileno(),fcntl.LOCK_EX|fcntl.LOCK_NB)
    except BlockingIOError:
        handle.close();raise RuntimeError('another benchmark owns this output')
    return handle

def main():
    p=argparse.ArgumentParser();p.add_argument('--stop-file',type=Path);p.add_argument('--worker',type=Path);p.add_argument('--corpus',type=Path);p.add_argument('--ganak',type=Path);p.add_argument('--d4',type=Path);p.add_argument('--split',choices=['public','holdout','all'],default='all');p.add_argument('--timeout',type=float,default=120);p.add_argument('--memory-gib',type=int,default=6);p.add_argument('--limit',type=int);p.add_argument('--output',type=Path,default=ROOT/'receipts/model_counting/benchmark.json');args=p.parse_args()
    if args.worker:return worker(args.worker,args.timeout)
    if not args.corpus or not args.ganak:p.error('--corpus and --ganak required')
    if not 0<args.timeout<=3600 or not 1<=args.memory_gib<=32:p.error('bounded time and memory required')
    manifest=json.loads((ROOT/'data/model_counting/manifest.json').read_text())
    rows=[r for r in manifest['instances'] if args.split=='all' or r['split']==args.split]
    if args.limit is not None:rows=rows[:args.limit]
    args.output=args.output.resolve();directory=args.output.parent;directory.mkdir(parents=True,exist_ok=True)
    output_lock=acquire_output_lock(args.output)
    logs=directory/(args.output.stem+'_logs');logs.mkdir(exist_ok=True)
    # Separate compilation from every measured subprocess; parsing/startup are included.
    t=time.perf_counter();native_library();compile_seconds=time.perf_counter()-t
    solvers={'perfectpower':[sys.executable,str(Path(__file__).resolve()),'--worker'], 'ganak':[str(args.ganak.resolve()),'--prob','0']}
    if args.d4:solvers['d4']=[str(args.d4.resolve())]
    metadata={'schema':'pp-cnf-benchmark/1','started_utc':datetime.now(timezone.utc).isoformat(),'dataset':manifest['dataset'],'doi':manifest['doi'],'manifest_sha256':hashlib.sha256((ROOT/'data/model_counting/manifest.json').read_bytes()).hexdigest(),'split':args.split,'instances':[r['name'] for r in rows],'limit':args.limit,'timeout_seconds':args.timeout,'memory_gib':args.memory_gib,'timing_scope':'cold subprocess wall time including Python/native or reference parsing and startup; native compilation separately warmed; serial alternating solver order','native_setup_seconds':compile_seconds,'native_source_sha256':hashlib.sha256((ROOT/'native/model_counting/counter.cpp').read_bytes()).hexdigest(),'python_source_sha256':hashlib.sha256((ROOT/'python/perfectpower/model_counting.py').read_bytes()).hexdigest(),'platform':platform.platform(),'cpu':next((l.split(':',1)[1].strip() for l in Path('/proc/cpuinfo').read_text().splitlines() if l.startswith('model name')),'unknown'),'solvers':{k:{'command':v,'binary_sha256':hashlib.sha256(Path(v[0]).read_bytes()).hexdigest()} for k,v in solvers.items()},'results':[]}
    def save():
        temp=args.output.with_suffix('.tmp');temp.write_text(json.dumps(metadata,indent=2)+'\n');temp.replace(args.output)
    save() # Fix scope before any results, including every unsupported/timeout case.
    for i,row in enumerate(rows):
        if args.stop_file and args.stop_file.exists():raise RuntimeError('benchmark stopped by its stop file')
        if hashlib.sha256((ROOT/'native/model_counting/counter.cpp').read_bytes()).hexdigest()!=metadata['native_source_sha256'] or hashlib.sha256((ROOT/'python/perfectpower/model_counting.py').read_bytes()).hexdigest()!=metadata['python_source_sha256']:raise RuntimeError('frozen counter changed during benchmark')
        path=args.corpus/row['name']
        if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('corpus hash differs: '+row['name'])
        result={'name':row['name'],'sha256':row['sha256'],'header':row['header'],'split':row['split'],'solvers':{}}
        order=list(solvers);order=order[i%len(order):]+order[:i%len(order)]
        for solver in order:
            if solver=='perfectpower':command=solvers[solver]+[str(path),'--timeout',str(args.timeout)]
            elif solver=='ganak':command=solvers[solver]+[str(path)]
            else:command=solvers[solver]+[str(path),'-mc']
            answer=run(command,args.timeout,args.memory_gib*1024**3,logs/(row['name']+'.'+solver+'.log'));result['solvers'][solver]=answer
            print(f'{i+1}/{len(rows)} {row["name"]} {solver}: {answer["status"]} {answer["seconds"]:.3f}s',flush=True)
        exact={v['count'] for v in result['solvers'].values() if v['status']=='EXACT'}
        result['agreement']='MATCH' if len(exact)==1 and sum(v['status']=='EXACT' for v in result['solvers'].values())>=2 else 'MISMATCH' if len(exact)>1 else 'UNCONFIRMED'
        metadata['results'].append(result);save()
        if result['agreement']=='MISMATCH':raise RuntimeError('EXACT COUNT DISAGREEMENT: '+row['name'])
    metadata['completed']=True;metadata['summary']={solver:{status:sum(r['solvers'][solver]['status']==status for r in metadata['results']) for status in sorted({r['solvers'][solver]['status'] for r in metadata['results']})} for solver in solvers};save();print(json.dumps(metadata['summary']),flush=True)
if __name__=='__main__':main()
