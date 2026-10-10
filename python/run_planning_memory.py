"""Fresh-process peak RSS for each compared public workflow (Linux)."""
import argparse
import json
from pathlib import Path
try:
    import resource
except ImportError:
    resource=None
import subprocess
import sys
from run_planning import parse_public,bank,GrayIndex,ortools_optimum
from perfectpower.planning import CompletionPlanner
from perfectpower.divisor_square import WorkLimit

ROOT=Path(__file__).resolve().parents[1]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case',type=int);parser.add_argument('--method',choices=['planner','gray','ortools'])
    args=parser.parse_args();rows=parse_public()
    if args.case is not None and (not 0 <= args.case < len(rows) or args.method is None):
        parser.error('worker needs a valid case index and method')
    if resource is None or sys.platform != 'linux':
        result={'schema':'pp-planning-memory/1','status':'unavailable','reason':'fresh-process peak RSS measurement requires Linux'}
        (ROOT/'receipts/planning/memory.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps(result));return
    if args.case is not None:
        spec=dict(rows[args.case]['specification'])
        if len(spec['variables'])==20:spec['state_limit']=1000000
        try:
            result=ortools_optimum(spec) if args.method=='ortools' else bank((CompletionPlanner if args.method=='planner' else GrayIndex)(spec))
            status='complete'
        except WorkLimit:
            status='WORK_LIMIT'
        print(json.dumps({'status':status,'peak_resident_bytes':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss*1024}))
        return
    output=[]
    for i,row in enumerate(rows):
        methods=['planner','gray','ortools'] if len(row['specification']['variables'])<=20 else ['planner','ortools']
        entry={'case':row['name']}
        for method in methods:
            command=[sys.executable,__file__,'--case',str(i),'--method',method]
            run=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,check=True,timeout=120)
            entry[method]=json.loads(run.stdout)
        output.append(entry);print(json.dumps(entry),flush=True)
    receipt={'schema':'pp-planning-memory/1','cases':output,'measurement':'Linux ru_maxrss, fresh process per method and case, bytes',
             'scope':'peak process RSS including interpreter, imports, model compilation and five-query bank; OR-Tools optimization only; failures retain attempted compilation memory'}
    (ROOT/'receipts/planning/memory.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__':main()
