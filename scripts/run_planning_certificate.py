"""Reproduce source-bound trace generation/replay with explicit resource limits."""
import argparse
import json
from pathlib import Path
import resource
import subprocess
import sys
import tempfile
import time
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'python'))
from perfectpower.planning_certificate import digest, verify
from verify_planning_independent import original_cases,bdd_input


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--case',type=int,default=50)
    p.add_argument('--certificate',type=Path,required=True)
    p.add_argument('--nodes',type=int,default=40000000)
    p.add_argument('--timeout',type=int,default=600)
    p.add_argument('--memory-mib',type=int,default=6144)
    p.add_argument('--receipt',type=Path,default=ROOT/'receipts/planning/independent/certificate_run.json')
    args=p.parse_args()
    weights,caps,_,_=original_cases()[args.case]
    text,order=bdd_input(weights,caps)
    rows=[[weights[j][k] for j in order] for k in range(len(caps))]
    certificate=args.certificate.resolve();certificate.parent.mkdir(parents=True,exist_ok=True)
    def limits():resource.setrlimit(resource.RLIMIT_AS,(args.memory_mib*1024**2,)*2)
    with tempfile.TemporaryDirectory() as tmp:
        binary=Path(tmp)/'bdd'
        subprocess.run(['g++','-O3','-std=c++17',str(ROOT/'native/independent_planning_bdd.cpp'),'-o',str(binary)],check=True)
        start=time.perf_counter()
        run=subprocess.run([str(binary),str(args.nodes),str(certificate)],input=text,text=True,capture_output=True,timeout=args.timeout,preexec_fn=limits)
        if run.returncode:raise RuntimeError(run.stdout+run.stderr)
        generated=json.loads(run.stdout)
        generation_seconds=time.perf_counter()-start
    start=time.perf_counter();replay=verify(certificate,rows,caps);seconds=time.perf_counter()-start
    if generated['count']!=replay['count']:raise RuntimeError('Generator/checker disagreement')
    result={'schema':'pp-bdd-certificate-run/1','case':args.case,'source_order_original_indices':order,
            'raw_source_sha256':digest(ROOT/'data/planning/mknap1.txt'),
            'sources':{name:digest(ROOT/name) for name in ('native/independent_planning_bdd.cpp','native/planning_certificate_trace.hpp','python/perfectpower/planning_certificate.py','scripts/run_planning_certificate.py')},
            'certificate':{'bytes':certificate.stat().st_size,'sha256':digest(certificate)},
            'generator':generated,'generation_seconds':generation_seconds,'diagnostics':run.stderr,
            'checker':replay,'checking_seconds':seconds,
            'full_unrestricted_population_kernel_proved':False}
    args.receipt.parent.mkdir(parents=True,exist_ok=True)
    args.receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))


if __name__=='__main__':main()
