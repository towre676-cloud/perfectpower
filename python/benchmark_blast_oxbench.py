#!/usr/bin/env python3
"""Run or replay complete OXBench pooled BLASTP evaluation."""
import argparse,gzip,lzma,json,os,subprocess,time,platform
from hashlib import sha256
from pathlib import Path
from perfectpower.blast_benchmark import load_dataset,evaluate,retain_reference_hits
from perfectpower.blast_io import tabular,FIELDS
from perfectpower.divisor_square import WorkLimit
ROOT=Path(__file__).resolve().parents[1];DATA=ROOT/'data/oxbench';OUT=ROOT/'receipts/blast/oxbench'
def digest(p):return sha256(p.read_bytes()).hexdigest()
def uncompressed_digest(path, byte_limit=250_000_000):
    """Hash the retained stream without allocating the complete decompressed output."""
    h=sha256();size=0
    with lzma.open(path,'rb') as stream:
        while chunk:=stream.read(1_048_576):
            size+=len(chunk)
            if size>byte_limit:raise WorkLimit('stream BLAST uncompressed byte budget exceeded')
            h.update(chunk)
    return h.hexdigest()
def write(p,obj):p.write_text(json.dumps(obj,indent=2,allow_nan=False)+'\n')
def main():
    p=argparse.ArgumentParser();p.add_argument('--run-blast',action='store_true');p.add_argument('--tasks',nargs='+',default=['blastp','blastp-fast'],choices=['blastp','blastp-fast']);p.add_argument('--blastp',default='blastp');p.add_argument('--timeout',type=int,default=600);p.add_argument('--threads',type=int,default=1);args=p.parse_args()
    manifest,records,groups,refs,mapping=load_dataset(DATA);OUT.mkdir(parents=True,exist_ok=True)
    fasta=''.join(f'>{k}\n{s}\n' for k,s in records.items());(DATA/'database.fasta').write_text(fasta)
    write(DATA/'records.json',mapping)
    protocol={'schema':'pp-oxbench-protocol/1','dataset_hash':manifest['retained_sha256'],'selection':'every ID in ox/info/ids.txt; no sampling','search':'all normalized occurrences against pooled database including all self hits','parameters':{'evalue':'0.001','coverage':'1/2','tasks':args.tasks,'seg':'yes','max_target_seqs':len(records),'max_hsps':'unlimited default (option omitted)','threads':args.threads,'timeout_seconds_per_task':args.timeout,'row_limit':2_000_000,'cell_limit_per_pair':1_000_000},'methods':['best bit-score single HSP','any single HSP','union HSP query intervals (incoherence allowed)','ordinary maximum-coverage BLAST-HSP DP','complete monotone nonoverlapping HSP chain existence with polynomial counts'],'annotation_independence':'structure-derived uppercase reference columns; labels withheld from BLAST and chain selection','precision_scope':'residue precision restricted to uppercase eligible reference residues. Cross-family membership is unknown; no retrieval precision or orthology score.','replicate_dependence':'sets may overlap and repeated sequences are retained as occurrences; unique count reported; macro family mean descriptive, no IID confidence interval'}
    write(OUT/'protocol.json',protocol)
    execution=json.loads((OUT/'execution.json').read_text()) if (OUT/'execution.json').exists() else {}
    for task in protocol['parameters']['tasks']:
        raw=DATA/(task+'.tsv');packed=DATA/(task+'.tsv.xz')
        if args.run_blast:
            command=[args.blastp,'-task',task,'-query',str(DATA/'database.fasta'),'-subject',str(DATA/'database.fasta'),'-evalue','0.001','-seg','yes','-max_target_seqs',str(len(records)),'-num_threads',str(args.threads),'-outfmt','6 '+' '.join(FIELDS)]
            start=time.perf_counter()
            result=subprocess.run(command,capture_output=True,text=True,timeout=args.timeout)
            execution[task]={'command':command,'seconds':time.perf_counter()-start,'returncode':result.returncode,'stderr':result.stderr,'version':subprocess.run([args.blastp,'-version'],check=True,capture_output=True,text=True).stdout,'executable_sha256':digest(Path(args.blastp)) if Path(args.blastp).is_file() else None,'platform':platform.platform()}
            write(OUT/'execution.json',execution)
            if result.returncode:raise RuntimeError('BLAST failed; incomplete run excluded')
            with packed.open('wb') as f:
                with lzma.LZMAFile(f,mode='wb',preset=6) as z:z.write(result.stdout.encode())
            if raw.exists(): raw.unlink()
        raw_digest=uncompressed_digest(packed)
        hits,stream_receipt=retain_reference_hits(packed,records,groups)
        start=time.perf_counter();receipt=evaluate(records,groups,refs,hits)
        receipt.update(stream_receipt)
        receipt.update({'dataset_sha256':manifest['retained_sha256'],'blast_output_sha256':digest(packed),'blast_uncompressed_sha256':raw_digest,'evaluation_seconds':time.perf_counter()-start,'task':task,'kernel_checked':False})
        write(OUT/(task+'-summary.json'),{k:v for k,v in receipt.items() if k not in ('pairs','families')})
        with (OUT/(task+'-evaluation.json.gz')).open('wb') as f:
            with gzip.GzipFile(fileobj=f,mode='wb',mtime=0) as z:z.write(json.dumps(receipt,sort_keys=True,allow_nan=False).encode())
        print(task,receipt['family_count'],receipt['record_count'],receipt['raw_hsps_replayed'],receipt['directed_positive_pairs'],receipt['totals'],flush=True)
if __name__=='__main__':main()
