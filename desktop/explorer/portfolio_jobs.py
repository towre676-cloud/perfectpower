"""One cancellable persistent portfolio worker per Explorer session."""
import json
import os
import subprocess
import sys
import threading
import time
import uuid

class PortfolioJobs:
    def __init__(self,explorer):
        self.explorer=explorer;self.process=None;self.busy=threading.Lock()
    def close(self):
        if self.process and self.process.poll() is None:self.process.kill()
    def submit(self,body):
        if not self.busy.acquire(blocking=False):raise ValueError('A portfolio calculation is already running. Wait or cancel it first.')
        e=self.explorer;job=uuid.uuid4().hex;folder=e.state/'runs'/job;folder.mkdir()
        entry={'id':job,'status':'running','started':time.time(),'request':body}
        with e.lock:e.jobs[job]=entry
        def work():
            start=time.monotonic()
            try:
                if not self.process or self.process.poll() is not None:
                    env=os.environ.copy();env['PYTHONPATH']=str(e.root/'python');env['PYTHONUTF8']='1'
                    self.process=subprocess.Popen([sys.executable,'-m','perfectpower.portfolio_explorer'],cwd=e.root,env=env,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=(folder/'stderr.txt').open('w'),text=True,creationflags=0x08000000 if os.name=='nt' else 0)
                p=self.process
                with e.lock:entry['_process']=p
                if entry.get('cancel_requested'):p.kill()
                p.stdin.write(json.dumps({'body':body,'folder':str(folder)})+'\n');p.stdin.flush()
                timed_out=threading.Event()
                def timeout():
                    timed_out.set()
                    if p.poll() is None:p.kill()
                timer=threading.Timer(min(3600,max(5,int(body.get('timeout',1200)))),timeout);timer.start()
                try:line=p.stdout.readline()
                finally:timer.cancel()
                response=json.loads(line) if line else {'error':'Worker stopped; no complete result is inferred.'}
                status='cancelled' if entry.get('cancel_requested') else 'timeout' if timed_out.is_set() else 'failed' if 'error' in response else 'complete'
                entry.update(status=status,result=response.get('result'),error=response.get('error'),exit_code=0 if status=='complete' else 1)
                if status!='complete':self.close()
                (folder/'stdout.txt').write_text(json.dumps(response))
            except Exception as error:
                self.close();entry.update(status='cancelled' if entry.get('cancel_requested') else 'failed',error=str(error))
            finally:
                with e.lock:
                    entry.pop('_process',None);entry['elapsed']=time.monotonic()-start
                    entry['artifacts']=[{'name':p.name,'bytes':p.stat().st_size} for p in folder.iterdir() if p.is_file()]
                    (folder/'result.json').write_text(json.dumps(entry,indent=2))
                self.busy.release()
        threading.Thread(target=work,daemon=True).start();return {'id':job}
