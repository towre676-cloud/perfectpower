"""Offline, authenticated loopback service for the full PerfectPower checkout."""
import argparse, json, os, secrets, subprocess, sys, threading, time, uuid, mimetypes
from fractions import Fraction
from http.server import BaseHTTPRequestHandler,ThreadingHTTPServer
from pathlib import Path
from urllib.parse import urlparse,parse_qs,unquote
ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/'python'))

def safe_json(v):
    if isinstance(v,Fraction):return str(v)
    if isinstance(v,int) and not isinstance(v,bool):return str(v) if abs(v)>2**53-1 else v
    if isinstance(v,dict):return {str(k):safe_json(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)):return [safe_json(x) for x in v]
    return v

def scan(spec):
    from perfectpower.core import integer_power_root
    coeff=[Fraction(x) for x in spec['coeff']]
    d=int(spec.get('d',2));lo=int(spec.get('lo',-20));hi=int(spec.get('hi',20))
    if not coeff or len(coeff)>25 or not 2<=d<=32 or hi<lo or hi-lo>100000:raise ValueError('Use degree at most 24, power 2–32 and an interval of at most 100,001 inputs.')
    if max(abs(lo),abs(hi))>10**9:raise ValueError('Input magnitude must be at most one billion.')
    points=[];values=[]
    for x in range(lo,hi+1):
        v=Fraction(0)
        for c in reversed(coeff):v=v*x+c
        y=integer_power_root(v.numerator,d) if v.denominator==1 else None
        if y is not None:
            points.append([x,y])
            if d%2==0 and y:points.append([x,-y])
        if hi-lo<=2000:values.append([x,str(v)])
    return {'kind':'bounded exact enumeration','equation':{'coeff':list(map(str,coeff)),'d':d},'interval':[lo,hi],'count':len(points),'points':points,'values':values,'scope':'Complete in the displayed integer x interval. Plotting uses floating-point coordinates; the point test uses exact arithmetic.'}

class Explorer:
    def __init__(self,root=ROOT,state=None):
        self.root=Path(root);self.catalog=json.loads((self.root/'desktop/explorer/dist/catalog.json').read_text())
        self.paths={f['path'] for f in self.catalog['files']};self.jobs={};self.lock=threading.RLock()
        self.state=Path(state or os.environ.get('PP_EXPLORER_STATE',Path.home()/'PerfectPower Explorer'))
        self.state.mkdir(parents=True,exist_ok=True);(self.state/'runs').mkdir(exist_ok=True)
        self.budget=None
        self.portfolio=None
        from perfectpower.explorer_live import LiveResearch
        self.live_research=LiveResearch(self.root,self.state)
        for p in sorted((self.state/'runs').glob('*/result.json'))[-100:]:
            try:self.jobs[p.parent.name]=json.loads(p.read_text())
            except (OSError,ValueError):pass
    def resolve(self,path):
        if path not in self.paths:raise ValueError('Choose a file from the bundled repository.')
        p=(self.root/path).resolve()
        if not p.is_relative_to(self.root.resolve()):raise ValueError('Invalid repository path.')
        return p
    def submit(self,body):
        if not isinstance(body,dict):raise ValueError('Request object required.')
        if body.get('kind')=='portfolio':
            if self.portfolio is None:
                sys.path.insert(0,str(self.root/'desktop/explorer'))
                from portfolio_jobs import PortfolioJobs
                self.portfolio=PortfolioJobs(self)
            return self.portfolio.submit(body)
        job=uuid.uuid4().hex;folder=self.state/'runs'/job;folder.mkdir()
        entry={'id':job,'status':'running','started':time.time(),'request':body}
        with self.lock:self.jobs[job]=entry
        def work():
            start=time.monotonic();proc=None
            try:
                if body.get('kind')=='scan':
                    scan_input=folder/'scan.json';scan_input.write_text(json.dumps(body['spec']),encoding='utf8')
                    args=[str(Path(__file__).resolve()),'--scan',str(scan_input)]
                else:
                    if body.get('kind')=='script':
                        path=self.resolve(body['path'])
                        if path.suffix!='.py':raise ValueError('Only a selected Python source file can run.')
                        args=[str(path),*body.get('args',[])]
                    else:
                        args=body.get('args')
                        if not isinstance(args,list) or not args or any(not isinstance(x,str) or len(x)>100000 for x in args):raise ValueError('Command arguments must be strings.')
                        if args[0] not in self.catalog['commands']:raise ValueError('Choose an available PerfectPower command.')
                        if args[0] in ('service','budget-lab'):raise ValueError('Open these services from the Visual Library instead.')
                        module=self.catalog['commands'][args[0]].get('module','perfectpower')
                        args=['-m',module,*(args[1:] if module!='perfectpower' else args)]
                files=body.get('files',{})
                if not isinstance(files,dict) or len(files)>8:raise ValueError('At most eight input files per run.')
                mapping={}
                for name,content in files.items():
                    if not isinstance(content,str) or len(content)>2000000:raise ValueError('Input file exceeds two million characters.')
                    if Path(name).name!=name or name in ('.','..'):raise ValueError('Input filename required.')
                    p=folder/name;p.write_text(content,encoding='utf8');mapping['@'+name]=str(p)
                args=[mapping.get(x,str(self.resolve(x)) if x in self.paths else x) for x in args]
                for index,argument in enumerate(args[:-1]):
                    if argument in ('--output','--out','--certificate-output','--lean-output'):
                        value=args[index+1]
                        if not Path(value).is_absolute():
                            target=(folder/value).resolve()
                            if not target.is_relative_to(folder.resolve()):raise ValueError('Relative outputs must stay inside this run folder.')
                            target.parent.mkdir(parents=True,exist_ok=True);args[index+1]=str(target)
                env=os.environ.copy();env['PYTHONPATH']=str(self.root/'python');env['PYTHONUTF8']='1';env['PP_EXPLORER_RUN_DIR']=str(folder)
                proc=subprocess.Popen([sys.executable,*args],cwd=self.root,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,creationflags=0x08000000 if os.name=='nt' else 0)
                with self.lock:entry['_process']=proc
                stdout_b,stderr_b=proc.communicate(timeout=min(3600,max(5,int(body.get('timeout',300)))))
                stdout=stdout_b.decode('utf8','replace');stderr=stderr_b.decode('utf8','replace');code=proc.returncode
                try:result=json.loads(stdout)
                except ValueError:result=None
                with self.lock:
                    entry['artifacts']=[{'name':p.relative_to(folder).as_posix(),'bytes':p.stat().st_size} for p in folder.rglob('*') if p.is_file()]
                    entry.update(status='cancelled' if entry.get('cancel_requested') else 'complete' if code==0 else 'failed',elapsed=time.monotonic()-start,exit_code=code,result=result,stdout=stdout[:8_000_000],stderr=stderr[:1_000_000])
                    entry.pop('_process',None)
                (folder/'stdout.txt').write_text(stdout,encoding='utf8');(folder/'stderr.txt').write_text(stderr,encoding='utf8')
            except subprocess.TimeoutExpired:
                if proc:proc.kill();proc.communicate()
                entry.update(status='timeout',elapsed=time.monotonic()-start,error='Run reached its selected time limit. No complete answer is inferred.')
            except Exception as e:entry.update(status='failed',elapsed=time.monotonic()-start,error=str(e))
            finally:
                with self.lock:entry.pop('_process',None);(folder/'result.json').write_text(json.dumps(safe_json(entry),indent=2,default=str),encoding='utf8')
        threading.Thread(target=work,daemon=True).start();return {'id':job}
    def public_job(self,job,detail=True):
        def preview(v):
            if isinstance(v,list):return [preview(x) for x in v[:250]]
            if isinstance(v,dict):return {k:preview(x) for k,x in list(v.items())[:250]}
            if isinstance(v,str):return v[:25000]
            return v
        with self.lock:
            result={k:v for k,v in self.jobs[job].items() if not k.startswith('_')}
            if not detail:
                result={k:v for k,v in result.items() if k not in ('result','stdout','stderr')}
                result['request']={k:v for k,v in result.get('request',{}).items() if k!='files'}
            else:
                result=preview(result)
                result['preview_limits']='Large arrays and strings are shortened in this preview. The exported files contain the complete saved output.'
            progress=self.state/'runs'/job/'progress.json'
            if result.get('status')=='running' and progress.is_file():
                try:result['progress']=json.loads(progress.read_text())
                except (OSError,ValueError):pass
            return safe_json(result)
    def close(self):
        if self.portfolio:self.portfolio.close()
        with self.lock:
            for job in self.jobs.values():
                p=job.get('_process')
                if p and p.poll() is None:p.kill()

def handler(explorer,token):
    class Handler(BaseHTTPRequestHandler):
        def respond(self,status,data,mime='application/json; charset=utf-8',extra=()):
            raw=json.dumps(safe_json(data),ensure_ascii=False,default=str).encode() if mime.startswith('application/json') else data
            self.send_response(status);self.send_header('Content-Type',mime);self.send_header('Content-Length',str(len(raw)));self.send_header('Cache-Control','no-store');self.send_header('X-Content-Type-Options','nosniff')
            for k,v in extra:self.send_header(k,v)
            self.end_headers();self.wfile.write(raw)
        def authorized(self):
            host=self.headers.get('Host','')
            if host not in (f'127.0.0.1:{self.server.server_port}',f'localhost:{self.server.server_port}'):return False
            return secrets.compare_digest(self.headers.get('X-Explorer-Token',''),token) or any(secrets.compare_digest(part.strip(),'pp_session='+token) for part in self.headers.get('Cookie','').split(';'))
        def do_GET(self):
            u=urlparse(self.path);q=parse_qs(u.query);path=unquote(u.path)
            if path=='/' and secrets.compare_digest(q.get('session',[''])[0],token):
                self.respond(302,b'','text/plain',[('Set-Cookie',f'pp_session={token}; HttpOnly; SameSite=Strict; Path=/'),('Location','/')]);return
            if not self.authorized():self.respond(403,{'error':'Open the application to start a local session.'});return
            try:
                if path=='/api/catalog':self.respond(200,explorer.catalog)
                elif path=='/api/portfolio/draft':
                    draft=explorer.state/'portfolio-draft.json'
                    self.respond(200,json.loads(draft.read_text()) if draft.is_file() else None)
                elif path=='/api/portfolio/model':
                    from perfectpower.portfolio_explorer import model
                    self.respond(200,model(explorer.root))
                elif path=='/api/research':self.respond(200,explorer.live_research.get(q.get('refresh',['0'])[0]=='1'))
                elif path=='/api/search':
                    needle=q.get('q',[''])[0].lower()
                    if len(needle)<3:raise ValueError('Use at least three characters for content search.')
                    matches=[]
                    for record in explorer.catalog['files']:
                        if record['kind']=='visual' or not record['path'].endswith(('.md','.lean','.py','.json','.txt','.csv','.cpp','.c','.h','.ts','.tsx','.js','.log','.smt2','.seq','.cnf')):continue
                        p=explorer.resolve(record['path']);tail=''
                        with p.open('r',encoding='utf8',errors='replace') as stream:
                            while True:
                                chunk=stream.read(65536)
                                if not chunk:break
                                text=tail+chunk;hit=text.lower().find(needle)
                                if hit>=0:
                                    matches.append(dict(record,summary=text[max(0,hit-70):hit+180].replace('\n',' ')));break
                                tail=text[-len(needle):]
                        if len(matches)>=40:break
                    self.respond(200,matches)
                elif path=='/api/jobs':self.respond(200,[explorer.public_job(j,detail=False) for j in list(explorer.jobs)[-100:]][::-1])
                elif path=='/api/job':self.respond(200,explorer.public_job(q['id'][0]))
                elif path=='/api/file':
                    p=explorer.resolve(q['path'][0]);offset=max(0,int(q.get('offset',['0'])[0]));size=p.stat().st_size
                    with p.open('rb') as f:f.seek(offset);raw=f.read(1000000)
                    self.respond(200,{'path':q['path'][0],'content':raw.decode('utf8','replace'),'offset':offset,'next':offset+len(raw) if offset+len(raw)<size else None,'bytes':size})
                elif path=='/api/elections':
                    from perfectpower.budget_lab import BudgetLab
                    if explorer.budget is None:explorer.budget=BudgetLab(explorer.root)
                    self.respond(200,explorer.budget.elections())
                elif path.startswith('/repo/'):
                    p=explorer.resolve(path[6:]);self.respond(200,p.read_bytes(),(mimetypes.guess_type(p.name)[0] or 'application/octet-stream'))
                elif path.startswith('/run/'):
                    bits=path[5:].split('/')
                    if len(bits)<2 or bits[0] not in explorer.jobs:raise ValueError('Unknown run file.')
                    filename='/'.join(bits[1:])
                    allowed={'stdout.txt','stderr.txt','result.json'}|{a['name'] for a in explorer.jobs[bits[0]].get('artifacts',[])}
                    if filename not in allowed:raise ValueError('Unknown run artifact.')
                    p=(explorer.state/'runs'/bits[0]/filename).resolve()
                    if not p.is_relative_to((explorer.state/'runs'/bits[0]).resolve()):raise ValueError('Invalid artifact path.')
                    inline=q.get('view',['0'])[0]=='1'
                    self.respond(200,p.read_bytes(),(mimetypes.guess_type(filename)[0] or 'application/octet-stream') if inline else 'application/octet-stream',[] if inline else [('Content-Disposition','attachment; filename='+Path(filename).name)])
                else:
                    name='index.html' if path=='/' else path.lstrip('/')
                    p=(explorer.root/'desktop/explorer/dist'/name).resolve()
                    if not p.is_relative_to((explorer.root/'desktop/explorer/dist').resolve()) or not p.is_file():self.respond(404,{'error':'Unknown page.'});return
                    self.respond(200,p.read_bytes(),mimetypes.guess_type(p.name)[0] or 'application/octet-stream')
            except (OSError,ValueError,KeyError,TypeError) as e:self.respond(400,{'error':str(e)})
        def do_POST(self):
            if not self.authorized():self.respond(403,{'error':'Local session required.'});return
            origin=self.headers.get('Origin')
            if origin and origin!=f'http://127.0.0.1:{self.server.server_port}':self.respond(403,{'error':'Local origin required.'});return
            try:
                size=int(self.headers.get('Content-Length','0'))
                if not 0<size<=4000000:raise ValueError('Request exceeds four million bytes.')
                body=json.loads(self.rfile.read(size))
                if self.path=='/api/portfolio/draft':
                    if not isinstance(body,dict) or set(body)!={'source','resources','prefix'}:raise ValueError('Portfolio draft required')
                    from perfectpower.portfolio_explorer import model
                    if body['source']!=model(explorer.root)['source_sha256']:raise ValueError('Draft source changed')
                    if not isinstance(body['prefix'],list) or len(body['prefix'])>50 or any(type(x) is not int or x not in (0,1) for x in body['prefix']):raise ValueError('Binary project decisions required')
                    if not isinstance(body['resources'],list) or len(body['resources'])!=5:raise ValueError('Five resource bounds required')
                    with explorer.lock:
                        target=explorer.state/'portfolio-draft.json';temp=target.with_suffix('.tmp');temp.write_text(json.dumps(body));temp.replace(target)
                    self.respond(200,{'saved':True})
                elif self.path=='/api/run':self.respond(200,explorer.submit(body))
                elif self.path=='/api/cancel':
                    with explorer.lock:
                        job=explorer.jobs[body['id']];p=job.get('_process');job['cancel_requested']=True
                        if p:p.kill()
                    self.respond(200,{'cancel_requested':p is not None})
                elif self.path=='/api/query':
                    from perfectpower.budget_lab import BudgetLab
                    if explorer.budget is None:explorer.budget=BudgetLab(explorer.root)
                    self.respond(200,explorer.budget.query(body))
                else:self.respond(404,{'error':'Unknown operation.'})
            except Exception as e:self.respond(400,{'error':str(e)})
        def log_message(self,*args):pass
    return Handler

def main():
    if len(sys.argv)==3 and sys.argv[1]=='--scan':
        print(json.dumps(safe_json(scan(json.loads(Path(sys.argv[2]).read_text())))));return
    p=argparse.ArgumentParser();p.add_argument('--port',type=int,default=0);p.add_argument('--state');p.add_argument('--no-browser',action='store_true');args=p.parse_args()
    token=secrets.token_urlsafe(32);explorer=Explorer(state=args.state);server=ThreadingHTTPServer(('127.0.0.1',args.port),handler(explorer,token))
    url=f'http://127.0.0.1:{server.server_port}/?session={token}'
    print(json.dumps({'url':url,'port':server.server_port}),flush=True)
    if not args.no_browser:
        import webbrowser
        webbrowser.open(url)
    if args.no_browser:
        def shutdown_on_eof():
            try:sys.stdin.read()
            finally:explorer.close();server.shutdown()
        threading.Thread(target=shutdown_on_eof,daemon=True).start()
    try:server.serve_forever()
    finally:explorer.close();server.server_close()
if __name__=='__main__':main()
