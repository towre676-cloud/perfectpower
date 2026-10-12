"""Android host for the unmodified PerfectPower repository engines."""
import importlib.util, json, os, secrets, sys, threading, time, uuid, traceback, runpy
from pathlib import Path
from http.server import ThreadingHTTPServer
_servers={}

def stop(url):
    item=_servers.pop(str(url),None)
    if item:
        explorer,server=item;explorer.close();server.shutdown();server.server_close()

def load_server(root):
    sys.path.insert(0,str(Path(root)/'python'))
    spec=importlib.util.spec_from_file_location('pp_desktop_server',Path(root)/'desktop/explorer/server.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    return module

def execute(payload):
    """Called in a separate Android process. Full output is written to private storage."""
    request=json.loads(str(payload));root=Path(request['root']);folder=Path(request['folder']);body=request['body']
    os.chdir(root);sys.path.insert(0,str(root/'python'));os.environ['PP_EXPLORER_RUN_DIR']=str(folder)
    os.environ['PP_NATIVE_DIR']=str(root/'mobile-native'/request['abi'])
    desktop=load_server(root);args=body.get('args',[])
    # NumPy 2 renamed trapz to trapezoid without changing this operation's API.
    # Keep the repository source intact while supporting its spelling on Android.
    import numpy as np
    if not hasattr(np,'trapezoid'):np.trapezoid=np.trapz
    catalog=json.loads((root/'desktop/explorer/dist/catalog.json').read_text())
    paths={f['path'] for f in catalog['files']}
    mapping={};files=body.get('files',{})
    if not isinstance(files,dict) or len(files)>8:raise ValueError('At most eight input files per run.')
    for name,content in files.items():
        if Path(name).name!=name or name in ('.','..') or not isinstance(content,str) or len(content)>2000000:raise ValueError('Invalid input file.')
        p=folder/name;p.write_text(content,encoding='utf8');mapping['@'+name]=str(p)
    if body.get('kind')!='scan':
        if not isinstance(args,list) or any(not isinstance(x,str) or len(x)>100000 for x in args):raise ValueError('Arguments must be strings.')
        args=[mapping.get(x,str(root/x) if x in paths else x) for x in args]
        for i,arg in enumerate(args[:-1]):
            if arg in ('--output','--out','--certificate-output','--lean-output'):
                target=Path(args[i+1]);target=target if target.is_absolute() else folder/target
                target=target.resolve()
                if not target.is_relative_to(folder.resolve()):raise ValueError('Outputs must stay in this run folder.')
                target.parent.mkdir(parents=True,exist_ok=True);args[i+1]=str(target)
    code=0;error=None
    import contextlib
    with (folder/'stdout.txt').open('w',encoding='utf8') as out,(folder/'stderr.txt').open('w',encoding='utf8') as err,contextlib.redirect_stdout(out),contextlib.redirect_stderr(err):
        try:
            if body.get('kind')=='scan':print(json.dumps(desktop.safe_json(desktop.scan(body['spec']))))
            elif body.get('kind')=='budget':
                from perfectpower.budget_lab import BudgetLab
                print(json.dumps(desktop.safe_json(BudgetLab(root).query(body['query']))))
            elif body.get('kind')=='script':
                path=body['path']
                if path not in paths or not path.endswith('.py'):raise ValueError('Select a bundled Python script.')
                sys.argv=[str(root/path),*args];runpy.run_path(str(root/path),run_name='__main__')
            else:
                if not args or args[0] not in catalog['commands']:raise ValueError('Select a bundled command.')
                if args[0] in ('service','budget-lab'):raise ValueError('Open Budget Lab in the Visual Library. The server command is unnecessary inside the app.')
                module=catalog['commands'][args[0]].get('module','perfectpower')
                sys.argv=[module,*(args[1:] if module!='perfectpower' else args)]
                runpy.run_module(module,run_name='__main__')
        except SystemExit as e:code=e.code if isinstance(e.code,int) else 1 if e.code else 0
        except BaseException as e:
            code=1;error=str(e);traceback.print_exc()
            if isinstance(e,(ImportError,FileNotFoundError)):error='This operation requires an unavailable dependency or external tool: '+str(e)+'. Its source and inputs are retained in the repository.'
    return json.dumps({'exit_code':code,'error':error})

def start(root,state,runner,abi):
    desktop=load_server(root)
    class MobileExplorer(desktop.Explorer):
        def submit(self,body):
            if not isinstance(body,dict):raise ValueError('Request object required.')
            job=uuid.uuid4().hex;folder=self.state/'runs'/job;folder.mkdir()
            entry={'id':job,'status':'running','started':time.time(),'request':body}
            class Process:
                def kill(self):runner.cancel(job)
                def poll(self):return None if entry['status']=='running' else 0
            entry['_process']=Process()
            with self.lock:self.jobs[job]=entry
            (folder/'result.json').write_text(json.dumps(desktop.safe_json({k:v for k,v in entry.items() if not k.startswith('_')}),indent=2),encoding='utf8')
            def work():
                begun=time.monotonic()
                try:
                    response=json.loads(str(runner.execute(json.dumps({'root':str(self.root),'folder':str(folder),'body':body,'abi':abi,'id':job}),min(3600,max(5,int(body.get('timeout',300)))))))
                    stdout=(folder/'stdout.txt').read_text(encoding='utf8') if (folder/'stdout.txt').exists() else ''
                    stderr=(folder/'stderr.txt').read_text(encoding='utf8') if (folder/'stderr.txt').exists() else ''
                    try:result=json.loads(stdout)
                    except ValueError:result=None
                    entry.update(status='cancelled' if entry.get('cancel_requested') else response.get('status') or ('complete' if response.get('exit_code')==0 else 'failed'),exit_code=response.get('exit_code'),error=response.get('error'),stdout=stdout[:8000000],stderr=stderr[:1000000],result=result)
                except Exception as e:entry.update(status='cancelled' if entry.get('cancel_requested') else 'failed',error=str(e))
                finally:
                    with self.lock:
                        entry.update(elapsed=time.monotonic()-begun,artifacts=[{'name':p.relative_to(folder).as_posix(),'bytes':p.stat().st_size} for p in folder.rglob('*') if p.is_file()])
                        entry.pop('_process',None);(folder/'result.json').write_text(json.dumps(desktop.safe_json(entry),indent=2,default=str),encoding='utf8')
            threading.Thread(target=work,daemon=True).start();return {'id':job}
    explorer=MobileExplorer(root,state)
    # Interrupted process state never masquerades as a completed run.
    for entry in explorer.jobs.values():
        if entry.get('status')=='running':
            entry.update(status='interrupted',error='Android stopped this run. Replay it to compute a fresh result.')
            (explorer.state/'runs'/entry['id']/'result.json').write_text(json.dumps(desktop.safe_json(entry),indent=2),encoding='utf8')
    token=secrets.token_urlsafe(32);base=desktop.handler(explorer,token)
    class Handler(base):
        def do_POST(self):
            if self.path!='/api/query':return super().do_POST()
            if not self.authorized():return self.respond(403,{'error':'Local session required.'})
            origin=self.headers.get('Origin')
            if origin and origin!=f'http://127.0.0.1:{self.server.server_port}':return self.respond(403,{'error':'Local origin required.'})
            try:
                length=int(self.headers.get('Content-Length','0'))
                if not 0<length<=4000000:raise ValueError('Invalid request length.')
                job=explorer.submit({'kind':'budget','query':json.loads(self.rfile.read(length)),'timeout':300})['id']
                while explorer.jobs[job]['status']=='running':time.sleep(.05)
                entry=explorer.jobs[job]
                if entry['status']!='complete':raise ValueError(entry.get('error') or entry.get('stderr') or entry['status'])
                self.respond(200,entry['result'])
            except Exception as e:self.respond(400,{'error':str(e)})
    server=ThreadingHTTPServer(('127.0.0.1',0),Handler)
    threading.Thread(target=server.serve_forever,daemon=True).start()
    url=f'http://127.0.0.1:{server.server_port}/?session={token}'
    _servers[url]=(explorer,server)
    return url
