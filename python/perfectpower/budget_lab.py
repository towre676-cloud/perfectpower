"""Local browser workbench for exact public participatory-budgeting portfolios."""
import argparse
import json
from http.server import BaseHTTPRequestHandler,HTTPServer
from pathlib import Path
from .resources import runtime_root
from .participatory_budgeting import BudgetElection,BudgetSession
from .divisor_square import WorkLimit

class BudgetLab:
    def __init__(self,root=None):
        root=runtime_root() if root is None else Path(root)
        self.root=root;self.manifest=json.loads((root/'data/participatory_budgeting/manifest.json').read_text());self.sessions={}
    def session(self,name):
        row=next((r for r in self.manifest['files'] if r['id']==name),None)
        if row is None:raise ValueError('unknown election')
        if name not in self.sessions:
            e=BudgetElection((self.root/'data/participatory_budgeting/raw'/row['filename']).read_bytes().decode('utf8'),row)
            if e.sha256!=row['sha256']:raise ValueError('election snapshot hash differs')
            self.sessions[name]=BudgetSession(e)
        return self.sessions[name]
    def elections(self):
        return [{'id':r['id'],'filename':r['filename'],'summary':self.session(r['id']).election.summary(),'projects':self.session(r['id']).election.projects} for r in self.manifest['files']]
    def query(self,body):
        if not isinstance(body,dict) or set(body)!= {'election','request'}:raise ValueError('election and request required')
        request=body['request']
        if not isinstance(request,dict):raise ValueError('request object required')
        request=dict(request)
        for k in ('budget','rank','seed'):
            if k in request and isinstance(request[k],str):
                raw=request[k]
                if len(raw)>24 or not raw or raw.lstrip('-').isdigit() is False or str(int(raw))!=raw:raise ValueError('canonical decimal integer required')
                request[k]=int(raw)
        return self.session(body['election']).evaluate(request)

def json_safe(value):
    if isinstance(value,list):return [json_safe(v) for v in value]
    if isinstance(value,dict):return {k:str(v) if k in ('count','maximizer_count','rank','budget') and type(v) is int else json_safe(v) for k,v in value.items()}
    return value

def handler(lab):
    class Handler(BaseHTTPRequestHandler):
        def reply(self,status,value,mime='application/json; charset=utf-8'):
            body=json.dumps(json_safe(value),ensure_ascii=False).encode('utf8') if mime.startswith('application/json') else value
            self.send_response(status);self.send_header('Content-Type',mime);self.send_header('Content-Length',str(len(body)));self.send_header('Cache-Control','no-store');self.end_headers();self.wfile.write(body)
        def do_GET(self):
            try:
                if self.path=='/':self.reply(200,(lab.root/'web/budget-lab/index.html').read_bytes(),'text/html; charset=utf-8')
                elif self.path=='/api/elections':self.reply(200,lab.elections())
                else:self.reply(404,{'error':'unknown route'})
            except (ValueError,OSError,KeyError) as e:self.reply(400,{'error':str(e)})
        def do_POST(self):
            try:
                if self.path!='/api/query':self.reply(404,{'error':'unknown route'});return
                origin=self.headers.get('Origin')
                if origin and origin not in (f'http://127.0.0.1:{self.server.server_port}',f'http://localhost:{self.server.server_port}'):raise ValueError('local workbench origin required')
                if self.headers.get('Content-Type','').split(';')[0]!='application/json':raise ValueError('JSON content type required')
                size=int(self.headers.get('Content-Length','0'))
                if not 0<size<=65536:raise ValueError('bounded JSON request required')
                self.reply(200,lab.query(json.loads(self.rfile.read(size))))
            except WorkLimit as e:self.reply(422,{'error':str(e),'status':'WORK_LIMIT'})
            except (ValueError,TypeError,KeyError) as e:self.reply(400,{'error':str(e)})
        def log_message(self,*args):pass
    return Handler

def add_commands(sub):
    p=sub.add_parser('budget-lab',help='serve the public budgeting workbench on localhost');p.add_argument('--port',type=int,default=8765)

def cli(args):
    if args.command!='budget-lab':return False
    if not 0<=args.port<=65535:raise ValueError('port 0..65535 required')
    server=HTTPServer(('127.0.0.1',args.port),handler(BudgetLab()))
    print(f'Budget Lab: http://127.0.0.1:{server.server_port}/',flush=True)
    try:server.serve_forever()
    except KeyboardInterrupt:pass
    finally:server.server_close()
    return True
