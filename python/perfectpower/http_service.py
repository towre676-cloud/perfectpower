"""Bounded loopback HTTP service with a serial, terminable query process."""
from http.server import BaseHTTPRequestHandler,ThreadingHTTPServer
import json
import socket
import threading
from pathlib import Path
from .resources import runtime_root
from .catalogue import Catalogue,encoded
from .query_service import dispatch
from .bounded_dispatch import BoundedDispatcher,QueryDeadline,QueryFailure

CLIENT='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>PerfectPower objects</title>
<style>body{font:17px system-ui;max-width:1050px;margin:40px auto;padding:0 24px;background:#f4f7f8;color:#173348}h1{font-size:32px}p{line-height:1.6}button,select{font:inherit;padding:8px;margin:8px 8px 8px 0}textarea{box-sizing:border-box;width:100%;min-height:240px;padding:18px;font:15px monospace;border:1px solid #bdcbd4;border-radius:8px}pre{white-space:pre-wrap;overflow-wrap:anywhere;background:white;padding:20px;border-radius:8px}#status{font-weight:bold}</style>
<h1>Exact object console</h1><p>Register a definition once, then query it by name. Results retain exact integers and rational values. Your catalogue persists between sessions. <a href="/atlas">Enter the interactive room of possibilities</a>.</p>
<select id="example" aria-label="Request example"><option value="register">Register sizes</option><option value="count">Count sizes</option><option value="page">View a page</option><option value="compare">Register a comparison</option><option value="partition">Count comparison parts</option><option value="transport">Move an address</option><option value="list">List objects</option></select><button id="load">Load example</button>
<textarea id="request" aria-label="JSON request"></textarea><button id="run">Run query</button><span id="status" role="status"></span><pre id="result">Choose an example to begin.</pre>
<script>
const examples={register:{op:'register',kind:'population',name:'sizes',specification:{kind:'domain',predicate:{op:'and',args:[{poly:[-1,1],relation:'>='},{poly:[-1000,1],relation:'<='}]},fields:{square_side:[0,0,0,1],cube_side:[0,0,1]}}},count:{op:'call',object:'sizes',method:'count'},page:{op:'call',object:'sizes',method:'page',args:{start:500,size:5}},list:{op:'list'}};
const request=document.getElementById('request'),status=document.getElementById('status'),result=document.getElementById('result');
examples.compare={op:'register',kind:'population_comparison',name:'comparison',specification:{universe:{kind:'domain',fields:{n:[0,1]},predicate:{op:'and',args:[{poly:[0,1],relation:'>='},{poly:[-100,1],relation:'<='}]}},left:{poly:[0,1],modulus:2,relation:'=',value:0},right:{poly:[-25,1],relation:'>='}}};
examples.partition={op:'call',object:'comparison',method:'summary'};
examples.transport={op:'call',object:'comparison',method:'transport',args:{source:'left',rank:20,target:'right'}};
document.getElementById('load').onclick=()=>{request.value=JSON.stringify(examples[document.getElementById('example').value],null,2)};
document.getElementById('run').onclick=async()=>{status.textContent='Running';try{JSON.parse(request.value);const response=await fetch('/query',{method:'POST',headers:{'Content-Type':'application/json'},body:request.value});const body=await response.text();result.textContent=body;status.textContent=response.ok?'Complete':'Request failed'}catch(e){status.textContent='Request failed';result.textContent=String(e)}};
document.getElementById('load').click();
</script></html>'''


class QueryHTTPServer(ThreadingHTTPServer):
    daemon_threads=True
    block_on_close=False
    request_queue_size=128
    def __init__(self,database,port=0,*,request_timeout=5,query_timeout=30,max_clients=32):
        if type(request_timeout) not in (int,float) or not 0<request_timeout<=600:
            raise ValueError('request timeout must be positive and at most 600 seconds')
        if type(max_clients) is not int or not 1<=max_clients<=128:
            raise ValueError('client limit must be 1 through 128')
        self.dispatcher=BoundedDispatcher(database,query_timeout)
        self.request_timeout=request_timeout;self.clients=threading.BoundedSemaphore(max_clients)
        super().__init__(('127.0.0.1',port),QueryHandler)
        self.atlas=runtime_root()/'web/room-of-possibilities/PerfectPower-Room-of-Possibilities.html'

    def process_request(self,request,address):
        if not self.clients.acquire(blocking=False):
            try:request.sendall(b'HTTP/1.0 503 Service Unavailable\r\nContent-Length: 0\r\nConnection: close\r\n\r\n')
            except OSError:pass
            self.shutdown_request(request);return
        try:super().process_request(request,address)
        except BaseException:self.clients.release();raise

    def process_request_thread(self,request,address):
        try:super().process_request_thread(request,address)
        finally:self.clients.release()

    def server_close(self):
        self.dispatcher.close()
        super().server_close()


class QueryHandler(BaseHTTPRequestHandler):
    def setup(self):
        self.request.settimeout(self.server.request_timeout)
        super().setup()
        self.body_timer=threading.Timer(self.server.request_timeout,self.expire_request)
        self.body_timer.daemon=True;self.body_timer.start()

    def expire_request(self):
        try:self.request.shutdown(socket.SHUT_RDWR)
        except OSError:pass

    def finish(self):
        if hasattr(self,'body_timer'):self.body_timer.cancel()
        super().finish()

    def log_message(self,*args):pass

    def allowed(self):
        port=self.server.server_port
        hosts={f'127.0.0.1:{port}',f'localhost:{port}'}
        host=self.headers.get('Host','')
        origin=self.headers.get('Origin')
        return host in hosts and (origin is None or origin in {'http://'+h for h in hosts})

    def answer(self,code,value,html=False):
        data=(value if html else encoded(value)).encode()
        try:
            self.send_response(code);self.send_header('Content-Type','text/html; charset=utf-8' if html else 'application/json; charset=utf-8')
            self.send_header('Content-Length',str(len(data)));self.send_header('Cache-Control','no-store');self.end_headers()
            self.wfile.write(data)
        except (BrokenPipeError,ConnectionResetError,socket.timeout):self.close_connection=True

    def do_GET(self):
        self.body_timer.cancel()
        if not self.allowed():self.answer(403,{'error':'unsupported host or origin'});return
        if self.path=='/':self.answer(200,CLIENT,html=True)
        elif self.path=='/atlas':
            if self.server.atlas.is_file():self.answer(200,self.server.atlas.read_text(encoding='utf-8'),html=True)
            else:self.answer(404,{'error':'atlas runtime asset unavailable; reinstall the complete wheel'})
        elif self.path=='/health':self.answer(200,{'schema':'pp-http-health/1','ok':True})
        else:self.answer(404,{'error':'unknown route'})

    def do_POST(self):
        if not self.allowed():self.answer(403,{'error':'unsupported host or origin'});return
        if self.path!='/query':self.answer(404,{'error':'unknown route'});return
        identity=None
        try:
            size=int(self.headers.get('Content-Length','-1'))
            if not 0<=size<=1000000:self.close_connection=True;self.answer(413,{'error':'body exceeds one-megabyte budget'});return
            if self.headers.get('Content-Type','').split(';')[0]!='application/json':self.answer(415,{'error':'JSON content type required'});return
            if self.headers.get('Transfer-Encoding'):self.answer(400,{'error':'transfer encoding unsupported'});return
            body=self.rfile.read(size)
            self.body_timer.cancel()
            if len(body)!=size:raise ValueError('incomplete request body')
            request=json.loads(body)
            if isinstance(request,dict):identity=request.get('request_id')
            result=self.server.dispatcher.call(request)
            self.answer(200,dict(schema='pp-query-response/1',request_id=identity,ok=True,result=json.loads(result)))
        except socket.timeout:
            self.close_connection=True;self.answer(408,{'error':'request body deadline exceeded'})
        except QueryDeadline as error:
            self.answer(504,dict(schema='pp-query-response/1',request_id=identity,ok=False,
                error=dict(type='QueryDeadline',message=str(error))))
        except QueryFailure as error:
            self.answer(400,dict(schema='pp-query-response/1',request_id=identity,ok=False,
                error=dict(type=error.name,message=error.message)))
        except RuntimeError as error:
            self.answer(503,dict(schema='pp-query-response/1',request_id=identity,ok=False,
                error=dict(type='WorkerUnavailable',message=str(error))))
        except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,RecursionError) as error:
            self.answer(400,dict(schema='pp-query-response/1',request_id=identity,ok=False,error=dict(type=type(error).__name__,message=str(error))))


def run(database,port):
    with QueryHTTPServer(database,port) as server:
        print(f'PerfectPower console: http://127.0.0.1:{server.server_port}',flush=True)
        try:server.serve_forever()
        except KeyboardInterrupt:pass
