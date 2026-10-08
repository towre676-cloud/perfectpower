"""Concurrent clients against the serialized loopback query server.

Exact per-request replay and persisted catalogue checks accompany timings.
This is not a multi-worker SQLite server or a throughput speedup claim.
"""
from concurrent.futures import ThreadPoolExecutor
from http.client import HTTPConnection
from pathlib import Path
from threading import Thread, Barrier
from tempfile import TemporaryDirectory
import hashlib,json,math,time
from .catalogue import Catalogue,encoded
from .query_service import dispatch
from .http_service import QueryHTTPServer


def workload(count):
    register=dict(op='register',kind='population',name='sizes',specification=dict(kind='domain',predicate=dict(op='and',args=[dict(poly=[-1,1],relation='>='),dict(poly=[-1000000,1],relation='<=')]),fields={'n':[0,1],'square':[0,0,1]}))
    requests=[]
    for i in range(count):
        variants=[dict(op='call',object='sizes',method='count'),
                  dict(op='call',object='sizes',method='select',args={'rank':(7919*i)%1000000}),
                  dict(op='call',object='sizes',method='page',args={'start':(997*i)%999995,'size':5}),
                  dict(op='definition',object='sizes'),
                  dict(op='call',object='sizes',method='__dict__'),
                  dict(op='call',object='sizes',method='select',args={'rank':-1})]
        requests.append(dict(variants[i%len(variants)],request_id=f'load-{i}'))
    return register,requests


def run_load(*,clients=16,requests=384,timeout=20,queue_size=None):
    if not 1<=clients<=64 or requests<clients or timeout<=0:raise ValueError('positive bounded clients, requests and timeout required')
    register,jobs=workload(requests)
    def expected(c,request):
        try:return dict(schema='pp-query-response/1',request_id=request['request_id'],ok=True,result=dispatch(c,request)),200
        except (ValueError,TypeError,KeyError,IndexError,ArithmeticError,RecursionError) as e:
            return dict(schema='pp-query-response/1',request_id=request['request_id'],ok=False,error=dict(type=type(e).__name__,message=str(e))),400
    with TemporaryDirectory() as directory:
        db=Path(directory)/'load.sqlite'
        with Catalogue(str(db)) as c:dispatch(c,register)
        with Catalogue(':memory:') as reference:
            dispatch(reference,register);answers=[expected(reference,r) for r in jobs]
        if queue_size is None:server=QueryHTTPServer(str(db))
        else:
            class LoadServer(QueryHTTPServer):request_queue_size=queue_size
            server=LoadServer(str(db))
        thread=Thread(target=server.serve_forever,kwargs={'poll_interval':.01},daemon=True);thread.start()
        barrier=Barrier(clients);latencies=[];mismatches=[];failures=[]
        def worker(k):
            barrier.wait();rows=[]
            for i in range(k,requests,clients):
                start=time.perf_counter();conn=HTTPConnection('127.0.0.1',server.server_port,timeout=timeout)
                try:
                    conn.request('POST','/query',body=encoded(jobs[i]),headers={'Content-Type':'application/json'})
                    response=conn.getresponse();body=json.loads(response.read())
                    exact=(response.status==answers[i][1] and encoded(body)==encoded(answers[i][0]))
                    rows.append((i,time.perf_counter()-start,exact,None))
                except Exception as exc:rows.append((i,time.perf_counter()-start,False,type(exc).__name__+': '+str(exc)))
                finally:conn.close()
            return rows
        started=time.perf_counter()
        try:
            with ThreadPoolExecutor(max_workers=clients) as pool:
                rows=[row for group in pool.map(worker,range(clients)) for row in group]
            elapsed=time.perf_counter()-started
        finally:server.shutdown();thread.join(timeout=timeout);server.server_close()
        for i,t,exact,error in rows:
            latencies.append(t)
            if error:failures.append(dict(request_id=jobs[i]['request_id'],error=error))
            elif not exact:mismatches.append(jobs[i]['request_id'])
        with Catalogue(str(db)) as c:
            persistence=c.get('sizes').count()==1000000
        latencies.sort()
        percentile=lambda p:latencies[min(len(latencies)-1,math.ceil(p*len(latencies))-1)]
        return dict(schema='pp-http-concurrency/1',clients=clients,requests=requests,
            queue_size=server.request_queue_size,wall_seconds=elapsed,requests_per_second=requests/elapsed,
            latency_seconds={'median':percentile(.5),'p95':percentile(.95),'maximum':latencies[-1]},
            replay_mismatches=mismatches,transport_failures=failures,persistence_replayed=persistence,
            workload_sha256=hashlib.sha256(encoded(jobs).encode()).hexdigest(),
            all_replayed=(not mismatches and not failures and persistence),
            scope='Concurrent loopback clients; one serialized query worker, no independent-reader or multi-process test')
