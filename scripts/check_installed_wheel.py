"""Exercise installed runtime from a directory outside the source checkout.

Run this after pip installing the wheel, with PYTHONPATH unset.
"""
import hashlib
from http.client import HTTPConnection
import json
from pathlib import Path
import tempfile
import threading
from perfectpower.resources import runtime_root
from perfectpower.compiler import PowerConstraint,compile_constraint
from perfectpower.checked_box import box_certificate
from perfectpower.checked_population import population_certificate
from perfectpower.checked_global_population import global_population_certificate
from perfectpower.checked_nonlinear_population import nonlinear_population_certificate
from perfectpower.checked_pell_population import pell_population_certificate
from perfectpower.checked_family_population import family_population_certificate
from perfectpower.checked_pell_family import pell_family_certificate
from perfectpower.checked_factorial_unit import unit_certificate
from perfectpower.checked_landau import landau_certificate
from perfectpower.http_service import QueryHTTPServer


def main():
    root=runtime_root()
    if root.name!='_assets':raise AssertionError('test must run against an installed wheel')
    manifest=json.loads((root/'runtime_manifest.json').read_text())
    for name,digest in manifest.items():
        if hashlib.sha256((root/name).read_bytes()).hexdigest()!=digest:
            raise AssertionError('runtime asset mismatch: '+name)
    # Expanded (5n-7)^3-2: test complete list loading from packaged registry.
    plan=compile_constraint(PowerConstraint((-345,735,-525,125),2))
    if list(plan.iter_hits(10))!=[(2,[-5,5])]:raise AssertionError('installed complete compiler result changed')
    if box_certificate([-2,0,0,1],2,[-2,5])['points']!=[[3,-5],[3,5]]:
        raise AssertionError('installed native query changed')
    if unit_certificate(37,2,3)['arithmetic']['unit']!=5:
        raise AssertionError('installed original factorial-unit proposal changed')
    population=population_certificate([0,0,1],2,[-2,2],[{'condition':['le',0,'y'],
        'objective':['add',['pow','x',2],['pow','y',2]]}])
    if population['results'][0]['minimum']!={'value':0,'points':[[0,0]]}:
        raise AssertionError('installed bivariate population objective changed')
    if not (root/'PerfectPower/QueryNative.lean').is_file():
        raise AssertionError('installed generic population proofs missing')
    global_query=global_population_certificate([{'condition':['le',0,'y']}],scale=5,shift=-7)
    if global_query['results'][0]['points']!=[[2,5]]:
        raise AssertionError('installed global affine query changed')
    if not (root/'PerfectPower/MordellMinus2Core.lean').is_file():
        raise AssertionError('installed global source proof missing')
    nonlinear=nonlinear_population_certificate([1,0,1],[{}],family='mordell_minus4')
    if nonlinear['source_count']!=8:raise AssertionError('installed nonlinear population changed')
    pell=pell_population_certificate(1000,[{}],global_ranks=[4])
    if pell['source_count']!=5 or pell['global_selections'][0]['point']!=[408,577]:
        raise AssertionError('installed Pell population changed')
    for name in ('PolynomialFibre','MordellMinus4Core','PellPopulation'):
        if not (root/f'PerfectPower/{name}.lean').is_file():raise AssertionError('installed proved source missing: '+name)
    broad=family_population_certificate([0,1],[{}],offset=15)
    if broad['source_count']!=8:raise AssertionError('installed square-difference population changed')
    empty=family_population_certificate([0,1],[{}],family='mordell_descent',offset=-9985)
    if empty['source_count']!=0:raise AssertionError('installed descent source changed')
    general=pell_family_certificate(3,100,global_ranks=[4])
    if general['source_count']!=5 or general['global_selections'][0]['point']!=[56,97]:
        raise AssertionError('installed general Pell access changed')
    if 'original_integral_for_all_indices' not in landau_certificate([2],[1,1])['lean']:
        raise AssertionError('installed universal integrality proposal missing')
    with tempfile.TemporaryDirectory() as directory:
        server=QueryHTTPServer(Path(directory)/'installed.sqlite')
        thread=threading.Thread(target=server.serve_forever,kwargs={'poll_interval':.01},daemon=True)
        thread.start()
        try:
            for route in ['/health','/atlas']:
                client=HTTPConnection(*server.server_address,timeout=10)
                client.request('GET',route);response=client.getresponse();body=response.read();client.close()
                if response.status!=200 or not body:raise AssertionError('installed route missing: '+route)
            client=HTTPConnection(*server.server_address,timeout=10)
            client.request('POST','/query',body='{"op":"list"}',headers={'Content-Type':'application/json'})
            response=client.getresponse();body=json.loads(response.read());client.close()
            if response.status!=200 or body['result']!=[]:raise AssertionError('installed process dispatch failed')
            for op,args,count in [('checked_nonlinear_population',dict(coefficients=[1,0,1],queries=[{}],family='mordell_minus4'),8),
                                  ('checked_pell_population',dict(cutoff=1000,queries=[{}],global_ranks=[4]),5),
                                  ('checked_family_population',dict(coefficients=[0,1],queries=[{}],offset=15),8),
                                  ('checked_pell_family',dict(D=3,cutoff=100),5)]:
                client=HTTPConnection(*server.server_address,timeout=10)
                client.request('POST','/query',body=json.dumps(dict(op=op,args=args)),headers={'Content-Type':'application/json'})
                response=client.getresponse();body=json.loads(response.read());client.close()
                if response.status!=200 or body['result']['source_count']!=count or body['result']['proof_status']!='emitted':
                    raise AssertionError('installed proved-family HTTP proposal failed: '+op)
        finally:server.shutdown();thread.join();server.server_close()
    print(json.dumps(dict(complete=True,assets=len(manifest),installed_root=str(root))))


if __name__=='__main__':main()
