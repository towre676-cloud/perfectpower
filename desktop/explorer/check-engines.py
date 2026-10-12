"""Exercise actual explorer engine routes and retain their outputs."""
import importlib.util,json,tempfile,time,unittest
from pathlib import Path
MODULE=Path(__file__).with_name('server.py')
spec=importlib.util.spec_from_file_location('explorer_server',MODULE);server=importlib.util.module_from_spec(spec);spec.loader.exec_module(server)
class Engines(unittest.TestCase):
 def test_signed_points(self):
  self.assertEqual(server.scan({'coeff':[-2,0,0,1],'lo':-20,'hi':20})['points'],[[3,5],[3,-5]])
  self.assertEqual(server.scan({'coeff':[0,1],'d':3,'lo':-10,'hi':10})['points'],[[-8,-2],[-1,-1],[0,0],[1,1],[8,2]])
 def test_fraction_domain(self):
  self.assertEqual(server.scan({'coeff':['1/2','1/2'],'lo':0,'hi':3})['points'],[[1,1],[1,-1]])
 def test_limits(self):
  with self.assertRaises(ValueError):server.scan({'coeff':[1],'lo':0,'hi':100001})
  with self.assertRaises(ValueError):server.scan({'coeff':[1],'d':1})
 def test_big_transport(self):
  self.assertEqual(server.safe_json({'n':2**60}),{'n':str(2**60)})
 def test_shipped_digest(self):
  from perfectpower.shipped_native import shipped_library
  source=server.ROOT/'native/completion_planner.cpp'
  self.assertIsNotNone(shipped_library('completion_planner',source))
 def test_requests(self):
  with tempfile.TemporaryDirectory() as state:
   engine=server.Explorer(state=state)
   cases=[['solve','--expr','(5*n - 7)**3 - 2','--domain','pos'],['exact-solve','--coeff','[-199,1,1,1,1]'],['plan','examples/planning/petersen_6.json'],['graph','flow','examples/graph_methods/flow.json'],['geometry-foundations','triangulate','examples/belyaev_geometry/triangulate.json'],['euclid','pell','examples/euclid_methods/pell.json'],['arithmetic-series','compile','examples/arithmetic_series/pell.json'],['model-count','examples/desktop_explorer/starter.cnf','--timeout','10']]
   outputs=[]
   for args in cases:
    job=engine.submit({'kind':'command','args':args,'timeout':20})['id']
    start=time.monotonic()
    while engine.public_job(job)['status']=='running' and time.monotonic()-start<25:time.sleep(.03)
    result=engine.public_job(job);outputs.append(result)
    self.assertEqual(result['status'],'complete',(args,result))
   self.assertEqual(outputs[2]['result']['summary']['count'],28)
   self.assertEqual(outputs[3]['result']['value'],5)
   self.assertEqual(outputs[-1]['result']['count'],'4')
   output=server.ROOT/'desktop/explorer/ENGINE_CHECKS.json';output.write_text(json.dumps(outputs,indent=2))
   with self.assertRaises(ValueError):engine.resolve('../README.md')
 def test_edited_input(self):
  with tempfile.TemporaryDirectory() as state:
   engine=server.Explorer(state=state);spec={'vertices':2,'source':0,'sink':1,'arcs':[[0,1,7]]}
   job=engine.submit({'kind':'command','args':['graph','flow','@input.json'],'files':{'input.json':json.dumps(spec)}})['id']
   while engine.public_job(job)['status']=='running':time.sleep(.03)
   self.assertEqual(engine.public_job(job)['result']['value'],7)
if __name__=='__main__':unittest.main()
