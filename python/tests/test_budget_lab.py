import itertools,json,threading,tempfile,unittest
from copy import deepcopy
from pathlib import Path
from urllib.request import Request,urlopen
from urllib.error import HTTPError
from http.server import HTTPServer
from perfectpower.participatory_budgeting import BudgetElection,BudgetSession
from perfectpower.budget_lab import BudgetLab,handler,json_safe
from perfectpower.planning import CompletionPlanner
ROOT=Path(__file__).resolve().parents[2]

TEXT='''META
key;value
num_projects;4
num_votes;3
budget;5.50
vote_type;approval
categories;a,b
budget_per_category;3.50,3.00
PROJECTS
project_id;cost;votes;category;name
x;1.50;2;a;Park
y;2.00;1;a;Trees
z;3.00;2;b;Lights
w;1.00;0;b;Bench
VOTES
voter_id;vote
1;x,z
2;x
3;y,z
'''
class BudgetTests(unittest.TestCase):
    def test_exact_scenarios_locks_order_and_rank(self):
        e=BudgetElection(TEXT);self.assertEqual(e.money_scale,2);self.assertEqual(e.support_audit,[])
        session=BudgetSession(e);ids=[p['project_id'] for p in e.projects]
        for budget in (0,3,7,11):
            for locks in ({},{'z':1},{'x':0,'w':1},{'x':1,'y':1,'z':1,'w':1},{'x':0,'y':0,'z':0,'w':0}):
                expected=[]
                for point in itertools.product((0,1),repeat=4):
                    if any(point[ids.index(k)]!=v for k,v in locks.items()):continue
                    costs=[sum(x*v['costs'][j] for x,v in zip(point,e.specification['variables'])) for j in range(3)]
                    if costs[0]<=budget and all(costs[j]<=e.specification['resources'][j]['max'] for j in (1,2)):expected.append(point)
                result=session.evaluate({'budget':budget,'locks':locks});self.assertEqual(result['count'],len(expected))
                for rank,point in enumerate(expected):
                    result=session.evaluate({'budget':budget,'locks':locks,'operation':'select','rank':rank})
                    self.assertEqual(result['plan']['point'],list(point))
                    fresh=BudgetSession(e);self.assertEqual(fresh.evaluate({'budget':budget,'locks':locks,'operation':'rank','point':list(point)})['rank'],rank)
                if expected:
                    scores=[sum(x*int(v['profit']) for x,v in zip(point,e.specification['variables'])) for point in expected]
                    result=session.evaluate({'budget':budget,'locks':locks});self.assertEqual(result['maximum'],str(max(scores)));self.assertEqual(result['maximizer_count'],scores.count(max(scores)))
        r=session.evaluate({});r['locks']['x']=1;self.assertEqual(session.evaluate({})['locks'],{})
    def test_support_and_cumulative_source_semantics(self):
        e=BudgetElection(TEXT.replace('x;1.50;2','x;1.50;9'));self.assertEqual(e.support_audit[0]['published'],'9')
        source=TEXT.replace('vote_type;approval','vote_type;cumulative').replace('cost;votes;category','cost;score;category').replace('voter_id;vote\n1;x,z\n2;x\n3;y,z','voter_id;vote;points\n1;x,z;1,1\n2;x;1\n3;y,z;1,1')
        e=BudgetElection(source);self.assertEqual(e.score_field,'score');self.assertEqual(e.support_audit,[])
        for bad in (TEXT.replace('num_projects;4','num_projects;3'),TEXT.replace('3;y,z','3;y,missing'),TEXT.replace('3;y,z','3;y,y'),TEXT.replace('cost;votes;category;name','cost;votes;votes;name'),TEXT.replace('3;y,z','1;y,z'),TEXT.replace('3.50,3.00','3.50')):
            with self.assertRaises(ValueError):BudgetElection(bad)
    def test_cache_errors_sampling(self):
        session=BudgetSession(BudgetElection(TEXT),cache_size=2)
        a=session.evaluate({'operation':'sample','seed':37});self.assertEqual(a,session.evaluate({'operation':'sample','seed':37}))
        self.assertGreater(session.hits,0)
        for b in (1,2,3):session.evaluate({'budget':b})
        self.assertEqual(len(session.cache),2)
        for request in ({'locks':{'q':0}},{'locks':{'x':True}},{'operation':'select','rank':True},{'operation':'view','rank':0},{'operation':'sample','seed':True},{'operation':'rank','point':[0,0,1,0],'locks':{'z':0}}):
            with self.assertRaises(ValueError):session.evaluate(request)
        self.assertEqual(session.evaluate({'budget':0,'locks':{'x':1}})['count'],0)
    def test_public_snapshots_complete(self):
        manifest=json.loads((ROOT/'data/participatory_budgeting/manifest.json').read_text())
        for row in manifest['files']:
            e=BudgetElection((ROOT/'data/participatory_budgeting/raw'/row['filename']).read_bytes().decode(),row)
            self.assertEqual(e.sha256,row['sha256']);self.assertEqual(len(e.projects),int(e.metadata['num_projects']));self.assertEqual(len(e.ballots),int(e.metadata['num_votes']))
        e=BudgetElection((ROOT/'data/participatory_budgeting/raw/France_Toulouse_2019.pb').read_bytes().decode());self.assertEqual(BudgetSession(e).evaluate({})['count'],283055991)
    def test_http_decimal_counts_and_routes(self):
        lab=BudgetLab(ROOT);name=lab.manifest['files'][2]['id']
        with HTTPServer(('127.0.0.1',0),handler(lab)) as server:
            t=threading.Thread(target=server.serve_forever,daemon=True);t.start();base=f'http://127.0.0.1:{server.server_port}'
            try:
                html=urlopen(base+'/').read().decode();self.assertIn('Explore the alternatives.',html)
                elections=json.load(urlopen(base+'/api/elections'));self.assertEqual(len(elections),4)
                def post(body,origin=None):
                    headers={'Content-Type':'application/json'}
                    if origin:headers['Origin']=origin
                    return urlopen(Request(base+'/api/query',data=json.dumps(body).encode(),headers=headers))
                body={'election':name,'request':{'operation':'select','rank':'0'}}
                result=json.load(post(body));self.assertIsInstance(result['count'],str)
                body['request']={'operation':'rank','point':result['plan']['point']};self.assertEqual(json.load(post(body))['rank'],'0')
                with self.assertRaises(HTTPError):post(body,'https://unrelated.example')
                with self.assertRaises(HTTPError):post({'election':'unknown','request':{}})
                with self.assertRaises(HTTPError):post({'election':name,'request':{'operation':'select','rank':'00'}})
                with self.assertRaises(HTTPError):urlopen(base+'/../pyproject.toml')
            finally:server.shutdown();t.join()
        self.assertEqual(json_safe({'count':2**64,'point':[0,1]}),{'count':str(2**64),'point':[0,1]})

if __name__=='__main__':unittest.main()
