"""Audit all root/event declarations and bind the replay to its exact sources."""
import hashlib,json,pathlib,re,sys
ROOT=pathlib.Path(__file__).resolve().parents[1]
DEST=ROOT/'receipts/root_events_lean'
def manifest():
 graph=json.loads((DEST/'graph_inputs.json').read_text())
 modules=['BernsteinRootTree','SturmChainAlgebra','DeterminantalEvents','FiniteGraphProbability','TriangularDeterminant','PaddedPrincipalMinor','Generated/RootEventFixtures']+graph['modules']
 audit=''.join('import PerfectPower.'+m.replace('/','.')+'\n' for m in modules);names=[]
 for m in modules:
  s=(ROOT/'PerfectPower'/(m+'.lean')).read_text();ns=re.search(r'^namespace (\S+)',s,re.M).group(1)
  names.extend(ns+'.'+n for n in re.findall(r'^theorem ([A-Za-z0-9_.]+)',s,re.M))
 audit+=''.join('#print axioms '+n+'\n' for n in names);(ROOT/'audit/RootEvents.lean').write_text(audit)
 sources=['receipts/monograph_development/root_and_gap_examples.json','receipts/monograph_development/connection_corpus.json','receipts/positive_geometry/connection_polytopes.json']
 data={'schema':'root-events-lean/1','modules':modules,'audited_declarations':len(names),'rational_source_models':graph['source_models'],'distinct_graph_laws':graph['distinct_models'],'module_sha256':{m:hashlib.sha256((ROOT/'PerfectPower'/(m+'.lean')).read_bytes()).hexdigest() for m in modules},'source_sha256':{p:hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sources}}
 (DEST/'inputs.json').write_text(json.dumps(data,indent=2)+'\n');print(len(modules),len(names))
def check(path):
 m=json.loads((DEST/'inputs.json').read_text());text=re.sub(r'\n +',' ',pathlib.Path(path).read_text())
 rows=re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",text)
 expected=re.findall(r'^#print axioms (\S+)',(ROOT/'audit/RootEvents.lean').read_text(),re.M)
 assert [n for n,a in rows]==expected and len(rows)==m['audited_declarations']
 allowed={'propext','Classical.choice','Quot.sound'}
 for n,a in rows:assert {x.strip() for x in a.split(',') if x.strip()}<=allowed,(n,a)
 assert 'error:' not in text and 'warning:' not in text
 for p,d in m['source_sha256'].items():assert hashlib.sha256((ROOT/p).read_bytes()).hexdigest()==d,p
 for p,d in m['module_sha256'].items():assert hashlib.sha256((ROOT/'PerfectPower'/(p+'.lean')).read_bytes()).hexdigest()==d,p
 (DEST/'axioms.log').write_text(text)
 print(f'Root/event Lean audit passed: {len(rows)} declarations; standard axioms only')
if __name__=='__main__':
 if sys.argv[1]=='--manifest':manifest()
 else:check(sys.argv[1])
