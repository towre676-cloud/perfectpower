"""Reject missing declarations, errors and nonstandard axioms in the monograph audit."""
import hashlib
import json
import pathlib
import re
import sys

root = pathlib.Path(__file__).resolve().parents[1]
text = pathlib.Path(sys.argv[1]).read_text()
text = re.sub(r'\n +', ' ', text)
rows = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text)
expected = re.findall(r'^#print axioms (\S+)', (root/'audit/MonographPush.lean').read_text(), re.M)
assert [name for name, _ in rows] == expected, 'missing, duplicate, or unexpected audit declarations'
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
for name, group in rows:
    assert {a.strip() for a in group.split(',') if a.strip()} <= allowed, (name, group)
assert 'error:' not in text and 'warning:' not in text
manifest=json.loads((root/'receipts/monograph_lean/inputs.json').read_text())
assert len(rows)==manifest['audited_declarations']
source=root/'receipts/monograph_development/operator_algebras.json'
assert hashlib.sha256(source.read_bytes()).hexdigest()==manifest['source_sha256']
for module, digest in manifest['module_sha256'].items():
    assert hashlib.sha256((root/'PerfectPower'/(module+'.lean')).read_bytes()).hexdigest()==digest, module
actual=[]
for module in manifest['modules']:
    src=(root/'PerfectPower'/(module+'.lean')).read_text()
    ns=re.search(r'^namespace (\S+)',src,re.M).group(1)
    actual.extend(ns+'.'+name for name in re.findall(r'^theorem (\w+)',src,re.M))
audit=(root/'audit/MonographPush.lean').read_text()
covered=[name for name in expected if not name.startswith('PerfectPower.ParallelAxiomBundles.')]
covered+=re.findall(r'⟨_,([A-Za-z0-9_.]+)⟩',audit)
assert sorted(covered)==sorted(actual), 'proof-bundle coverage mismatch'
assert len(covered)==manifest['audited_declarations']
(root/'receipts/monograph_lean/axioms.log').write_text(text)
print(f'Monograph Lean audit passed: {len(covered)} declarations in {len(rows)} groups; standard axioms only')
