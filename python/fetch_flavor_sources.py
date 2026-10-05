"""Refresh pinned original PDG sources automatically; fail on a changed edition."""
import hashlib,json,urllib.request
from pathlib import Path
base=Path(__file__).resolve().parents[1]/'receipts/flavor_prediction/sources'
for row in json.loads((base/'manifest.json').read_text()):
    target=base/row['file']
    if target.exists() and hashlib.sha256(target.read_bytes()).hexdigest()==row['sha256']:
        print(row['file'],'already pinned');continue
    data=urllib.request.urlopen(row['url'],timeout=60).read()
    if hashlib.sha256(data).hexdigest()!=row['sha256']:
        raise RuntimeError('source changed; retain the pinned edition: '+row['url'])
    target.write_bytes(data);print(row['file'],len(data),'downloaded')
