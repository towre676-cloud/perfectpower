#!/usr/bin/env python3
"""Export shared web interfaces, or the dedicated --family integral-studio feed."""
import argparse,hashlib,json,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
def export():
    assets={}
    for folder in ('app-hub','simple-explorer','shared','portfolio-geometry','challenge','arithmetic-transport','integral-families'):
        for p in sorted((ROOT/'web'/folder).glob('*')):
            if p.is_file() and p.suffix in ('.html','.css','.js','.mjs','.json','.txt'):
                assets[folder+'/'+p.name]=p.read_text()
    raw=json.dumps({'schema':'our-apps.web-payload/1','assets':assets,'hashes':{k:hashlib.sha256(v.encode()).hexdigest() for k,v in assets.items()}},sort_keys=True,separators=(',',':'))
    envelope={'schema':'our-apps.web-live/1','source_parent':subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip(),'payload_json':raw,'payload_sha256':hashlib.sha256(raw.encode()).hexdigest()}
    (ROOT/'data/app_web_live.json').write_text(json.dumps(envelope,sort_keys=True,indent=2)+'\n')
    return {'assets':len(assets),'payload_sha256':envelope['payload_sha256']}

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--family',choices=('all','integral-studio'),default='all',
                        help='Export all web families, or only the dedicated integral-studio feed.')
    args=parser.parse_args(argv)
    if args.family=='integral-studio':
        # Do not collect or read the unrelated shared application payload.
        subprocess.run([sys.executable,str(ROOT/'python/export_integral_atlas.py')],
                       cwd=ROOT,check=True)
        return 0
    print(json.dumps(export()))
    return 0

if __name__=='__main__':raise SystemExit(main())
