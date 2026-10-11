#!/usr/bin/env python3
"""Frozen extra cohort from the verified dynasp_all generated-width source."""
import argparse
import hashlib
import json
import tarfile
from pathlib import Path
from profile_counting_structure import profile
from trace_counting_origins import identity, text, members, header
from perfectpower.model_counting import CNF

ROOT=Path(__file__).resolve().parent.parent


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--archive',type=Path,required=True)
    p.add_argument('--origins',type=Path,required=True)
    p.add_argument('--first-selection',type=Path,required=True)
    p.add_argument('--corpus',type=Path,required=True)
    p.add_argument('--manifest',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    if a.manifest.exists() or a.output.exists():raise ValueError('fresh outputs required')
    origins=json.loads(a.origins.read_text());first=json.loads(a.first_selection.read_text())
    assert hashlib.sha256(a.archive.read_bytes()).hexdigest()==origins['archive_sha256']
    known=set(origins['known_normalized_hashes'])|{r['normalized_sha256']for r in first['selected']}
    oversized_n=set()
    for f in ('manifest.json','mc2025_manifest.json'):
        for r in json.loads((ROOT/'data/model_counting'/f).read_text())['instances']:
            if r['name']in origins['known_byte_limit_exclusions']:oversized_n.add(int(r['header'].split()[2]))
    selection={'schema':'pp-cnf-advantage-selection/1','scope':'Generated-width dynasp_all extension, not production or unseen-family evidence',
               'protocol_sha256':hashlib.sha256((ROOT/'docs/MODEL_COUNTING_DYNASP_PROTOCOL.md').read_bytes()).hexdigest(),
               'source_identities':{n:hashlib.sha256((ROOT/'python'/n).read_bytes()).hexdigest()for n in ('select_dynasp_advantage.py','trace_counting_origins.py','profile_counting_structure.py')},
               'origins_sha256':hashlib.sha256(a.origins.read_bytes()).hexdigest(),
               'counter_sha256':hashlib.sha256((ROOT/'native/model_counting/counter.cpp').read_bytes()).hexdigest(),
               'first_selection_sha256':hashlib.sha256(a.first_selection.read_bytes()).hexdigest(),
               'inventory':[],'selected':[],'completed':False}
    seen=set()
    with tarfile.open(a.archive)as archive:
        for name,raw in members(archive):
            if '/dynasp_all/'not in name or not name.endswith(('.cnf','.cnf.xz','.cnf.gz')):continue
            row={'member':name,'family':'dynasp_all','compressed_sha256':hashlib.sha256(raw).hexdigest()}
            t=text(raw,name)
            if t is None:row['status']='BYTE_PROFILE_LIMIT'
            else:
                row['sha256']=hashlib.sha256(t.encode()).hexdigest()
                try:
                    f=CNF.parse(t);key=identity(t);row['normalized_sha256']=key
                    if key in known:row['status']='KNOWN_NORMALIZED_MATCH'
                    elif f.variables in oversized_n:row['status']='CONSERVATIVE_KNOWN_UNNORMALIZED_UNIVERSE_EXCLUSION'
                    elif key in seen:row['status']='COLLECTION_NORMALIZED_DUPLICATE'
                    else:
                        seen.add(key);metrics=profile(t);row['profile']=metrics
                        if metrics.get('unit_contradiction'):row['status']='UNIT_CONTRADICTION'
                        elif metrics.get('all_components_accepted')and metrics.get('largest_component',0)>256:row['status']='PREDICTED_TRACTABLE'
                        elif metrics.get('graph_status')=='PROFILED'and not metrics.get('all_components_accepted'):row['status']='REJECTED_CONTROL'
                        else:row['status']='OUTSIDE_SELECTION_RULE'
                except (ValueError,RuntimeError)as e:row.update(status='INPUT_UNSUPPORTED',reason=str(e))
            selection['inventory'].append(row)
            if len(selection['inventory'])%50==0:print('profiled',len(selection['inventory']),flush=True)
    selected=[]
    for label,cap in [('PREDICTED_TRACTABLE',24),('REJECTED_CONTROL',12)]:
        pool=[r for r in selection['inventory']if r['status']==label]
        selected+=sorted(pool,key=lambda r:(r['sha256'],r['member']))[:cap]
    lookup={r['member']:r for r in selected};a.corpus.mkdir(parents=True,exist_ok=True)
    manifest={'schema':'pp-mc-corpus/1','dataset':'Fresh generated-width dynasp_all extensions','archive_url':origins['archive_url'],
              'archive_sha256':origins['archive_sha256'],'selection':'Frozen structural labels and SHA256 order before timing','instances':[]}
    with tarfile.open(a.archive)as archive:
        for name,raw in members(archive):
            if name not in lookup:continue
            row=lookup[name];t=text(raw,name);assert hashlib.sha256(t.encode()).hexdigest()==row['sha256']
            file=f'advantage_dynasp_{selected.index(row):03}.cnf';(a.corpus/file).write_text(t);n,m=header(raw,name)
            manifest['instances'].append({'name':file,'sha256':row['sha256'],'bytes':len(t.encode()),'header':f'p cnf {n} {m}',
                                          'source_member':name,'family':'dynasp_all','structural_group':row['status'],
                                          'normalized_sha256':row['normalized_sha256']})
            selection['selected'].append(dict(row,name=file))
    manifest['instances'].sort(key=lambda r:r['name']);selection['selected'].sort(key=lambda r:r['name'])
    selection['completed']=True;selection['selected_group_counts']={k:sum(r['status']==k for r in selected)for k in ('PREDICTED_TRACTABLE','REJECTED_CONTROL')}
    a.manifest.write_text(json.dumps(manifest,indent=2)+'\n');selection['manifest_sha256']=hashlib.sha256(a.manifest.read_bytes()).hexdigest()
    a.output.write_text(json.dumps(selection,indent=2)+'\n');print(selection['selected_group_counts'],flush=True)


if __name__=='__main__':main()
