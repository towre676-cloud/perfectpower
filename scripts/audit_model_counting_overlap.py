#!/usr/bin/env python3
"""Detect normalized CNF repeats, beyond byte hashes and renamed comments.

The fingerprint ignores whitespace, comment text, clause/literal order,
duplicate clauses/literals and tautologies, but preserves declared variables.
It does not solve equivalence or canonicalize variable permutations.
"""
import argparse
import hashlib
import json
import struct
from pathlib import Path


def fingerprint(path):
    header=None;clauses=set();current=[];seen=0
    with path.open() as stream:
        for line in stream:
            tokens=line.split()
            if not tokens or tokens[0]=='c' or tokens==['%']:continue
            if tokens[0]=='p':
                if header is not None or len(tokens)!=4 or tokens[1]!='cnf':raise ValueError('invalid header')
                header=tuple(map(int,tokens[2:]));
                if min(header)<0:raise ValueError('negative dimensions')
                continue
            if header is None:raise ValueError('missing header')
            for token in tokens:
                x=int(token)
                if x:
                    if abs(x)>header[0]:raise ValueError('invalid literal')
                    current.append(x)
                else:
                    seen+=1;literals=set(current);current=[]
                    if any(-v in literals for v in literals):continue
                    encoded=','.join(map(str,sorted(literals))).encode('ascii')
                    clauses.add(hashlib.sha256(encoded).digest())
    if header is None or current or seen!=header[1]:raise ValueError('incomplete DIMACS')
    h=hashlib.sha256();h.update(struct.pack('>Q',header[0]))
    for clause in sorted(clauses):h.update(clause)
    return h.hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--prior-manifest',type=Path,required=True);p.add_argument('--prior-corpus',type=Path,required=True)
    p.add_argument('--evaluation-manifest',type=Path,required=True);p.add_argument('--evaluation-corpus',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    prior=json.loads(a.prior_manifest.read_text());evaluation=json.loads(a.evaluation_manifest.read_text())
    index={};prior_rows=[]
    for row in prior['instances']:
        path=a.prior_corpus/row['name']
        if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('prior hash changed')
        value=fingerprint(path);index.setdefault(value,[]).append(row['name'])
        prior_rows.append({'name':row['name'],'fingerprint':value})
    rows=[]
    for row in evaluation['instances']:
        path=a.evaluation_corpus/row['name']
        if hashlib.sha256(path.read_bytes()).hexdigest()!=row['sha256']:raise ValueError('evaluation hash changed')
        value=fingerprint(path)
        rows.append({'name':row['name'],'fingerprint':value,'normalized_repeats':index.get(value,[])})
    report={'schema':'pp-cnf-overlap/1','prior_manifest_sha256':hashlib.sha256(a.prior_manifest.read_bytes()).hexdigest(),
            'evaluation_manifest_sha256':hashlib.sha256(a.evaluation_manifest.read_bytes()).hexdigest(),
            'method':'SHA256 of sorted unique SHA256 clause fingerprints and declared variable universe; SHA256 collision resistance assumed',
            'limits':'Does not exclude semantic equivalence, variable renaming or related generation families among nonmatching fingerprints',
            'normalized_repeats':sum(bool(r['normalized_repeats']) for r in rows),
            'prior_instances':prior_rows,'evaluation_instances':rows}
    a.output.write_text(json.dumps(report,indent=2)+'\n')
    print('normalized repeats',report['normalized_repeats'],'of',len(rows),flush=True)


if __name__=='__main__':main()
