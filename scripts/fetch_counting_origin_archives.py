#!/usr/bin/env python3
"""Download and checksum-pin the five source archives used by the study."""
import argparse
import hashlib
import json
import urllib.request
from pathlib import Path

SOURCES=[(2020,'10004947','c69a07dc1f1fed5cdbc434d005ea5752'),
         (2021,'10006441','74463335843cdbec64a5d0993fd66518'),
         (2022,'10014715','afe4d1d517c12f018f17e08b85aa27d1'),
         (2023,'10012822','0519f1ae0003c68ec06ff217259a8be2'),
         (2024,'14969231','d2976e44c6a678404c01da779cb09007')]


def hashes(path):
    md5=hashlib.md5();sha=hashlib.sha256()
    with path.open('rb')as f:
        while block:=f.read(4*1024**2):md5.update(block);sha.update(block)
    return md5.hexdigest(),sha.hexdigest()


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--years',type=int,nargs='+',choices=range(2020,2025),default=list(range(2020,2025)))
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True);report=[]
    for year,record,expected in SOURCES:
        if year not in a.years:continue
        file=f'mc{year}-track1-mc_collected.tar';dest=a.output/file
        url=f'https://zenodo.org/records/{record}/files/{file}?download=1'
        if not dest.exists():
            part=dest.with_suffix('.part')
            request=urllib.request.Request(url,headers={'User-Agent':'PerfectPower structural research'})
            with urllib.request.urlopen(request,timeout=60)as response,part.open('wb')as out:
                while block:=response.read(4*1024**2):out.write(block)
            actual,_=hashes(part)
            if actual!=expected:raise ValueError(f'{year}: archive checksum differs')
            part.replace(dest)
        actual,sha=hashes(dest)
        if actual!=expected:raise ValueError(f'{year}: existing archive checksum differs')
        report.append({'year':year,'file':file,'url':url,'md5':actual,'sha256':sha,'bytes':dest.stat().st_size})
        print(year,'verified',flush=True)
    (a.output/'source_archives.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__=='__main__':main()
