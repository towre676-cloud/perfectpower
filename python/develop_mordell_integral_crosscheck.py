"""Compare completed lists against the independent Bennett-Ghadermarzi census."""
import argparse,hashlib,json,re,subprocess,tempfile,urllib.request
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
SOURCES=[dict(name='0-10^6.pdf',sign=-1,pages=25,sha256='5ad1afe4b3f64fbebfc8939e297782392c0b04d544d51d2a50f97732b44ab903'),
         dict(name='0-10^6n.pdf',sign=1,pages=120,sha256='5ee7772c7a1f7dfbc468fd6a5333f49bce69817f994d784324197b9fab68b235')]


def parse_table(text,sign):
    rows={}
    pattern=r'(?<!\d)(-?\d+)\s+(\d+)\s+((?:\[\s*-?\d+\s*,\s*-?\d+\s*\]\s*)+)'
    for match in re.finditer(pattern,text):
        k,n=int(match[1]),int(match[2])
        points=[list(map(int,p)) for p in re.findall(r'\[\s*(-?\d+)\s*,\s*(-?\d+)\s*\]',match[3])]
        if k*sign<=0 or k in rows or len(points)!=n or any(y*y!=x*x*x+k for x,y in points):
            raise ArithmeticError('published table row does not match its equation or count')
        rows[k]=points
    if not rows or max(map(abs,rows))<=10000:
        raise ArithmeticError('extracted table does not cover the coefficient frontier')
    return rows


def main():
    parser=argparse.ArgumentParser();parser.add_argument('--negative',type=Path);parser.add_argument('--positive',type=Path)
    args=parser.parse_args();catalog={};provenance=[]
    with tempfile.TemporaryDirectory(prefix='pp-mordell-census-') as directory:
        for source,local in zip(SOURCES,[args.negative,args.positive]):
            url='https://personal.math.ubc.ca/~bennett/'+source['name']
            path=local or Path(directory)/source['name']
            if local is None:path.write_bytes(urllib.request.urlopen(url,timeout=60).read())
            digest=hashlib.sha256(path.read_bytes()).hexdigest()
            if digest!=source['sha256']:raise ArithmeticError('published census digest changed')
            text=subprocess.check_output(['pdftotext','-f','1','-l',str(source['pages']),'-layout',str(path),'-'],text=True)
            rows=parse_table(text,source['sign']);catalog.update(rows)
            provenance.append(dict(url=url,sha256=digest,bytes=path.stat().st_size,
                extracted_pages=source['pages'],largest_extracted_coefficient=max(map(abs,rows))))
    compared=[];mismatches=[]
    for path in sorted((ROOT/'receipts/mordell_completion').glob('[mp][0-9]*.json')):
        packet=json.loads(path.read_text())
        if packet.get('status')!='complete':continue
        expected=sorted(catalog.get(packet['k'],[]));actual=sorted([list(map(int,p)) for p in packet['integral_points']])
        row=dict(k=packet['k'],published_integral_points=expected,match=expected==actual)
        compared.append(row)
        if not row['match']:mismatches.append(packet['k'])
    receipt=dict(schema='pp-mordell-published-integral-crosscheck/1',authors=['Michael A. Bennett','Amir Ghadermarzi'],
        source_page='https://personal.math.ubc.ca/~bennett/BeGa-data.html',sources=provenance,
        curves_compared=len(compared),mismatches=mismatches,rows=compared,
        scope='independent published-census agreement; absent coefficient rows represent empty published lists; no new Lean completeness proof')
    (ROOT/'receipts/mordell_completion/published_integral_crosscheck.json').write_text(json.dumps(receipt,indent=2)+'\n')
    if mismatches:raise ArithmeticError(f'published census mismatches: {mismatches}')
    print(len(compared),'independent integral lists agree')


if __name__=='__main__':main()
