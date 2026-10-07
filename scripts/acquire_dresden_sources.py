"""Download public research resources into a caller-selected directory.

Payload signatures are checked: HTML download challenge pages cannot masquerade
as PDFs or ZIPs. Bulk resources stay outside the repository.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
from urllib.request import urlopen
from html.parser import HTMLParser

RESOURCES={
 'venus2016.pdf':('https://escholarship.org/content/qt6cr1s6jd/qt6cr1s6jd.pdf','pdf'),
 'venus2020.html':('https://www.scielo.org.mx/scielo.php?script=sci_arttext&pid=S0185-25742020000200095','html'),
 'eclipse2025.xml':('https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13141895/fullTextXML','xml'),
 'eclipse_figure1.jpg':('https://cdn.ncbi.nlm.nih.gov/pmc/blobs/7df6/13141895/dbd0afd4ca8f/sciadv.adt9039-f1.jpg','jpeg'),
 'eclipse_figure8.jpg':('https://cdn.ncbi.nlm.nih.gov/pmc/blobs/7df6/13141895/4a2f9f23654f/sciadv.adt9039-f8.jpg','jpeg'),
 'forstemann_46_59.pdf':('https://www.famsi.org/mayawriting/codices/pdf/5_dresden_fors_schele_pp46-59.pdf','pdf'),
 'forstemann_13_24.pdf':('https://www.famsi.org/mayawriting/codices/pdf/2_dresden_fors_schele_pp13-24.pdf','pdf'),
 'eclipse_supplements.zip':('https://www.ebi.ac.uk/europepmc/webservices/rest/PMC13141895/supplementaryFiles','zip')}

class PublishedTableParser(HTMLParser):
    def __init__(self):
        super().__init__();self.tables=[];self.table=None;self.row=None;self.cell=None;self.span=1
    def handle_starttag(self,tag,attrs):
        if tag=='table':self.table=[]
        elif tag=='tr' and self.table is not None:self.row=[]
        elif tag in ('td','th') and self.row is not None:
            self.cell=[];self.span=int(dict(attrs).get('colspan','1'))
    def handle_endtag(self,tag):
        if tag in ('td','th') and self.cell is not None:
            self.row.extend([' '.join(self.cell)]+['COLSPAN']*(self.span-1));self.cell=None
        elif tag=='tr' and self.row is not None:self.table.append(self.row);self.row=None
        elif tag=='table' and self.table is not None:self.tables.append(self.table);self.table=None
    def handle_data(self,data):
        if self.cell is not None and data.strip():self.cell.append(data.strip())


def extract_venus(html):
    """Source-specific extraction; fail if the table layout changes."""
    p=PublishedTableParser();p.feed(html)
    records=[]
    for idx,pages,start in [(2,[46,47],8),(3,[48,49,50],1)]:
        if idx>=len(p.tables):raise ValueError('published table missing')
        for row in p.tables[idx]:
            if not row or not row[0].isdigit() or not 1<=int(row[0])<=13:continue
            numbers=[v for v in row[start:] if v.isdigit()]
            if len(numbers)!=4*len(pages):raise ValueError('unexpected numeric source-table layout')
            for j,page in enumerate(pages):
                for col,value in zip('ABCD',numbers[j*4:j*4+4]):
                    records.append({'page':page,'row':int(row[0]),'column':col,'reported_number':int(value),
                        'source_location':f'Table {idx-1}, Dresden page {page}, row {row[0]}, column {col}'})
    if len(records)!=260 or len({(r['page'],r['row'],r['column']) for r in records})!=260:
        raise ValueError('complete unique table required')
    return records


def valid(data,kind):
    return {'pdf':data.startswith(b'%PDF-'), 'zip':data.startswith(b'PK\x03\x04'),
            'jpeg':data.startswith(b'\xff\xd8\xff'),
            'xml':b'<article' in data[:2000],
            'html':b'Elucidating the Visual Language' in data}.get(kind,False)


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('destination',type=Path)
    p.add_argument('--extract-venus',action='store_true')
    p.add_argument('--timeout',type=int,default=40)
    args=p.parse_args();args.destination.mkdir(parents=True,exist_ok=True)
    def fetch(item):
        name,(url,kind)=item
        try:
            data=urlopen(url,timeout=args.timeout).read()
            if not valid(data,kind):raise ValueError('wrong payload signature; not retained')
            (args.destination/name).write_bytes(data)
            return {'name':name,'url':url,'status':'downloaded','bytes':len(data),
                    'sha256':hashlib.sha256(data).hexdigest()}
        except Exception as e:return {'name':name,'url':url,'status':'unavailable','reason':str(e)}
    results=list(ThreadPoolExecutor(4).map(fetch,RESOURCES.items()))
    (args.destination/'acquisition.json').write_text(json.dumps(results,indent=2)+'\n')
    if args.extract_venus:
        records=extract_venus((args.destination/'venus2020.html').read_text())
        (args.destination/'venus_extracted_records.json').write_text(json.dumps(records,indent=2)+'\n')
    print(json.dumps(results,indent=2))

if __name__=='__main__':main()
