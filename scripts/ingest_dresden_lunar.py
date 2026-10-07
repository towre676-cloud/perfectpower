"""Read unchanged source XLSX bytes with standard-library ZIP/XML tools.

No workbook is created or modified. Cached numeric cells are retained as their
original decimal strings; integer Julian days use floor(JDN), explicitly.
"""
import argparse
from decimal import Decimal,ROUND_FLOOR
from pathlib import Path
import hashlib,json,zipfile
import xml.etree.ElementTree as ET

NS={'m':'http://schemas.openxmlformats.org/spreadsheetml/2006/main'}

def numeric_cells(path):
    with zipfile.ZipFile(path) as z:root=ET.fromstring(z.read('xl/worksheets/sheet1.xml'))
    cells={}
    for cell in root.findall('.//m:c',NS):
        value=cell.find('m:v',NS)
        if value is not None and cell.get('t') not in ('s','str','b','e'):
            cells[cell.attrib['r']]=value.text
    return cells


def ingest(s1,s2):
    cells=numeric_cells(s2);refs=sorted((ref for ref in cells if ref.startswith('E') and ref[1:].isdigit() and int(ref[1:])>=2),key=lambda ref:int(ref[1:]))
    if refs!=['E'+str(r) for r in range(2,8054)]:raise ValueError('expected 8052 contiguous source JDN entries')
    days=[int(Decimal(cells[r]).to_integral_value(rounding=ROUND_FLOOR)) for r in refs]
    numeric=numeric_cells(s1);reported=[]
    for row in range(1,869):
        value=numeric.get('B'+str(row))
        if value is None:continue
        n=Decimal(value)
        if n!=int(n) or not 1<=int(n)<=405:continue
        entries=[]
        for col in 'CDEFGHI':
            day=numeric.get(col+str(row));frequency=numeric.get(col+str(row+1))
            if day is not None and frequency is not None:
                entries.append({'cell':col+str(row+1),'days':int(Decimal(day)),'frequency':frequency})
        reported.append({'months':int(n),'source_row':row,'cells':entries})
    if sorted(r['months'] for r in reported)!=list(range(1,406)):raise ValueError('405 source interval rows required')
    return {'schema':'pp-dresden-lunar-source/1','source':'https://doi.org/10.1126/sciadv.adt9039',
            'attribution':'John Justeson and Justin Lowry, supplementary tables S1 and S2 (2025), CC BY 4.0',
            'source_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (s1,s2)},
            'integer_day_convention':'floor(JDN), using original cached decimal strings',
            'observation_kind':'authors modeled crescent visibility at Monte Alban; not ancient observations',
            'source_jdn_column':'E2:E8053','cached_jdn':[cells[r] for r in refs],
            'days':days,'reported_rows':reported}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('source_directory',type=Path);p.add_argument('output',type=Path)
    args=p.parse_args();data=ingest(args.source_directory/'adt9039_table_s1.xlsx',args.source_directory/'adt9039_table_s2.xlsx')
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({'appearances':len(data['days']),'reported_spans':len(data['reported_rows']),'output':str(args.output)}))

if __name__=='__main__':main()
