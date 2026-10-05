"""Extract numerical parameters from Bober's independent 52-row Table 2.

Only mathematical parameters and provenance are saved, not the source article.
Run with --html for an already downloaded source, or fetch the specified URL.
"""
import argparse,hashlib,html,json,re,urllib.request
from pathlib import Path

URL='https://arxiv.org/html/0709.1977v1'


def extract(data):
    source=data.decode();start=source.index('<table id="S6.T2.1"')
    table=source[start:];table=table[:table.index('</table>')]
    rows=[]
    for row in re.findall(r'<tr[^>]*>(.*?)</tr>',table,re.S)[1:]:
        cells=re.findall(r'<td[^>]*>(.*?)</td>',row,re.S)
        texts=[html.unescape(x) for x in re.findall(r'alttext="([^"]*)"',cells[1])]
        numbers=re.findall(r'\[([0-9,]+)\]',texts[0])
        if len(numbers)!=2:raise ValueError('unexpected source parameter shape')
        a,b=[[int(n) for n in part.split(',')] for part in numbers]
        if sum(a)!=sum(b):raise ValueError('unbalanced source row')
        rows.append({'table_line':len(rows)+1,'numerator':a,'denominator':b})
    if len(rows)!=52:raise ValueError('expected precisely 52 sporadic parameter rows')
    return {'source':URL,'source_sha256':hashlib.sha256(data).hexdigest(),'table':'2',
            'author':'Jonathan W. Bober','title':'Factorial ratios, hypergeometric series, and a family of step functions',
            'scope':'independent numerical parameters; no article prose reproduced','rows':rows}


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--html');parser.add_argument('--out',default='data/gamma_bober52.json')
    args=parser.parse_args();data=Path(args.html).read_bytes() if args.html else urllib.request.urlopen(URL,timeout=30).read()
    Path(args.out).write_text(json.dumps(extract(data),indent=2)+'\n')
