"""Standalone offline browser for the exact arithmetic atlas (no remote assets)."""
import json


def render(catalogue, pairs, summary):
    def strings(value):
        if isinstance(value,bool) or value is None:return value
        if isinstance(value,int):return str(value)  # preserve integers beyond JavaScript precision
        if isinstance(value,list):return [strings(v) for v in value]
        if isinstance(value,dict):return {k:strings(v) for k,v in value.items()}
        return value
    data=json.dumps(strings({'curves':catalogue,'pairs':pairs,'summary':summary}),separators=(',',':'))
    html = '''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>PerfectPower · Divisor-sum results</title>
<style>
:root{color-scheme:dark;font:17px system-ui;background:#101821;color:#e6edf3}body{max-width:1200px;margin:auto;padding:32px}h1{font-size:clamp(28px,5vw,48px);letter-spacing:-.04em;margin-bottom:12px}p{line-height:1.65;max-width:900px;color:#c3d2df}strong{color:#79dfcb}.controls{display:flex;gap:12px;flex-wrap:wrap;padding:20px 0}input,select,button{font:inherit;padding:10px;border:1px solid #4b667a;border-radius:6px;background:#192733;color:#fff}input{min-width:280px}label{display:flex;gap:8px;align-items:center}table{border-collapse:collapse;width:100%;font-size:15px}th,td{text-align:left;vertical-align:top;padding:12px;border-bottom:1px solid #344553}th{color:#79dfcb}code{overflow-wrap:anywhere}#table{overflow-x:auto}footer{padding-top:30px;color:#9cb1c4}button{cursor:pointer}
</style>
<h1>Divisor sums → complete equations</h1>
<p><strong>3,080 complete quartic lists · 5,401 integer points · 218 square divisor-sum joins.</strong>
Explore equations whose entire integer solution sets are enumerated, and a finite grid of two-prime products.
The separate census covers every n from 1 through 1,000,000. Its 6,871 square hits are complete within that interval.</p>
<p>For prime p, sigma(p⁴)=1+p+p²+p³+p⁴. The only prime input giving a square is p=3:
sigma(81)=121. Products need more care: sigma(2)=3 and sigma(11)=12 are nonsquares, but sigma(22)=36.</p>
<div class="controls"><label>Collection <select id="kind"><option value="curves">Complete quartics</option><option value="pairs">Two-prime square joins</option></select></label>
<label>Search <input id="search" placeholder="Coefficients, prime, or category"></label>
<label><input type="checkbox" id="empty" style="min-width:0">Empty quartics only</label>
<button id="download">Download matching rows</button></div>
<p id="scope"></p><p id="count" aria-live="polite"></p><div id="table"></div>
<footer>All integers are stored as decimal strings in this viewer, preserving exact large values. Python arithmetic and Lean proof status are recorded separately in the accompanying packets and validation logs. No internet connection is required.</footer>
<script id="data" type="application/json">'''+data.replace('<','\\u003c')+'''</script>
<script>
'use strict';const data=JSON.parse(document.getElementById('data').textContent);
const $=id=>document.getElementById(id);let matching=[];
function cell(row,text){const td=document.createElement('td');td.textContent=text;row.appendChild(td);}
function refresh(){const kind=$('kind').value;const q=$('search').value.trim().toLowerCase().replace(/\\s+/g,'');
 matching=data[kind].filter(r=>{if(kind==='curves'&&$('empty').checked&&r.points.length)return false;
 const key=kind==='curves'?[r.coefficients.join(','),...r.categories].join('|'):[r.p,r.a,r.q,r.b,r.n].join('|');return key.toLowerCase().includes(q);});
 $('scope').textContent=kind==='curves'?'Each row gives every integer point of y²=f(x). Coefficients run from constant term to x⁴.':'Complete for distinct primes p<q≤1,000 and exponents 1≤a,b≤8. This is a finite grid, not a global two-prime classification.';
 $('count').textContent=matching.length+' matching rows. Showing the first '+Math.min(100,matching.length)+'. Download contains every match.';
 const table=document.createElement('table');const head=document.createElement('tr');
 for(const label of(kind==='curves'?['Coefficients [z,w,v,u,1]','All integer points (x,y)','Bound |x|','Category']:['Prime powers','n','sigma(n) = root²','Both factors squares'])){const th=document.createElement('th');th.textContent=label;head.appendChild(th);}table.appendChild(head);
 for(const r of matching.slice(0,100)){const row=document.createElement('tr');if(kind==='curves'){cell(row,r.coefficients.join(', '));cell(row,r.points.length?r.points.map(p=>'('+p.join(', ')+')').join('  '):'No integer points');cell(row,r.coordinate_bound);cell(row,r.categories.join(', '));}else{cell(row,r.p+'^'+r.a+' × '+r.q+'^'+r.b);cell(row,r.n);cell(row,r.sigma+' = '+r.root+'²');cell(row,r.both_factors_square?'Yes':'No — matching nonsquare factors');}table.appendChild(row);}
 $('table').replaceChildren(table);}
for(const id of ['kind','search','empty'])$(id).addEventListener('input',refresh);
$('download').addEventListener('click',()=>{const blob=new Blob([JSON.stringify({integer_encoding:'decimal_strings',collection:$('kind').value,rows:matching},null,2)],{type:'application/json'});const url=URL.createObjectURL(blob);const a=document.createElement('a');a.href=url;a.download='perfectpower-selected-results.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);});refresh();
</script></html>'''

    return (html.replace('3,080',f"{summary['complete_quartic_equations']:,}")
                .replace('5,401',f"{summary['integer_points_across_equations']:,}")
                .replace('218 square',f"{summary['prime_pair_square_hits']:,} square")
                .replace('1,000,000',f"{summary['bounded_domain'][1]:,}")
                .replace('6,871',f"{summary['bounded_hits']['2']:,}")
                .replace('q≤1,000',f"q≤{summary.get('prime_limit',1000):,}")
                .replace('a,b≤8',f"a,b≤{summary.get('max_exponent',8)}"))
