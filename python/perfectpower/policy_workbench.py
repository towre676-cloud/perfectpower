"""Offline SVG policy viewer; exact BigInt rational decisions in the browser."""
from pathlib import Path
from .catalogue import encoded


def write_html(policy,path):
    packet=policy.evidence()
    if packet['status']!='COMPLETE_DECISION_REGIONS' or len(packet['target_basis'][0])!=2:raise ValueError('complete two-parameter policy required')
    data={k:packet[k] for k in ('cells','target_box','target_origin','target_basis')}
    data['target_box']=list(map(str,data['target_box']))
    for cell in data['cells']:cell['setting']=list(map(str,cell['setting']))
    payload=encoded(data).replace('<','\\u003c')
    document='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Exact setting policy</title>
<style>body{font:17px system-ui;max-width:1050px;margin:40px auto;padding:0 24px;color:#173348;background:#f4f7f8}main{display:flex;gap:30px;flex-wrap:wrap}svg{width:480px;max-width:100%;background:white;border:1px solid #bdcbd4}section{flex:1;min-width:260px}input{font:inherit;width:160px;padding:8px}label{display:block;margin:20px 0}pre{white-space:pre-wrap;background:white;padding:18px}p{line-height:1.6}</style>
<h1>Exact setting policy</h1><p>Choose an operating point. Regions show which integer settings minimize the declared calibration cost. Boundaries retain every tied setting.</p>
<main><svg id="map" viewBox="0 0 480 480" aria-label="Calibration regions"></svg><section><label>First target parameter <input id="x" value="1/2"></label><label>Second target parameter <input id="y" value="1/2"></label><pre id="result"></pre></section></main>
<p>The geometry is drawn approximately. Decisions use exact rational arithmetic; enter integers, decimals or fractions.</p>
<script id="data" type="application/json">PAYLOAD</script><script>
const data=JSON.parse(document.getElementById('data').textContent),map=document.getElementById('map'),x=document.getElementById('x'),y=document.getElementById('y'),result=document.getElementById('result');
function rat(v){let s=String(v),a=s.split('/');if(a.length===2)return [BigInt(a[0]),BigInt(a[1])];a=s.split('.');if(a.length===2){const sign=s.startsWith('-')?-1n:1n;return [sign*BigInt(a[0].replace('-','')+a[1]),10n**BigInt(a[1].length)]}return [BigInt(s),1n]}
function add(a,b){return [a[0]*b[1]+b[0]*a[1],a[1]*b[1]]}function mul(a,b){return [a[0]*b[0],a[1]*b[1]]}function le(a,b){if(a[1]<=0n||b[1]<=0n)throw Error('positive denominators required');return a[0]*b[1]<=b[0]*a[1]}
function num(v){const a=rat(v);return Number(a[0])/Number(a[1])}const box=data.target_box.map(num);
function coord(v){return [20+440*(num(v[0])-box[0])/(box[1]-box[0]),460-440*(num(v[1])-box[2])/(box[3]-box[2])]}
const ns='http://www.w3.org/2000/svg';function element(name,attrs){const e=document.createElementNS(ns,name);Object.entries(attrs).forEach(([k,v])=>e.setAttribute(k,v));map.append(e);return e}
data.cells.forEach((c,i)=>{const pts=c.vertices.map(coord),colour=`hsl(${(i*137)%360},55%,78%)`;if(pts.length===1)element('circle',{cx:pts[0][0],cy:pts[0][1],r:4,fill:colour,stroke:'#173348'});else element(c.dimension===1?'polyline':'polygon',{points:pts.map(v=>v.join(',')).join(' '),fill:c.dimension===1?'none':colour,stroke:'#173348','stroke-width':1});if(c.dimension===2){const centre=pts.reduce((a,v)=>[a[0]+v[0]/pts.length,a[1]+v[1]/pts.length],[0,0]);element('text',{x:centre[0],y:centre[1],'text-anchor':'middle','font-size':10}).textContent=c.setting.join(',')}});
const cursor=element('circle',{cx:0,cy:0,r:6,fill:'#173348',stroke:'white','stroke-width':2});
function draw(){try{const point=[rat(x.value),rat(y.value)];for(let i=0;i<2;i++)if(!le(rat(data.target_box[2*i]),point[i])||!le(point[i],rat(data.target_box[2*i+1])))throw Error('Point outside the policy box');const winners=data.cells.filter(c=>c.inequalities.every(g=>le(g.normal.reduce((s,v,i)=>add(s,mul(rat(v),point[i])),[0n,1n]),rat(g.rhs)))).map(c=>c.setting);const pos=coord([x.value,y.value]);cursor.setAttribute('cx',pos[0]);cursor.setAttribute('cy',pos[1]);result.textContent=JSON.stringify({parameter:[x.value,y.value],minimizers:winners,tie:winners.length>1},null,2)}catch(error){result.textContent=String(error)}}
[x,y].forEach(e=>e.addEventListener('input',draw));draw();
</script></html>'''.replace('PAYLOAD',payload)
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(document)
    return dict(path=str(path),cells=len(packet['cells']))
