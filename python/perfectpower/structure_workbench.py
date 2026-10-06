"""Inspect recorded root geometry alongside exact structural explanations."""
from pathlib import Path
from .catalogue import encoded


def write_workbench(cases,path):
    payload=encoded(cases).replace('<','\\u003c')
    html='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Polynomial structure workbench</title>
<style>body{font:17px system-ui;color:#173348;background:#f3f6f8;max-width:1160px;margin:36px auto;padding:0 24px}h1{font-size:38px}p{line-height:1.6}main{display:grid;grid-template-columns:1fr 1fr;gap:24px}svg{width:100%;background:white;border:1px solid #c9d9df}pre{font:13px ui-monospace,monospace;white-space:pre-wrap;background:white;padding:18px;max-height:390px;overflow:auto}select{font:inherit;padding:8px}input[type=range]{width:100%}.badge{background:#d9eeee;border-radius:6px;padding:12px}@media(max-width:750px){main{grid-template-columns:1fr}h1{font-size:30px}}</style>
<h1>Read the geometry inside the polynomial</h1><p>Explore three recorded families. Root positions show how the polynomial changes; exact identities explain whether this changes the curve's shape, approaches a node, or preserves two elliptic quotients. Teal segments indicate root velocity, shortened for display. Orange markers locate colliding roots for the generic quintic.</p>
<select id="family" aria-label="Polynomial family"></select><p class="badge" id="diagnosis"></p>
<main><section><svg id="plot" viewBox="0 0 600 480" aria-label="Complex roots and root velocities"></svg><p id="parameter"></p><input id="sample" type="range" min="0" value="0" aria-label="Recorded parameter sample"><label><input id="normalize" type="checkbox"> Show shape coordinates</label><p id="coordinates"></p><p id="polynomial"></p></section><section><h2>Exact structural explanation</h2><pre id="explanation"></pre><h2>Differential consequence</h2><pre id="operator"></pre></section></main>
<p>All root locations and plotted velocities are numerical approximations. The coordinate identities, quotient maps and differential operators are exact rational algebra. This viewer selects precomputed samples; it does not perform symbolic calculations or certify numerical root locations.</p>
<script type="application/json" id="data">PAYLOAD</script><script>
const cases=JSON.parse(document.getElementById('data').textContent),select=document.getElementById('family'),slider=document.getElementById('sample'),normalize=document.getElementById('normalize'),plot=document.getElementById('plot');
Object.entries(cases).forEach(([key,c])=>{const e=document.createElement('option');e.value=key;e.textContent=c.title;select.append(e)});
function draw(){const c=cases[select.value],row=c.samples[Number(slider.value)],shape=normalize.checked,roots=shape?row.shape_roots:row.roots,velocity=shape?row.shape_velocities:row.velocities;
const radius=Math.max(1,...roots.map(p=>Math.hypot(...p)))*1.32,scale=190/radius,point=p=>[300+p[0]*scale,240-p[1]*scale],ns='http://www.w3.org/2000/svg';plot.replaceChildren();
function element(name,attrs,text){const e=document.createElementNS(ns,name);Object.entries(attrs).forEach(([k,v])=>e.setAttribute(k,v));if(text)e.textContent=text;plot.append(e)}
element('line',{x1:30,y1:240,x2:570,y2:240,stroke:'#d6e0e6'});element('line',{x1:300,y1:30,x2:300,y2:450,stroke:'#d6e0e6'});
roots.forEach((p,i)=>{const q=point(p),v=velocity[i],length=Math.hypot(...v),factor=.12/Math.max(1,length),end=point([p[0]+factor*v[0],p[1]+factor*v[1]]);element('line',{x1:q[0],y1:q[1],x2:end[0],y2:end[1],stroke:'#167e87','stroke-width':3});element('circle',{cx:q[0],cy:q[1],r:5,fill:'#173348'});element('text',{x:q[0]+8,y:q[1]-8,'font-size':12},String(i+1))});
if(!shape)(c.collision_roots||[]).forEach(p=>{const q=point(p);element('circle',{cx:q[0],cy:q[1],r:8,fill:'none',stroke:'#bc641f','stroke-width':2})});
element('text',{x:35,y:30,'font-size':14},(shape?'Shape coordinates':'Original x coordinates')+' · axis radius '+radius.toPrecision(4));
document.getElementById('parameter').textContent='t = '+row.parameter+' · '+roots.length+' roots';document.getElementById('coordinates').textContent=c.shape_coordinate;
document.getElementById('polynomial').textContent=c.polynomial;document.getElementById('diagnosis').textContent=c.diagnosis;
document.getElementById('explanation').textContent=JSON.stringify(c.explanation,null,2);document.getElementById('operator').textContent=JSON.stringify(c.operator,null,2)}
select.addEventListener('change',()=>{slider.value=0;slider.max=cases[select.value].samples.length-1;draw()});slider.addEventListener('input',draw);normalize.addEventListener('change',draw);select.value=Object.keys(cases)[0];slider.max=cases[select.value].samples.length-1;draw();
</script></html>'''
    Path(path).write_text(html.replace('PAYLOAD',payload))
