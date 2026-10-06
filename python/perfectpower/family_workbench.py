"""Offline inspection of precomputed marked period continuations."""
from pathlib import Path
from .catalogue import encoded


def write_workbench(cases,path):
    payload=encoded(cases).replace('<','\\u003c')
    document='''<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>Curve family workbench</title>
<style>body{font:17px system-ui;color:#163348;background:#f3f6f8;max-width:1080px;margin:40px auto;padding:0 24px}h1{font-size:38px}p{line-height:1.6}main{display:flex;gap:30px;flex-wrap:wrap}section{flex:1;min-width:280px}svg{width:100%;background:white;border:1px solid #ccd8e0}pre{font:14px ui-monospace,monospace;white-space:pre-wrap;background:white;padding:20px;max-height:500px;overflow:auto}select{font:inherit;padding:8px}input{width:100%}.badge{background:#d8ecee;padding:10px;display:inline-block;border-radius:6px}</style>
<h1>Polynomial structure into period response</h1><p>Select a family and inspect its marked period along the recorded parameter path. The differential equation is derived exactly from the polynomial. Values plotted here are numerical continuation samples.</p>
<select id="family" aria-label="Curve family"></select><main><section><h2>Marked period magnitude</h2><svg id="plot" viewBox="0 0 600 340" aria-label="Numerical period magnitude versus parameter"></svg><p>Parameter sample <span id="parameter"></span></p><input id="sample" type="range" min="0" max="20" value="0" aria-label="Recorded parameter sample"><p id="value"></p></section><section><h2>Compiled differential object</h2><p class="badge" id="dimensions"></p><pre id="operator"></pre><p>Coefficients below multiply F, F′, F″ and successive derivatives. Each coefficient array is ordered from constant term to highest parameter power.</p></section></main><h2>Continuation evidence</h2><pre id="evidence"></pre>
<script type="application/json" id="data">PAYLOAD</script><script>
const cases=JSON.parse(document.getElementById('data').textContent),select=document.getElementById('family'),slider=document.getElementById('sample'),plot=document.getElementById('plot');
Object.keys(cases).forEach(name=>{const option=document.createElement('option');option.value=name;option.textContent=name.replaceAll('_',' ');select.append(option)});
function draw(){const c=cases[select.value],rows=c.continuation.trajectory,index=Number(slider.value),row=rows[index],values=rows.map(r=>Math.hypot(...r.observable)),lo=Math.min(...values),hi=Math.max(...values),span=hi-lo||1;
const coords=values.map((v,i)=>[35+530*i/(rows.length-1),290-240*(v-lo)/span]);plot.replaceChildren();const ns='http://www.w3.org/2000/svg';
function element(name,attrs,text){const e=document.createElementNS(ns,name);Object.entries(attrs).forEach(([k,v])=>e.setAttribute(k,v));if(text)e.textContent=text;plot.append(e)}
element('polyline',{points:coords.map(p=>p.join(',')).join(' '),fill:'none',stroke:'#167e87','stroke-width':3});element('circle',{cx:coords[index][0],cy:coords[index][1],r:6,fill:'#173348'});
element('text',{x:35,y:320,'font-size':14},rows[0].parameter.join(' + i '));element('text',{x:450,y:320,'font-size':14},rows.at(-1).parameter.join(' + i '));element('text',{x:35,y:25,'font-size':14},'|period| '+lo.toPrecision(5)+' to '+hi.toPrecision(5));
document.getElementById('parameter').textContent=row.parameter.join(' + i ');document.getElementById('value').textContent='Observable [real, imaginary]: '+JSON.stringify(row.observable);
document.getElementById('dimensions').textContent='Genus '+c.summary.genus+' · '+c.summary.state_dimension+' period coordinates · observable order '+c.observable.order;
document.getElementById('operator').textContent=JSON.stringify(c.observable.polynomial_operator,null,2);
document.getElementById('evidence').textContent=JSON.stringify({contour:c.continuation.initialization.contour,endpoint_comparisons:c.errors,parameter_segments_exclude_poles:c.continuation.path_exclusion.exact_no_excluded_zero_on_segments,numerical_error_certified:false},null,2)}
select.addEventListener('change',()=>{slider.value=0;slider.max=cases[select.value].continuation.trajectory.length-1;draw()});slider.addEventListener('input',draw);draw();
</script></html>'''.replace('PAYLOAD',payload)
    path=Path(path);path.parent.mkdir(parents=True,exist_ok=True);path.write_text(document)
