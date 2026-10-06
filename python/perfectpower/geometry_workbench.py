"""Offline interactive client for exact local metric packets."""
import json
from pathlib import Path


def write_html(workbench, path, resolution=9):
    panels = {}
    for name, packet in workbench.packets.items():
        grid = workbench.grid(name, resolution)
        transport={}
        if packet['chart_data']['chart'] in ('branch','infinity'):
            for target,panel in workbench.packets.items():
                if panel['chart_data']['chart']=='finite' and workbench.transition(name,target)['complete']:
                    transport[target]=[workbench.transport(name,target,row['point']) for row in grid]
        panels[name] = dict(chart=packet['chart_data']['chart'], box=packet['box'], grid=grid,
                            paths=[workbench.segment(name, grid[0]['point'], row['point']) for row in grid],transport=transport)
    payload = json.dumps(dict(resolution=resolution, panels=panels)).replace('<', '\\u003c')
    document = '''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>PerfectPower local geometry</title>
<style>body{margin:40px auto;max-width:960px;font:17px system-ui;color:#173348;background:#f4f7f8;padding:0 24px}h1{font-size:32px}main{display:flex;gap:30px;flex-wrap:wrap}canvas{border:1px solid #ccd7dd;max-width:100%;height:auto}section{flex:1;min-width:260px}label{display:block;margin:16px 0}pre{white-space:pre-wrap;background:white;padding:18px;border-radius:8px;font-size:14px}select,input{font:inherit}p{line-height:1.6}</style>
<h1>Exact local geometry workbench</h1><p>Inspect finite, branch and infinity panels. Each displayed point has rational density bounds and a certified straight-path length interval from the panel's lower corner.</p>
<main><canvas id="map" width="440" height="440"></canvas><section><label>Panel <select id="panel"></select></label>
<label>Horizontal grid index <input id="x" type="range" min="0"></label><label>Vertical grid index <input id="y" type="range" min="0"></label>
<pre id="detail"></pre></section></main><p>The colour map uses approximate midpoints for display. The readout retains exact rational bounds. Certified overlap transports appear when the full source panel fits a finite panel. Straight paths stay inside one panel.</p>
<script id="data" type="application/json">PAYLOAD</script><script>
const data=JSON.parse(document.getElementById('data').textContent), n=data.resolution;
const panel=document.getElementById('panel'), x=document.getElementById('x'), y=document.getElementById('y'), canvas=document.getElementById('map'), ctx=canvas.getContext('2d');
Object.keys(data.panels).forEach(k=>{const o=document.createElement('option');o.value=k;o.textContent=k;panel.append(o)});
x.max=y.max=n-1;x.value=y.value=Math.floor(n/2);
function rational(s){const a=s.split('/');return Number(a[0])/(a[1]?Number(a[1]):1)}
function draw(){const p=data.panels[panel.value], mid=p.grid.map(r=>(rational(r.density_interval[0])+rational(r.density_interval[1]))/2), lo=Math.min(...mid), hi=Math.max(...mid), w=canvas.width/n;
mid.forEach((v,i)=>{const t=hi===lo?.5:(v-lo)/(hi-lo);ctx.fillStyle=`hsl(${195-40*t},65%,${85-45*t}%)`;ctx.fillRect((i%n)*w,(n-1-Math.floor(i/n))*w,w+1,w+1)});
const i=Number(y.value)*n+Number(x.value);ctx.strokeStyle='#fb6f3d';ctx.lineWidth=4;ctx.strokeRect(Number(x.value)*w+2,(n-1-Number(y.value))*w+2,w-4,w-4);
document.getElementById('detail').textContent=JSON.stringify({chart:p.chart,box:p.box,point:p.grid[i].point,density_interval:p.grid[i].density_interval,path_from_lower_corner:p.paths[i],certified_transports:Object.fromEntries(Object.entries(p.transport).map(([target,rows])=>[target,rows[i]]))},null,2)}
[panel,x,y].forEach(e=>e.addEventListener('input',draw));draw();
</script></html>'''.replace('PAYLOAD', payload)
    path = Path(path); path.parent.mkdir(parents=True, exist_ok=True); path.write_text(document)
    return dict(path=str(path), panels=len(panels), points_per_panel=resolution**2)
