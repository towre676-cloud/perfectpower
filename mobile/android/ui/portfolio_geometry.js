import * as THREE from 'three';
import {OrbitControls} from 'three/addons/controls/OrbitControls.js';

const COLORS=['#67dbc0','#88b9ff','#d0a6ff','#ffbe83','#ff8ead'];
const e=x=>String(x??'').replace(/[&<>"']/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const integer=x=>{try{return BigInt(x).toLocaleString();}catch{return String(x??'—');}};
// Counts never pass through floating-point arithmetic. Only the final geometric ratio does.
export function share(value,total,units=10000n){const a=BigInt(value),b=BigInt(total);return b===0n?0:Number(a*units/b)/Number(units);}
export function resourceUse(spec,point){return spec.resources.map((_,k)=>spec.variables.reduce((sum,v,j)=>sum+BigInt(v.costs[k])*BigInt(point[j]??0),0n).toString());}
export function footprint(spec,resources,result,project){
 const selected=result?.selection?.point;
 return {project:spec.variables[project],use:selected?resourceUse(spec,selected):null,
         limits:resources.map(r=>({min:String(r.min??0),max:String(r.max)}))};
}
export function mountPortfolioGeometry(host,model,{onProject=()=>{},mode='live'}={}){
 const spec=model.specification;let result=null,resources=structuredClone(spec.resources),focus=0,axes=[0,1,2],disposed=false,sceneView=null;
 host.classList.add('portfolio-geometry');
 host.innerHTML=`<div class="geometry-heading"><div><div class="eyebrow">Geometric observatory</div><h2>See the shape of your choices.</h2><p>Rotate the resource prism, inspect a project, and trace the footprints of computed selections.</p></div><span class="geometry-mode">${mode==='retained'?'Retained engine results':'Connected to your exact results'}</span></div><div class="geometry-toolbar"><label>Horizontal axis<select data-geo-axis="0"></select></label><label>Vertical axis<select data-geo-axis="1"></select></label><label>Depth axis<select data-geo-axis="2"></select></label><button data-geo-reset>Reset view</button><button data-geo-motion aria-pressed="false">Start orbit</button></div><div class="geometry-grid"><section class="geometry-stage"><div data-geo-canvas class="geometry-canvas" role="img" aria-label="Interactive three-dimensional resource projection"></div><div class="geometry-stage-caption"><span><b class="geometry-dot mint"></b> Original projects</span><span><b class="geometry-dot gold"></b> Focused project</span><span><b class="geometry-dot violet"></b> Computed portfolio</span></div><p class="geometry-scope">The prism shows bounds for three selected resources. A project point is a single project’s cost, not a portfolio. The counting engine checks all five resources; a projection alone cannot establish feasibility.</p></section><section class="geometry-inspector"><label>Inspect an original project<select data-geo-project aria-label="Inspect original project">${spec.variables.map((v,j)=>`<option value="${j}">${e(v.name)}</option>`).join('')}</select></label><div data-geo-details></div><div data-geo-radar></div></section></div><section class="geometry-lens"><div><div class="eyebrow">Decision lens</div><h3>How a decision divides the possibilities</h3></div><div data-geo-branches></div></section><details class="geometry-matrix"><summary>The complete project-resource geometry</summary><p>Each tile compares one original project’s resource cost with the currently selected resource ceiling. Select a row to inspect it in the prism. Exact costs remain visible.</p><div data-geo-matrix></div></details>`;
 const $=s=>host.querySelector(s);
 for(const select of host.querySelectorAll('[data-geo-axis]')){select.innerHTML=spec.resources.map((r,k)=>`<option value="${k}">Resource ${k+1}</option>`).join('');select.value=String(axes[Number(select.dataset.geoAxis)]);select.onchange=()=>{const slot=Number(select.dataset.geoAxis),next=Number(select.value),old=axes[slot],other=axes.indexOf(next);if(other!==-1)axes[other]=old;axes[slot]=next;host.querySelectorAll('[data-geo-axis]').forEach(s=>s.value=String(axes[Number(s.dataset.geoAxis)]));sceneView?.update();};}
 function choose(j){focus=j;$('[data-geo-project]').value=String(j);render();onProject(j);}
 $('[data-geo-project]').onchange=evt=>choose(Number(evt.target.value));
 function radar(data){
  const cx=160,cy=145,r=102,angles=spec.resources.map((_,k)=>-Math.PI/2+k*2*Math.PI/5);
  const xy=(k,f)=>`${(cx+Math.cos(angles[k])*r*f).toFixed(2)},${(cy+Math.sin(angles[k])*r*f).toFixed(2)}`;
  const scaling=resources.map((bound,k)=>Math.max(1,Number(bound.max),Number(data.project.costs[k]),Number(data.use?.[k]??0)));
  const shape=values=>values.map((v,k)=>xy(k,Number(v)/scaling[k])).join(' ');
  const ceiling=resources.map(v=>Number(v.max)),floor=resources.map(v=>Number(v.min??0));
  return `<svg viewBox="0 0 320 290" role="img" aria-label="Five-resource footprint of the focused project and computed portfolio"><defs><linearGradient id="geo-radar-fill-${host.id}" x2="1" y2="1"><stop stop-color="#d7a4ff" stop-opacity=".35"/><stop offset="1" stop-color="#67dbc0" stop-opacity=".05"/></linearGradient></defs>${[.25,.5,.75,1].map(f=>`<polygon points="${angles.map((_,k)=>xy(k,f)).join(' ')}" fill="none" stroke="#b0d1db" stroke-opacity=".13"/>`).join('')}${angles.map((_,k)=>`<line x1="${cx}" y1="${cy}" x2="${xy(k,1).split(',')[0]}" y2="${xy(k,1).split(',')[1]}" stroke="${COLORS[k]}" stroke-opacity=".35"/><text x="${cx+Math.cos(angles[k])*(r+20)}" y="${cy+Math.sin(angles[k])*(r+20)+4}" text-anchor="middle" fill="${COLORS[k]}" font-size="12">R${k+1}</text>`).join('')}<polygon points="${shape(ceiling)}" fill="#67dbc0" fill-opacity=".05" stroke="#67dbc0" stroke-dasharray="5 5" stroke-width="1.5"/><polygon points="${shape(floor)}" fill="none" stroke="#88b9ff" stroke-dasharray="2 3"/>${data.use?`<polygon points="${shape(data.use)}" fill="url(#geo-radar-fill-${host.id})" stroke="#d7a4ff" stroke-width="2.5"/>`:''}<polygon points="${shape(data.project.costs)}" fill="#ffce88" fill-opacity=".16" stroke="#ffce88" stroke-width="2"/></svg><div class="geometry-radar-key"><span>Gold: focused project</span><span>Mint dashes: ceilings</span><span>Violet: computed portfolio</span></div><p class="geometry-small">Each spoke is scaled separately to keep the whole footprint visible. Read the exact resource table for numerical comparisons.</p>`;
 }
 function branches(){
  const c=result?.conditional;
  if(!c||!result.branches)return '<div class="geometry-wait">A conditional query will draw its actual include/exclude populations here. No population is inferred from the project cloud.</div>';
  const total=BigInt(c.count),bs=result.branches,root=BigInt(result.summary.count);
  const widths=bs.map(b=>share(b.count,total)*510),x=[35,35+widths[0]],count=integer(c.count);
  return `<svg viewBox="0 0 580 175" role="img" aria-label="Exact conditional decision split"><defs><linearGradient id="geo-branch-line-${host.id}"><stop stop-color="#67dbc0"/><stop offset="1" stop-color="#d0a6ff"/></linearGradient></defs><circle cx="290" cy="27" r="11" fill="#172c3b" stroke="#d0a6ff" stroke-width="2"/><path d="M290 39 Q290 65 162 89 M290 39 Q290 65 418 89" fill="none" stroke="url(#geo-branch-line-${host.id})" stroke-width="2"/><text x="290" y="65" text-anchor="middle" fill="#dce9ef" font-size="13">${e(count)} completions</text>${bs.map((b,i)=>`<rect x="${x[i]}" y="91" width="${Math.max(0,widths[i])}" height="13" rx="3" fill="${i?'#d0a6ff':'#67dbc0'}"/><text x="${i?418:162}" y="135" text-anchor="middle" fill="${i?'#d0a6ff':'#67dbc0'}" font-size="14">${i?'Include':'Exclude'} project_${c.prefix.length+1}</text><text x="${i?418:162}" y="158" text-anchor="middle" fill="#dce9ef" font-size="12">${e(integer(b.count))} choices · best ${e(b.maximum??'none')}</text>`).join('')}</svg><p class="geometry-small">${c.prefix.length} original decisions are fixed. ${integer(c.count)} / ${integer(root)} portfolios remain under these decisions and the computed resource limits. Widths are rounded drawing ratios; labels preserve exact integers.${total===0n?' This conditional population is empty.':''}</p>`;
 }
 function render(){
  if(disposed)return;
  const data=footprint(spec,resources,result,focus),v=data.project;
  $('[data-geo-details]').innerHTML=`<div class="geometry-project-title"><span>Project ${focus+1}</span><strong>${e(v.name)}</strong><b>Score ${e(v.profit)}</b></div><table><caption>Exact resource coordinates</caption><thead><tr><th>Resource</th><th>Project</th><th>Portfolio</th><th>Ceiling</th></tr></thead><tbody>${resources.map((r,k)=>`<tr><th style="color:${COLORS[k]}">R${k+1}</th><td>${integer(v.costs[k])}</td><td>${data.use?integer(data.use[k]):'—'}</td><td>${integer(r.max)}</td></tr>`).join('')}</tbody></table>${result?.selection?`<p class="geometry-small">Displayed portfolio score: ${e(result.selection.profit)}. ${mode==='retained'?'This is a retained exact engine result.':'This comes from your completed engine query.'}</p>`:'<p class="geometry-small">Calculate a portfolio to add its resource vector.</p>'}`;
  $('[data-geo-radar]').innerHTML=radar(data);$('[data-geo-branches]').innerHTML=branches();
  $('[data-geo-matrix]').innerHTML=`<div class="geometry-heatmap">${spec.variables.map((p,j)=>`<button data-geo-row="${j}" class="${focus===j?'geo-focused':''}" aria-label="Inspect ${e(p.name)}"><span>${e(p.name)}</span>${p.costs.map((cost,k)=>{const ratio=Math.min(1,Number(cost)/Math.max(1,Number(resources[k].max)));return `<b title="Resource ${k+1}: ${integer(cost)}" style="background:color-mix(in srgb,${COLORS[k]} ${20+ratio*75}%,#132330)">${integer(cost)}</b>`;}).join('')}</button>`).join('')}</div>`;
  host.querySelectorAll('[data-geo-row]').forEach(b=>b.onclick=()=>choose(Number(b.dataset.geoRow)));sceneView?.update();
 }
 function buildScene(){
  const container=$('[data-geo-canvas]');let renderer;
  try{renderer=new THREE.WebGLRenderer({antialias:true,alpha:true});}catch{return null;}
  renderer.setPixelRatio(Math.min(devicePixelRatio,1.5));renderer.setClearColor(0x0b1726,1);container.append(renderer.domElement);
  const scene=new THREE.Scene(),camera=new THREE.PerspectiveCamera(42,1,.01,50);camera.position.set(2.1,1.6,2.4);
  const controls=new OrbitControls(camera,renderer.domElement);controls.target.set(.4,.4,.4);controls.enableDamping=true;controls.dampingFactor=.07;controls.minDistance=.6;controls.maxDistance=7;controls.autoRotateSpeed=.45;controls.enablePan=false;
  scene.add(new THREE.AmbientLight(0xbbe2ff,2));const light=new THREE.DirectionalLight(0xffffff,3);light.position.set(3,4,2);scene.add(light);
  const content=new THREE.Group();scene.add(content);let meshes=[],frame,visible=true;
  const raycaster=new THREE.Raycaster(),mouse=new THREE.Vector2();
  function clean(){content.traverse(o=>{o.geometry?.dispose();if(o.material){for(const m of Array.isArray(o.material)?o.material:[o.material]){m.map?.dispose();m.dispose();}}});content.clear();meshes=[];}
  function line(points,color,opacity=1){const geometry=new THREE.BufferGeometry().setFromPoints(points.map(p=>new THREE.Vector3(...p)));const item=new THREE.Line(geometry,new THREE.LineBasicMaterial({color,transparent:true,opacity}));content.add(item);return item;}
  function label(text,position,color){const c=document.createElement('canvas');c.width=512;c.height=72;const ctx=c.getContext('2d');ctx.fillStyle=color;ctx.font='32px system-ui';ctx.textAlign='center';ctx.fillText(text,256,48);const texture=new THREE.CanvasTexture(c);const sprite=new THREE.Sprite(new THREE.SpriteMaterial({map:texture,transparent:true,depthTest:false}));sprite.position.set(...position);sprite.scale.set(.57,.08,1);content.add(sprite);}
  function update(){
   clean();const point=result?.selection?.point,use=point?resourceUse(spec,point):null;
   const scales=axes.map(k=>Math.max(1,Number(resources[k].max),...spec.variables.map(v=>Number(v.costs[k])),Number(use?.[k]??0)));
   const projectPoint=v=>axes.map((k,j)=>Number(v.costs[k])/scales[j]);
   const ceiling=axes.map((k,j)=>Number(resources[k].max)/scales[j]),floor=axes.map((k,j)=>Number(resources[k].min??0)/scales[j]);
   for(let j=0;j<3;j++){
    const end=[0,0,0];end[j]=1.06;line([[0,0,0],end],COLORS[axes[j]],.8);const pos=[.03,.03,.03];pos[j]=1.13;label(`R${axes[j]+1} · ${integer(scales[j])}`,pos,COLORS[axes[j]]);
   }
   for(let i=0;i<=10;i++){const q=i/10;line([[q,0,0],[q,0,1]],0x416175,.22);line([[0,0,q],[1,0,q]],0x416175,.22);}
   const dimensions=ceiling.map((v,j)=>Math.max(.0001,v-floor[j]));
   const box=new THREE.BoxGeometry(...dimensions),wire=new THREE.LineSegments(new THREE.EdgesGeometry(box),new THREE.LineBasicMaterial({color:0x67dbc0,transparent:true,opacity:.75}));box.dispose();wire.position.set(...ceiling.map((v,j)=>(v+floor[j])/2));content.add(wire);
   const volume=new THREE.Mesh(new THREE.BoxGeometry(...dimensions),new THREE.MeshBasicMaterial({color:0x67dbc0,transparent:true,opacity:.035,depthWrite:false,side:THREE.DoubleSide}));volume.position.copy(wire.position);content.add(volume);
   spec.variables.forEach((v,j)=>{
    const chosen=point?.[j]==='1'||point?.[j]===1,size=.009+Math.sqrt(Number(v.profit))/3000;
    const mesh=new THREE.Mesh(new THREE.IcosahedronGeometry(size*(focus===j?1.8:1),1),new THREE.MeshStandardMaterial({color:focus===j?0xffce88:chosen?0xd0a6ff:0x67dbc0,emissive:focus===j?0x5d3910:0x0b3e36,metalness:.35,roughness:.25}));mesh.position.set(...projectPoint(v));mesh.userData.project=j;content.add(mesh);meshes.push(mesh);
   });
   const fv=projectPoint(spec.variables[focus]);line([[0,0,0],fv],0xffce88,.85);line([[fv[0],0,0],[fv[0],fv[1],0],fv],0xffce88,.3);
   if(use){const end=axes.map((k,j)=>Number(use[k])/scales[j]);line([[0,0,0],end],0xd0a6ff,1);const marker=new THREE.Mesh(new THREE.OctahedronGeometry(.038),new THREE.MeshStandardMaterial({color:0xd0a6ff,emissive:0x54266b,metalness:.3,roughness:.2}));marker.position.set(...end);content.add(marker);label('Computed portfolio',end.map((v,j)=>v+(j===1?.075:0)),'#e6cbff');
    let sum=[0,0,0];const path=[[0,0,0]];spec.variables.forEach((v,j)=>{if(point[j]==='1'||point[j]===1){const delta=projectPoint(v);sum=sum.map((x,k)=>x+delta[k]);path.push([...sum]);}});line(path,0xd0a6ff,.45);
   }
  }
  const resize=new ResizeObserver(()=>{const w=container.clientWidth,h=container.clientHeight;if(!w||!h)return;renderer.setSize(w,h);camera.aspect=w/h;camera.updateProjectionMatrix();});resize.observe(container);
  const observer=new IntersectionObserver(entries=>{visible=entries[0].isIntersecting;});observer.observe(container);
  let down=null;const pointerDown=event=>{down=[event.clientX,event.clientY];},pointerUp=event=>{if(!down||Math.hypot(event.clientX-down[0],event.clientY-down[1])>5)return;const rect=renderer.domElement.getBoundingClientRect();mouse.set((event.clientX-rect.left)/rect.width*2-1,-(event.clientY-rect.top)/rect.height*2+1);raycaster.setFromCamera(mouse,camera);const hits=raycaster.intersectObjects(meshes);if(hits.length)choose(hits[0].object.userData.project);};
  renderer.domElement.addEventListener('pointerdown',pointerDown);renderer.domElement.addEventListener('pointerup',pointerUp);
  function draw(){frame=requestAnimationFrame(draw);if(visible&&!document.hidden){controls.update();renderer.render(scene,camera);}}draw();
  const reset=()=>{camera.position.set(2.1,1.6,2.4);controls.target.set(.4,.4,.4);};
  const orbit=enabled=>{controls.autoRotate=enabled&&!matchMedia('(prefers-reduced-motion: reduce)').matches;};
  return {update,reset,orbit,dispose(){cancelAnimationFrame(frame);resize.disconnect();observer.disconnect();controls.dispose();clean();renderer.dispose();renderer.domElement.remove();}};
 }
 sceneView=buildScene();if(!sceneView)$('[data-geo-canvas]').innerHTML='<div class="geometry-fallback">3D acceleration is unavailable. The five-resource footprint, exact tables, decision lens and project matrix remain fully usable.</div>';
 $('[data-geo-reset]').onclick=()=>sceneView?.reset();$('[data-geo-motion]').onclick=event=>{const next=event.currentTarget.getAttribute('aria-pressed')!=='true';event.currentTarget.setAttribute('aria-pressed',String(next));event.currentTarget.textContent=next?'Stop orbit':'Start orbit';sceneView?.orbit(next);};render();
 return {update(nextResources,nextResult){resources=structuredClone(nextResources);result=nextResult;render();},focus:choose,dispose(){disposed=true;sceneView?.dispose();host.replaceChildren();}};
}
