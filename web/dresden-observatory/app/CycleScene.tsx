'use client';
import {useEffect,useRef,useState} from 'react';
import {RotateCcw,Move} from 'lucide-react';
import type {WebGPURenderer,Scene,Mesh} from 'three/webgpu';
import eclipse from '@/lib/data/eclipse_stations.json';

type Props={day:number;mode:'calendar'|'eclipse';selected:number;onSelect:(n:number)=>void;playing:boolean};
export default function CycleScene(props:Props){
 const host=useRef<HTMLDivElement>(null),current=useRef(props),reset=useRef<()=>void>(()=>{});
 const [backend,setBackend]=useState('Preparing the observatory'),[error,setError]=useState('');current.current=props;
 useEffect(()=>{let disposed=false,renderer:WebGPURenderer|undefined,scene:Scene|undefined,cleanup=()=>{};
  async function start(){
   const THREE=await import('three/webgpu');const {OrbitControls}=await import('three/addons/controls/OrbitControls.js');
   if(disposed||!host.current)return;const box=host.current;
   renderer=new THREE.WebGPURenderer({antialias:true,alpha:true});renderer.setPixelRatio(Math.min(devicePixelRatio,2));
   await renderer.init();if(disposed){renderer.dispose();return;}
   setBackend((renderer.backend as unknown as {isWebGPUBackend?:boolean}).isWebGPUBackend?'WebGPU':'WebGL 2');
   box.appendChild(renderer.domElement);renderer.domElement.setAttribute('aria-label','Interactive three-dimensional calendar rings. Drag to rotate; scroll to zoom.');renderer.domElement.setAttribute('role','img');
   scene=new THREE.Scene();const camera=new THREE.PerspectiveCamera(38,1,.1,100);camera.position.set(7,8,10);
   const controls=new OrbitControls(camera,renderer.domElement);controls.enableDamping=true;controls.enablePan=false;controls.minDistance=7;controls.maxDistance=20;controls.maxPolarAngle=Math.PI*.8;controls.target.set(0,.25,0);
   reset.current=()=>{camera.position.set(7,8,10);controls.target.set(0,.25,0);controls.update();};
   scene.add(new THREE.AmbientLight(0xb9cbd8,2));const key=new THREE.DirectionalLight(0xffe2b8,4);key.position.set(4,7,5);scene.add(key);
   const group=new THREE.Group();scene.add(group);
   const rings:[number,number,string][]=[[13,1.45,'#d49865'],[20,2.15,'#e8d4af'],[365,3.02,'#5eb6b4'],[584,3.9,'#869db6']];
   const markers:Mesh[]=[],calendarObjects:Mesh[]=[],stationObjects:Mesh[]=[];
   rings.forEach(([period,radius,color],j)=>{
    const geometry=new THREE.TorusGeometry(radius,.026,8,180),material=new THREE.MeshStandardMaterial({color,metalness:.7,roughness:.32});const ring=new THREE.Mesh(geometry,material);ring.rotation.x=Math.PI/2;ring.position.y=j*.16;group.add(ring);calendarObjects.push(ring);
    const tickN=period===365?73:period===584?73:period;
    for(let i=0;i<tickN;i++){const angle=i/tickN*Math.PI*2;const tick=new THREE.Mesh(new THREE.BoxGeometry(.018,.025,.12),new THREE.MeshBasicMaterial({color,transparent:true,opacity:.5}));tick.position.set(Math.cos(angle)*radius,j*.16,Math.sin(angle)*radius);tick.rotation.y=-angle+Math.PI/2;group.add(tick);calendarObjects.push(tick);}
    const marker=new THREE.Mesh(new THREE.SphereGeometry(.105,16,12),new THREE.MeshStandardMaterial({color,emissive:color,emissiveIntensity:.6,metalness:.4,roughness:.2}));group.add(marker);markers.push(marker);
   });
   const core=new THREE.Mesh(new THREE.TorusGeometry(.68,.028,8,100),new THREE.MeshBasicMaterial({color:'#d49865'}));core.rotation.x=Math.PI/2;core.position.y=.2;group.add(core);
   const connectorGeometry=new THREE.BufferGeometry().setFromPoints([new THREE.Vector3(0,0,0),new THREE.Vector3(4,0,0)]);const hand=new THREE.Line(connectorGeometry,new THREE.LineBasicMaterial({color:'#d49865',transparent:true,opacity:.45}));hand.position.y=.6;group.add(hand);
   eclipse.stations.forEach(r=>{const a=r.month/405*Math.PI*2-Math.PI/2;const p=new THREE.Mesh(new THREE.SphereGeometry(.075,12,8),new THREE.MeshStandardMaterial({color:r.station===19?'#ea817c':r.classification==='intended'?'#dca478':'#5a7289',emissive:r.classification==='intended'?'#835027':'#172839',emissiveIntensity:.5}));p.position.set(Math.cos(a)*3.9,.42,Math.sin(a)*3.9);p.userData.station=r.station;group.add(p);stationObjects.push(p);});
   const ray=new THREE.Raycaster(),pointer=new THREE.Vector2();let down=[0,0];
   const pointerDown=(e:PointerEvent)=>{down=[e.clientX,e.clientY];};
   const pointerUp=(e:PointerEvent)=>{if(current.current.mode!=='eclipse'||Math.hypot(e.clientX-down[0],e.clientY-down[1])>6)return;const b=renderer!.domElement.getBoundingClientRect();pointer.set((e.clientX-b.left)/b.width*2-1,-(e.clientY-b.top)/b.height*2+1);ray.setFromCamera(pointer,camera);const hits=ray.intersectObjects(stationObjects);if(hits[0])current.current.onSelect(hits[0].object.userData.station);};
   renderer.domElement.addEventListener('pointerdown',pointerDown);renderer.domElement.addEventListener('pointerup',pointerUp);
   const resize=()=>{if(!renderer)return;const w=box.clientWidth,h=box.clientHeight;renderer.setSize(w,h);camera.aspect=w/h;camera.updateProjectionMatrix();};const observer=new ResizeObserver(resize);observer.observe(box);resize();
   renderer.setAnimationLoop(()=>{if(disposed||!renderer||!scene)return;const {day,mode,selected}=current.current;calendarObjects.forEach(o=>o.visible=mode==='calendar');markers.forEach((m,j)=>{m.visible=mode==='calendar';const [period,radius]=rings[j];const a=day/period*Math.PI*2-Math.PI/2;m.position.set(Math.cos(a)*radius,j*.16,Math.sin(a)*radius);});stationObjects.forEach(o=>{o.visible=mode==='eclipse';o.scale.setScalar(o.userData.station===selected?2.1:1);});hand.rotation.y=-(mode==='eclipse'?eclipse.stations[selected-1].month/405:day/584)*Math.PI*2+Math.PI/2;controls.update();renderer.render(scene,camera);});
   cleanup=()=>{observer.disconnect();controls.dispose();renderer?.domElement.removeEventListener('pointerdown',pointerDown);renderer?.domElement.removeEventListener('pointerup',pointerUp);renderer?.setAnimationLoop(null);scene?.traverse(o=>{const m=o as Mesh;m.geometry?.dispose();const mats=Array.isArray(m.material)?m.material:[m.material];mats.forEach(a=>a?.dispose());});renderer?.dispose();renderer?.domElement.remove();};
  }
  start().catch(()=>{if(!disposed){setError('3D is unavailable in this browser. The timeline, calendar calculations and source views remain available.');setBackend('2D research views');}});
  return()=>{disposed=true;cleanup();};
 },[]);
 return <div className="scene-shell"><div className="scene-host" ref={host}/>{error&&<><svg className="scene-fallback" viewBox="0 0 500 360" role="img" aria-label="Two-dimensional calendar and eclipse phase projection">{[58,89,120,151].map((radius,j)=><circle key={radius} cx="250" cy="180" r={radius} fill="none" stroke={['#d49865','#e8d4af','#5eb6b4','#869db6'][j]} strokeWidth="1.5"/>)}{props.mode==='calendar'?[13,20,365,584].map((period,j)=>{const radius=[58,89,120,151][j],angle=props.day/period*Math.PI*2-Math.PI/2;return <circle key={period} cx={250+Math.cos(angle)*radius} cy={180+Math.sin(angle)*radius} r="6" fill={['#d49865','#e8d4af','#5eb6b4','#869db6'][j]}/>;}):eclipse.stations.map(r=>{const angle=r.month/405*Math.PI*2-Math.PI/2;return <circle key={r.station} cx={250+Math.cos(angle)*151} cy={180+Math.sin(angle)*151} r={r.station===props.selected?6:3} fill={r.station===19?'#ea817c':r.classification==='intended'?'#d49865':'#869db6'} role="button" tabIndex={0} aria-label={`Select station ${r.station}`} onClick={()=>props.onSelect(r.station)} onKeyDown={e=>{if(e.key==='Enter'||e.key===' '){e.preventDefault();props.onSelect(r.station);}}}/>;})}</svg><p className="scene-error scene-error-small">{error}</p></>}<div className="scene-top"><span className="eyebrow">{props.mode==='calendar'?'Interlocking calendar phases':'69 stations / 405 lunations'}</span><span className="backend">{backend}</span></div><div className="scene-bottom"><span><Move size={14}/> {error?'2D phase projection':'Drag to orbit · scroll to zoom'}</span><button className="quiet" onClick={()=>reset.current()} aria-label="Reset camera"><RotateCcw size={14}/>Reset view</button></div><div className="scene-watermark">{props.mode==='calendar'?'13 · 20 · 365 · 584':'11,959'}</div></div>;
}
