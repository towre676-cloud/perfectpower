import React, {useEffect, useRef, useState} from 'react';
import {createRoot} from 'react-dom/client';
import {createResonanceScene} from './resonance-scene.js';
import envelope from './atlas-data.json';

const DATA=JSON.parse(envelope.payload_json);
const MODES=[
 {name:'The framework',sub:'384 · 264 · E₈',title:'The connected field',text:'The original blue, violet, coral and gold arrangement becomes a continuous three-dimensional scene. Flowing paths show the relationships being explored; their choreography is schematic.'},
 {name:'Resonance',sub:'The phase torus',title:'A finer circle',text:'Q = exp(iπ/221760), q = exp(iπ/840), and Q²⁶⁴ = q. The fiber contains 264 branches: 240 primitive and 24 of lower conductor. The torus and knot are visual motifs rather than a physical model.'},
 {name:'Higher structure',sub:'The ascending tower',title:'Layers of structure',text:'The rising, braided tower preserves the higher-category motif of the supplied references. It is a conceptual illustration. The implemented exact phase maps and Coxeter action do not by themselves establish a higher categorical equivalence.'},
 {name:'The nerve',sub:'Simplices & connection',title:'A language of connections',text:'Lines, triangles and tetrahedra echo the original nerve construction. These simplices are schematic. The exact integral families remain available in the calculators and monograph.'}
];
const NODE_KEYS={cyclotomic:'left',e8:'right',bridge:'upper',convergence:'lower',fiber:'center'};
const ANCHORS=[
 {key:'left',className:'blue',name:'Cyclotomic field',value:'384 conjugates',detail:'φ(1680) = 384. The phase q is a primitive 1680th root of unity. Its 56th power is a primitive 30th root.'},
 {key:'right',className:'coral',name:'E₈ root system',value:'240 roots + 8 Cartan directions',detail:'The coral cloud uses the exported E₈ root projection. Its 240 roots form eight Coxeter orbits of length 30. The Lie algebra has dimension 248.'},
 {key:'upper',className:'violet',name:'Phase bridge',value:'q⁵⁶ = ζ₃₀',detail:'The eight primitive 30th-root eigenphases are reached from the 384 primitive 1680th-root phases, each with multiplicity 48.'},
 {key:'center',className:'lavender',name:'The refined fiber',value:'264 branches',detail:'The power map z ↦ z²⁶⁴ has 264 preimages of q. Exactly 240 are primitive at conductor 443520. These branches are distinct mathematical objects from the E₈ roots.'},
 {key:'lower',className:'gold',name:'Integral synthesis',value:'Raghava · periods · Mellin',detail:'Raghava’s arcsine moment family gives exact powers of π. Refining π/840 to π/221760 scales moment order j by 264⁻²ʲ. The E₈ root and Cartan Mellin terms cancel at weight 2.'}
];

export function ResonanceExperience(){
 const host=useRef(null),scene=useRef(null),labels=useRef({}),progress=useRef(null),clock=useRef(null);
 const [mode,setMode]=useState(0),[playing,setPlaying]=useState(true),[auto,setAuto]=useState(true),[settings,setSettings]=useState(false),[detail,setDetail]=useState(null),[error,setError]=useState(''),[ready,setReady]=useState(false),[speed,setSpeed]=useState(1),[glow,setGlow]=useState(1),[quiet,setQuiet]=useState(false),[notice,setNotice]=useState(''),[reduced,setReduced]=useState(false);
 const modeRef=useRef(0);
 useEffect(()=>{
  let firstFrame=true;
  const reducedMotion=window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  setReduced(reducedMotion);setPlaying(!reducedMotion);
  try{
   const api=createResonanceScene(host.current,{data:DATA,onError:e=>setError(String(e?.message||e)),onSelect:key=>{const item=ANCHORS.find(x=>x.key===(NODE_KEYS[key]||key));if(item)setDetail(item);},onFrame:frame=>{
    if(firstFrame){firstFrame=false;setReady(true);}
    if(Number.isInteger(frame.mode)&&frame.mode!==modeRef.current){modeRef.current=frame.mode;setMode(frame.mode);}
    if(progress.current)progress.current.style.transform=`scaleX(${Math.max(0,Math.min(1,frame.progress||0))})`;
    if(clock.current)clock.current.textContent=`${String(Math.floor((frame.elapsed||0)/60)).padStart(2,'0')}:${String(Math.floor((frame.elapsed||0)%60)).padStart(2,'0')}`;
    if(frame.nodes)for(const item of ANCHORS){const node=labels.current[item.key],p=Array.isArray(frame.nodes)?frame.nodes.find(n=>(NODE_KEYS[n.id]||n.id)===item.key):frame.nodes[item.key];if(node&&p){const margin=host.current.clientWidth<580?58:82;node.style.left=`${Math.max(margin,Math.min(host.current.clientWidth-margin,p.x))}px`;node.style.top=`${p.y}px`;node.style.opacity=p.visible===false?'0':'1';}}
   }});
   scene.current=api;api.setPlaying(!reducedMotion);
   return()=>{api.dispose();scene.current=null;};
  }catch(e){setError(String(e?.message||e));}
 },[]);
 useEffect(()=>{scene.current?.setPlaying(playing);},[playing]);
 useEffect(()=>{scene.current?.setAuto(auto);},[auto]);
 useEffect(()=>{scene.current?.setSpeed(speed);},[speed]);
 useEffect(()=>{scene.current?.setBloom(glow);},[glow]);
 useEffect(()=>{const fn=e=>{if(e.target instanceof HTMLInputElement||e.target instanceof HTMLButtonElement)return;if(e.code==='Space'){e.preventDefault();setPlaying(v=>!v);}if(e.key==='Escape'){setDetail(null);setSettings(false);setQuiet(false);}};window.addEventListener('keydown',fn);return()=>window.removeEventListener('keydown',fn);},[]);
 function choose(i){modeRef.current=i;setMode(i);scene.current?.setMode(i);}
 function save(){try{const url=scene.current?.capture();if(!url)throw Error('The image is not ready yet.');const a=document.createElement('a');a.href=url;a.download='PerfectPower-Resonance.png';a.click();setNotice('Image saved');}catch(e){setNotice(e.message);}setTimeout(()=>setNotice(''),3500);}
 async function fullscreen(){try{if(document.fullscreenElement)await document.exitFullscreen();else await document.getElementById('resonance-app').requestFullscreen();}catch{setNotice('Fullscreen is unavailable in this view.');setTimeout(()=>setNotice(''),3500);}}
 return <div className={`resonance-experience ${quiet?'quiet':''}`}>
  <div ref={host} className="resonance-canvas" role="img" aria-label="An animated three-dimensional field of blue cyclotomic orbits, a violet phase bridge, coral E8 roots, a lavender 264-branch fiber, and gold integral connections." />
  <div className="resonance-vignette" />
  <header className="resonance-header chrome"><a href="/research" className="resonance-brand"><span className="brand-orbit">∫</span><span>PERFECTPOWER<small>CATEGORICAL · SPECTRAL · CYCLOTOMIC</small></span></a><div className="header-actions"><span className={`playback-status ${playing?'running':''}`}><i />{playing?(auto?'AUTONOMOUS SEQUENCE':'LIVE MOTION'):'PAUSED'}</span><button onClick={()=>setQuiet(v=>!v)} aria-label="Hide interface" title="Hide interface">◫</button><button onClick={fullscreen} aria-label="Toggle fullscreen" title="Fullscreen">⛶</button></div></header>
  <div className="scene-heading chrome"><span className="scene-eyebrow">THE 384–264 RESONANCE</span><h1>{MODES[mode].name}</h1><p>{MODES[mode].sub}</p></div>
  <div className="node-labels chrome" aria-label="Structures in the scene">{ANCHORS.map(item=><button key={item.key} ref={n=>labels.current[item.key]=n} aria-label={`${item.name}: ${item.value}`} className={`node-label ${item.className} node-${item.key}`} onClick={()=>setDetail(item)}><span>{item.name}</span><strong>{item.value}</strong></button>)}</div>
  {!ready&&!error&&<div className="scene-loading" role="status"><div className="loading-orbit" /><span>Opening the resonance field</span></div>}
  {error&&<div className="scene-error" role="alert"><h2>The 3D scene could not start</h2><p>{error}</p><p>Try a browser with WebGL enabled.</p><a href="./atlas.html">Open the geometric atlas</a><a href="./calculator.html">Open the exact calculators</a></div>}
  <div className="scene-tools chrome"><button className="tool-button" onClick={()=>setSettings(v=>!v)} aria-expanded={settings}>Tune the scene <span>☷</span></button><button className="tool-button" onClick={()=>setDetail({name:MODES[mode].title,detail:MODES[mode].text})}>About this view <span>↗</span></button></div>
  {settings&&<section className="scene-settings chrome" aria-label="Scene settings"><div className="drawer-top"><h2>Motion & atmosphere</h2><button onClick={()=>setSettings(false)} aria-label="Close settings">×</button></div><label className="range-label">Speed <output>{speed.toFixed(2)}×</output><input aria-label="Animation speed" type="range" min="0.25" max="2" step="0.05" value={speed} onChange={e=>setSpeed(+e.target.value)} /></label><label className="range-label">Glow <output>{glow.toFixed(1)}×</output><input aria-label="Glow intensity" type="range" min="0.4" max="1.6" step="0.1" value={glow} onChange={e=>setGlow(+e.target.value)} /></label><label className="toggle-label"><input type="checkbox" checked={auto} onChange={e=>setAuto(e.target.checked)} />Change scenes automatically</label><button className="plain-action" onClick={()=>scene.current?.resetCamera()}>Reset camera</button><button className="plain-action" onClick={save}>Save this frame ↓</button><p>Drag to orbit. Scroll to move closer. Space pauses motion.{reduced?' Reduced motion is enabled; playback starts paused.':''}</p></section>}
  {detail&&<aside className="scene-detail chrome" aria-label="Selected structure"><div className="drawer-top"><h2>{detail.name}</h2><button onClick={()=>setDetail(null)} aria-label="Close details">×</button></div>{detail.value&&<p className="detail-value">{detail.value}</p>}<p>{detail.detail}</p><a href="./calculator.html">Explore the exact integrals ↗</a><a href="/PerfectPower-Deep-Integral-Monograph.pdf">Read the mathematics ↗</a><div className="reference-links">Visual references <a href="https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19" target="_blank" rel="noreferrer">Framework</a><a href="https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af" target="_blank" rel="noreferrer">Resonance</a></div></aside>}
  <footer className="resonance-footer chrome"><div className="playback-controls"><button className="play-toggle" onClick={()=>setPlaying(v=>!v)} aria-label={playing?'Pause animation':'Play animation'} aria-pressed={playing}>{playing?<span className="pause-icon"><i/><i/></span>:<span className="play-icon">▶</span>}</button><div><span>{auto?'CONTINUOUS EXPLORATION':'SCENE HELD'}</span><time ref={clock}>00:00</time></div></div><nav className="scene-navigation" aria-label="Visualization scenes">{MODES.map((item,i)=><button key={item.name} aria-pressed={mode===i} className={mode===i?'active':''} onClick={()=>choose(i)}><span className="mode-number">0{i+1}</span><span>{item.name}</span>{mode===i&&<span className="mode-progress"><i ref={progress}/></span>}</button>)}</nav><button className="info-toggle" onClick={()=>setDetail({name:'The visual and the mathematics',detail:'Inspired by the two Claude visualizations supplied by the user and attributed by the user to Cody Lakeland. Their original palette, glowing orbits, connecting flows and four-part sequence are retained. Node placement, toroidal knots, braids and simplices are illustrative. Exact branch counts, root coordinates and integral identities are supplied by the reproducible PerfectPower calculations; no physical E8 model or categorical unification is claimed.'})} aria-label="Sources and mathematical scope">i</button></footer>
  <p className="gesture-hint chrome">DRAG TO ORBIT <span>·</span> SCROLL TO EXPLORE</p>
  {quiet&&<button className="restore-ui" onClick={()=>setQuiet(false)}>Show controls</button>}
  {notice&&<div className="scene-notice" role="status">{notice}</div>}
 </div>;
}

const mount=typeof document==='undefined'?null:document.getElementById('resonance-app');
if(mount)createRoot(mount).render(<ResonanceExperience/>);
