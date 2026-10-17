import React, {useEffect, useRef, useState} from 'react';
import {createRoot} from 'react-dom/client';
import {createResonanceScene} from './resonance-scene.js';
import {placeLabels} from './resonance-layout.js';
import {MathIdentity, MathDefinition, RootReadout, MATH_VIEWS, CHAPTER_MATH, NODE_MATH} from './resonance-math.jsx';
export {MathIdentity, RootReadout} from './resonance-math.jsx';
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
 {key:'left',className:'blue',name:'Cyclotomic field',value:'φ(1680) = 384',detail:'φ(1680) = 384. The phase q is a primitive 1680th root of unity. Its 56th power is a primitive 30th root.'},
 {key:'right',className:'coral',name:'E₈ root system',value:'240 = 8 × 30',detail:'The coral cloud uses the exported E₈ root projection. Its 240 roots form eight Coxeter orbits of length 30. The Lie algebra has dimension 248.'},
 {key:'upper',className:'violet',name:'Phase bridge',value:'q⁵⁶ = ζ₃₀',detail:'The eight primitive 30th-root eigenphases are reached from the 384 primitive 1680th-root phases, each with multiplicity 48.'},
 {key:'center',className:'lavender',name:'The refined fiber',value:'Q²⁶⁴ = q',detail:'The power map z ↦ z²⁶⁴ has 264 preimages of q. Exactly 240 are primitive at conductor 443520. These branches are distinct mathematical objects from the E₈ roots.'},
 {key:'lower',className:'gold',name:'Integral synthesis',value:'M₁(2 sin θ) = 2θ²',detail:'Raghava’s arcsine moment family gives exact powers of π. Refining π/840 to π/221760 scales moment order j by 264⁻²ʲ. The E₈ root and Cartan Mellin terms cancel at weight 2.'}
];

export function ResonanceExperience(){
 const host=useRef(null),scene=useRef(null),labels=useRef({}),progress=useRef(null),clock=useRef(null),labelSizes=useRef({}),focusRef=useRef(null),rootRef=useRef(-1),noticeTimer=useRef(null);
 const [mode,setMode]=useState(0),[playing,setPlaying]=useState(true),[auto,setAuto]=useState(true),[settings,setSettings]=useState(false),[detail,setDetail]=useState(null),[error,setError]=useState(''),[ready,setReady]=useState(false),[speed,setSpeed]=useState(1),[glow,setGlow]=useState(1),[quiet,setQuiet]=useState(true),[notice,setNotice]=useState(''),[reduced,setReduced]=useState(false),[quality,setQuality]=useState('auto'),[focus,setFocus]=useState(null),[selectedRoot,setSelectedRoot]=useState(0),[restart,setRestart]=useState(0);
 const modeRef=useRef(0),experience=useRef(null),mathBanner=useRef(null);
 const [mathVisible,setMathVisible]=useState(true);
 useEffect(()=>{
  let firstFrame=true;
  const reducedMotion=window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  setReduced(reducedMotion);setPlaying(!reducedMotion);
  let api,observer;
  try{
   api=createResonanceScene(host.current,{data:DATA,reducedMotion,onError:e=>{setError(String(e?.message||e));scene.current?.dispose();scene.current=null;},onSelect:key=>inspect(key),onFrame:frame=>{
    if(firstFrame){firstFrame=false;setReady(true);}
    if(Number.isInteger(frame.mode)&&frame.mode!==modeRef.current){modeRef.current=frame.mode;setMode(frame.mode);}
    if(progress.current)progress.current.style.transform=`scaleX(${Math.max(0,Math.min(1,frame.progress||0))})`;
    if(clock.current)clock.current.textContent=`${String(Math.floor((frame.elapsed||0)/60)).padStart(2,'0')}:${String(Math.floor((frame.elapsed||0)%60)).padStart(2,'0')}`;
    if(frame.focus!==undefined&&frame.focus!==focusRef.current){focusRef.current=frame.focus;setFocus(frame.focus);}
    if(Number.isInteger(frame.selectedRoot)&&frame.selectedRoot!==rootRef.current){rootRef.current=frame.selectedRoot;setSelectedRoot(frame.selectedRoot);}
    if(frame.nodes){
     const w=host.current.clientWidth,h=host.current.clientHeight;
     const projected=(Array.isArray(frame.nodes)?frame.nodes:Object.entries(frame.nodes).map(([id,p])=>({...p,id}))).map(p=>({...p,id:NODE_KEYS[p.id]||p.id}));
     const placements=placeLabels(projected,labelSizes.current,w,h,{focus:NODE_KEYS[frame.focus]||null,top:host.current.offsetTop>0?12:(w<580?170:100),bottom:w<580?130:105});
     for(const p of placements){const node=labels.current[p.id];if(!node)continue;node.style.left=`${p.x}px`;node.style.top=`${p.y}px`;node.style.visibility=p.visible?'visible':'hidden';node.style.opacity=p.visible?'1':'0';node.disabled=!p.visible;node.setAttribute('aria-hidden',String(!p.visible));}
    }
   }});
   scene.current=api;api.setPlaying(!reducedMotion);api.setAuto(auto);api.setSpeed(speed);api.setBloom(glow);api.setQuality?.(quality);
   const measure=()=>{for(const item of ANCHORS){const node=labels.current[item.key];if(node)labelSizes.current[item.key]={width:node.offsetWidth,height:node.offsetHeight};}};
   observer=new ResizeObserver(measure);observer.observe(host.current);for(const node of Object.values(labels.current))if(node)observer.observe(node);measure();
   return()=>{observer.disconnect();api.dispose();scene.current=null;};
  }catch(e){observer?.disconnect();api?.dispose();scene.current=null;setError(String(e?.message||e));}
 },[restart]);
 useEffect(()=>{scene.current?.setPlaying(playing);},[playing]);
 useEffect(()=>{scene.current?.setAuto(auto&&!detail?.math);},[auto,detail?.math]);
 useEffect(()=>{
  if(!mathVisible||!mathBanner.current||!experience.current)return;
  const measure=()=>experience.current?.style.setProperty('--math-headroom',`${Math.ceil(mathBanner.current.getBoundingClientRect().bottom-experience.current.getBoundingClientRect().top+14)}px`);
  const observer=new ResizeObserver(measure);observer.observe(mathBanner.current);measure();
  return()=>observer.disconnect();
 },[mathVisible,quiet,mode,focus,error]);
 useEffect(()=>{scene.current?.setSpeed(speed);},[speed]);
 useEffect(()=>{scene.current?.setBloom(glow);},[glow]);
 useEffect(()=>{scene.current?.setQuality?.(quality);},[quality]);
 useEffect(()=>()=>clearTimeout(noticeTimer.current),[]);
 useEffect(()=>{const fn=e=>{if(e.key==='Escape'){e.preventDefault();closeDetail();setSettings(false);setQuiet(false);return;}if(e.target instanceof Element&&e.target.closest('input,button,select,textarea,a,[contenteditable=true]'))return;if(e.code==='Space'){e.preventDefault();setPlaying(v=>!v);}};window.addEventListener('keydown',fn);return()=>window.removeEventListener('keydown',fn);},[]);
 function inspect(id){const key=NODE_KEYS[id]||id,item=ANCHORS.find(x=>x.key===key);if(!item)return;setQuiet(false);const sceneId=Object.keys(NODE_KEYS).find(id=>NODE_KEYS[id]===key);setSettings(false);setDetail({...item,math:NODE_MATH[key]});focusRef.current=sceneId;setFocus(sceneId);scene.current?.setFocus?.(sceneId);}
 function closeDetail(){setDetail(null);focusRef.current=null;setFocus(null);scene.current?.setFocus?.(null);}
 function choose(i){closeDetail();modeRef.current=i;setMode(i);scene.current?.setMode(i);}
 function notify(text){setNotice(text);clearTimeout(noticeTimer.current);noticeTimer.current=setTimeout(()=>setNotice(''),3500);}
 function retry(){closeDetail();setSettings(false);setError('');setReady(false);setRestart(n=>n+1);}
 function save(){try{const url=scene.current?.capture();if(!url)throw Error('The image is not ready yet.');const a=document.createElement('a');a.href=url;a.download='PerfectPower-Resonance.png';a.click();notify('Image saved');}catch(e){notify(e.message);}}
 async function fullscreen(){try{if(document.fullscreenElement)await document.exitFullscreen();else await document.getElementById('resonance-app').requestFullscreen();}catch{notify('Fullscreen is unavailable in this view.');}}
 const mathKind=NODE_MATH[NODE_KEYS[focus]]||CHAPTER_MATH[mode],identity=MATH_VIEWS[mathKind];
 function readIdentity(){setQuiet(false);setSettings(false);setDetail({name:identity.title,detail:identity.explanation,math:mathKind});}
 return <div ref={experience} className={`resonance-experience ${mathVisible?'has-math':''} ${quiet?'quiet':''} ${error?'unavailable':''} ${focus?'is-focused':''}`}>
  <div ref={host} className="resonance-canvas" role="img" aria-label="An animated three-dimensional field of blue cyclotomic orbits, a violet phase bridge, coral E8 roots, a lavender 264-branch fiber, and gold integral connections." />
  <div className="resonance-atmosphere" aria-hidden="true" /><div className="resonance-vignette" />
  <header className="resonance-header chrome" inert={quiet||!!error}><a href="/research" className="resonance-brand"><span className="brand-orbit">∫</span><span>PERFECTPOWER<small>CATEGORICAL · SPECTRAL · CYCLOTOMIC</small></span></a><div className="header-actions"><span className={`playback-status ${playing?'running':''}`}><i />{playing?(focus?'CLOSE STUDY':detail?.math?'READING MATHEMATICS':auto?'AUTONOMOUS SEQUENCE':'LIVE MOTION'):'PAUSED'}</span><button onClick={()=>setQuiet(v=>!v)} aria-label="Enter cinema view" title="Cinema view">◫</button><button onClick={fullscreen} aria-label="Toggle fullscreen" title="Fullscreen">⛶</button></div></header>
  <div key={mode} className="scene-heading chrome" hidden={mathVisible} inert={quiet||!!error}><span className="scene-eyebrow">THE 384–264 RESONANCE</span><h1>{MODES[mode].name}</h1><p>{MODES[mode].sub}</p></div>
  <div className="node-labels math-annotations" aria-label="Equations attached to the structures" hidden={!mathVisible} inert={!mathVisible||!!error||!!focus}>{ANCHORS.map(item=><button key={item.key} ref={n=>labels.current[item.key]=n} aria-label={`${item.name}: ${item.value}`} className={`node-label ${item.className} node-${item.key}`} onClick={()=>inspect(item.key)}><span>{item.name}</span><strong>{item.value}</strong></button>)}</div>
  {mathVisible&&!error&&<section ref={mathBanner} className={`math-banner math-${mathKind}`} aria-label="Mathematics in the scene">
   <div className="math-banner-top"><span>{identity.label}</span><button onClick={readIdentity}>Read this identity ↗</button></div>
   <MathIdentity kind={mathKind}/>
   <p aria-live="polite">{identity.caption}</p>
  </section>}
  {!error&&<button className="math-visibility" aria-label="Show mathematical annotations" aria-pressed={mathVisible} onClick={()=>setMathVisible(v=>!v)}><span aria-hidden="true">∑</span> {mathVisible?'Hide math':'Show math'}</button>}
  {!ready&&!error&&<div className="scene-loading" role="status"><div className="loading-orbit" /><span>Opening the resonance field</span></div>}
  {error&&<div className="scene-error" role="alert"><h2>The 3D scene could not start</h2><p>{error}</p><p>Try a browser with WebGL enabled.</p><button className="restart-scene" onClick={retry}>Restart the scene</button><a href="./atlas.html">Open the geometric atlas</a><a href="./calculator.html">Open the exact calculators</a></div>}
  <div className="scene-tools chrome" inert={quiet||!!error}><button className="tool-button" onClick={()=>{closeDetail();setSettings(v=>!v);}} aria-expanded={settings}>Tune the scene <span>☷</span></button><button className="tool-button" onClick={()=>{closeDetail();setDetail({name:MODES[mode].title,detail:MODES[mode].text});}}>About this view <span>↗</span></button></div>
  {settings&&<section className="scene-settings chrome" aria-label="Scene settings" inert={quiet||!!error}><div className="drawer-top"><h2>Motion & atmosphere</h2><button onClick={()=>setSettings(false)} aria-label="Close settings">×</button></div><label className="range-label">Speed <output>{speed.toFixed(2)}×</output><input aria-label="Animation speed" type="range" min="0.25" max="2" step="0.05" value={speed} onChange={e=>setSpeed(+e.target.value)} /></label><label className="range-label">Glow <output>{glow.toFixed(1)}×</output><input aria-label="Glow intensity" type="range" min="0.4" max="1.6" step="0.1" value={glow} onChange={e=>setGlow(+e.target.value)} /></label><label className="quality-label">Scene detail<select aria-label="Rendering quality" value={quality} onChange={e=>setQuality(e.target.value)}><option value="auto">Adaptive</option><option value="high">Full detail</option><option value="eco">Efficient</option></select></label><label className="toggle-label"><input type="checkbox" checked={auto} onChange={e=>setAuto(e.target.checked)} />Change scenes automatically</label><button className="plain-action" onClick={()=>{closeDetail();scene.current?.resetCamera();}}>Reset camera</button><button className="plain-action" onClick={save}>Save this frame ↓</button><p>Drag to orbit. Scroll to move closer. Space pauses motion.{reduced?' Reduced motion is enabled; playback starts paused.':''}</p></section>}
  {detail&&<aside className="scene-detail chrome" aria-label="Selected structure" inert={quiet||!!error}><div className="drawer-top"><h2>{detail.name}</h2><button onClick={closeDetail} aria-label="Close details">×</button></div>{detail.value&&<p className="detail-value">{detail.value}</p>}<p>{detail.detail}</p>{detail.math&&<div className="detail-mathematics"><MathIdentity kind={detail.math}/><MathDefinition kind={detail.math}/>{detail.math!==mathKind&&<p>{MATH_VIEWS[detail.math].caption}</p>}</div>}{focus==='e8'&&<div className="root-study"><span>Following the Coxeter action</span><strong>Orbit {DATA.roots[selectedRoot].orbit+1} · step {DATA.roots[selectedRoot].step+1} of 30</strong><p>56 adjacent roots highlighted</p><RootReadout root={DATA.roots[selectedRoot]}/></div>}{focus&&<button className="return-field" onClick={closeDetail}>← Return to the whole field</button>}<a href="./calculator.html">Explore the exact integrals ↗</a><a href="/PerfectPower-Deep-Integral-Monograph.pdf">Read the mathematics ↗</a><div className="reference-links">Visual references <a href="https://claude.ai/public/artifacts/1db99748-b7fd-477b-8a9c-1bb54fb33a19" target="_blank" rel="noreferrer">Framework</a><a href="https://claude.ai/public/artifacts/4fd0f32a-22b6-4fae-b2d2-1f3732d324af" target="_blank" rel="noreferrer">Resonance</a></div></aside>}
  <footer className="resonance-footer chrome" inert={quiet||!!error}><div className="playback-controls"><button className="play-toggle" onClick={()=>setPlaying(v=>!v)} aria-label={playing?'Pause animation':'Play animation'} aria-pressed={playing}>{playing?<span className="pause-icon"><i/><i/></span>:<span className="play-icon">▶</span>}</button><div><span>{focus?'CLOSE STUDY':detail?.math?'IDENTITY HELD':auto?'CONTINUOUS EXPLORATION':'SCENE HELD'}</span><time ref={clock}>00:00</time></div></div><nav className="scene-navigation" aria-label="Visualization scenes">{MODES.map((item,i)=><button key={item.name} aria-pressed={mode===i} className={mode===i?'active':''} onClick={()=>choose(i)}><span className="mode-number">0{i+1}</span><span>{item.name}</span>{mode===i&&<span className="mode-progress"><i ref={progress}/></span>}</button>)}</nav><button className="info-toggle" onClick={()=>{closeDetail();setDetail({name:'The visual and the mathematics',detail:'Inspired by the two Claude visualizations supplied by the user and attributed by the user to Cody Lakeland. Their original palette, glowing orbits, connecting flows and four-part sequence are retained. Node placement, toroidal knots, braids and simplices are illustrative. Exact branch counts, root coordinates and integral identities are supplied by the reproducible PerfectPower calculations; no physical E8 model or categorical unification is claimed.'});}} aria-label="Sources and mathematical scope">i</button></footer>
  <p className="gesture-hint chrome" inert={quiet||!!error}>DRAG TO ORBIT <span>·</span> SCROLL TO EXPLORE</p>
  {quiet&&<button className="restore-ui" autoFocus onClick={()=>setQuiet(false)}><span className="controls-glyph" aria-hidden="true">◫</span> Show controls</button>}
  {notice&&<div className="scene-notice" role="status">{notice}</div>}
 </div>;
}

const mount=typeof document==='undefined'?null:document.getElementById('resonance-app');
if(mount)createRoot(mount).render(<ResonanceExperience/>);
