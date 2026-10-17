import React,{useEffect,useMemo,useRef} from 'react';
import {Canvas,useFrame,useThree} from '@react-three/fiber';
import * as THREE from 'three';
import {OrbitControls} from 'three/examples/jsm/controls/OrbitControls.js';
import {EffectComposer} from 'three/examples/jsm/postprocessing/EffectComposer.js';
import {RenderPass} from 'three/examples/jsm/postprocessing/RenderPass.js';
import {UnrealBloomPass} from 'three/examples/jsm/postprocessing/UnrealBloomPass.js';
import {OutputPass} from 'three/examples/jsm/postprocessing/OutputPass.js';
import {ConvexGeometry} from 'three/examples/jsm/geometries/ConvexGeometry.js';
import rootEnvelope from './e8-roots.json';
import {gramMatrix} from './math-engine.mjs';
import {energySlice,ellipsoidPoint} from './studio-geometry.mjs';
import {primitive1680,phaseFiber264,eigenphases30,characterEmbedding,powerMapCurves,e8Edges,compositionPositions,bezierPoint,EMBEDDING_ROTATIONS} from './cinematic-geometry.mjs';

const BLUE='#5cbcff',CORAL='#ff8b89',VIOLET='#b9a0ff',LAVENDER='#c2b4ff',GOLD='#f6ce83',CYAN='#83e6ed';
const DOMAIN=primitive1680(),FIBER=phaseFiber264(),PHASES=eigenphases30(),ROOTS=rootEnvelope.roots;
const EDGES=e8Edges(ROOTS);
const ROOT_POSITIONS=ROOTS.map(p=>[p.x*1.83,p.y*1.83,p.z*1.28]);

function useDisposal(resource){useEffect(()=>()=>resource?.dispose?.(),[resource]);return resource;}

function GlowMaterial({color,opacity=.4,power=2.1,time}){
 const material=useDisposal(useMemo(()=>new THREE.ShaderMaterial({
  transparent:true,depthWrite:false,side:THREE.DoubleSide,blending:THREE.AdditiveBlending,
  uniforms:{uColor:{value:new THREE.Color(color)},uOpacity:{value:opacity},uPower:{value:power},uTime:{value:0}},
  vertexShader:`varying vec3 vNormal;varying vec3 vView;varying vec3 vLocal;varying vec2 vUv;void main(){vUv=uv;vLocal=position;vec4 p=modelViewMatrix*vec4(position,1.);vNormal=normalize(normalMatrix*normal);vView=normalize(-p.xyz);gl_Position=projectionMatrix*p;}`,
  fragmentShader:`varying vec3 vNormal;varying vec3 vView;varying vec3 vLocal;varying vec2 vUv;uniform vec3 uColor;uniform float uOpacity;uniform float uPower;uniform float uTime;void main(){float rim=pow(1.-abs(dot(normalize(vNormal),normalize(vView))),uPower);float grain=.93+.07*sin(vLocal.x*31.+sin(vLocal.y*23.)+vLocal.z*17.);float pulse=pow(max(0.,cos(vUv.x*6.283185-uTime*.8)),24.);vec3 c=uColor*(.3+2.35*rim+pulse*.85)*grain;gl_FragColor=vec4(c,uOpacity*(.18+.82*rim+pulse*.15));}`
 }),[color,opacity,power]));
 useFrame(()=>{material.uniforms.uTime.value=time?.current||0;});
 return <primitive attach="material" object={material}/>;
}

function SweptCharacterRibbon({radius,tube,character,offset,color,time}){
 const geometry=useDisposal(useMemo(()=>{
  const count=640,positions=[],uvs=[],indices=[];
  for(let i=0;i<=count;i++)for(const side of[-1,1]){
   const theta=2*Math.PI*i/count,minor=character*theta+offset+side*.31,r=radius+tube*Math.cos(minor);
   positions.push(r*Math.cos(theta),r*Math.sin(theta),tube*Math.sin(minor));uvs.push(i/count,(side+1)/2);
  }
  for(let i=0;i<count;i++){const a=i*2;indices.push(a,a+1,a+3,a,a+3,a+2);}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));g.setAttribute('uv',new THREE.Float32BufferAttribute(uvs,2));g.setIndex(indices);g.computeVertexNormals();return g;
 },[radius,tube,character,offset]));
 return <mesh geometry={geometry}><GlowMaterial color={color} opacity={.7} power={1.25} time={time}/></mesh>;
}

function Tube({points,color,opacity=1,radius=.018,closed=false,emission=1.5,segments}){
 const geometry=useDisposal(useMemo(()=>new THREE.TubeGeometry(new THREE.CatmullRomCurve3(points.map(p=>new THREE.Vector3(...p)),closed,'centripetal'),segments||Math.max(24,points.length),radius,5,closed),[points,radius,closed,segments]));
 return <mesh geometry={geometry}><meshStandardMaterial color={color} emissive={color} emissiveIntensity={emission} metalness={.25} roughness={.28} transparent opacity={opacity} depthWrite={opacity>.9}/></mesh>;
}

function GlowPoints({points,color,size=8,opacity=1,colors,dynamic=false}){
 const geometry=useDisposal(useMemo(()=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(points.flat(),3));g.setAttribute('color',new THREE.Float32BufferAttribute(points.flatMap((p,i)=>new THREE.Color(colors?.[i]||color).toArray()),3));return g;},[points,color,colors]));
 const material=useDisposal(useMemo(()=>new THREE.ShaderMaterial({
  transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,
  uniforms:{uSize:{value:size},uOpacity:{value:opacity}},
  vertexShader:`attribute vec3 color;varying vec3 vColor;uniform float uSize;void main(){vColor=color;vec4 p=modelViewMatrix*vec4(position,1.);gl_Position=projectionMatrix*p;gl_PointSize=clamp(uSize*19./max(1.,-p.z),2.,35.);}`,
  fragmentShader:`varying vec3 vColor;uniform float uOpacity;void main(){float d=length(gl_PointCoord-.5)*2.;if(d>1.)discard;float core=exp(-d*d*28.);float halo=pow(1.-d,2.);gl_FragColor=vec4(vColor*(1.+core*1.8),uOpacity*(halo*.55+core));}`
 }),[]));
 useEffect(()=>{material.uniforms.uOpacity.value=opacity;material.uniforms.uSize.value=size;},[opacity,size,material]);
 return <points geometry={geometry} material={material}/>;
}

function Ring({radius=1,color,rotation=[0,0,0],position=[0,0,0],tube=.014,opacity=.65}){
 return <mesh rotation={rotation} position={position}><torusGeometry args={[radius,tube,7,160]}/><meshStandardMaterial color={color} emissive={color} emissiveIntensity={1.65} transparent opacity={opacity} metalness={.3} roughness={.25}/></mesh>;
}

function PhaseCharacterBody({kind='domain',quality,time}){
 const domain=kind==='domain',fiber=kind==='fiber';
 const data=domain?DOMAIN:fiber?FIBER:PHASES;
 const color=domain?BLUE:fiber?LAVENDER:VIOLET;
 const radius=domain?1.42:fiber?1.24:1.11,tube=domain?.43:fiber?.37:.21,character=fiber?11:7;
 const path=useMemo(()=>Array.from({length:domain?1024:768},(_,i)=>characterEmbedding(Math.PI*2*i/(domain?1024:768),{radius,tube,character})),[domain,fiber]);
 const points=useMemo(()=>data.map(p=>p.position),[data]);
 const colors=useMemo(()=>data.map(p=>fiber?(p.primitive?LAVENDER:'#221b30'):domain?(p.sector>0?'#7cd3ff':'#719cfa'):(p.sector>0?GOLD:CYAN)),[data,domain,fiber]);
 const marker=useRef(null);
 useFrame(()=>{if(!marker.current)return;const index=Math.floor(time.current*(domain?7:fiber?11:1.3))%data.length;marker.current.position.set(...data[index].position);});
 return <group rotation={EMBEDDING_ROTATIONS[kind]}>
  <mesh rotation={[0,0,0]}><torusGeometry args={[radius,tube*.98,quality==='eco'?18:32,quality==='eco'?128:240]}/><GlowMaterial color={color} opacity={domain?.48:fiber?.58:.42}/></mesh>
  <Tube points={path} closed color={color} radius={domain?.021:fiber?.022:.028} opacity={.84} emission={2.0}/>
  {(domain||fiber)&&[0,2*Math.PI/3,4*Math.PI/3].map(offset=><SweptCharacterRibbon key={offset} radius={radius} tube={tube*1.015} character={character} offset={offset} color={color} time={time}/>)}
  <Ring radius={radius+tube+.04} color={color} opacity={.26} tube={.008}/>
  <Ring radius={radius-tube-.04} color={color} opacity={.28} tube={.008}/>
  <GlowPoints points={points} colors={colors} color={color} size={domain?7:fiber?7.5:19} opacity={domain?.85:.95}/>
  <mesh ref={marker}><sphereGeometry args={[domain?.045:fiber?.05:.075,12,10]}/><meshBasicMaterial color={color} toneMapped={false}/></mesh>
  {!domain&&!fiber&&PHASES.map(p=><group key={p.a} position={p.position}>
   <mesh><sphereGeometry args={[.115,20,16]}/><GlowMaterial color={p.sector>0?GOLD:CYAN} opacity={.8}/></mesh>
   <Ring radius={.18} tube={.012} color={p.sector>0?GOLD:CYAN} rotation={[Math.PI/2,p.theta,0]} opacity={.75}/>
  </group>)}
 </group>;
}

function RootCrystal({time,quality}){
 const geometry=useDisposal(useMemo(()=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(EDGES.flatMap(([a,b])=>[...ROOT_POSITIONS[a],...ROOT_POSITIONS[b]]),3));return g;},[]));
 const hull=useDisposal(useMemo(()=>new ConvexGeometry(ROOT_POSITIONS.map(p=>new THREE.Vector3(...p))),[]));
 const selectedGeometry=useDisposal(useMemo(()=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.BufferAttribute(new Float32Array(56*6),3));return g;},[]));
 const marker=useRef(null),selected=useRef(-1),rays=useRef(null);
 const orbitPaths=useMemo(()=>Array.from({length:8},(_,orbit)=>ROOTS.filter(p=>p.orbit===orbit).sort((a,b)=>a.step-b.step).map(p=>ROOT_POSITIONS[p.id])),[]);
 useFrame(()=>{
  const n=Math.floor(time.current*.65)%ROOTS.length;
  if(n===selected.current)return;selected.current=n;
  const values=selectedGeometry.attributes.position.array;
  ROOTS[n].neighbors.forEach((j,i)=>{values.set(ROOT_POSITIONS[n],i*6);values.set(ROOT_POSITIONS[j],i*6+3);});
  selectedGeometry.attributes.position.needsUpdate=true;
  marker.current?.position.set(...ROOT_POSITIONS[n]);
 });
 return <group>
  <mesh geometry={hull}><GlowMaterial color={CORAL} opacity={.2} power={2.5}/></mesh>
  <lineSegments geometry={geometry}><lineBasicMaterial color={CORAL} transparent opacity={quality==='eco'?.037:.055} blending={THREE.AdditiveBlending} depthWrite={false}/></lineSegments>
  <lineSegments geometry={selectedGeometry} ref={rays}><lineBasicMaterial color="#ffd6bc" transparent opacity={.38} blending={THREE.AdditiveBlending} depthWrite={false}/></lineSegments>
  {orbitPaths.map((p,i)=><Tube key={i} points={p} color={CORAL} closed opacity={i%2?.24:.36} radius={.008} emission={1.2}/>)}
  <GlowPoints points={ROOT_POSITIONS} color={CORAL} size={8.2} opacity={1}/>
  <mesh ref={marker}><sphereGeometry args={[.065,16,12]}/><meshBasicMaterial color="#ffe9cf" toneMapped={false}/></mesh>
 </group>;
}

function IntegralSculpture({time,quality}){
 const slice=useMemo(()=>energySlice(gramMatrix(),[.7,.8,.13,.02]),[]);
 const geometry=useDisposal(useMemo(()=>{
  const longitudes=quality==='eco'?72:112,latitudes=quality==='eco'?36:56,positions=[],indices=[];
  for(let j=0;j<=latitudes;j++)for(let i=0;i<=longitudes;i++)positions.push(...ellipsoidPoint(slice,2*Math.PI*i/longitudes,-Math.PI/2+Math.PI*j/latitudes).map(x=>x*.43));
  for(let j=0;j<latitudes;j++)for(let i=0;i<longitudes;i++){const a=j*(longitudes+1)+i,b=a+longitudes+1;indices.push(a,b,a+1,b,b+1,a+1);}
  const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));g.setIndex(indices);g.computeVertexNormals();return g;
 },[slice,quality]));
 const lines=useMemo(()=>Array.from({length:12},(_,j)=>Array.from({length:160},(_,i)=>ellipsoidPoint(slice,2*Math.PI*i/159,Math.PI*(j/11-.5)).map(x=>x*.43))),[slice]);
 const selector=useMemo(()=>Array.from({length:321},(_,i)=>{
  const theta=Math.PI*i/320,u=theta*(Math.PI-theta),angle=2*theta;
  return[(1.05+.27*u/(Math.PI**2/4))*Math.cos(angle),(1.05+.27*u/(Math.PI**2/4))*Math.sin(angle),.65*(u/(Math.PI**2/4)-.5)];
 }),[]);
 const marker=useRef(null);
 useFrame(()=>{const theta=((time.current*.11)%1)*Math.PI,u=theta*(Math.PI-theta),angle=theta*2;marker.current?.position.set((1.05+.27*u/(Math.PI**2/4))*Math.cos(angle),(1.05+.27*u/(Math.PI**2/4))*Math.sin(angle),.65*(u/(Math.PI**2/4)-.5));});
 return <group rotation={[.24,-.28,-.14]}>
  <mesh geometry={geometry}><GlowMaterial color={GOLD} opacity={.62} power={1.65}/></mesh>
  {lines.filter((_,i)=>i>0&&i<11).map((p,i)=><Tube key={i} points={p} color={GOLD} radius={.008} opacity={.3} emission={1.35}/>)}
  <Tube points={selector} color="#ffdf9d" radius={.024} opacity={.9} emission={2.2}/>
  <Ring radius={1.62} color={GOLD} opacity={.35} rotation={[.8,.35,.1]} tube={.014}/>
  <mesh ref={marker}><sphereGeometry args={[.055,16,12]}/><meshBasicMaterial color="#fff0c9" toneMapped={false}/></mesh>
 </group>;
}

function MappingStreams({positions,time,quality}){
 const curves=useMemo(()=>powerMapCurves(DOMAIN,PHASES,positions,{count:quality==='eco'?32:80}),[positions,quality]);
 const particleGeometry=useDisposal(useMemo(()=>{const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.BufferAttribute(new Float32Array(curves.length*3),3));return g;},[curves]));
 useFrame(()=>{const p=particleGeometry.attributes.position.array;curves.forEach((curve,i)=>p.set(bezierPoint(...curve.control,(time.current*.10+i/curves.length)%1),i*3));particleGeometry.attributes.position.needsUpdate=true;});
 return <group>
  {curves.map((curve,i)=><Tube key={i} points={curve.points} color={i%3?BLUE:VIOLET} radius={quality==='eco'?.006:.007} opacity={i%4?.11:.22} emission={1.9} segments={48}/>)}
  <points geometry={particleGeometry}><pointsMaterial color="#b3d4ff" size={.055} sizeAttenuation transparent opacity={.9} blending={THREE.AdditiveBlending} depthWrite={false}/></points>
 </group>;
}

function RelationshipRibbon({start,end,color,time,index=0}){
 const points=useMemo(()=>{
  const p1=[start[0]*.7,start[1]*.7,2.1+index*.18],p2=[end[0]*.75,end[1]*.7,1.6+index*.18];
  return Array.from({length:80},(_,i)=>bezierPoint(start,p1,p2,end,i/79));
 },[start,end,index]);
 return <Tube points={points} color={color} radius={.012} opacity={.18} emission={1.2}/>;
}

function Bloom({quality,onError}){
 const {gl,scene,camera,size}=useThree();
 const composer=useMemo(()=>{
  const c=new EffectComposer(gl);c.addPass(new RenderPass(scene,camera));
  const bloom=new UnrealBloomPass(new THREE.Vector2(size.width,size.height),quality==='eco'?.72:.86,.72,.62);
  c.addPass(bloom);c.addPass(new OutputPass());return c;
 },[gl,scene,camera,quality]);
 useEffect(()=>{composer.setPixelRatio(gl.getPixelRatio());composer.setSize(size.width,size.height);},[composer,size.width,size.height,gl]);
 useEffect(()=>()=>{for(const pass of composer.passes)pass.dispose?.();composer.dispose();},[composer]);
 useFrame(()=>{try{composer.render();}catch(error){onError?.(error);}},1);
 return null;
}

function CameraAndTime({time,playing,reducedMotion,chapter,resetKey,onFrame,field}){
 const {camera,gl,size,invalidate}=useThree();
 const controls=useRef(null),manual=useRef(false),lastFrame=useRef(-1),frameCallback=useRef(onFrame);
 frameCallback.current=onFrame;
 const portrait=size.width/size.height<.9;
 const positions=useMemo(()=>compositionPositions(portrait),[portrait]);
 useEffect(()=>{
  const c=new OrbitControls(camera,gl.domElement);c.enableDamping=true;c.dampingFactor=.075;c.enablePan=false;c.minDistance=portrait?16:10;c.maxDistance=portrait?36:26;c.maxPolarAngle=Math.PI*.7;c.minPolarAngle=Math.PI*.24;
  const start=()=>{manual.current=true;};c.addEventListener('start',start);c.addEventListener('change',invalidate);controls.current=c;
  return()=>{c.removeEventListener('start',start);c.removeEventListener('change',invalidate);c.dispose();controls.current=null;};
 },[camera,gl,invalidate,portrait]);
 useEffect(()=>{manual.current=false;const width=portrait?8.4:14.2,height=portrait?14.4:11.2;const distance=Math.max(height,width/(size.width/size.height))/(2*Math.tan(THREE.MathUtils.degToRad(40)/2));camera.fov=40;camera.position.set(portrait?1.5:1.4,.4,distance);controls.current?.target.set(0,0,0);camera.updateProjectionMatrix();invalidate();},[camera,portrait,resetKey,size.width,size.height,invalidate]);
 useFrame((state,dt)=>{
  if(playing&&!reducedMotion)time.current+=Math.min(dt,.05);
  const c=controls.current;if(!c)return;
  if(!manual.current){
   const width=portrait?8.4:14.2,height=portrait?14.4:11.2,distance=Math.max(height,width/(size.width/size.height))/(2*Math.tan(THREE.MathUtils.degToRad(40)/2));
   const focus=portrait?[[0,.0,0],[-.28,.65,0],[.35,-.2,0],[0,-.65,0]][chapter%4]:[[0,0,0],[-.55,.4,0],[.55,0,0],[0,-.48,0]][chapter%4];
   const motion=reducedMotion?0:time.current;
   const goal=new THREE.Vector3(Math.sin(motion*.08)*1.45+.55,Math.sin(motion*.05)*.38+.25,distance);
   if(reducedMotion||!playing){camera.position.copy(goal);c.target.set(...focus);}else{camera.position.lerp(goal,1-Math.exp(-dt*1.2));c.target.lerp(new THREE.Vector3(...focus),1-Math.exp(-dt*1.3));}
  }
  c.update();
  if(!playing||reducedMotion||state.clock.elapsedTime-lastFrame.current>.09){
   lastFrame.current=state.clock.elapsedTime;const anchors={};
   field.current?.updateMatrixWorld(true);
   for(const [key,p] of Object.entries(positions)){const v=new THREE.Vector3(...p);if(field.current)v.applyMatrix4(field.current.matrixWorld);v.project(camera);anchors[key]={x:(v.x*.5+.5)*size.width,y:(-.5*v.y+.5)*size.height,visible:v.z<1&&v.z>-1&&Math.abs(v.x)<1.1&&Math.abs(v.y)<1.1};}
   frameCallback.current?.({elapsed:time.current,anchors});
  }
 });
 return null;
}

function Field({chapter,playing,reducedMotion,quality,onReady,onError,onFrame,resetKey}){
 const {size,gl}=useThree(),time=useRef(0),fired=useRef(false),field=useRef(null);
 const positions=useMemo(()=>compositionPositions(size.width/size.height<.9),[size.width/size.height<.9]);
 useEffect(()=>{const lost=e=>{e.preventDefault();onError?.(new Error('The cinematic graphics context was interrupted.'));};gl.domElement.addEventListener('webglcontextlost',lost);return()=>gl.domElement.removeEventListener('webglcontextlost',lost);},[gl,onError]);
 useFrame(()=>{if(!fired.current){fired.current=true;onReady?.();}if(field.current){field.current.rotation.y=.11*Math.sin(time.current*.105);field.current.rotation.x=.028*Math.sin(time.current*.078);field.current.rotation.z=.012*Math.sin(time.current*.062);}},-1);
 return <>
  <color attach="background" args={['#050710']}/><fog attach="fog" args={['#050710',25,55]}/>
  <ambientLight intensity={.35}/><hemisphereLight color="#c4d8ff" groundColor="#080b1c" intensity={1.4}/>
  <pointLight position={[-5,2,6]} color={BLUE} intensity={65} distance={20}/><pointLight position={[5,1,5]} color={CORAL} intensity={65} distance={20}/><pointLight position={[0,-4,5]} color={GOLD} intensity={55} distance={16}/>
  <group ref={field}>
  <group position={positions.cyclotomic}><PhaseCharacterBody kind="domain" quality={quality} time={time}/></group>
  <group position={positions.e8}><RootCrystal quality={quality} time={time}/></group>
  <group position={positions.bridge}><PhaseCharacterBody kind="bridge" quality={quality} time={time}/></group>
  <group position={positions.fiber}><PhaseCharacterBody kind="fiber" quality={quality} time={time}/></group>
  <group position={positions.integral}><IntegralSculpture quality={quality} time={time}/></group>
  <MappingStreams positions={positions} time={time} quality={quality}/>
  <RelationshipRibbon start={positions.bridge} end={positions.integral} color={GOLD} time={time}/>
  </group>
  <CameraAndTime time={time} playing={playing} reducedMotion={reducedMotion} chapter={chapter} resetKey={resetKey} onFrame={onFrame} field={field}/>
  <Bloom quality={quality} onError={onError}/>
 </>;
}

class Boundary extends React.Component{constructor(p){super(p);this.state={error:null};}static getDerivedStateFromError(error){return{error};}componentDidCatch(error){this.props.onError?.(error);}render(){return this.state.error?null:this.props.children;}}
function Unsupported({onError}){useEffect(()=>{onError?.(new Error('This device did not provide the WebGL graphics context.'));},[onError]);return null;}

export default function CinematicScene({chapter=0,playing=true,reducedMotion=false,quality='auto',onReady,onError,onFrame,resetKey=0}){
 const eco=quality==='eco'||quality==='auto'&&typeof navigator!=='undefined'&&((navigator.deviceMemory||8)<4||(navigator.hardwareConcurrency||8)<4);
 return <Boundary onError={onError}><Canvas frameloop={playing&&!reducedMotion?'always':'demand'} dpr={eco?[1,1.15]:[1,1.65]} camera={{position:[1,.4,17],fov:40,near:.1,far:90}} gl={{antialias:!eco,alpha:false,powerPreference:eco?'low-power':'high-performance',preserveDrawingBuffer:true}} onCreated={({gl})=>{gl.toneMapping=THREE.ACESFilmicToneMapping;gl.toneMappingExposure=1.0;}} fallback={<Unsupported onError={onError}/>} style={{touchAction:'none'}} aria-label="Cinematic mathematical field of cyclotomic phases, the 264-phase fiber, E8 roots and the integral energy surface">
  <Field chapter={chapter} playing={playing} reducedMotion={reducedMotion} quality={eco?'eco':'high'} onReady={onReady} onError={onError} onFrame={onFrame} resetKey={resetKey}/>
 </Canvas></Boundary>;
}
