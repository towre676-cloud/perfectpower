import React, {useEffect, useMemo, useRef, useState} from 'react';
import {Canvas, useFrame, useThree} from '@react-three/fiber';
import * as THREE from 'three';
import {OrbitControls} from 'three/examples/jsm/controls/OrbitControls.js';
import envelope from './e8-roots.json';
import {gramMatrix, sampleDensity, fourierCoefficients} from './math-engine.mjs';
import {PRIMITIVE_30, GOLDEN_ROOT_ANGLES, coefficientVector, goldenCharacter, densityDisplay, energySlice, ellipsoidPoint, normalizedEnergyPoint} from './studio-geometry.mjs';

const ROOT_DATA = envelope.roots;
const PALETTE = {gold:'#efc889', cyan:'#75dae2', ivory:'#f5eedf', muted:'#91a4b3', blue:'#8da6c9', violet:'#a3a5cb', ink:'#06111c'};
const ORBIT_COLORS = ['#789bb3', '#a4b9c6', '#8ba8b6', '#a1b4c7', '#7396ad', '#c4d1d8', '#9ba7bf', '#a4bbcc'];
const CAMERA = {
  integral:{position:[8.7,5.3,13.4],target:[0,.45,0],fov:38},
  spectrum:{position:[1.2,1.2,16.8],target:[0,0,0],fov:38},
  fourier:{position:[8.0,6.5,12.3],target:[0,.15,0],fov:39},
  energy:{position:[8.8,5.6,10.4],target:[0,0,0],fov:39}
};

function useDispose(resource) {
  useEffect(() => () => resource?.dispose?.(), [resource]);
  return resource;
}

function Line({points, color=PALETTE.ivory, opacity=1, closed=false, ...rest}) {
  const geometry = useDispose(useMemo(() => {
    const p = points.map(point => new THREE.Vector3(...point));
    if (closed && p.length) p.push(p[0].clone());
    return new THREE.BufferGeometry().setFromPoints(p);
  }, [points, closed]));
  return <line geometry={geometry} {...rest}><lineBasicMaterial color={color} transparent opacity={opacity} depthWrite={false}/></line>;
}

function Segments({positions, color=PALETTE.muted, opacity=.4}) {
  const geometry = useDispose(useMemo(() => {
    const g = new THREE.BufferGeometry();
    g.setAttribute('position',new THREE.Float32BufferAttribute(positions.flat(),3));
    return g;
  }, [positions]));
  return <lineSegments geometry={geometry}><lineBasicMaterial color={color} transparent opacity={opacity} depthWrite={false}/></lineSegments>;
}

function GlowPoints({points, colors, color=PALETTE.ivory, size=5, opacity=1}) {
  const geometry = useDispose(useMemo(() => {
    const g = new THREE.BufferGeometry();
    g.setAttribute('position',new THREE.Float32BufferAttribute(points.flat(),3));
    const c = colors ? colors.flatMap(value => new THREE.Color(value).toArray()) : points.flatMap(() => new THREE.Color(color).toArray());
    g.setAttribute('color',new THREE.Float32BufferAttribute(c,3));
    return g;
  }, [points, colors, color]));
  const material = useDispose(useMemo(() => new THREE.ShaderMaterial({
    transparent:true,depthWrite:false,blending:THREE.AdditiveBlending,
    uniforms:{uSize:{value:size},uOpacity:{value:opacity}},
    vertexShader:`attribute vec3 color; varying vec3 vColor; uniform float uSize;
      void main(){vColor=color;vec4 p=modelViewMatrix*vec4(position,1.0);gl_Position=projectionMatrix*p;gl_PointSize=clamp(uSize*14.0/max(1.0,-p.z),2.0,26.0);}`,
    fragmentShader:`varying vec3 vColor;uniform float uOpacity;
      void main(){float d=length(gl_PointCoord-.5)*2.;if(d>1.)discard;float halo=pow(max(0.,1.-d),2.);float core=1.-smoothstep(.0,.32,d);gl_FragColor=vec4(vColor*(.65+core*.6),(halo*.55+core*.7)*uOpacity);}`
  }), []));
  useEffect(() => {material.uniforms.uSize.value=size;material.uniforms.uOpacity.value=opacity;},[material,size,opacity]);
  return <points geometry={geometry} material={material}/>;
}

function Dot({position, color=PALETTE.gold, radius=.07, opacity=1}) {
  return <mesh position={position}><sphereGeometry args={[radius,16,12]}/><meshStandardMaterial color={color} emissive={color} emissiveIntensity={.55} metalness={.25} roughness={.24} transparent opacity={opacity}/></mesh>;
}

function AxisTicks({extent=5, y=0, z=0, step=1, color=PALETTE.muted}) {
  const positions=useMemo(() => {
    const p=[];
    for(let x=-extent;x<=extent+.0001;x+=step)p.push([x,y-.055,z],[x,y+.055,z]);
    p.push([-extent-.2,y,z],[extent+.25,y,z]);
    return p;
  },[extent,y,z,step]);
  return <Segments positions={positions} color={color} opacity={.5}/>;
}

/** Camera transitions occur on a mathematical view change; user orbiting takes priority. */
function CameraRig({view, resetKey=0}) {
  const {camera,gl,invalidate} = useThree();
  const controls = useRef(null), moving=useRef(true), targetPosition=useRef(new THREE.Vector3()), targetLook=useRef(new THREE.Vector3());
  useEffect(() => {
    const c=new OrbitControls(camera,gl.domElement);
    c.enableDamping=true;c.dampingFactor=.09;c.minDistance=6;c.maxDistance=28;
    c.maxPolarAngle=Math.PI*.93;c.enablePan=true;c.screenSpacePanning=true;
    c.addEventListener('start',()=>{moving.current=false;});
    c.addEventListener('change',invalidate);
    controls.current=c;
    return()=>{controls.current=null;c.dispose();};
  },[camera,gl,invalidate]);
  useEffect(()=>{
    const preset=CAMERA[view]||CAMERA.integral;
    targetPosition.current.set(...preset.position);targetLook.current.set(...preset.target);
    camera.fov=preset.fov;camera.updateProjectionMatrix();moving.current=true;
    if(typeof window!=='undefined'&&window.matchMedia('(prefers-reduced-motion: reduce)').matches){
      camera.position.copy(targetPosition.current);controls.current?.target.copy(targetLook.current);moving.current=false;
    }
    invalidate();
  },[view,resetKey,camera,invalidate]);
  useFrame((_,delta)=>{
    const c=controls.current;if(!c)return;
    if(moving.current){
      const alpha=1-Math.exp(-Math.min(delta,.05)*5.2);
      camera.position.lerp(targetPosition.current,alpha);c.target.lerp(targetLook.current,alpha);
      if(camera.position.distanceToSquared(targetPosition.current)<.00004&&c.target.distanceToSquared(targetLook.current)<.00004)moving.current=false;
    }
    c.update();
    if(moving.current)invalidate();
  });
  return null;
}

function DensityRibbon({points,color,opacity=.25}) {
  const geometry=useDispose(useMemo(()=>{
    const positions=[],colors=[],indices=[];
    const c=new THREE.Color(color);
    points.forEach(({position:p},i)=>{
      positions.push(p[0],0,-.045,p[0],p[1],-.045);
      colors.push(...c.clone().multiplyScalar(.25).toArray(),...c.toArray());
      if(i<points.length-1){const n=i*2;indices.push(n,n+1,n+3,n,n+3,n+2);}
    });
    const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));g.setAttribute('color',new THREE.Float32BufferAttribute(colors,3));g.setIndex(indices);g.computeVertexNormals();return g;
  },[points,color]));
  return <mesh geometry={geometry}><meshBasicMaterial vertexColors transparent opacity={opacity} side={THREE.DoubleSide} depthWrite={false}/></mesh>;
}

const DensityCurves=React.memo(function DensityCurves({parts}){
  return parts.map((part,index)=><group key={index}>
    <DensityRibbon points={part} color={PALETTE.cyan} opacity={.25}/>
    <Line points={part.map(p=>p.position)} color={PALETTE.cyan} opacity={.95}/>
    <Line points={part.map(p=>[p.position[0],p.position[1],-.08])} color={PALETTE.ivory} opacity={.2}/>
  </group>);
});

function IntegralView({coefficients,progress,quality}) {
  const coeff=coefficientVector(coefficients);
  const values=useMemo(()=>sampleDensity(coeff,quality==='eco'?500:1000),[...coeff,quality]);
  const display=useMemo(()=>densityDisplay(values),[values]);
  const scan=Math.max(0,Math.min(1,Number(progress)||0))*Math.PI;
  const closest=useMemo(()=>values.reduce((a,b)=>Math.abs(b.theta-scan)<Math.abs(a.theta-scan)?b:a,values[0]),[values,scan]);
  const scanX=10*(scan/Math.PI-.5),scanY=closest?4.5*closest.density/display.maxDensity:0;
  const floor=useMemo(()=>{
    const a=[];
    for(let j=0;j<=12;j++){let x=10*(j/12-.5);a.push([x,0,-1],[x,0,1]);}
    for(let j=-2;j<=2;j++)a.push([-5,0,j*.5],[5,0,j*.5]);
    return a;
  },[]);
  const rootMarkers=useMemo(()=>GOLDEN_ROOT_ANGLES.map((theta,i)=>({x:10*(theta/Math.PI-.5),color:goldenCharacter([1,7,11,13][i])>0?PALETTE.gold:PALETTE.cyan})),[]);
  return <group position={[0,-2,0]}>
    <Segments positions={floor} color="#527081" opacity={.16}/>
    <AxisTicks/>
    <Line points={[[-5,0,0],[-5,4.75,0]]} color={PALETTE.muted} opacity={.45}/>
    <DensityCurves parts={display.parts}/>
    {display.parts.map((part,index)=><DensityRibbon key={index} points={part.filter(p=>p.theta>=scan)} color={PALETTE.gold} opacity={.35}/>)}
    {rootMarkers.map(({x,color},i)=><group key={i} position={[x,0,0]}>
      <Line points={[[0,-.1,0],[0,4.85,0]]} color={color} opacity={.22}/>
      <mesh position={[0,-.025,0]} rotation={[Math.PI/2,0,0]}><torusGeometry args={[.06,.009,6,28]}/><meshBasicMaterial color={color}/></mesh>
      <Dot position={[0,4.88,0]} color={color} radius={.034}/>
    </group>)}
    <Line points={[[scanX,0,.06],[scanX,scanY,.06]]} color={PALETTE.gold} opacity={.9}/>
    <Dot position={[scanX,scanY,.06]} radius={.055}/>
    <mesh position={[scanX,0,0]} rotation={[-Math.PI/2,0,0]}><circleGeometry args={[.085,24]}/><meshBasicMaterial color={PALETTE.gold} transparent opacity={.7} side={THREE.DoubleSide}/></mesh>
  </group>;
}

function PhaseNode({exponent,selected,onSelectPhase}) {
  const {gl}=useThree();
  const angle=2*Math.PI*exponent/30,radius=4.55;
  const position=[radius*Math.cos(angle),radius*Math.sin(angle),.12];
  const color=goldenCharacter(exponent)>0?PALETTE.gold:PALETTE.cyan;
  const active=Number(selected)===exponent;
  return <group position={position}>
    <mesh onClick={event=>{event.stopPropagation();onSelectPhase?.(exponent);}} onPointerOver={event=>{event.stopPropagation();gl.domElement.style.cursor='pointer';}} onPointerOut={()=>{gl.domElement.style.cursor='';}}>
      <sphereGeometry args={[.23,12,10]}/><meshBasicMaterial visible={false}/>
    </mesh>
    <Dot position={[0,0,0]} radius={active ? .105 : .065} color={color}/>
    <mesh><torusGeometry args={[active ? .19 : .135,active ? .016 : .009,8,42]}/><meshBasicMaterial color={color} transparent opacity={active?1:.58}/></mesh>
    {active&&<mesh><torusGeometry args={[.26,.006,6,42]}/><meshBasicMaterial color={color} transparent opacity={.35}/></mesh>}
  </group>;
}

function SpectrumView({progress,selectedPhase,onSelectPhase}) {
  const orbitPaths=useMemo(()=>Array.from({length:8},(_,orbit)=>ROOT_DATA.filter(root=>root.orbit===orbit).sort((a,b)=>a.step-b.step).map(root=>[root.x*3.75,root.y*3.75,root.z*.65])),[]);
  const allPoints=useMemo(()=>ROOT_DATA.map(root=>[root.x*3.75,root.y*3.75,root.z*.65]),[]);
  const pointColors=useMemo(()=>ROOT_DATA.map(root=>ORBIT_COLORS[root.orbit]),[]);
  const circle=useMemo(()=>Array.from({length:241},(_,i)=>{const a=i/240*Math.PI*2;return[4.55*Math.cos(a),4.55*Math.sin(a),.12];}),[]);
  const ticks=useMemo(()=>Array.from({length:30},(_,i)=>{const a=i/30*Math.PI*2;return[[4.41*Math.cos(a),4.41*Math.sin(a),.12],[4.64*Math.cos(a),4.64*Math.sin(a),.12]];}).flat(),[]);
  const step=Math.min(29,Math.floor(((Number(progress)||0)%1)*30));
  const highlights=useMemo(()=>ROOT_DATA.filter(root=>root.step===step).map(root=>[root.x*3.75,root.y*3.75,root.z*.65]),[step]);
  const e=PRIMITIVE_30.includes(Number(selectedPhase))?Number(selectedPhase):1;
  const angle=e*2*Math.PI/30;
  const axis=useMemo(()=>[[0,0,.13],[4.55*Math.cos(angle),4.55*Math.sin(angle),.13]],[angle]);
  const arc=useMemo(()=>{const count=Math.max(2,e*6);return Array.from({length:count},(_,i)=>{const theta=angle*i/(count-1);return[.9*Math.cos(theta),.9*Math.sin(theta),.14];});},[angle,e]);
  return <group>
    {orbitPaths.map((path,i)=><Line key={i} points={path} closed color={ORBIT_COLORS[i]} opacity={.12}/>) }
    <GlowPoints points={allPoints} colors={pointColors} size={5.6}/>
    <GlowPoints points={highlights} color={PALETTE.ivory} size={10}/>
    <Line points={circle} color={PALETTE.muted} opacity={.3}/>
    <Segments positions={ticks} color={PALETTE.ivory} opacity={.32}/>
    <Line points={[[-4.85,0,-.15],[4.85,0,-.15]]} color={PALETTE.muted} opacity={.13}/>
    <Line points={[[0,-4.85,-.15],[0,4.85,-.15]]} color={PALETTE.muted} opacity={.13}/>
    <Line points={axis} color={goldenCharacter(e)>0?PALETTE.gold:PALETTE.cyan} opacity={.42}/>
    <Line points={arc} color={goldenCharacter(e)>0?PALETTE.gold:PALETTE.cyan} opacity={.65}/>
    <Dot position={[0,0,.13]} color={PALETTE.ivory} radius={.035}/>
    {PRIMITIVE_30.map(exponent=><PhaseNode key={exponent} exponent={exponent} selected={e} onSelectPhase={onSelectPhase}/>)}
  </group>;
}

function Stem({x,y,z,color,active=false}) {
  const h=Math.abs(y),sign=Math.sign(y)||1;
  return <group>
    {h>1e-8&&<mesh position={[x,y/2,z]}><cylinderGeometry args={[active ? .023 : .014,active ? .023 : .014,h,7]}/><meshStandardMaterial color={color} emissive={color} emissiveIntensity={active ? .6 : .2} roughness={.4}/></mesh>}
    <Dot position={[x,y,z]} color={color} radius={active ? .065 : .035} opacity={active?1:.8}/>
  </group>;
}

function FourierView({progress}) {
  const values=useMemo(()=>Array.from({length:32},(_,i)=>({n:i+1,...fourierCoefficients(i+1)})),[]);
  const largest=useMemo(()=>Math.max(...values.flatMap(v=>[Math.abs(v.A),Math.abs(v.K)])),[values]);
  const height=2.45/largest;
  const index=Math.max(0,Math.min(31,Math.floor((Number(progress)||0)*32)));
  const positions=useMemo(()=>{
    const p=[];
    for(let i=0;i<=8;i++){const x=-5+i*1.25;p.push([x,-2.6,-1.4],[x,2.6,-1.4],[x,-2.6,1.4],[x,2.6,1.4]);}
    for(let y=-2;y<=2;y++)p.push([-5,y,-1.4],[5,y,-1.4],[-5,y,1.4],[5,y,1.4]);
    return p;
  },[]);
  const selected=values[index],sx=-5+index*10/31;
  return <group>
    <Segments positions={positions} color={PALETTE.muted} opacity={.11}/>
    <Line points={[[-5.2,0,-1.4],[5.3,0,-1.4]]} color={PALETTE.gold} opacity={.5}/>
    <Line points={[[-5.2,0,1.4],[5.3,0,1.4]]} color={PALETTE.cyan} opacity={.5}/>
    <Line points={[[sx,-2.65,-1.4],[sx,2.65,-1.4],[sx,2.65,1.4],[sx,-2.65,1.4]]} color={PALETTE.ivory} opacity={.15}/>
    {values.map((v,i)=><group key={v.n}>
      <Stem x={-5+i*10/31} y={v.A*height} z={-1.4} color={PALETTE.gold} active={i===index}/>
      <Stem x={-5+i*10/31} y={v.K*height} z={1.4} color={PALETTE.cyan} active={i===index}/>
    </group>)}
    <Line points={[[sx,selected.A*height,-1.4],[sx,selected.K*height,1.4]]} color={PALETTE.ivory} opacity={.3}/>
  </group>;
}

function Ellipsoid({slice,fraction=1,color=PALETTE.gold,opacity=.15}) {
  const geometry=useDispose(useMemo(()=>{
    const longs=72,lats=36,positions=[],indices=[];
    for(let j=0;j<=lats;j++)for(let i=0;i<=longs;i++)positions.push(...ellipsoidPoint(slice,Math.PI*2*i/longs,-Math.PI/2+Math.PI*j/lats,fraction));
    for(let j=0;j<lats;j++)for(let i=0;i<longs;i++){const a=j*(longs+1)+i,b=a+longs+1;indices.push(a,b,a+1,b,b+1,a+1);}
    const g=new THREE.BufferGeometry();g.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));g.setIndex(indices);g.computeVertexNormals();return g;
  },[slice,fraction]));
  const latitudes=useMemo(()=>[-.8,-.4,0,.4,.8].map(latitude=>Array.from({length:121},(_,i)=>ellipsoidPoint(slice,Math.PI*2*i/120,latitude,fraction))),[slice,fraction]);
  const longitudes=useMemo(()=>Array.from({length:12},(_,j)=>Array.from({length:61},(_,i)=>ellipsoidPoint(slice,Math.PI*2*j/12,-Math.PI/2+Math.PI*i/60,fraction))),[slice,fraction]);
  return <group>
    <mesh geometry={geometry} renderOrder={1}><meshPhysicalMaterial color={color} emissive={color} emissiveIntensity={.055} metalness={.35} roughness={.3} transparent opacity={opacity} depthWrite={false} side={THREE.DoubleSide} clearcoat={.4}/></mesh>
    {latitudes.map((p,i)=><Line key={`a${i}`} points={p} color={color} opacity={.16}/>) }
    {longitudes.map((p,i)=><Line key={`b${i}`} points={p} color={color} opacity={.12}/>) }
  </group>;
}

function EnergyView({coefficients}) {
  const coeff=coefficientVector(coefficients);
  const slice=useMemo(()=>energySlice(gramMatrix(),coeff),[...coeff]);
  const point=useMemo(()=>normalizedEnergyPoint(slice),[slice]);
  const axes=useMemo(()=>[0,1,2].map(i=>[-1,1].map(sign=>[0,1,2].map(j=>i===j?sign*4.2:0))).flat(),[]);
  const innerFraction=Math.max(0,Math.min(1,(slice.energy-slice.minimum)/(slice.level-slice.minimum)));
  const principal=useMemo(()=>slice.eigen.vectors.map((vector,i)=>vector.map(v=>v*slice.radii[i]*slice.worldScale)),[slice]);
  return <group>
    <Segments positions={axes} color={PALETTE.ivory} opacity={.23}/>
    <Ellipsoid slice={slice} color={PALETTE.gold} opacity={.09}/>
    {innerFraction>1e-8&&<Ellipsoid slice={slice} fraction={innerFraction} color={PALETTE.cyan} opacity={.18}/>}
    <Dot position={[0,0,0]} color={PALETTE.ivory} radius={.04}/>
    {principal.map((p,i)=><Line key={i} points={[p.map(v=>-v),p]} color={i===0?PALETTE.gold:PALETTE.muted} opacity={.36}/>) }
    <Line points={[[0,0,0],point]} color={PALETTE.ivory} opacity={.55}/>
    <Dot position={point} color={PALETTE.ivory} radius={.09}/>
    <mesh position={point}><sphereGeometry args={[.17,20,16]}/><meshBasicMaterial color={PALETTE.ivory} transparent opacity={.09} depthWrite={false}/></mesh>
  </group>;
}

function Ready({onReady,onError}) {
  const {gl}=useThree();const fired=useRef(false);
  useFrame(()=>{if(!fired.current){fired.current=true;onReady?.();}});
  useEffect(()=>{
    const canvas=gl.domElement;
    const lost=event=>{event.preventDefault();onError?.(new Error('The graphics context was interrupted. The exact equations and 2D view remain available.'));};
    canvas.addEventListener('webglcontextlost',lost,false);
    return()=>{canvas.removeEventListener('webglcontextlost',lost,false);canvas.style.cursor='';};
  },[gl,onError]);
  return null;
}

function WebGLUnavailable({onError}) {
  useEffect(()=>{onError?.(new Error('This device did not provide a WebGL context. The exact equations and 2D view remain available.'));},[onError]);
  return <div className="studio-webgl-fallback" role="status">The exact mathematical view is available without 3D graphics.</div>;
}

class SceneBoundary extends React.Component {
  constructor(props){super(props);this.state={error:null};}
  static getDerivedStateFromError(error){return {error};}
  componentDidCatch(error){this.props.onError?.(error);}
  render(){return this.state.error?null:this.props.children;}
}

/**
 * Self-contained R3F scene. No remote textures, arbitrary particles, or invented
 * edges: geometry consists of an integral graph, exported E8 roots, exact
 * eigenphases/Fourier coefficients, and a true quadratic energy slice.
 */
export default function StudioScene({view='integral',coefficients=[1,0,0,0],progress=0,playing=false,selectedPhase=1,onSelectPhase,onReady,onError,quality='auto',resetKey=0}) {
  const effectiveQuality=quality==='auto'&&typeof navigator!=='undefined'&&((navigator.deviceMemory||8)<4||(navigator.hardwareConcurrency||8)<4)?'eco':quality;
  // The mathematical scan is supplied by the UI. Paused/reduced-motion views
  // never add independent orbiting or decorative time-dependent movement.
  const dpr=effectiveQuality==='eco'?[1,1.25]:[1,1.75];
  return <SceneBoundary onError={onError}>
    <Canvas dpr={dpr} frameloop="demand" camera={{position:CAMERA.integral.position,fov:38,near:.1,far:70}} gl={{antialias:true,alpha:false,powerPreference:effectiveQuality==='eco'?'low-power':'high-performance',preserveDrawingBuffer:true}}
      onCreated={({gl})=>{gl.setClearColor(PALETTE.ink);gl.toneMapping=THREE.ACESFilmicToneMapping;gl.toneMappingExposure=1.15;}}
      fallback={<WebGLUnavailable onError={onError}/>}
      style={{touchAction:'none'}} aria-label={`Interactive ${view} mathematics; drag to orbit and pinch to zoom`}>
      <color attach="background" args={[PALETTE.ink]}/>
      <fog attach="fog" args={[PALETTE.ink,22,45]}/>
      <ambientLight intensity={.35}/>
      <hemisphereLight color="#c7dfed" groundColor="#1c3444" intensity={1.4}/>
      <directionalLight position={[5,7,8]} intensity={2.4} color="#f3d6a8"/>
      <pointLight position={[-6,2,5]} color="#69dce5" intensity={40} distance={22} decay={2}/>
      <pointLight position={[5,-3,-2]} color="#d9b782" intensity={25} distance={20} decay={2}/>
      <CameraRig view={view} resetKey={resetKey}/>
      {view==='integral'&&<IntegralView coefficients={coefficients} progress={progress} quality={effectiveQuality}/>}
      {view==='spectrum'&&<SpectrumView progress={progress} selectedPhase={selectedPhase} onSelectPhase={onSelectPhase}/>}
      {view==='fourier'&&<FourierView progress={progress}/>}
      {view==='energy'&&<EnergyView coefficients={coefficients}/>}
      <Ready onReady={onReady} onError={onError}/>
    </Canvas>
  </SceneBoundary>;
}
