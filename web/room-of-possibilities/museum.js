import * as THREE from 'three';
import { RoomEnvironment } from 'three/addons/environments/RoomEnvironment.js';

export const ROOM={workshop:0,map:58,family:116};
const V=(x,y,z)=>new THREE.Vector3(x,y,z);
const metal=color=>new THREE.MeshStandardMaterial({color,metalness:.7,roughness:.32});
function mesh(group,geometry,material,position,rotation){const m=new THREE.Mesh(geometry,material);m.position.set(...position);if(rotation)m.rotation.set(...rotation);group.add(m);return m}
function strip(group,x,y,z,w,h,d,color){return mesh(group,new THREE.BoxGeometry(w,h,d),new THREE.MeshBasicMaterial({color}),[x,y,z])}
export function gearGeometry(){const shape=new THREE.Shape();const teeth=16;for(let i=0;i<teeth*4;i++){let t=i/(teeth*4)*Math.PI*2,r=i%4===0||i%4===3?.16:.205,x=Math.cos(t)*r,y=Math.sin(t)*r;if(i===0)shape.moveTo(x,y);else shape.lineTo(x,y)}shape.closePath();const hole=new THREE.Path();hole.absarc(0,0,.058,0,Math.PI*2,true);shape.holes.push(hole);const g=new THREE.ExtrudeGeometry(shape,{depth:.07,bevelEnabled:true,bevelSize:.009,bevelThickness:.008,bevelSegments:1,steps:1});g.translate(0,0,-.035);return g}
export function roundedBlock(w,h,d,r=.06){const s=new THREE.Shape();const x=-w/2,y=-h/2;s.moveTo(x+r,y);s.lineTo(x+w-r,y);s.quadraticCurveTo(x+w,y,x+w,y+r);s.lineTo(x+w,y+h-r);s.quadraticCurveTo(x+w,y+h,x+w-r,y+h);s.lineTo(x+r,y+h);s.quadraticCurveTo(x,y+h,x,y+h-r);s.lineTo(x,y+r);s.quadraticCurveTo(x,y,x+r,y);const g=new THREE.ExtrudeGeometry(s,{depth:d,bevelEnabled:true,bevelSize:.018,bevelThickness:.018,bevelSegments:1,steps:1});g.translate(0,0,-d/2);return g}
function text(group,value,x,y,z,width,color='#d6d8ce'){const c=document.createElement('canvas');c.width=1024;c.height=160;const ctx=c.getContext('2d');ctx.fillStyle=color;ctx.textAlign='center';ctx.textBaseline='middle';ctx.font='500 52px system-ui';ctx.fillText(value,512,80);const tex=new THREE.CanvasTexture(c);tex.colorSpace=THREE.SRGBColorSpace;const m=mesh(group,new THREE.PlaneGeometry(width,width/6.4),new THREE.MeshBasicMaterial({map:tex,transparent:true,depthWrite:false}),[x,y,z]);return m}
export function createMuseum(scene,renderer){
 const environment=new THREE.PMREMGenerator(renderer),room=new RoomEnvironment();const env=environment.fromScene(room,.06);scene.environment=env.texture;room.dispose();environment.dispose();
 scene.fog=new THREE.FogExp2('#080f16',.006);scene.background=new THREE.Color('#080f16');
 const halls=[];
 for(const [name,offset] of Object.entries(ROOM)){
  const g=new THREE.Group();g.position.x=offset;g.userData.room=name;scene.add(g);halls.push(g);
  const floor=new THREE.MeshStandardMaterial({color:name==='workshop'?'#0e1922':name==='map'?'#0a2228':'#121529',metalness:.25,roughness:.82});
  mesh(g,new THREE.BoxGeometry(46,.25,40),floor,[0,-.24,0]);
  const grid=new THREE.GridHelper(44,22,name==='map'?'#40666d':'#2a3d4a','#1c2f39');grid.position.y=-.105;g.add(grid);
  const accent=name==='workshop'?'#c39a5d':name==='map'?'#72dac6':'#a3acf4';
  for(const x of [-22,22]){
   strip(g,x,.0,0,.04,.035,38,accent);
   for(const z of [-17,-7,7,17]){mesh(g,new THREE.BoxGeometry(.22,9,.3),metal('#344958'),[x,4.4,z]);strip(g,x-.14,5,z,.04,7,.1,accent)}
  }
  for(const z of [-17]){mesh(g,new THREE.BoxGeometry(44,.22,.24),metal('#2b404f'),[0,8.8,z]);strip(g,0,8.65,z,39,.045,.09,accent)}
  mesh(g,new THREE.BoxGeometry(44,10,.2),metal('#0d1921'),[0,4.8,-20]);
  text(g,name==='workshop'?'01 / THE SEARCH HALL':name==='map'?'02 / THE CONSTRAINT ATLAS':'03 / THE EXACT FAMILY',0,6.9,-19.85,24,accent);
  text(g,name==='workshop'?'EVERY DEFINED DESIGN HAS A PLACE':name==='map'?'SAME OBJECTS. VISIBLE REQUIREMENTS.':'STRUCTURE REPLACES ENUMERATION',0,5.3,-19.84,19,'#92aebb');
  if(name!=='workshop'){
   const ring=mesh(g,new THREE.TorusGeometry(name==='family'?13:18,.045,8,100),new THREE.MeshBasicMaterial({color:accent}),[0,-.055,0],[Math.PI/2,0,0]);
   const inner=mesh(g,new THREE.CylinderGeometry(name==='family'?12:17.5,name==='family'?12:17.5,.09,80),new THREE.MeshStandardMaterial({color:name==='family'?'#161d2c':'#122a30',metalness:.5,roughness:.4}),[0,-.085,0]);
  }
  const key=new THREE.PointLight(accent,120,45,2);key.position.set(-8,7,9);g.add(key);
 }
 const corridor=new THREE.Group();scene.add(corridor);
 for(let x=23;x<115;x+=2.5){if(x>35&&x<81||x>93){strip(corridor,x,-.08,12,1.3,.025,.1,'#557c85');strip(corridor,x,-.08,-12,1.3,.025,.1,'#557c85')}}
 const constraints=new THREE.Group();constraints.position.x=ROOM.map;scene.add(constraints);constraints.visible=false;
 const box=new THREE.Box3(V(-9.075,0,-9.8),V(9.075,5.4,9.8));const cage=new THREE.Box3Helper(box,'#548780');constraints.add(cage);
 for(let a=0;a<3;a++){const grid=new THREE.GridHelper(22,11,'#335d61','#233f45');grid.position.y=a*2.7;constraints.add(grid);text(constraints,'ARM '+(a+1),0,a*2.7+.5,-11.5,4,'#7bcdbb')}
 const edges=[[0,1],[0,2],[0,4],[1,3],[1,5],[2,3],[2,6],[3,7],[4,5],[4,6],[5,7],[6,7]];
 const corners=[];for(let i=0;i<8;i++)corners.push(V((i&1)?9.075:-9.075,(i&2)?5.4:0,(i&4)?9.8:-9.8));
 let sheet,contours=[];
 function update({load,size,visible,room='workshop'}){
  for(const hall of halls)hall.visible=hall.userData.room===room;
  constraints.visible=visible;
  if(sheet){constraints.remove(sheet);sheet.geometry.dispose();sheet.material.dispose();sheet=null}
  const n=V(1/1.65,1/2.7,1/2.8),c=12-size,points=[];
  for(const [i,j] of edges){const a=corners[i],b=corners[j],va=n.dot(a)+c,vb=n.dot(b)+c;if(va*vb>0||va===vb)continue;const t=va/(va-vb);if(t>=0&&t<=1){const p=a.clone().lerp(b,t);if(!points.some(q=>q.distanceTo(p)<1e-6))points.push(p)}}
  if(points.length>=3){const center=points.reduce((s,p)=>s.add(p),V(0,0,0)).divideScalar(points.length),normal=n.clone().normalize(),u=normal.clone().cross(V(0,1,0)).normalize(),v=normal.clone().cross(u);points.sort((a,b)=>Math.atan2(a.clone().sub(center).dot(v),a.clone().sub(center).dot(u))-Math.atan2(b.clone().sub(center).dot(v),b.clone().sub(center).dot(u)));const positions=[];for(let i=1;i<points.length-1;i++)for(const p of [points[0],points[i],points[i+1]])positions.push(...p.toArray());const geo=new THREE.BufferGeometry();geo.setAttribute('position',new THREE.Float32BufferAttribute(positions,3));geo.computeVertexNormals();sheet=new THREE.Mesh(geo,new THREE.MeshBasicMaterial({color:'#69d5c3',transparent:true,opacity:.15,side:THREE.DoubleSide,depthWrite:false}));constraints.add(sheet)}
  for(const line of contours){constraints.remove(line);line.geometry.dispose();line.material.dispose()}contours=[];
  for(let a=1;a<=3;a++){const pts=[];for(let m=1;m<=12;m+=.08){const g=load*a/m;if(g>=1&&g<=8)pts.push(V((m-6.5)*1.65,(a-1)*2.7+.09,(g-4.5)*2.8))}if(pts.length>1){const line=new THREE.Line(new THREE.BufferGeometry().setFromPoints(pts),new THREE.LineBasicMaterial({color:'#edb775'}));constraints.add(line);contours.push(line)}}
 }
 return {update,constraints,halls,sheet:()=>sheet,dispose:()=>env.dispose()};
}
