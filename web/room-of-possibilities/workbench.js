import * as THREE from 'three';
import {roundedBlock} from './museum.js';
const offsets=[[0,0,0],[-.95,.08,0],[-1.05,.1,0],[.15,.65,0],[.15,.85,0],[.2,.25,1.05],[-1.05,.1,.3],[-1.05,.1,.3],[-1.05,.1,0],[.2,.25,1.05],[.65,.6,0],[.95,.1,0]];
const colors=['#658795','#79cbd3','#b7d3d8','#dfba7a','#dfba7a','#edbd7e','#b7d3d8','#72bcbf','#b7d3d8','#76929f','#dfba7a','#bda8f0'];
export function createWorkbench(scene,parts){
 const root=new THREE.Group();root.visible=false;scene.add(root);
 const table=new THREE.Mesh(roundedBlock(8.5,.38,6,.2),new THREE.MeshStandardMaterial({color:'#183341',metalness:.7,roughness:.35}));table.position.y=-.24;root.add(table);
 const modelGroup=new THREE.Group();modelGroup.scale.setScalar(3.2);root.add(modelGroup);
 function chip(text){const c=document.createElement('canvas');c.width=512;c.height=128;const ctx=c.getContext('2d');ctx.fillStyle='#0b1b25ee';ctx.strokeStyle='#628491';ctx.lineWidth=3;ctx.beginPath();ctx.roundRect(2,2,508,124,18);ctx.fill();ctx.stroke();ctx.fillStyle='#e3eceb';ctx.font='600 64px system-ui';ctx.textAlign='center';ctx.textBaseline='middle';ctx.fillText(text,256,65);const texture=new THREE.CanvasTexture(c);texture.colorSpace=THREE.SRGBColorSpace;const sprite=new THREE.Sprite(new THREE.SpriteMaterial({map:texture,transparent:true,depthWrite:false}));sprite.scale.set(2,.5,1);return sprite;}
 const labels=[chip('MOTOR'),chip('GEAR DRIVE'),chip('ARM'),chip('LOAD')];labels.forEach(x=>root.add(x));
 let model,meshes=[],amount=0;
 function setModel(d){model=d;for(const m of meshes){modelGroup.remove(m);m.material.dispose()}meshes=parts.map((part,i)=>{const material=part.material.clone();material.color.set(colors[i]||'#a9c6ca');const mesh=new THREE.Mesh(part.geometry,material);modelGroup.add(mesh);return mesh});}
 function frame(now,dt,explode,reduced){const next=reduced?(explode?1:0):amount+((explode?1:0)-amount)*(1-Math.exp(-dt*5));const moving=Math.abs(next-amount)>1e-5;amount=next;if(!model)return false;parts.forEach((part,i)=>{const mesh=meshes[i],local=part.userData.transform(model),offset=offsets[i]||[0,0,0];mesh.position.set(...local.p).addScaledVector(new THREE.Vector3(...offset),amount);mesh.rotation.set(...(local.r||[0,0,0]));if(part.userData.rotor)mesh.rotation.z=reduced?0:now*.0006*(1+model.g*.08);mesh.scale.set(...local.s)});
 [2,5,4,11].forEach((i,j)=>{labels[j].visible=amount>.75;labels[j].position.copy(meshes[i].position).multiplyScalar(3.2);labels[j].position.y+=j===2?1.1:1.2;labels[j].position.x+=j===0?-1:j===3?-.4:0;});return moving;
 }
 return {root,setModel,frame,get amount(){return amount},get componentCount(){return meshes.length},open(d){amount=0;setModel(d);root.visible=true},close(){root.visible=false}};
}
