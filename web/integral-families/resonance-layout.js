// Place measured HTML labels inside the scene's clear area. The geometry
// remains untouched; labels move only when their measured boxes collide.
const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
const intersects=(a,b,gap)=>a.x-a.width/2 < b.x+b.width/2+gap && a.x+a.width/2+gap > b.x-b.width/2 && a.y < b.y+b.height+gap && a.y+a.height+gap > b.y;
export function placeLabels(points,sizes,width,height,{focus=null,top=90,bottom=115,gap=7}={}){
 if(!Number.isFinite(width)||!Number.isFinite(height)||width<=0||height<=0)return [];
 const visible=points.map(p=>{
  const size=sizes[p.id]||{width:110,height:42},w=Math.min(width-16,size.width),h=size.height;
  return {...p,width:w,height:h,visible:p.visible!==false&&(!focus||focus===p.id)&&Number.isFinite(p.x)&&Number.isFinite(p.y)&&p.x>-70&&p.x<width+70&&p.y>-70&&p.y<height+70,
   x:clamp(p.x,w/2+8,width-w/2-8),y:clamp(p.y,top,Math.max(top,height-bottom-h))};
 });
 const placed=[];
 for(const p of visible.filter(p=>p.visible).sort((a,b)=>a.y-b.y||a.x-b.x)){
  const target=p.y,limit=Math.max(top,height-bottom-p.height),step=p.height+gap;
  let best=null;
  search:for(let distance=0;distance<=visible.length;distance++)for(const sign of distance?[1,-1]:[1]){
   const candidate={...p,y:clamp(target+sign*distance*step,top,limit)};
   if(!placed.some(other=>intersects(candidate,other,gap))){best=candidate;break search;}
  }
  // Five labels fit the supported scene sizes; preserve the bounded target
  // if an exceptionally short embedding leaves no collision-free position.
  Object.assign(p,best||{y:target});placed.push(p);
 }
 return visible;
}
