import * as THREE from 'three';

// These surfaces are visual motifs. Only the scene's separately retained
// E8 point cloud and neighbor edges carry the exact root interpretation.
const TAU = Math.PI * 2;
const PALETTE = [0x6496ff, 0xff7864, 0xb478ff, 0xffc896, 0xb4b4ff];
const finite = p => Number.isFinite(p.x) && Number.isFinite(p.y) && Number.isFinite(p.z);

/** A closed (or tapered open) strip with a parallel-transport width frame. */
export function createRibbonGeometry(curve, width = .035, segments = 160, closed = true) {
  if (!(width > 0) || !Number.isFinite(width) || !Number.isInteger(segments) || segments < 8) throw new Error('A positive width and at least eight ribbon segments are required.');
  const points = [], tangents = [], frames = [], axis = new THREE.Vector3(), q = new THREE.Quaternion();
  const read = t => {
    const p = typeof curve === 'function' ? curve(t) : curve.getPoint(t);
    const result = p?.isVector3 ? p.clone() : new THREE.Vector3(...p);
    if (!finite(result)) throw new Error('Ribbon coordinates must be finite.');
    return result;
  };
  for (let i = 0; i <= segments; i++) points.push(read(i / segments));
  if (closed && points[0].distanceTo(points[segments]) > 1e-6) throw new Error('A closed ribbon must have coincident end points.');
  for (let i = 0; i <= segments; i++) {
    const previous = points[i === 0 ? (closed ? segments - 1 : 0) : i - 1];
    const next = points[i === segments ? (closed ? 1 : segments) : i + 1];
    const t = next.clone().sub(previous);
    if (t.lengthSq() < 1e-15) throw new Error('A ribbon curve must have a nonzero tangent.');
    tangents.push(t.normalize());
  }
  const centroid = new THREE.Vector3();
  for (let i = 0; i < (closed ? segments : segments + 1); i++) centroid.add(points[i]);
  centroid.multiplyScalar(1 / (closed ? segments : segments + 1));
  axis.copy(points[0]).sub(centroid).addScaledVector(tangents[0], -points[0].clone().sub(centroid).dot(tangents[0]));
  if (axis.lengthSq() < 1e-12) {
    axis.set(Math.abs(tangents[0].y) < .85 ? 0 : 1, Math.abs(tangents[0].y) < .85 ? 1 : 0, 0);
    axis.cross(tangents[0]);
  }
  frames.push(axis.normalize().clone());
  for (let i = 1; i <= segments; i++) {
    q.setFromUnitVectors(tangents[i - 1], tangents[i]);
    const n = frames[i - 1].clone().applyQuaternion(q);
    n.addScaledVector(tangents[i], -n.dot(tangents[i])).normalize(); frames.push(n);
  }
  // Remove the accumulated closed-loop twist instead of hiding a visible seam.
  if (closed) {
    const cross = new THREE.Vector3().crossVectors(frames[segments], frames[0]);
    const correction = Math.atan2(tangents[0].dot(cross), frames[segments].dot(frames[0]));
    for (let i = 1; i <= segments; i++) frames[i].applyAxisAngle(tangents[i], correction * i / segments);
  }
  const position = [], uv = [], indices = [];
  for (let i = 0; i <= segments; i++) {
    const t = i / segments, taper = closed ? 1 : .12 + .88 * Math.pow(Math.sin(Math.PI * t), .4);
    for (let side = 0; side < 2; side++) {
      const p = points[i].clone().addScaledVector(frames[i], (side - .5) * width * taper);
      position.push(p.x, p.y, p.z); uv.push(t, side);
    }
    if (i < segments) { const a = i * 2; indices.push(a, a + 1, a + 2, a + 1, a + 3, a + 2); }
  }
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.Float32BufferAttribute(position, 3));
  g.setAttribute('uv', new THREE.Float32BufferAttribute(uv, 2)); g.setIndex(indices); g.computeVertexNormals();
  // Smooth the duplicate seam vertices; UVs deliberately remain 0 and 1.
  if (closed) {
    const n = g.attributes.normal;
    for (let side = 0; side < 2; side++) {
      axis.fromBufferAttribute(n, side).add(new THREE.Vector3().fromBufferAttribute(n, segments * 2 + side)).normalize();
      n.setXYZ(side, axis.x, axis.y, axis.z); n.setXYZ(segments * 2 + side, axis.x, axis.y, axis.z);
    }
  }
  g.computeBoundingSphere(); return g;
}

const surfaceVertex = `
  uniform float uTime;
  uniform float uMotion;
  varying vec2 vUv;
  varying vec3 vNormal;
  varying vec3 vView;
  varying vec3 vLocal;
  void main(){
    vUv=uv; vLocal=position;
    float wave=sin(position.y*8.+uTime*.7)*sin(position.x*7.-uTime*.45);
    vec3 p=position+normal*(wave*.012*uMotion);
    vec4 mv=modelViewMatrix*vec4(p,1.);
    vView=-mv.xyz; vNormal=normalize(normalMatrix*normal);
    gl_Position=projectionMatrix*mv;
  }`;
const surfaceFragment = `
  uniform vec3 uColor;
  uniform float uTime;
  uniform float uOpacity;
  uniform float uRibbon;
  uniform float uPhase;
  varying vec2 vUv;
  varying vec3 vNormal;
  varying vec3 vView;
  varying vec3 vLocal;
  void main(){
    float facing=abs(dot(normalize(vNormal),normalize(vView)));
    float fresnel=pow(1.-facing,2.5);
    float edge=pow(abs(vUv.y*2.-1.),18.);
    float phase=vUv.x*6.28318530718;
    float signal=pow(.5+.5*cos(phase*7.-uTime*1.5+uPhase),20.);
    float fine=pow(.5+.5*sin(vLocal.y*56.+uTime*.55),16.);
    float broad=.5+.5*sin(phase*3.-uTime*.6+uPhase);
    float strength=mix(.012+fresnel*.24+fine*.027,.045+edge*.32+fresnel*.21+signal*.09,uRibbon);
    vec3 color=uColor*(.72+fresnel*.66+broad*.09)+vec3(.72,.81,1.)*edge*uRibbon*.18;
    gl_FragColor=vec4(color,strength*uOpacity);
  }`;
const filamentVertex = `
  attribute float aPhase;
  uniform float uTime;
  varying float vPhase;
  void main(){ vPhase=aPhase; gl_Position=projectionMatrix*modelViewMatrix*vec4(position,1.); }
`;
const filamentFragment = `
  uniform vec3 uColor;
  uniform float uTime;
  uniform float uOpacity;
  uniform float uPhase;
  varying float vPhase;
  void main(){
    float comet=pow(.5+.5*cos(vPhase*6.28318530718-uTime*.66+uPhase),24.);
    float shimmer=.75+.25*sin(vPhase*44.-uTime*.45+uPhase);
    gl_FragColor=vec4(uColor*(.8+comet*.85),uOpacity*(.26*shimmer+comet*.74));
  }`;

function surface(color, ribbon, opacity, phase = 0) {
  return new THREE.ShaderMaterial({ vertexShader: surfaceVertex, fragmentShader: surfaceFragment,
    transparent: true, depthWrite: false, side: THREE.DoubleSide, blending: THREE.AdditiveBlending,
    uniforms: { uColor: { value: new THREE.Color(color) }, uTime: { value: 0 }, uOpacity: { value: opacity }, uRibbon: { value: ribbon ? 1 : 0 }, uMotion: { value: ribbon ? 1 : .25 }, uPhase: { value: phase } },
  });
}

export function createResonanceEffects({ nodes }) {
  if (!Array.isArray(nodes) || nodes.length !== 5 || nodes.some(n => !n.visual?.isObject3D)) throw new Error('Five visual nodes are required.');
  const animated = [], materials = [], secondary = [], bodies = [];
  const register = (material, base) => { material.userData.baseOpacity = base; materials.push(material); return material; };
  const field = (parent, geometry, color, opacity = .65) => {
    const material = register(surface(color, false, opacity), opacity);
    const mesh = new THREE.Mesh(geometry, material); parent.add(mesh); return mesh;
  };
  const filament = (parent, curve, color, opacity = .7, count = 200, closed = true, phase = 0) => {
    const positions = [], phases = [];
    for (let i = 0; i <= count; i++) { const p = curve(i / count); positions.push(...(p.isVector3 ? p.toArray() : p)); phases.push(i / count); }
    const g = new THREE.BufferGeometry(); g.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3)); g.setAttribute('aPhase', new THREE.Float32BufferAttribute(phases, 1));
    const m = register(new THREE.ShaderMaterial({ vertexShader: filamentVertex, fragmentShader: filamentFragment,
      transparent: true, depthWrite: false, blending: THREE.AdditiveBlending,
      uniforms: { uColor: { value: new THREE.Color(color) }, uTime: { value: 0 }, uOpacity: { value: opacity }, uPhase: { value: phase } },
    }), opacity);
    const line = new THREE.Line(g, m); parent.add(line); return line;
  };
  const ribbon = (parent, curve, color, width = .06, phase = 0, closed = true) => {
    const m = register(surface(color, true, .9, phase), .9);
    const mesh = new THREE.Mesh(createRibbonGeometry(curve, width, 180, closed), m); parent.add(mesh);
    filament(parent, curve, color, .66, 200, closed, phase); return mesh;
  };
  const circle = (r, tilt = 0, phase = 0) => t => {
    const a = TAU * t + phase;
    return new THREE.Vector3(r * Math.cos(a), r * Math.sin(a) * Math.cos(tilt), r * Math.sin(a) * Math.sin(tilt));
  };
  const spin = (group, x, y, z, phase = 0) => animated.push({ group, x, y, z, phase, base: group.rotation.clone() });
  for (let i = 0; i < 5; i++) {
    const body = new THREE.Group(), detail = new THREE.Group();
    body.name = `resonance-field-${i}`; detail.name = `resonance-detail-${i}`;
    nodes[i].visual.add(body); body.add(detail); bodies.push(body); secondary.push(detail);
  }

  // Blue: intersecting phase shells retain an airy armillary silhouette.
  field(bodies[0], new THREE.SphereGeometry(.71, 36, 24), PALETTE[0], .8);
  for (let j = 0; j < 3; j++) {
    const arm = new THREE.Group(); bodies[0].add(arm); arm.rotation.z = j * Math.PI / 3;
    ribbon(arm, circle(.91 + j * .035, .35 + j * .48), PALETTE[0], .056, j * 2);
    spin(arm, .04 * (j - 1), .055, .018, j);
  }
  for (let j = 0; j < 5; j++) filament(secondary[0], circle(.74, j * Math.PI / 5), 0x9cbcff, .2, 160, true, j);

  // Coral: a faint faceted cage leaves every verified root unobscured.
  const facet = field(bodies[1], new THREE.IcosahedronGeometry(.99, 1), PALETTE[1], .45);
  const cageGeometry = new THREE.EdgesGeometry(facet.geometry, 1);
  const cageMaterial = new THREE.LineBasicMaterial({ color: 0xff9986, transparent: true, opacity: .18, blending: THREE.AdditiveBlending, depthWrite: false });
  const cage = new THREE.LineSegments(cageGeometry, cageMaterial); bodies[1].add(cage);
  materials.push(cageMaterial); cageMaterial.userData.baseOpacity = .18;
  spin(facet, .025, .045, -.02); spin(cage, .025, .045, -.02);
  for (let j = 0; j < 3; j++) {
    const orbit = new THREE.Group(); secondary[1].add(orbit); orbit.rotation.z = j * Math.PI / 3;
    filament(orbit, circle(.89, .65 + j * .4), PALETTE[1], .26, 180, true, j * 2.1);
  }

  // Violet: two broad open strands orbit a fine inner double helix.
  const helix = (phase, radius = .42) => t => {
    const a = t * TAU * 1.65 + phase;
    return new THREE.Vector3(radius * Math.cos(a), (t - .5) * 1.72, radius * Math.sin(a));
  };
  for (let j = 0; j < 2; j++) ribbon(bodies[2], helix(j * Math.PI), PALETTE[2], .075, j * 2, false);
  for (let j = 0; j < 5; j++) {
    const y = -.64 + j * .32, r = .42;
    filament(secondary[2], t => { const a = TAU * t; return new THREE.Vector3(r * Math.cos(a), y + .055 * Math.sin(a * 2), r * Math.sin(a)); }, 0xd1a6ff, .22, 100, true, j);
  }
  const violetVeil = field(secondary[2], new THREE.SphereGeometry(.6, 32, 20), PALETTE[2], .35); violetVeil.scale.set(.95, 1.48, .8);
  spin(bodies[2], .025, .095, -.015);

  // Gold: nested oscillating ribbons suggest arcsine moments and convergence;
  // the source-backed numeric convergence curve remains a separate object.
  for (let j = 0; j < 4; j++) {
    const level = j < 2 ? bodies[3] : secondary[3], scale = .98 - j * .16;
    const curve = t => {
      const a = TAU * t, r = scale * (.79 + .11 * Math.cos(a * 4));
      return new THREE.Vector3(r * Math.cos(a), r * Math.sin(a), .19 * Math.sin(a * 3 + j * .55));
    };
    const petal = new THREE.Group(); level.add(petal); petal.rotation.set(j * .21, j * .3, j * .24);
    ribbon(petal, curve, PALETTE[3], .065 - j * .009, j * 1.8); spin(petal, .016, -.028, .027 * (j % 2 ? -1 : 1), j);
  }
  field(secondary[3], new THREE.SphereGeometry(.53, 32, 20), PALETTE[3], .45).scale.z = .65;

  // Lavender: interlocked knots surround the shared refinement node.
  const knot = (phase = 0) => t => {
    const a = TAU * t, r = .58 + .17 * Math.cos(a * 3 + phase);
    return new THREE.Vector3(r * Math.cos(a * 2), r * Math.sin(a * 2), .24 * Math.sin(a * 3 + phase));
  };
  const knotBody = new THREE.Group(); bodies[4].add(knotBody);
  ribbon(knotBody, knot(), PALETTE[4], .065, .8);
  const counterpart = new THREE.Group(); secondary[4].add(counterpart); counterpart.rotation.set(1.1, .3, .8);
  ribbon(counterpart, knot(Math.PI), 0xc9c5ff, .037, 3.2);
  field(bodies[4], new THREE.SphereGeometry(.55, 32, 22), PALETTE[4], .65);
  filament(secondary[4], circle(.93, 1.1), 0xe1daff, .32, 200, true, 2);
  spin(knotBody, .035, .075, .025); spin(counterpart, -.04, .026, -.035);

  return {
    update(time, modeWeights, quality = 'high', focus = null) {
      const eco = quality === 'eco' || quality === 'low' || quality === 0;
      for (const detail of secondary) detail.visible = !eco;
      for (const m of materials) if (m.uniforms?.uTime) m.uniforms.uTime.value = time;
      for (const a of animated) {
        a.group.rotation.x = a.base.x + a.x * time + .15 * Math.sin(time * .12 + a.phase);
        a.group.rotation.y = a.base.y + a.y * time + .12 * Math.cos(time * .1 + a.phase);
        a.group.rotation.z = a.base.z + a.z * time + a.phase * .24;
      }
      // Focus is handled by the scene's common node fader; effects must not
      // overwrite its uniform opacity or invent a second selection policy.
    },
  };
}
