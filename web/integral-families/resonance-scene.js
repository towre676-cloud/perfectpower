import * as THREE from 'three';
import { OrbitControls } from 'three/addons/controls/OrbitControls.js';
import { EffectComposer } from 'three/addons/postprocessing/EffectComposer.js';
import { RenderPass } from 'three/addons/postprocessing/RenderPass.js';
import { UnrealBloomPass } from 'three/addons/postprocessing/UnrealBloomPass.js';
import { OutputPass } from 'three/addons/postprocessing/OutputPass.js';

// The geometry is mathematical where a source exists; the connecting spaces,
// towers and braids are visual metaphors, not claims of a proved equivalence.
export const SCENE_MODES = Object.freeze(['colimit', 'resonance', 'tower', 'nerve']);
export const NODE_ANCHORS = Object.freeze([
  Object.freeze([-4.8, 0, 0]), Object.freeze([4.8, 0, 0]),
  Object.freeze([0, 3.2, 0]), Object.freeze([0, -3.2, 0]),
  Object.freeze([0, 0, 0]),
]);
const COLORS = [0x6496ff, 0xff7864, 0xb478ff, 0xffc896, 0xb4b4ff];
const IDS = ['cyclotomic', 'e8', 'bridge', 'convergence', 'fiber'];
const TAU = Math.PI * 2;
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const smooth = x => x * x * (3 - 2 * x);

function payload(data) {
  const p = typeof data?.payload_json === 'string' ? JSON.parse(data.payload_json) : data;
  if (!p || !Array.isArray(p.roots) || p.roots.length !== 240) throw new Error('The scene requires the verified 240-root E8 data.');
  for (const r of p.roots) if (![r.x, r.y, r.z].every(Number.isFinite)) throw new Error('Invalid root projection.');
  return p;
}

function pointsGeometry(positions, colors, sizes) {
  const g = new THREE.BufferGeometry();
  g.setAttribute('position', new THREE.Float32BufferAttribute(positions, 3));
  g.setAttribute('color', new THREE.Float32BufferAttribute(colors, 3));
  g.setAttribute('aSize', new THREE.Float32BufferAttribute(sizes, 1));
  return g;
}

export function createRootGeometry(data) {
  const p = payload(data), positions = [], colors = [], sizes = [], color = new THREE.Color(COLORS[1]);
  for (const r of p.roots) {
    positions.push(r.x * .93, r.y * .93, r.z * .62);
    const light = .72 + .28 * r.orbit / 7;
    colors.push(color.r * light, color.g * light, color.b * light);
    sizes.push(1.7 + .65 * (r.step % 5) / 4);
  }
  return pointsGeometry(positions, colors, sizes);
}

export function createFlowCurve(start, end, bend = 0) {
  const a = start?.isVector3 ? start.clone() : new THREE.Vector3(...start);
  const b = end?.isVector3 ? end.clone() : new THREE.Vector3(...end);
  if (![...a.toArray(), ...b.toArray(), bend].every(Number.isFinite)) throw new Error('Finite curve coordinates are required.');
  const delta = b.clone().sub(a), normal = new THREE.Vector3(-delta.y, delta.x, .3 * delta.length()).normalize();
  const c = a.clone().addScaledVector(delta, .32).addScaledVector(normal, bend);
  const d = a.clone().addScaledVector(delta, .68).addScaledVector(normal, bend);
  return new THREE.CubicBezierCurve3(a, c, d, b);
}

const pointVertex = `
  attribute float aSize;
  varying vec3 vColor;
  varying float vFlicker;
  uniform float uTime;
  uniform float uScale;
  uniform float uPixelRatio;
  uniform float uTwinkle;
  void main(){
    vColor=color;
    vFlicker=mix(1.,.65+.35*sin(uTime*.55+position.x*13.7+position.y*6.3),uTwinkle);
    vec4 mv=modelViewMatrix*vec4(position,1.);
    gl_PointSize=clamp(aSize*uScale*uPixelRatio*(60./max(1.,-mv.z)),1.,52.);
    gl_Position=projectionMatrix*mv;
  }`;
const pointFragment = `
  varying vec3 vColor;
  varying float vFlicker;
  uniform float uOpacity;
  void main(){
    float d=length(gl_PointCoord-.5)*2.;
    if(d>1.) discard;
    float halo=exp(-d*d*6.5)*.6;
    float core=exp(-d*d*38.)*.85;
    gl_FragColor=vec4(vColor,(halo+core)*uOpacity*vFlicker);
  }`;

function pointMaterial(colorScale = 1, twinkle = 0) {
  return new THREE.ShaderMaterial({
    vertexShader: pointVertex, fragmentShader: pointFragment, vertexColors: true,
    transparent: true, depthWrite: false, blending: THREE.AdditiveBlending,
    uniforms: { uTime: { value: 0 }, uScale: { value: colorScale }, uPixelRatio: { value: 1 }, uTwinkle: { value: twinkle }, uOpacity: { value: 1 } },
  });
}

function seeded(index, salt = 0) {
  const x = Math.sin((index + 1) * 127.1 + salt * 311.7) * 43758.5453123;
  return x - Math.floor(x);
}

function cloudGeometry(count, colorValue, kind) {
  const positions = [], colors = [], sizes = [], color = new THREE.Color(colorValue);
  for (let i = 0; i < count; i++) {
    const t = i / count, golden = i * 2.399963229728653;
    let x, y, z;
    if (kind === 'fiber') {
      const a = t * TAU, r = .7 + .14 * Math.cos(a * 11);
      x = r * Math.cos(a); y = r * Math.sin(a); z = .38 * Math.sin(a * 5);
    } else if (kind === 'spiral') {
      const a = t * TAU * 5, r = .23 + .53 * t;
      x = r * Math.cos(a); y = r * Math.sin(a); z = (t - .5) * 1.1;
    } else if (kind === 'converge') {
      const r = .86 * Math.sqrt(t), a = t * TAU * 9;
      x = r * Math.cos(a); y = r * Math.sin(a); z = .4 * Math.sin(a * .6);
    } else {
      const yy = 1 - 2 * (i + .5) / count, radius = Math.sqrt(1 - yy * yy) * .78;
      x = Math.cos(golden) * radius; y = yy * .78; z = Math.sin(golden) * radius;
    }
    positions.push(x, y, z);
    const intensity = .6 + .4 * seeded(i, 2);
    colors.push(color.r * intensity, color.g * intensity, color.b * intensity);
    sizes.push(1.4 + 1.7 * seeded(i, 3));
  }
  return pointsGeometry(positions, colors, sizes);
}

function line(points, color, opacity = .25) {
  const g = new THREE.BufferGeometry().setFromPoints(points);
  const m = new THREE.LineBasicMaterial({ color, transparent: true, opacity, blending: THREE.AdditiveBlending, depthWrite: false });
  m.userData.baseOpacity = opacity;
  return new THREE.Line(g, m);
}

function ring(radius, color, opacity = .3, samples = 160) {
  const pts = [];
  for (let i = 0; i <= samples; i++) { const a = TAU * i / samples; pts.push(new THREE.Vector3(radius * Math.cos(a), radius * Math.sin(a), 0)); }
  return line(pts, color, opacity);
}

function fadeGroup(group, opacity) {
  group.visible = opacity > .003;
  if (!group.visible) return;
  group.traverse(object => {
    if (!object.material) return;
    const materials = Array.isArray(object.material) ? object.material : [object.material];
    for (const m of materials) {
      if (m.uniforms?.uOpacity) m.uniforms.uOpacity.value = opacity * (m.userData.baseOpacity ?? 1);
      else m.opacity = opacity * (m.userData.baseOpacity ?? 1);
    }
  });
}

function makeGlowTexture() {
  const canvas = document.createElement('canvas'); canvas.width = canvas.height = 128;
  const ctx = canvas.getContext('2d');
  if (!ctx) throw new Error('A drawing context is unavailable.');
  const g = ctx.createRadialGradient(64, 64, 0, 64, 64, 64);
  g.addColorStop(0, 'rgba(255,255,255,1)'); g.addColorStop(.1, 'rgba(255,255,255,.65)'); g.addColorStop(.3, 'rgba(255,255,255,.14)'); g.addColorStop(1, 'rgba(255,255,255,0)');
  ctx.fillStyle = g; ctx.fillRect(0, 0, 128, 128);
  return new THREE.CanvasTexture(canvas);
}

export function createResonanceScene(host, { data, onFrame, onSelect, onError } = {}) {
  if (!host || typeof host.appendChild !== 'function') throw new Error('A scene host is required.');
  const source = payload(data);
  const scene = new THREE.Scene();
  scene.fog = new THREE.FogExp2(0x030311, .018);
  const camera = new THREE.PerspectiveCamera(43, 1, .1, 120);
  camera.position.set(0, .1, 16.9);
  let renderer;
  try {
    renderer = new THREE.WebGLRenderer({ antialias: false, alpha: true, powerPreference: 'high-performance', preserveDrawingBuffer: true });
  } catch (error) {
    onError?.(error); throw error;
  }
  renderer.setClearColor(0x010110, 0);
  renderer.outputColorSpace = THREE.SRGBColorSpace;
  renderer.toneMapping = THREE.ACESFilmicToneMapping;
  renderer.toneMappingExposure = 1.12;
  renderer.domElement.setAttribute('aria-label', 'Animated mathematical resonance: cyclotomic phases, E8 roots, integral convergence and categorical motifs');
  renderer.domElement.setAttribute('role', 'img');
  renderer.domElement.className = 'resonance-canvas';
  renderer.domElement.style.cssText = 'display:block;width:100%;height:100%;touch-action:none;';
  host.appendChild(renderer.domElement);

  const controls = new OrbitControls(camera, renderer.domElement);
  controls.enableDamping = true; controls.dampingFactor = .045; controls.enablePan = false;
  controls.minDistance = 9; controls.maxDistance = 29; controls.rotateSpeed = .5;
  controls.minPolarAngle = Math.PI * .18; controls.maxPolarAngle = Math.PI * .82;
  const composer = new EffectComposer(renderer);
  composer.addPass(new RenderPass(scene, camera));
  const bloom = new UnrealBloomPass(new THREE.Vector2(1, 1), .7, .65, .14);
  composer.addPass(bloom);
  const outputPass = new OutputPass(); composer.addPass(outputPass);

  const glowTexture = makeGlowTexture();
  const root = new THREE.Group(); scene.add(root);
  const pointMaterials = [], flows = [], allModeGroups = [], nodes = [], pickTargets = [];
  const state = { disposed: false, playing: true, auto: true, speed: 1, density: 1, bloom: .7, elapsed: 0, mode: 0, modeStart: 0, last: 0, frame: 0, fps: 60, width: 1, height: 1, pixelRatio: 1, contextLost: false, failed: false, visible: !document.hidden, dragging: false, interactedAt: -100, previousMode: 0, transitionStart: -10 };
  const clockVector = new THREE.Vector3(), raycaster = new THREE.Raycaster(), pointer = new THREE.Vector2();
  const nodeProjection = IDS.map(id => ({ id, x: 0, y: 0, visible: true }));
  const modeAnchors = [
    NODE_ANCHORS,
    [[-4.9, -.3, 0], [4.9, -.3, 0], [0, 3.4, -.6], [0, -3.4, -.6], [0, 0, 0]],
    [[0, -3.5, 0], [0, -1.75, 0], [0, 0, 0], [0, 1.75, 0], [0, 3.5, 0]],
    [[-3.9, .1, 0], [3.9, .1, 0], [0, 3, -.7], [0, -3, -.7], [0, 0, 1.1]],
  ];
  const anchorVectors = modeAnchors.map(anchors => anchors.map(a => new THREE.Vector3(...a)));

  // A deterministic star volume and a quiet depth grid retain the original's
  // midnight-blue atmosphere while making camera parallax immediately legible.
  const starsP = [], starsC = [], starsS = [];
  for (let i = 0; i < 1350; i++) {
    starsP.push((seeded(i, 7) - .5) * 52, (seeded(i, 8) - .5) * 34, -8 - seeded(i, 9) * 30);
    const c = new THREE.Color().setHSL(.61 + .12 * seeded(i, 10), .35, .28 + .35 * seeded(i, 11));
    starsC.push(c.r, c.g, c.b); starsS.push(.35 + seeded(i, 12) * 1.4);
  }
  const starsMaterial = pointMaterial(1, 1); starsMaterial.userData.baseOpacity = .72; pointMaterials.push(starsMaterial);
  const stars = new THREE.Points(pointsGeometry(starsP, starsC, starsS), starsMaterial); scene.add(stars);
  const grid = new THREE.GridHelper(50, 40, 0x2b3b70, 0x141e42);
  grid.position.set(0, -4.65, -7); grid.material.transparent = true; grid.material.opacity = .17; grid.material.depthWrite = false; scene.add(grid);

  const makePointObject = (geometry, scale = 1, twinkle = 0) => {
    const m = pointMaterial(scale, twinkle); pointMaterials.push(m);
    return new THREE.Points(geometry, m);
  };
  const nodeCounts = [384, 240, 96, 130, 264];
  const kinds = ['sphere', 'root', 'spiral', 'converge', 'fiber'];
  for (let i = 0; i < 5; i++) {
    const group = new THREE.Group(); group.position.copy(anchorVectors[0][i]); root.add(group);
    const visual = new THREE.Group(); group.add(visual);
    const cloud = makePointObject(i === 1 ? createRootGeometry(source) : cloudGeometry(nodeCounts[i], COLORS[i], kinds[i]), i === 4 ? 1.5 : 1.1);
    visual.add(cloud);
    const haloMaterial = new THREE.SpriteMaterial({ map: glowTexture, color: COLORS[i], transparent: true, opacity: .28, blending: THREE.AdditiveBlending, depthWrite: false });
    haloMaterial.userData.baseOpacity = .28;
    const halo = new THREE.Sprite(haloMaterial); halo.scale.setScalar(i === 4 ? 2.5 : 2.25); visual.add(halo);
    const corona = ring(i === 4 ? 1.02 : 1.08, COLORS[i], .3); corona.rotation.x = .35; visual.add(corona);
    const corona2 = ring(i === 4 ? 1.12 : 1.16, COLORS[i], .11); corona2.rotation.set(1.1, .25, .3); visual.add(corona2);
    const hit = new THREE.Mesh(new THREE.SphereGeometry(.95, 10, 6), new THREE.MeshBasicMaterial({ visible: false }));
    hit.userData.nodeIndex = i; group.add(hit); pickTargets.push(hit);
    nodes.push({ group, visual, cloud, halo, corona, corona2 });
  }

  function makeFlow(group, start, end, colorA, colorB, bend, count = 34, thickness = .011, speed = 1) {
    const curve = createFlowCurve(start, end, bend), samples = 96;
    const geometry = new THREE.TubeGeometry(curve, samples, thickness, 4, false);
    const colorArray = new Float32Array(geometry.attributes.position.count * 3);
    const a = new THREE.Color(colorA), b = new THREE.Color(colorB), c = new THREE.Color();
    for (let i = 0; i < geometry.attributes.position.count; i++) {
      c.copy(a).lerp(b, Math.floor(i / 5) / samples); c.toArray(colorArray, i * 3);
    }
    geometry.setAttribute('color', new THREE.BufferAttribute(colorArray, 3));
    const material = new THREE.MeshBasicMaterial({ vertexColors: true, transparent: true, opacity: .18, blending: THREE.AdditiveBlending, depthWrite: false });
    material.userData.baseOpacity = .18;
    const mesh = new THREE.Mesh(geometry, material); group.add(mesh);
    const positions = new Float32Array(count * 3), colors = [], sizes = [];
    for (let i = 0; i < count; i++) { c.copy(a).lerp(b, i / count); colors.push(c.r, c.g, c.b); sizes.push(i % 7 === 0 ? 3.7 : 1.8); }
    const beads = makePointObject(pointsGeometry(positions, colors, sizes), 1.25);
    group.add(beads);
    // Precomputed samples keep the animation independent of allocation and
    // curve reconstruction. All particles circulate in elapsed seconds.
    const lookup = curve.getPoints(512), lut = new Float32Array(lookup.length * 3);
    lookup.forEach((v, i) => v.toArray(lut, i * 3));
    flows.push({ group, beads, positions: beads.geometry.attributes.position, lut, count, speed, offset: seeded(flows.length, 20) });
    return mesh;
  }

  // 01 — The reference's diamond: blue ↔ coral, violet above, gold below,
  // lavender in the centre. Offset paths are distinct, moving strands.
  const colimit = new THREE.Group(); root.add(colimit); allModeGroups.push(colimit);
  const edges = [[0, 2], [2, 1], [0, 3], [3, 1], [0, 4], [4, 1], [2, 4], [4, 3]];
  for (let k = 0; k < edges.length; k++) {
    const [a, b] = edges[k];
    makeFlow(colimit, NODE_ANCHORS[a], NODE_ANCHORS[b], COLORS[a], COLORS[b], (k % 2 ? 1 : -1) * .38, 29, .009, .035 + k * .003);
  }
  makeFlow(colimit, [-4.8, 0, -.5], [4.8, 0, -.5], COLORS[0], COLORS[1], 2.55, 76, .006, .024);
  makeFlow(colimit, [4.8, 0, -.7], [-4.8, 0, -.7], COLORS[1], COLORS[0], 2.55, 76, .006, .019);
  const equator = ring(5.2, 0x7d80bf, .06, 200); equator.scale.y = .67; equator.rotation.x = .24; colimit.add(equator);

  // 02 — A continuous braided resonance surface, not a count-based root /
  // field identification. Every strand is a real spatial curve.
  const resonance = new THREE.Group(); root.add(resonance); allModeGroups.push(resonance);
  const torusGroup = new THREE.Group(); resonance.add(torusGroup);
  for (let strand = 0; strand < 11; strand++) {
    const path = [], color = new THREE.Color().setHSL(.61 + .035 * strand, .75, .62);
    for (let j = 0; j <= 360; j++) {
      const t = TAU * j / 360, q = t * 3 + strand * TAU / 11, r = 2.05 + .48 * Math.cos(q);
      path.push(new THREE.Vector3(r * Math.cos(t * 2), r * Math.sin(t * 2) * .72, .85 * Math.sin(q)));
    }
    torusGroup.add(line(path, color, strand % 3 ? .22 : .5));
  }
  const torusPositions = [], torusColors = [], torusSizes = [];
  for (let j = 0; j < 720; j++) {
    const t = TAU * j / 720, q = t * 11, r = 2.05 + .48 * Math.cos(q);
    torusPositions.push(r * Math.cos(t * 3), r * Math.sin(t * 3) * .72, .85 * Math.sin(q));
    const c = new THREE.Color().setHSL(.59 + .17 * j / 720, .75, .68);
    torusColors.push(c.r, c.g, c.b); torusSizes.push(j % 11 ? 1.5 : 3);
  }
  torusGroup.add(makePointObject(pointsGeometry(torusPositions, torusColors, torusSizes), 1.1));
  for (let i = 0; i < 4; i++) makeFlow(resonance, modeAnchors[1][i], [0, 0, 0], COLORS[i], COLORS[4], (i % 2 ? -1 : 1) * .65, 42, .009, .04 + i * .006);

  // 03 — A five-level tower. Elliptical planes and rising helical strands
  // replace flat stacked cards with a spatial, inspectable construction.
  const tower = new THREE.Group(); root.add(tower); allModeGroups.push(tower);
  const towerPlanes = [];
  for (let level = 0; level < 5; level++) {
    const y = -3.5 + level * 1.75, plane = new THREE.Group(); plane.position.y = y;
    const outline = ring(2.12, COLORS[level], .24); outline.rotation.x = Math.PI / 2; plane.add(outline);
    const inner = ring(1.76, COLORS[level], .1); inner.rotation.x = Math.PI / 2; plane.add(inner);
    for (let k = 0; k < 4; k++) {
      const a = TAU * k / 4, b = a + Math.PI;
      plane.add(line([new THREE.Vector3(2.12 * Math.cos(a), 0, 2.12 * Math.sin(a)), new THREE.Vector3(2.12 * Math.cos(b), 0, 2.12 * Math.sin(b))], COLORS[level], .08));
    }
    tower.add(plane); towerPlanes.push(plane);
    if (level < 4) for (let side = 0; side < 3; side++) {
      const a = side * TAU / 3 + level * .3;
      makeFlow(tower, [1.75 * Math.cos(a), y, 1.75 * Math.sin(a)], [1.75 * Math.cos(a + .45), y + 1.75, 1.75 * Math.sin(a + .45)], COLORS[level], COLORS[level + 1], .2, 18, .008, .07);
    }
  }

  // 04 — A simplicial nerve, explicitly schematic: translucent faces,
  // filigree edges, and particles travel around several overlapping covers.
  const nerve = new THREE.Group(); root.add(nerve); allModeGroups.push(nerve);
  const nervePositions = [new THREE.Vector3(-3.9, .1, 0), new THREE.Vector3(3.9, .1, 0), new THREE.Vector3(0, 3, -.7), new THREE.Vector3(0, -3, -.7), new THREE.Vector3(0, 0, 1.1)];
  for (let a = 0; a < 5; a++) for (let b = a + 1; b < 5; b++) {
    makeFlow(nerve, nervePositions[a], nervePositions[b], COLORS[a], COLORS[b], .16 * (a - b), 25, .008, .035);
    for (let c = b + 1; c < 5; c++) {
      const geometry = new THREE.BufferGeometry().setFromPoints([nervePositions[a], nervePositions[b], nervePositions[c]]);
      geometry.computeVertexNormals();
      const material = new THREE.MeshBasicMaterial({ color: COLORS[(a + b + c) % 5], transparent: true, opacity: .024, side: THREE.DoubleSide, blending: THREE.AdditiveBlending, depthWrite: false });
      material.userData.baseOpacity = .024;
      nerve.add(new THREE.Mesh(geometry, material));
    }
  }
  const coverRings = [];
  for (let i = 0; i < 5; i++) {
    const r = ring(1.7, COLORS[i], .12); r.position.copy(nervePositions[i]).multiplyScalar(.66); r.rotation.set(i * .32, i * .25, 0); nerve.add(r); coverRings.push(r);
  }
  allModeGroups.forEach((group, index) => fadeGroup(group, index === 0 ? 1 : 0));

  function resize() {
    if (state.disposed) return;
    const width = Math.max(1, host.clientWidth), height = Math.max(1, host.clientHeight);
    state.width = width; state.height = height;
    const mobile = width < 650;
    state.pixelRatio = Math.min(window.devicePixelRatio || 1, mobile ? 1.3 : 1.6);
    renderer.setPixelRatio(state.pixelRatio); renderer.setSize(width, height, false);
    composer.setPixelRatio(state.pixelRatio); composer.setSize(width, height);
    camera.aspect = width / height;
    // Preserve the entire diamond in narrow viewports rather than clipping
    // both of the reference's blue/coral lobes.
    camera.fov = 43;
    const minDistance = Math.max(16.9, 7.1 / (Math.tan(THREE.MathUtils.degToRad(43 / 2)) * camera.aspect));
    if (!state.dragging) camera.position.setLength(minDistance);
    controls.maxDistance = Math.max(29, minDistance * 1.4);
    camera.updateProjectionMatrix();
    for (const material of pointMaterials) material.uniforms.uPixelRatio.value = state.pixelRatio;
  }
  const observer = new ResizeObserver(resize); observer.observe(host); resize();
  function modeTo(index) {
    const next = ((Math.trunc(index) % 4) + 4) % 4;
    if (next === state.mode) { state.modeStart = state.elapsed; return; }
    state.previousMode = state.mode; state.mode = next; state.modeStart = state.elapsed; state.transitionStart = state.playing ? state.elapsed : state.elapsed - 2.2;
  }
  const onStart = () => { state.dragging = true; state.interactedAt = state.elapsed; };
  const onEnd = () => { state.dragging = false; state.interactedAt = state.elapsed; };
  controls.addEventListener('start', onStart); controls.addEventListener('end', onEnd);
  let pointerStartX = 0, pointerStartY = 0;
  const pointerDown = e => { pointerStartX = e.clientX; pointerStartY = e.clientY; };
  const pointerUp = e => {
    if (Math.hypot(e.clientX - pointerStartX, e.clientY - pointerStartY) > 7) return;
    const rect = renderer.domElement.getBoundingClientRect();
    pointer.set((e.clientX - rect.left) / rect.width * 2 - 1, -(e.clientY - rect.top) / rect.height * 2 + 1);
    raycaster.setFromCamera(pointer, camera);
    const hits = raycaster.intersectObjects(pickTargets, false);
    if (hits.length) onSelect?.(IDS[hits[0].object.userData.nodeIndex]);
  };
  renderer.domElement.addEventListener('pointerdown', pointerDown);
  renderer.domElement.addEventListener('pointerup', pointerUp);
  const visibility = () => { state.visible = !document.hidden; state.last = 0; };
  document.addEventListener('visibilitychange', visibility);
  const contextLost = e => { e.preventDefault(); state.contextLost = true; onError?.(new Error('The graphics context was interrupted. Reload to restart the visualization.')); };
  renderer.domElement.addEventListener('webglcontextlost', contextLost);

  function updateFlows(time) {
    for (const flow of flows) {
      if (!flow.group.visible) continue;
      const array = flow.positions.array, lut = flow.lut, max = lut.length / 3 - 1;
      for (let i = 0; i < flow.count; i++) {
        const t = ((i / flow.count + time * flow.speed + flow.offset) % 1) * max;
        const at = Math.floor(t), frac = t - at, a = at * 3, b = (at + 1) * 3, out = i * 3;
        array[out] = lut[a] + (lut[b] - lut[a]) * frac;
        array[out + 1] = lut[a + 1] + (lut[b + 1] - lut[a + 1]) * frac;
        array[out + 2] = lut[a + 2] + (lut[b + 2] - lut[a + 2]) * frac;
      }
      flow.positions.needsUpdate = true;
      flow.beads.geometry.setDrawRange(0, Math.max(5, Math.floor(flow.count * state.density)));
    }
  }

  function animate(timestamp) {
    if (state.disposed) return;
    state.frame = requestAnimationFrame(animate);
    if (!state.visible || state.contextLost || state.failed) return;
    const dt = state.last ? Math.min(.07, (timestamp - state.last) / 1000) : 1 / 60;
    state.last = timestamp;
    state.fps += ((1 / Math.max(.001, dt)) - state.fps) * .04;
    if (state.playing) state.elapsed += dt * state.speed;
    const t = state.elapsed;
    if (state.auto && state.playing && t - state.modeStart >= 18) modeTo(state.mode + 1);
    const transition = smooth(clamp((t - state.transitionStart) / 2.2, 0, 1));
    for (let i = 0; i < 4; i++) fadeGroup(allModeGroups[i], i === state.mode ? transition : i === state.previousMode ? 1 - transition : 0);
    const breathe = Math.sin(t * .65);
    for (let i = 0; i < nodes.length; i++) {
      const node = nodes[i], oldAnchor = anchorVectors[state.previousMode][i], newAnchor = anchorVectors[state.mode][i];
      node.group.position.lerpVectors(oldAnchor, newAnchor, transition);
      node.group.position.z += .07 * Math.sin(t * .4 + i);
      node.visual.rotation.y = t * (i === 1 ? -.095 : .055 + i * .009);
      node.visual.rotation.z = .1 * Math.sin(t * .18 + i);
      node.visual.rotation.x = .14 * Math.cos(t * .21 + i);
      const scale = state.mode === 2 ? .67 : i === 4 ? .9 : 1;
      node.visual.scale.setScalar(scale * (1 + .018 * Math.sin(t * .8 + i)));
      node.halo.material.opacity = .22 + .07 * Math.sin(t * .8 + i);
      node.corona.rotation.z = t * .06 * (i % 2 ? -1 : 1);
      node.corona2.rotation.y = t * .045 + i;
    }
    root.rotation.y = .045 * Math.sin(t * .14);
    root.rotation.x = .025 * Math.sin(t * .11);
    torusGroup.rotation.y = t * .075;
    torusGroup.rotation.z = .15 * Math.sin(t * .2);
    for (let i = 0; i < towerPlanes.length; i++) towerPlanes[i].rotation.y = t * .045 * (i % 2 ? -1 : 1);
    for (let i = 0; i < coverRings.length; i++) coverRings[i].rotation.y = t * .05 + i * .25;
    stars.rotation.y = t * .0015;
    grid.material.opacity = .12 + .025 * breathe;
    for (const material of pointMaterials) { material.uniforms.uTime.value = t; material.uniforms.uScale.value = (material.userData.scale ?? 1) * (1 + .04 * breathe); }
    updateFlows(t);
    // A restrained camera drift gives the self-running scene depth; direct
    // manipulation temporarily takes priority and damping remains continuous.
    if (!state.dragging && t - state.interactedAt > 8 && state.playing) {
      controls.autoRotate = true; controls.autoRotateSpeed = .17;
    } else controls.autoRotate = false;
    controls.update(dt);
    try { composer.render(dt); }
    catch (error) { state.failed = true; cancelAnimationFrame(state.frame); onError?.(error); return; }
    root.updateMatrixWorld(true);
    for (let i = 0; i < nodes.length; i++) {
      nodes[i].group.getWorldPosition(clockVector); clockVector.y -= state.mode === 2 ? .72 : 1.18; clockVector.project(camera);
      const p = nodeProjection[i]; p.x = (clockVector.x * .5 + .5) * state.width; p.y = (-clockVector.y * .5 + .5) * state.height; p.visible = clockVector.z > -1 && clockVector.z < 1;
    }
    onFrame?.({ elapsed: t, phase: t % TAU, mode: state.mode, progress: clamp((t - state.modeStart) / 18, 0, 1), fps: state.fps, nodes: nodeProjection });
  }
  for (const material of pointMaterials) material.userData.scale = material.uniforms.uScale.value;
  state.frame = requestAnimationFrame(animate);

  return {
    setMode(index) { if (Number.isFinite(index)) modeTo(index); },
    setPlaying(value) { state.playing = Boolean(value); state.last = 0; },
    setSpeed(value) { if (Number.isFinite(value)) state.speed = clamp(value, .1, 3); },
    setDensity(value) { if (Number.isFinite(value)) state.density = clamp(value, .15, 1); },
    setBloom(value) { if (Number.isFinite(value)) { state.bloom = clamp(value, 0, 2); bloom.strength = state.bloom; } },
    setAuto(value) { state.auto = Boolean(value); state.modeStart = state.elapsed; },
    resetCamera() { controls.reset(); camera.position.set(0, .1, 16.9); controls.target.set(0, 0, 0); state.interactedAt = state.elapsed; resize(); },
    capture() { if (state.disposed || state.contextLost || state.failed) return null; composer.render(); return renderer.domElement.toDataURL('image/png'); },
    diagnostics() { return { engine: 'three', renderer: 'WebGL', modes: SCENE_MODES, mode: state.mode, playing: state.playing, auto: state.auto, elapsed: state.elapsed, fps: Math.round(state.fps), roots: source.roots.length, nodes: 5, flows: flows.length, geometries: renderer.info.memory.geometries, textures: renderer.info.memory.textures, drawCalls: renderer.info.render.calls, pixelRatio: state.pixelRatio, contextLost: state.contextLost, failed: state.failed, disposed: state.disposed }; },
    dispose() {
      if (state.disposed) return;
      state.disposed = true; cancelAnimationFrame(state.frame); observer.disconnect();
      document.removeEventListener('visibilitychange', visibility);
      renderer.domElement.removeEventListener('pointerdown', pointerDown); renderer.domElement.removeEventListener('pointerup', pointerUp); renderer.domElement.removeEventListener('webglcontextlost', contextLost);
      controls.removeEventListener('start', onStart); controls.removeEventListener('end', onEnd); controls.dispose();
      const geometries = new Set(), materials = new Set(), textures = new Set([glowTexture]);
      scene.traverse(o => { if (o.geometry) geometries.add(o.geometry); if (o.material) for (const m of Array.isArray(o.material) ? o.material : [o.material]) { materials.add(m); for (const value of Object.values(m)) if (value?.isTexture) textures.add(value); } });
      geometries.forEach(g => g.dispose()); materials.forEach(m => m.dispose()); textures.forEach(t => t.dispose());
      bloom.dispose(); outputPass.dispose(); composer.dispose(); renderer.dispose(); renderer.domElement.remove();
    },
  };
}
