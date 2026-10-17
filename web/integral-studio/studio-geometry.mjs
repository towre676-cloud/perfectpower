/** Pure geometry transforms. Every displayed point is derived from the integral. */
export const PRIMITIVE_30 = Object.freeze([1, 7, 11, 13, 17, 19, 23, 29]);
export const GOLDEN_ROOT_ANGLES = Object.freeze([1, 7, 11, 13].map(n => n * Math.PI / 15));

export function coefficientVector(value) {
  if (Array.isArray(value) || ArrayBuffer.isView(value)) return Array.from(value).slice(0, 4).map(n => Number(n) || 0);
  return ['a', 'b', 'c', 'd'].map(key => Number(value?.[key]) || 0);
}

export function goldenCharacter(n) {
  const r = ((n % 5) + 5) % 5;
  return r === 0 ? 0 : r === 1 || r === 4 ? 1 : -1;
}

/** Roots are never connected by a line crossing an infinite logarithmic spike. */
export function splitDensity(samples, roots = GOLDEN_ROOT_ANGLES) {
  const result = Array.from({length: roots.length + 1}, () => []);
  for (const sample of samples) {
    const theta = Number(sample.theta), density = Number(sample.density);
    if (!Number.isFinite(theta) || !Number.isFinite(density)) continue;
    let interval = 0;
    while (interval < roots.length && theta > roots[interval]) interval++;
    result[interval].push({...sample, theta, density: Math.max(0, density)});
  }
  return result.filter(part => part.length > 1);
}

export function densityDisplay(samples, roots = GOLDEN_ROOT_ANGLES, height = 4.5, width = 10) {
  const maxDensity = Math.max(1e-10, ...samples.map(p => Number.isFinite(p.density) ? p.density : 0));
  return {
    maxDensity,
    parts: splitDensity(samples, roots).map(part => part.map(p => ({
      ...p, position: [width * (p.theta / Math.PI - .5), height * p.density / maxDensity, 0]
    })))
  };
}

function solve3(a, b) {
  const m = a.map((row, i) => [...row, b[i]]);
  for (let col = 0; col < 3; col++) {
    let pivot = col;
    for (let row = col + 1; row < 3; row++) if (Math.abs(m[row][col]) > Math.abs(m[pivot][col])) pivot = row;
    [m[col], m[pivot]] = [m[pivot], m[col]];
    if (Math.abs(m[col][col]) < 1e-14) throw new Error('The energy slice is singular.');
    const divisor = m[col][col];
    for (let j = col; j < 4; j++) m[col][j] /= divisor;
    for (let row = 0; row < 3; row++) if (row !== col) {
      const factor = m[row][col];
      for (let j = col; j < 4; j++) m[row][j] -= factor * m[col][j];
    }
  }
  return m.map(row => row[3]);
}

/** Jacobi diagonalization for a real symmetric positive definite 3 × 3 matrix. */
export function eigenSymmetric3(matrix) {
  const a = matrix.map(row => [...row]);
  const vectors = [[1, 0, 0], [0, 1, 0], [0, 0, 1]];
  for (let iteration = 0; iteration < 40; iteration++) {
    let p = 0, q = 1;
    for (const [i, j] of [[0, 2], [1, 2]]) if (Math.abs(a[i][j]) > Math.abs(a[p][q])) {p = i; q = j;}
    if (Math.abs(a[p][q]) < 1e-14) break;
    const angle = .5 * Math.atan2(2 * a[p][q], a[q][q] - a[p][p]);
    const c = Math.cos(angle), s = Math.sin(angle);
    const app = a[p][p], aqq = a[q][q], apq = a[p][q];
    a[p][p] = c*c*app - 2*c*s*apq + s*s*aqq;
    a[q][q] = s*s*app + 2*c*s*apq + c*c*aqq;
    a[p][q] = a[q][p] = 0;
    for (let k = 0; k < 3; k++) if (k !== p && k !== q) {
      const akp = a[k][p], akq = a[k][q];
      a[k][p] = a[p][k] = c*akp - s*akq;
      a[k][q] = a[q][k] = s*akp + c*akq;
    }
    for (let k = 0; k < 3; k++) {
      const vkp = vectors[k][p], vkq = vectors[k][q];
      vectors[k][p] = c*vkp - s*vkq;
      vectors[k][q] = s*vkp + c*vkq;
    }
  }
  const order = [0, 1, 2].sort((i, j) => a[i][i] - a[j][j]);
  return {values: order.map(i => a[i][i]), vectors: order.map(i => vectors.map(row => row[i]))};
}

/**
 * A fixed-d slice of E = tᵀGt. Coordinates are uᵢ = tᵢ√Gᵢᵢ.
 * This norm scaling is explicit: no ill-conditioned fake spherical geometry.
 */
export function energySlice(gram, coefficients) {
  const t = coefficientVector(coefficients);
  while (t.length < 4) t.push(0);
  const norms = gram.map((row, i) => Math.sqrt(row[i]));
  const h = gram.slice(0, 3).map((row, i) => row.slice(0, 3).map((v, j) => v / (norms[i] * norms[j])));
  const cross = gram.slice(0, 3).map((row, i) => row[3] / norms[i]);
  const center = solve3(h, cross.map(v => -v * t[3]));
  const minimum = gram[3][3] * t[3]**2 + center.reduce((sum, v, i) => sum + v * cross[i] * t[3], 0);
  const energy = t.reduce((sum, v, i) => sum + t.reduce((s, w, j) => s + v * gram[i][j] * w, 0), 0);
  const level = Math.max(energy, minimum) + Math.max(1, .08 * Math.abs(energy));
  const eigen = eigenSymmetric3(h);
  if (eigen.values.some(v => v <= 0)) throw new Error('The energy form is not positive definite.');
  const radii = eigen.values.map(v => Math.sqrt(Math.max(0, level - minimum) / v));
  const point = t.slice(0, 3).map((v, i) => v * norms[i]);
  const worldScale = 3.6 / Math.max(...radii, .01);
  return {center, minimum, energy, level, eigen, radii, point, worldScale, norms, h};
}

export function ellipsoidPoint(slice, longitude, latitude, fraction = 1) {
  const unit = [Math.cos(latitude) * Math.cos(longitude), Math.sin(latitude), Math.cos(latitude) * Math.sin(longitude)];
  return [0, 1, 2].map(row => slice.eigen.vectors.reduce((sum, vector, i) => sum + vector[row] * slice.radii[i] * unit[i] * Math.sqrt(fraction), 0) * slice.worldScale);
}

export function normalizedEnergyPoint(slice) {
  return slice.point.map((value, i) => (value - slice.center[i]) * slice.worldScale);
}
