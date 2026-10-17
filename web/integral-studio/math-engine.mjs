/**
 * Exact formula metadata and independent floating-point numerics for the
 * cyclotomic integral studio. No display clipping takes place in this module.
 * New analytic identities are documented in INTEGRAL_STUDIO_MATHEMATICS.md;
 * these numerical checks are not a replacement for their proofs.
 */
export const PHI = (1 + Math.sqrt(5)) / 2;
export const EXPONENTS = Object.freeze([1, 7, 11, 13, 17, 19, 23, 29]);
export const ROOT_INDICES = Object.freeze([1, 7, 11, 13]);
export const ROOT_ANGLES = Object.freeze(ROOT_INDICES.map(k => Math.PI * k / 15));
export const BASIS_NAMES = Object.freeze(['A', 'K', 'P', 'R']);
export const BASIS_DEFINITIONS = Object.freeze([
  { name: 'A', tex: 'A=\\log|Q_+Q_-|', description: 'Cyclotomic product logarithm' },
  { name: 'K', tex: 'K=\\log|Q_+/Q_-|', description: 'Golden character logarithm' },
  { name: 'P', tex: 'P=u^2', description: 'Fifth-weight selector' },
  { name: 'R', tex: 'R=u^2(u+\\pi^2/2)', description: 'Seventh-weight selector' },
]);

export const PRECISION = Object.freeze({
  arithmetic: 'IEEE-754 binary64; about 15 significant decimal digits',
  quadrature: 'Independent root-split Gauss-Legendre with fourth-order endpoint flattening',
  singularities: 'Four integrable logarithmic singularities; point values there may be infinite',
  interpretation: 'Energy is integrated in theta measure; density is (aA+bK+cP+dR)^2',
  formalization: 'The new Gram identities have written analytic proofs; they are not claimed as new Lean theorems.',
});

export function chi5(n) {
  if (!Number.isSafeInteger(n)) throw new TypeError('chi5 needs a safe integer');
  return [0, 1, -1, -1, 1][((n % 5) + 5) % 5];
}

function gcd(a, b) {
  a = Math.abs(a); b = Math.abs(b);
  while (b) [a, b] = [b, a % b];
  return a;
}

function mobius(n) {
  let sign = 1;
  for (let p = 2; p * p <= n; p++) {
    if (n % p === 0) {
      n /= p;
      sign = -sign;
      if (n % p === 0) return 0;
      while (n % p === 0) n /= p;
    }
  }
  return n > 1 ? -sign : sign;
}

/** Exact integer c_q(n)=sum_{d|gcd(q,n)} d mu(q/d). */
export function ramanujanSum(q, n) {
  if (!Number.isSafeInteger(q) || q < 1 || !Number.isSafeInteger(n)) {
    throw new TypeError('ramanujanSum needs a positive safe conductor and a safe integer');
  }
  const g = gcd(q, n);
  let result = 0;
  for (let d = 1; d * d <= g; d++) if (g % d === 0) {
    result += d * mobius(q / d);
    const e = g / d;
    if (e !== d) result += e * mobius(q / e);
  }
  return result;
}

/** Cosine coefficients: f(theta)=sum_{n>=1} coefficient(n) cos(n theta). */
export function fourierCoefficients(n) {
  if (!Number.isSafeInteger(n) || n < 1) throw new TypeError('Positive Fourier index required');
  return {
    A: -ramanujanSum(30, n) / n,
    K: -Math.sqrt(5) * chi5(n) * ramanujanSum(6, n) / n,
    aInteger: -ramanujanSum(30, n),
    kSqrt5Integer: -chi5(n) * ramanujanSum(6, n),
    denominator: n,
  };
}

function compensatedSum(terms) {
  let value = 0, carry = 0;
  for (const term of terms) {
    const y = term - carry;
    const next = value + y;
    carry = (next - value) - y;
    value = next;
  }
  return value;
}

function dirichletL5(s) {
  // Grouping a complete character period gives a rapidly decreasing, positive
  // second difference. 4096 periods leave a tail far below binary64 precision.
  const terms = [];
  for (let k = 0; k < 4096; k++) {
    const a = 5 * k;
    terms.push((a + 1) ** -s - (a + 2) ** -s - (a + 3) ** -s + (a + 4) ** -s);
  }
  return compensatedSum(terms);
}

export const SPECIAL_VALUES = Object.freeze({
  zeta5: 1.036927755143369926331365486457034168,
  zeta7: 1.008349277381922826839797549849796760,
  L5: dirichletL5(5),
  L7: dirichletL5(7),
});

const pi = Math.PI;
const gAA = 8 * pi ** 3 / 45;
const gAK = -4 * pi ** 3 / 75;
const gKK = 8 * pi ** 3 / 15;
const gAP = 832 * pi * SPECIAL_VALUES.zeta5 / 1125;
const gAR = 157976 * pi * SPECIAL_VALUES.zeta7 / 28125;
const gKP = 41 * pi * Math.sqrt(5) * SPECIAL_VALUES.L5 / 54;
const gKR = 1825 * pi * Math.sqrt(5) * SPECIAL_VALUES.L7 / 324;
const gPP = pi ** 9 / 630;
const gPR = 4 * pi ** 11 / 3465;
const gRR = 101 * pi ** 13 / 120120;

const GRAM = [
  [gAA, gAK, gAP, gAR],
  [gAK, gKK, gKP, gKR],
  [gAP, gKP, gPP, gPR],
  [gAR, gKR, gPR, gRR],
];

/** All ten independent inner products, including exact symbolic identities. */
export const ALL_GRAM = Object.freeze([
  [0, 0, '\\frac{8\\pi^3}{45}', 'Parseval / Ramanujan sum'],
  [0, 1, '-\\frac{4\\pi^3}{75}', 'Quadratic Gauss sum / L(2,chi5)'],
  [0, 2, '\\frac{832\\pi}{1125}\\zeta(5)', 'Bernoulli selector / Euler factors'],
  [0, 3, '\\frac{157976\\pi}{28125}\\zeta(7)', 'Bernoulli selector / Euler factors'],
  [1, 1, '\\frac{8\\pi^3}{15}', 'Parseval / quadratic character'],
  [1, 2, '\\frac{41\\pi\\sqrt5}{54}L(5,\\chi_5)', 'Bernoulli selector / character filter'],
  [1, 3, '\\frac{1825\\pi\\sqrt5}{324}L(7,\\chi_5)', 'Bernoulli selector / character filter'],
  [2, 2, '\\frac{\\pi^9}{630}', 'Euler beta integral'],
  [2, 3, '\\frac{4\\pi^{11}}{3465}', 'Euler beta integral'],
  [3, 3, '\\frac{101\\pi^{13}}{120120}', 'Euler beta integral'],
].map(([i, j, exactTex, mechanism]) => Object.freeze({
  i, j, label: `${BASIS_NAMES[i]}${BASIS_NAMES[j]}`,
  value: GRAM[i][j], exactTex, mechanism,
})));

/** Return a copy so callers cannot mutate the formula source. */
export function gramMatrix() { return GRAM.map(row => [...row]); }

export function quadratics(x) {
  const root5 = Math.sqrt(5);
  return {
    plus: 4 * x * x + (1 - root5) * x - (3 + root5) / 2,
    minus: 4 * x * x + (1 + root5) * x - (3 - root5) / 2,
    quartic: 16 * x ** 4 + 8 * x ** 3 - 16 * x * x - 8 * x + 1,
  };
}

function logCosDifference(theta, alpha) {
  // Unlike cos(theta)-cos(alpha), this retains precision near a root.
  return Math.LN2
    + Math.log(Math.abs(Math.sin((theta + alpha) / 2)))
    + Math.log(Math.abs(Math.sin((theta - alpha) / 2)));
}

export function basisAtTheta(theta) {
  if (!Number.isFinite(theta) || theta < 0 || theta > pi) {
    throw new RangeError('theta must be in [0, pi]');
  }
  const lp = Math.log(4) + logCosDifference(theta, ROOT_ANGLES[0])
    + logCosDifference(theta, ROOT_ANGLES[2]);
  const lm = Math.log(4) + logCosDifference(theta, ROOT_ANGLES[1])
    + logCosDifference(theta, ROOT_ANGLES[3]);
  const u = theta * (pi - theta);
  return [lp + lm, lp - lm, u * u, u * u * (u + pi * pi / 2)];
}

function validateCoefficients(coefficients) {
  if (!Array.isArray(coefficients) || coefficients.length !== 4
    || coefficients.some(x => !Number.isFinite(x))) {
    throw new TypeError('Four finite coefficients [a,b,c,d] are required');
  }
  return coefficients;
}

function weightedAmplitude(coefficients, basis) {
  let value = 0;
  for (let k = 0; k < 4; k++) if (coefficients[k] !== 0) value += coefficients[k] * basis[k];
  return value;
}

export function evaluateEnergy(coefficients) {
  validateCoefficients(coefficients);
  const contributions = ALL_GRAM.map(({ i, j, label, value: entry, exactTex }) => ({
    i, j, label, entry, exactTex,
    value: (i === j ? 1 : 2) * coefficients[i] * coefficients[j] * entry,
  }));
  return {
    value: compensatedSum(contributions.map(c => c.value)),
    contributions,
    gradient: GRAM.map(row => 2 * compensatedSum(row.map((x, i) => x * coefficients[i]))),
  };
}

const quadratureCache = new Map();
function gaussLegendre(order) {
  if (quadratureCache.has(order)) return quadratureCache.get(order);
  const points = [];
  for (let i = 0; i < Math.ceil(order / 2); i++) {
    let z = Math.cos(pi * (i + 0.75) / (order + 0.5));
    let derivative = 0;
    for (let iteration = 0; iteration < 30; iteration++) {
      let p0 = 1, p1 = z;
      for (let n = 2; n <= order; n++) [p0, p1] = [p1, ((2 * n - 1) * z * p1 - (n - 1) * p0) / n];
      derivative = order * (z * p1 - p0) / (z * z - 1);
      const next = z - p1 / derivative;
      if (Math.abs(next - z) < 2e-16) { z = next; break; }
      z = next;
    }
    const weight = 2 / ((1 - z * z) * derivative * derivative);
    points.push({ node: (1 - z) / 2, weight: weight / 2 });
    if (Math.abs(z) > 1e-15) points.push({ node: (1 + z) / 2, weight: weight / 2 });
  }
  points.sort((a, b) => a.node - b.node);
  quadratureCache.set(order, points);
  return points;
}

function integrateFunction(fn, endTheta, order) {
  if (!Number.isFinite(endTheta) || endTheta < 0 || endTheta > pi) {
    throw new RangeError('endTheta must be in [0, pi]');
  }
  if (!Number.isSafeInteger(order) || order < 8 || order > 256) {
    throw new RangeError('Gauss-Legendre order must be an integer from 8 to 256');
  }
  const breaks = [0, ...ROOT_ANGLES.filter(t => t < endTheta), endTheta];
  const terms = [];
  const nodes = gaussLegendre(order);
  let evaluations = 0;
  for (let i = 0; i < breaks.length - 1; i++) {
    const lo = breaks[i], hi = breaks[i + 1], width = hi - lo;
    if (width === 0) continue;
    for (const { node: t, weight } of nodes) {
      // q=t^4/(t^4+(1-t)^4) removes endpoint logarithmic stiffness.
      const a = t ** 4, b = (1 - t) ** 4, denominator = a + b;
      const q = a / denominator;
      const jacobian = width * 4 * t ** 3 * (1 - t) ** 3 / denominator ** 2;
      const theta = q < 0.5 ? lo + width * q : hi - width * (1 - q);
      // The omitted value is below rounding resolution at an endpoint. Its
      // transformed weight vanishes cubically; never replace infinity by a cap.
      if (!(theta > lo && theta < hi)) continue;
      terms.push(weight * jacobian * fn(theta));
      evaluations++;
    }
  }
  return { value: compensatedSum(terms), panels: Math.max(0, breaks.length - 1), evaluations };
}

/** Independent numerical integration: no Gram formula is used here. */
export function integrateEnergy(coefficients, endTheta = pi, { order = 64 } = {}) {
  validateCoefficients(coefficients);
  return integrateFunction(theta => weightedAmplitude(coefficients, basisAtTheta(theta)) ** 2, endTheta, order).value;
}

export function integrateEnergyDetailed(coefficients, endTheta = pi, { order = 64 } = {}) {
  validateCoefficients(coefficients);
  const fine = integrateFunction(theta => weightedAmplitude(coefficients, basisAtTheta(theta)) ** 2, endTheta, order);
  const coarse = integrateEnergy(coefficients, endTheta, { order: Math.max(8, Math.floor(order / 2)) });
  return { ...fine, estimatedError: Math.abs(fine.value - coarse), order,
    method: 'Root-split Gauss-Legendre; fourth-order endpoint flattening',
    errorIsRigorous: false };
}

/** Independent inner product for mathematical validation and the check panel. */
export function integrateBasisProduct(i, j, { order = 64 } = {}) {
  if (![i, j].every(k => Number.isInteger(k) && k >= 0 && k < 4)) throw new RangeError('Basis index must be 0..3');
  return integrateFunction(theta => {
    const values = basisAtTheta(theta);
    return values[i] * values[j];
  }, pi, order).value;
}

export function sampleDensity(coefficients, count = 400) {
  validateCoefficients(coefficients);
  if (!Number.isSafeInteger(count) || count < 2 || count > 100000) throw new RangeError('Sample count must be 2..100000');
  return Array.from({ length: count }, (_, i) => {
    // Half-step samples never coincide with a root j*pi/15 at integer count.
    const theta = pi * (i + 0.5) / count;
    const basis = basisAtTheta(theta);
    const amplitude = weightedAmplitude(coefficients, basis);
    return { theta, x: Math.cos(theta), amplitude, density: amplitude * amplitude, basis };
  });
}

/** Symmetric Jacobi diagonalization for a 3x3/4x4 energy slice. */
export function eigenDecomposition(matrix) {
  const n = matrix.length;
  if (![3, 4].includes(n) || matrix.some(row => row.length !== n || row.some(x => !Number.isFinite(x)))) {
    throw new TypeError('A finite symmetric 3x3 or 4x4 matrix is required');
  }
  const a = matrix.map(row => [...row]);
  for (let i = 0; i < n; i++) for (let j = 0; j < n; j++) {
    if (Math.abs(a[i][j] - a[j][i]) > 1e-12 * Math.max(1, Math.abs(a[i][j]))) throw new TypeError('Matrix must be symmetric');
  }
  const v = Array.from({ length: n }, (_, i) => Array.from({ length: n }, (_, j) => +(i === j)));
  let iterations = 0;
  for (; iterations < 128; iterations++) {
    let p = 0, q = 1;
    for (let i = 0; i < n; i++) for (let j = i + 1; j < n; j++) if (Math.abs(a[i][j]) > Math.abs(a[p][q])) [p, q] = [i, j];
    const scale = Math.max(1, ...a.map((row, i) => Math.abs(row[i])));
    if (Math.abs(a[p][q]) < 1e-15 * scale) break;
    const angle = 0.5 * Math.atan2(2 * a[p][q], a[q][q] - a[p][p]);
    const c = Math.cos(angle), s = Math.sin(angle);
    const app = a[p][p], aqq = a[q][q], apq = a[p][q];
    a[p][p] = c * c * app - 2 * s * c * apq + s * s * aqq;
    a[q][q] = s * s * app + 2 * s * c * apq + c * c * aqq;
    a[p][q] = a[q][p] = 0;
    for (let k = 0; k < n; k++) if (k !== p && k !== q) {
      const akp = a[k][p], akq = a[k][q];
      a[k][p] = a[p][k] = c * akp - s * akq;
      a[k][q] = a[q][k] = s * akp + c * akq;
    }
    for (let k = 0; k < n; k++) {
      const vkp = v[k][p], vkq = v[k][q];
      v[k][p] = c * vkp - s * vkq;
      v[k][q] = s * vkp + c * vkq;
    }
  }
  const order = Array.from({ length: n }, (_, i) => i).sort((i, j) => a[i][i] - a[j][j]);
  return { values: order.map(i => a[i][i]), vectors: v.map(row => order.map(i => row[i])), iterations };
}
