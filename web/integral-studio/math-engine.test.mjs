import test from 'node:test';
import assert from 'node:assert/strict';
import {
  PHI, ROOT_ANGLES, EXPONENTS, ALL_GRAM, SPECIAL_VALUES,
  chi5, ramanujanSum, fourierCoefficients, quadratics, basisAtTheta,
  gramMatrix, evaluateEnergy, integrateEnergy, integrateEnergyDetailed,
  integrateBasisProduct, sampleDensity, eigenDecomposition,
} from './math-engine.mjs';

const close = (actual, expected, relative = 1e-9, message = '') => {
  assert.ok(Math.abs(actual - expected) <= relative * Math.max(1, Math.abs(expected)),
    `${message}: ${actual} vs ${expected}`);
};

test('all ten analytic Gram entries agree with independent singular quadrature', () => {
  for (const { i, j, label, value } of ALL_GRAM) {
    close(integrateBasisProduct(i, j, { order: 64 }), value, 1e-9, label);
  }
});

test('signed mixtures, cancellation, and gradients obey the actual integral', () => {
  const mixtures = [[0.3, -0.7, 0.1, -0.02], [-2, 0.5, -0.3, 0.04], [3, 10, 0, 0], [1, 1, 1, 1]];
  for (const coefficients of mixtures) {
    const exact = evaluateEnergy(coefficients);
    assert.ok(exact.value > 0);
    close(integrateEnergy(coefficients), exact.value, 1e-9);
    close(exact.contributions.reduce((s, t) => s + t.value, 0), exact.value, 1e-13);
    for (let i = 0; i < 4; i++) {
      const h = 1e-5;
      const plus = [...coefficients], minus = [...coefficients];
      plus[i] += h; minus[i] -= h;
      close((evaluateEnergy(plus).value - evaluateEnergy(minus).value) / (2 * h), exact.gradient[i], 1e-6);
    }
  }
});

test('known zeta, character, Parseval, beta, and orthogonality cases remain intact', () => {
  const g = gramMatrix();
  close(g[0][2], 2.409179592943102276992596742113, 1e-14);
  close(g[0][3], 17.79342065861614223439, 1e-14);
  close(g[1][2], 5.15054250969631116959, 1e-14);
  close(g[1][1], 8 * Math.PI ** 3 / 15, 1e-15);
  close(g[2][2], Math.PI ** 9 / 630, 1e-15);
  close(3 * g[0][0] + 10 * g[0][1], 0, 1e-14);
  assert.ok(SPECIAL_VALUES.L5 > 0.96 && SPECIAL_VALUES.L5 < 0.97);
  assert.ok(SPECIAL_VALUES.L7 > 0.99 && SPECIAL_VALUES.L7 < 1);
});

test('stable log factors match the polynomial and retain true singularities', () => {
  close(PHI * PHI, PHI + 1, 1e-15);
  for (let i = 1; i < 200; i++) {
    const theta = Math.PI * i / 200;
    if (ROOT_ANGLES.some(a => Math.abs(theta - a) < 1e-7)) continue;
    const x = Math.cos(theta), q = quadratics(x), basis = basisAtTheta(theta);
    close(q.plus * q.minus, q.quartic, 1e-13);
    close(basis[0], Math.log(Math.abs(q.quartic)), 2e-11);
    close(basis[1], Math.log(Math.abs(q.plus / q.minus)), 2e-11);
  }
  for (const theta of [0, Math.PI]) {
    const b = basisAtTheta(theta);
    close(b[0], 0, 1e-13);
    assert.equal(b[2], 0); assert.equal(b[3], 0);
    assert.ok(b.every(Number.isFinite));
  }
  for (let i = 0; i < ROOT_ANGLES.length; i++) {
    const b = basisAtTheta(ROOT_ANGLES[i]);
    assert.equal(b[0], -Infinity);
    assert.equal(b[1], i === 0 || i === 2 ? -Infinity : Infinity);
    assert.ok(Number.isFinite(b[2]) && Number.isFinite(b[3]));
    assert.ok(basisAtTheta(ROOT_ANGLES[i] + 1e-10).every(Number.isFinite));
  }
});

test('exact Ramanujan and Gauss coefficients reproduce direct phase sums', () => {
  for (let n = 1; n <= 180; n++) {
    const c = fourierCoefficients(n);
    const directA = EXPONENTS.reduce((s, e) => s + Math.cos(2 * Math.PI * e * n / 30), 0);
    const directK = EXPONENTS.reduce((s, e) => s + chi5(e) * Math.cos(2 * Math.PI * e * n / 30), 0);
    close(-n * c.A, directA, 2e-12);
    close(-n * c.K, directK, 2e-12);
    assert.equal(Number.isInteger(c.aInteger), true);
    assert.equal(Number.isInteger(c.kSqrt5Integer), true);
  }
  assert.equal(ramanujanSum(30, 0), 8);
  assert.equal(ramanujanSum(30, 30), 8);
  assert.equal(ramanujanSum(30, 1), -1);
  assert.equal(chi5(-1), 1);
  assert.equal(chi5(-2), -1);
  assert.equal(chi5(5), 0);
});

test('partial integrals increase and work at every singularity boundary', () => {
  const coefficients = [1, -0.4, 0.03, -0.004];
  const endpoints = [0, ...ROOT_ANGLES, Math.PI];
  let previous = -1;
  for (const theta of endpoints) {
    const value = integrateEnergy(coefficients, theta);
    assert.ok(Number.isFinite(value) && value >= previous);
    previous = value;
  }
  assert.equal(integrateEnergy(coefficients, 0), 0);
  close(previous, evaluateEnergy(coefficients).value, 1e-9);
  const detail = integrateEnergyDetailed(coefficients);
  assert.equal(detail.errorIsRigorous, false);
  assert.equal(detail.panels, 5);
  assert.ok(detail.evaluations >= 300 && detail.estimatedError < 1e-6);
});

test('density is raw transformed energy, and pure polynomial sampling is regular', () => {
  for (const coefficients of [[0, 0, 0, 0], [1, 1, 0.1, -0.01], [0, 0, 1, 0]]) {
    const samples = sampleDensity(coefficients, 401);
    assert.equal(samples.length, 401);
    for (const point of samples) {
      assert.ok(Number.isFinite(point.density));
      assert.ok(point.density >= 0);
      close(point.density, point.amplitude ** 2, 1e-15);
      close(point.x, Math.cos(point.theta), 1e-15);
    }
  }
  assert.equal(evaluateEnergy([0, 0, 0, 0]).value, 0);
  assert.equal(integrateEnergy([0, 0, 0, 0]), 0);
});

test('symmetric eigensystem reconstructs Gram and proves positive eigenvalues numerically', () => {
  const g = gramMatrix(), decomposition = eigenDecomposition(g);
  assert.ok(decomposition.values.every(value => value > 0));
  const { values, vectors } = decomposition;
  for (let i = 0; i < 4; i++) for (let j = 0; j < 4; j++) {
    close(values.reduce((s, value, k) => s + vectors[i][k] * value * vectors[j][k], 0), g[i][j], 1e-11);
    close(vectors.reduce((s, row) => s + row[i] * row[j], 0), +(i === j), 1e-13);
  }
  const copy = gramMatrix(); copy[0][0] = 0;
  assert.notEqual(gramMatrix()[0][0], 0);
});

test('invalid or ambiguous numerical input is rejected', () => {
  assert.throws(() => evaluateEnergy([1, 2]), TypeError);
  assert.throws(() => evaluateEnergy([1, 2, Infinity, 4]), TypeError);
  assert.throws(() => basisAtTheta(-0.01), RangeError);
  assert.throws(() => integrateEnergy([1, 0, 0, 0], 4), RangeError);
  assert.throws(() => integrateEnergy([1, 0, 0, 0], 1, { order: 1 }), RangeError);
  assert.throws(() => ramanujanSum(0, 1), TypeError);
  assert.throws(() => fourierCoefficients(0), TypeError);
  assert.throws(() => sampleDensity([1, 2, 3, 4], 0), RangeError);
  assert.throws(() => eigenDecomposition([[1, 2, 3], [0, 1, 0], [0, 0, 1]]), TypeError);
});
