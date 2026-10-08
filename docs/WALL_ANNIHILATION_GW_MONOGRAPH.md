# Annihilation-phase gravitational waves from the biased wall network

This study closes the open item "annihilation-phase gravitational waves" of the wall chapters in docs/FLAVOR_COSMOLOGY_MONOGRAPH.md. The earlier lattice work measured the area parameter and annihilation factor with the Press-Ryden-Spergel (PRS) equation (receipts/flavor_cosmology/wall_network.json), then the GW efficiency and spectral shape of the physical, unbiased network during scaling (receipts/flavor_cosmology/wall_gw.json). The GW spectrum was explicitly computed before annihilation. Here a vacuum bias is switched on in the physical-equation simulation with tensor modes. The network scales first, then collapses inside the box, and the tensor modes then propagate freely. Three questions are answered within the stated box and time limits:

1. How do the false-vacuum fraction and wall area fall, and how does the annihilation time depend on the bias? Is this consistent with the pressure-balance law tau_ann proportional to (sigma/Delta V)^(1/2)?
2. What happens to the GW energy and spectrum during the collapse?
3. Is the residual GW background, once the walls are gone, a freely propagating radiation component, with a^4 rho_gw constant?

All numbers below are in receipts/flavor_cosmology/wall_annihilation_gw.json, which is produced from the cached series receipts/flavor_cosmology/wall_annihilation_gw_series.json.

## 1. Model

The walls of the supplied model are phi^4 kinks to about 10^-6, as shown in the earlier tension sandwich. The reduced field therefore has

    V(phi) = (lam/4)(phi^2-1)^2 + eps s(tau) (phi^3/3 - phi),
    dV/dphi = (phi^2-1)(lam phi + eps s(tau)).

**Choice of bias.** The cubic bias is used rather than the linear bias -eps phi. Its derivative eps(phi^2-1) vanishes at phi=+-1, so both minima stay *exactly* at +-1 for every eps<lam, not just to leading order. The vacuum splitting is exactly Delta V = V(-1)-V(+1) = 4 eps/3. The true vacuum is phi=+1, and phi<0 marks the false vacuum. The barrier top moves to phi=-eps/lam. The curvature in the false vacuum is V''(-1)=2(lam-eps)>0, so the false vacuum is metastable for eps<lam. The wall tension changes only at relative order eps/lam, and the unbiased sigma=(2 sqrt2/3) sqrt(lam) is used throughout. A linear bias would shift the minima by eps/(2 lam), giving O(eps/lam) shifts in the vacuum values that the cubic form avoids.

**Switch-on.** s(tau) is a C^1 smoothstep from 0 at tau_on to 1 at tau_on+5, with tau_on=40. Before the switch-on the evolution is identical to the unbiased network with the same seed. That makes the unbiased run of the same seed an exact control for everything the bias adds. After the ramp eps is a constant *physical* energy density. With the physical equation, no PRS rescaling is needed. Switching on at tau=40 is a numerical device: a bias present during the tachyonic formation stage shifts the mean of the growing field by eps/lam, which is comparable to the initial rms of 0.1. That would bias the domain populations rather than test pressure-driven annihilation. The tau_on=30 control below shows how strong that effect is.

## 2. Method

Radiation era with a=tau in comoving lattice units, so H=1/tau^2 and cosmic time t=tau^2/2. The equations are

    phi'' + 2 phi'/tau - lap phi = -tau^2 dV/dphi,
    u_ij'' + 2 u_ij'/tau - lap u_ij = 16 pi G d_i phi d_j phi   (G=1),

with the transverse-traceless projection Lambda u = PuP - (1/2) P tr(PuP) applied in Fourier space when measuring (Garcia-Bellido, Figueroa and Sastre). This is exactly wall_network.evolve_physical_gw with the bias added. A test checks that eps=0 reproduces that function to float32 rounding. The stencils were rewritten to be allocation-free for speed. The parameters are lam=2/(w_ref tau_ref)^2 with w_ref=2 and tau_ref=96, so the comoving wall width is 2 lattice spacings at tau=96. The main box is N=192 (control N=128 with the same lam), with dx=1, dt=0.2, tau_i=10 and the Gaussian initial field of wall_network (rms 0.1, cut at a quarter of Nyquist). The evolution is float32 and periodic.

Two GW energies are recorded:

* rho_gw = <h'h'>/(32 pi G a^2), the kinetic convention of wall_gw.json, used for the efficiency eps_gw = rho_gw/(G A^2 sigma^2);
* rho_avg = (<h'h'> + <grad h . grad h>)/(64 pi G a^2), with the lattice dispersion k_eff^2 = sum_i (2 sin(k_i/2))^2. For free sub-horizon tensor waves u = sin(k tau)/tau, the comoving energy a^4 rho_avg is constant up to O(1/(k tau)) terms, whereas the kinetic part alone oscillates. This is the quantity used for the conservation check and for E = a^4 rho_avg, the "comoving GW energy".

The wall area uses the sign-changing-link estimator (2/3 per link), A = (comoving area density) tau/2. The false-vacuum fraction is the volume fraction with phi<0. The primary annihilation time tau_ann is the first time after tau_on at which the false fraction falls below 1 percent, linearly interpolated between measurements. This is the same criterion as wall_network.json. Secondary criteria are 10 percent, and A falling to half its scaling value A_ref.

**Runs.** Stage 1 (network only, no tensors, measured every unit of tau to tau=160): N=192 with eps = 1.5, 2.5, 4, 6, 9 x 10^-6 and seeds 0 and 1, plus unbiased seeds 0 and 1; switch-on controls tau_on=30 and 50 at eps=4x10^-6; a box control N=128 at eps = 2.5, 4, 6, 9 x 10^-6. Stage 2 (with tensor modes, measured every 4 units to tau=158): N=192, eps = 0, 2.5, 4, 6 x 10^-6, seeds 0 and 1. The lattice has lam=5.43x10^-5 and sigma=6.95x10^-3, so sigma/Delta V runs from 579 to 3472.

## 3. Expected exponent

In the scaling regime rho_wall = A sigma/t. The classical pressure-balance estimate says the network annihilates when the bias pressure Delta V reaches C_ann rho_wall, that is

    t_ann = C_ann A sigma/Delta V = K sigma/Delta V.

This is exactly the convention of dimensionful_walls.annihilation (rho_wall = 2 A sigma H, H = 1/(2t)). With a = tau, t = tau^2/2, so

    tau_ann = (2 K sigma/Delta V)^(1/2),   p = 1/2 in conformal time (p = 1 in cosmic time).

The PRS calibration measured K = C_ann A = 1.79, and its four biased runs fall as tau_ann proportional to eps1^(-0.49), consistent with p=1/2. Note, however, that the PRS runs grow the bias as eps1 tau from the start. The law is asymptotic: it assumes the bias has acted on a scaling network for many Hubble times, and that the walls can respond within a Hubble time, with velocities below 1.

## 4. Results: false-vacuum fraction, wall area and annihilation time

The unbiased networks form at tau of about 40 to 48. Before that, A passes through a formation transient up to 2.6 at tau of about 26 to 30. Over the window 48<=tau<=96, A = 0.836 and 0.780 for the two seeds, so A_ref = 0.808. This agrees with the PRS value 0.807 and the earlier physical-equation value 0.82. After tau of about 96 the box limits the network, and A drifts up to 1.23 and 0.94 by tau=160.

Once the bias is on, the false fraction falls monotonically from 0.5 (figure, top left). The fall steepens during the collapse and leaves a tail of small, slowly dying pockets at the 10^-3 level. A falls about 10 units of tau before the false fraction reaches 1 percent.

| eps (10^-6) | sigma/Delta V | Delta V/(lam/4) | tau_ann (1%), seed 0 / 1 | tau (10%) | tau (A=A_ref/2) | pressure balance, K_PRS | width at tau_ann |
|---|---|---|---|---|---|---|---|
| 1.5 | 3472 | 0.15 | 131.6 / 147.5 | 110.1 / 123.3 | 121.6 / 135.4 | 111.6 | 1.46 / 1.30 |
| 2.5 | 2083 | 0.25 | 114.9 / 125.5 | 95.4 / 102.3 | 105.6 / 112.1 | 86.4 | 1.67 / 1.53 |
| 4 | 1302 | 0.39 | 106.1 / 109.5 | 84.1 / 86.6 | 93.3 / 97.3 | 68.3 | 1.81 / 1.75 |
| 6 | 868 | 0.59 | 100.5 / 97.3 | 76.0 / 75.6 | 83.4 / 84.2 | 55.8 | 1.91 / 1.97 |
| 9 | 579 | 0.89 | 93.2 / 84.3 | 69.2 / 67.3 | 75.0 / 71.9 | 45.6 | 2.06 / 2.28 |

(The GW runs below repeat eps = 2.5, 4 and 6 x 10^-6 at measurement spacing 4. They give tau_ann = 115.2/125.5, 106.1/109.6 and 100.6/97.1, which agrees with the dense scan to within the interpolation.)

**Exponent.** A pure power law through all ten points gives

    tau_ann (1%) proportional to (sigma/Delta V)^p,   p = 0.247 +- 0.023,

that is, an exponent of 0.49 in cosmic time. The other criteria give p = 0.300 +- 0.018 (10 percent) and p = 0.309 +- 0.017 (A half). The seeds separately give p = 0.19 and 0.31, and the N=128 box control gives p = 0.20. **The pressure-balance prediction p = 1/2 is therefore not reproduced in this window: the measured exponent is about half of it.** This is not in tension with the PRS calibration, which gave p of about 0.49. The difference has an identifiable cause. The physical-equation network only forms at tau of about 40 to 48, and the bias must act on an already-formed network. Collapse then needs a finite conformal time, because walls move at v<1 and the largest false domains, of size comparable to the horizon, must be swept out. For the strongest bias tau_ann - tau_on is 45 to 60, which is close to that causal minimum. It is not the pressure-balance time: the classical estimate with K_PRS would be 45.6, *before* tau_on+ramp. The two controls show the same dependence on history directly. Moving the switch-on from 40 to 50 delays annihilation from 106.1 to 116.8 at eps = 4 x 10^-6. Switching on at tau=30, during the formation transient, gives 51.7, because the bias then acts on the population itself.

An offset law that keeps the pressure-balance exponent in cosmic time fits the ten points with 9 percent rms residual:

    t_ann - t_0 = K sigma/Delta V,   K = 1.95,  t_0 = 3088 (tau_0 = 78.6).

Seed by seed it gives K = 1.44 and 2.46. Remarkably, the slope K = 1.95 (1.44 to 2.46) agrees with the PRS K = 1.79 measured independently. The data are therefore consistent with the claim that the marginal cost of a weaker bias is the classical one. The fit cannot *prove* p=1/2, though: the range of sigma/Delta V is only a factor of 6, and the offset absorbs the history. The 10 percent and A-half criteria give K = 1.55 and 1.89. The N=128 control (same lam, smaller box) gives K = 1.62 with tau_0 = 73.5, and its annihilation is 4 to 9 percent earlier at equal eps. The box therefore matters at that level. Two further systematics push in opposite directions. The walls are only 1.3 to 1.5 lattice spacings thick at the latest annihilations, which slows them (pinning) and raises p. The box-driven rise of A after tau of about 96 speeds late collapse and lowers p. The large bias-to-barrier ratios (0.15 to 0.89, against 0.08 to 0.21 in the PRS study) mean that the strongest-bias points are not in the small-bias regime.

## 5. Results: GW energy through annihilation

The bias is switched on at tau=40, and the tensor source only becomes significant once the walls form. a^4 rho_gw at tau=40 is less than 2 x 10^-6 of its final value in every run. A "scaling-phase GW energy before the bias acts" therefore does not exist in these boxes. The scaling reference is the **same-seed unbiased run**, which is identical up to tau_on. Comparing the comoving energies E = a^4 rho_avg gives the following.

| eps (10^-6), seed | tau_ann | E(tau_ann)/E_unb(tau_ann) | E_end/E_unb(tau_ann) | share of E_end made after tau_ann | eps_avg(unbiased, tau_ann) | E ratio by band, end/unbiased(tau_ann): k<0.1 / 0.1-0.5 / 0.5-pi/2 |
|---|---|---|---|---|---|---|
| 2.5, 0 | 115.2 | 1.24 | 1.46 | 0.15 | 1.13 | 1.25 / 1.97 / 5.6 |
| 4, 0 | 106.1 | 1.31 | 1.53 | 0.15 | 1.10 | 1.29 / 1.79 / 6.1 |
| 6, 0 | 100.6 | 1.33 | 1.45 | 0.09 | 1.08 | 1.14 / 1.52 / 6.0 |
| 2.5, 1 | 125.5 | 1.16 | 1.42 | 0.18 | 0.91 | 1.06 / 2.46 / 4.4 |
| 4, 1 | 109.6 | 1.32 | 1.47 | 0.10 | 0.84 | 1.03 / 2.09 / 5.3 |
| 6, 1 | 97.1 | 1.50 | 1.47 | -0.02 | 0.83 | 0.96 / 1.74 / 5.4 |

**Does eps_gw jump?** Yes, moderately. The GW energy a collapsing network has produced by tau_ann exceeds that of the unbiased network at the same time by a factor of 1.16 to 1.50. Including the tail of the collapse (pockets below 1 percent), the final residual is **1.42 to 1.53 times** the unbiased energy at tau_ann (mean 1.47). The extra energy is 42 to 53 percent of what the scaling network had radiated by then. Between 0 and 18 percent of the final energy is made after the false fraction drops below 1 percent. The instantaneous efficiency rho_gw/(G A^2 sigma^2) diverges as A goes to 0, which is trivial. With A held at A_ref, the biased efficiency peaks at 0.82 to 1.23 (kinetic convention), compared with 0.51 to 0.66 for the unbiased network at that time. Thereafter it decays as a^-4. The jump is far below an order of magnitude. In this model the collapse adds roughly half again to the scaling-network output; it does not dominate it.

**Spectrum.** The collapse puts its extra energy mostly at short wavelengths. On the largest scales (k<0.1, near the box) the final spectrum equals the unbiased one at tau_ann within plus or minus 30 percent. At 0.1<=k<0.5 it is 1.5 to 2.5 times higher, and at 0.5<=k<pi/2 it is 4.4 to 6.1 times higher. The UV slope (fit window 1.5 k_peak < k < pi/2, as in wall_gw) flattens from -1.22 to -1.54 for the unbiased network at tau_ann. It is -0.80 to -0.94 for the biased networks at tau_ann and **-0.56 to -0.73 for the residual**. Above k = pi/2 the ratio is 8 to 29, but there the lattice is not trustworthy (the UV bump near k of about 3 to 4 appears in the unbiased run too). The flattening is therefore established only for 0.1<k<pi/2, that is, wavelengths from 4 to about 60 lattice spacings, or 2 to 30 wall widths. It is plausibly the collapse of small false pockets and the scalar radiation they release. The peak does not move measurably. Both before and after annihilation it sits in the first or second bin above the box mode (k_peak = 0.035 to 0.048). That is f/H_ann = k tau_ann/(2 pi) = 0.55 to 0.95, while the box mode itself is at 0.53 to 0.69. The ratio of end to unbiased peak k (0.73 to 1.38) is one bin either way. **Only f_peak/H_ann <~ 1 is established, the IR slope is not measurable (fewer than three bins below the peak), and no peak shift can be resolved.**

## 6. Results: residual GW after the walls disappear

From tau_ann+8 to tau=158 (7 to 14 measurements, windows of 24 to 53 units of tau), the oscillation-averaged comoving energy a^4 rho_avg is constant. Its relative spread is 0.5 to 3.1 percent, and the fitted log-slopes d ln E/d ln tau are -0.20, -0.06, -0.01, 0.09, 0.23 and 0.56. The largest slope belongs to the latest annihilation (eps = 2.5 x 10^-6, seed 1), which has the shortest window and is still finishing its last pockets. Free propagation, rho_gw proportional to a^-4, is therefore confirmed at the few-percent level. The kinetic convention alone is *not* constant: a^4 <h'h'>/(32 pi) changes with log-slopes 0.6 to 3.3. The dominant box-scale modes have k tau of only about 4 to 8, so they are neither equipartitioned nor oscillation-averaged. In the unbiased scaling network, too, the kinetic part is only 0.47 to 0.77 of rho_avg at tau_ann. This convention ambiguity, a factor of about 1.5, applies to every lattice efficiency quoted in either convention. It is why the template update below uses only a ratio of like quantities. A unit test checks the conservation of rho_avg a^4 on a single tensor plane wave against the exact solution u = sin(k tau)/tau. The 1 percent residual there comes from the leapfrog half-step lag between u and u'.

## 7. Comparison with the declared template and with the literature

**Template (dimensionful_walls).** The classical template evaluates rho_gw = eps_gw G A^2 sigma^2 at H_ann, with t_ann = K sigma/Delta V. The lattice now supplies:

* K: the offset-law slope 1.95 (seed range 1.44 to 2.46), consistent with K_PRS = 1.79. The offset t_0 is dropped when applying it to the supplied model, because there the bias acts for about 10^25 Hubble times before annihilation and the history offset is negligible. That is an extrapolation, not a measurement.
* eps_gw at annihilation: the scaling efficiency of wall_gw.json (0.481, kinetic convention) times the measured collapse enhancement 1.42 to 1.53 gives **eps_gw,ann = 0.68 to 0.74**, with central value 0.71. This is essentially the originally declared 0.7. In the oscillation-averaged convention with A fixed at A_ref, the residual referred back to tau_ann gives 1.22 to 1.69 directly. The unbiased network itself gives 0.83 to 1.13 at the same time in that convention, so this is the same enhancement on a higher baseline.
* Spectrum: f_peak/H_ann between 0.55 and 0.95 (box-bounded), with a UV slope of -0.56 to -0.73 for the residual, against -1 in the template. The causal f^3 IR remains a supplied input.

Propagated through the same functions with A = 0.807:

| input set | K | eps_gw | f/H | T_ann (MeV) | peak frequency (nHz) | peak Omega h^2 |
|---|---|---|---|---|---|---|
| declared (dimensionful_walls) | 2.4 (A=0.8, C=3) | 0.70 | 1.0 | 30.0 | 3.41 | 2.36e-12 |
| wall_gw lattice update (scaling only) | 1.79 | 0.48 | 0.72 | 34.7 | 2.83 | 0.92e-12 |
| this work, central | 1.95 | 0.71 | 0.72 | 33.3 | 2.71 | 1.60e-12 |
| this work, corners | 1.79 to 1.95 | 0.68 to 0.74 | 0.55 to 0.95 | 33.3 to 34.7 | 2.1 to 3.7 | 1.31e-12 to 1.68e-12 |

Including the annihilation phase therefore raises the lattice-calibrated amplitude by a factor of about 1.4 to 1.8 over the scaling-only update. The result lies between that update and the fully declared template, at 0.55 to 0.71 of the declared peak. The UV tail is flatter than the template's f^-1. With the template's middle-segment and UV slopes, the integrated Omega would therefore be underestimated above the peak. That effect is not propagated here, because the lattice establishes the slope only over about one decade.

**Literature.** Hiramatsu, Kawasaki and Saikawa (arXiv:1002.1555, "Gravitational waves from collapsing domain walls") simulated biased Z2 walls with tensor modes. Kawasaki and Saikawa (arXiv:1102.5628) studied wall GW spectra, and Hiramatsu, Kawasaki and Saikawa (arXiv:1309.5001) gave the scaling efficiency (eps of about 0.7 plus or minus 0.4, the reference calibration already used by dimensionful_walls) and the peak at the Hubble scale. Those works, as summarised in Saikawa's review (arXiv:1703.02576), established a GW peak at about the horizon scale at annihilation, a spectrum falling roughly as f^-1 above it, and the practice of evaluating the scaling-network estimate at t_ann. In that literature the collapse phase changes the amplitude by an O(1) factor rather than by orders of magnitude. This lattice agrees qualitatively on all three points: a box-bounded peak at f/H of order 1, an O(1) enhancement of 1.4 to 1.5, and a decaying UV tail. It differs on the UV slope (-0.6 to -0.7 after annihilation, against -1 during scaling) over the range 0.1<k<pi/2. Our boxes are much smaller than those runs. Whether the flatter residual tail survives at larger N and thinner walls relative to the box is open. On the bias dependence, the literature defines C_ann through t_ann = C_ann A sigma/Delta V. Kawasaki, Saikawa and Sekiguchi (arXiv:1412.0789) calibrate this for axion-like walls, and Babichev and collaborators (arXiv:2504.07902), already cited in the flavor monograph, report a different bias dependence in their real-scalar simulations. Our finding, that p_eff is about 0.25 rather than 0.5 in the window reachable at 192^3, together with a strong dependence on when the bias acts, is another reason not to read the classical exponent off small simulations without controlling the history. The literature numbers quoted here are given only as context, from the cited abstracts and review. They have not been re-derived here.

## 8. Scope and not claimed

Established, within float32 lattice evolution on 192^3 (128^3 control), two seeds:

* the false-fraction and area histories of the biased physical network, and tau_ann for five biases and three criteria;
* p_eff = 0.25 +- 0.02 (1 percent criterion; 0.30 to 0.31 for the softer criteria) in the window sigma/Delta V = 579 to 3472, with a switch-on at tau=40;
* the offset fit K = 1.95 (1.44 to 2.46 by seed), consistent with K_PRS = 1.79;
* a collapse enhancement of the comoving GW energy of 1.42 to 1.53 over the same-seed unbiased network at tau_ann, concentrated at 0.1<k<pi/2;
* a^4 rho_avg constant to 0.5 to 3 percent after annihilation.

Not claimed:

* **p = 1/2 is not confirmed.** The pressure-balance law is neither confirmed nor refuted as an asymptotic statement. The window is short, the walls form late and the bias-to-barrier ratio reaches 0.89.
* No peak position beyond f/H_ann <~ 1, and no peak shift. The IR slope is not measured, and the causal f^3 remains a template input.
* The UV flattening is not established above k = pi/2 or at other wall-width-to-box ratios. It is not propagated into Omega h^2.
* The value of the efficiency inherits the factor of about 1.5 kinetic-versus-averaged convention ambiguity of the box-scale modes. Only the enhancement ratio is convention-free.
* Applying K and the enhancement to the supplied model assumes the small-bias, long-history regime, which is about 25 orders of magnitude away in Delta V/sigma H.
* No backreaction of the GWs or the walls on the expansion, no thermal friction, no scalar-radiation decay channel (the scalar remnants of the collapse are evolved as a free classical field), and no certified integration.
* The switch-on is a numerical device that keeps the bias out of the formation stage. It is not a model of the thermal onset of the bias, h(T), in dimensionful_walls.

## 9. Reproduction

    PYTHONPATH=python OPENBLAS_NUM_THREADS=1 python python/develop_wall_annihilation_gw.py

This analyses the cached series receipts/flavor_cosmology/wall_annihilation_gw_series.json (0.95 MB, sha256 recorded in the receipt) and writes receipts/flavor_cosmology/wall_annihilation_gw.json. The flags --simulate-scan (network-only runs, about 15 minutes on two processes), --simulate-gw (tensor runs, one to two hours on two otherwise free cores, longer when shared) or --simulate regenerate the cache. Then run python scripts/plot_wall_annihilation_gw.py for receipts/flavor_cosmology/wall_annihilation_gw.png. The module is python/perfectpower/wall_annihilation_gw.py (evolve_biased_gw, tt_spectra, annihilation_times, power_law_fit, pressure_balance_tau). Ten tests in python/tests/test_wall_annihilation_gw.py (about 2 s) check the following: the allocation-free stencils against wall_network; the exact minima, Delta V = 4 eps/3 and metastability of the cubic bias; static uniform vacua under the bias; the ramp; reproduction of evolve_physical_gw at eps=0; the kinetic TT part against wall_network.gw_energy_spectrum and the gradient part on a plane wave; constancy of a^4 rho_avg for a free tensor wave against the exact solution; annihilation of a small biased network but not of the unbiased one; and the fit and interpolation helpers.
