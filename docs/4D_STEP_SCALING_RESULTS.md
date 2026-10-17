# SU(2) 4D torus step scaling — results, stage 1 (L/a = 4 -> 8) — 2026-10-17

**Status: Monte Carlo measurement only. Not a proof, not a bound, no Lean consequence.** Stage 1 of `docs/4D_STEP_SCALING_PLAN.md` (rev. 2): formula verification, pipeline validation, SU(2) 4->8, compact U(1) control 4->8. **6->12 and 8->16 have NOT been run** (code, job lists and analysis exist; see "What remains"). With only one lattice pair there is **no continuum extrapolation and no claim of running** (plan rule).

## Setup (what was actually done)
* Action/ensemble: SU(2) Wilson plaquette action, beta = 4/g0^2, **periodic boundary conditions in all 4 directions** (no twist, no background field), L^4 torus. Update: Kennedy–Pendleton heatbath + 4 microcanonical overrelaxation sweeps per sweep. Hot start unless noted; 500 thermalisation sweeps discarded; measurements every 5 sweeps.
* Flow: Wilson flow, Lüscher RK3, step eps = 0.02 (check eps = 0.01); E = clover energy density; also plaquette E (stored); Q = clover topological charge of the flowed field. t = c^2 L^2/8, c in {0.3, 0.4} (c = 0.5 stored for Q at L<=8).
* Coupling: g^2_GF = t^2 <E> / N. Two normalisations, both reported: **"cont N"** = Fodor et al. periodic-torus continuum N(c) (arXiv:1208.1051) — this *defines* the scheme; **"tree-impr. N"** = lattice tree-level N_hat(c, L/a) (non-zero modes: exact lattice momentum sum for Wilson flow + clover E; zero-mode term at its continuum value (N^2-1)c^4/64 — an approximation). They share the same continuum limit; they differ by O(a^2).
* Step scaling: fit 1/g^2 - beta/4 = sum_(m<=M) c_m (4/beta)^m (Fodor et al. eq. (36) analogue, M = 2 and 3) at each L over 9 betas {2.6, 2.8, 3.0, 3.2, 3.4, 3.6, 3.9, 4.3, 5.0}; solve g^2_GF(L=4, beta*) = u; Sigma(u) = g^2_GF(L=8, beta*) from the L=8 fit at the same beta*. Errors: Gaussian bootstrap (600–1000 resamplings) of the per-ensemble means with their Gamma-method errors (Wolff windowing), i.e. **statistical + beta-interpolation, nothing else**. The M = 2 vs 3 difference is the fit-form systematic.
* Statistics: L=4: 4000 measurements per beta (sep 5 sweeps); L=8: 1200 per beta (beta=3.4 hot: 1200 + cold start 600).

## Formula verification (details in the plan's changelog)
* t = c^2L^2/8 (c = sqrt(8t)/L), N(c) = 3(N^2-1)/(128 pi^2)(1+delta(c)), delta = -pi^2c^4/3 + theta_3(e^(-1/c^2))^4 - 1: Fodor–Holland–Kuti–Nógrádi–Wong, **arXiv:1208.1051** eqs. (2),(3),(31),(32). Infinite-volume E(t) normalisation 3(N^2-1)g^2/(128 pi^2 t^2): Lüscher **arXiv:1006.4518** (quoted in 1301.4388 eq. (5)). Fritzsch–Ramos **arXiv:1301.4388** is the Schrödinger-functional version — **not** the periodic torus used here (different N); twisted torus: Ramos **arXiv:1308.4558**.
* b0 = 11/(24 pi^2) for SU(2) **correct** (11N/(48 pi^2); cross-check Fodor et al. eq. (34): b_1 = 22/3 -> 22/3/(16 pi^2) = b0). 1/Sigma = 1/u - 2 b0 ln 2 **correct** with u = g^2; 2 b0 ln 2 = 0.064378. Corrected in the plan: two-loop comparison is only indicative (b_2 not universal for this zero-mode scheme, Fodor et al. Sect. 4); explicit N(c) added; abelian normalisation for U(1) added; U(1) transition beta_T = 1.0111331(21) (hep-lat/0210010).

## Pipeline validation
* **Tree level (SU(2))**, beta = 40, 80, 160, t^2<E>/(N_hat g0^2) extrapolated to g0^2 -> 0: L=4: c=0.3 1.030, c=0.4 1.027, c=0.5 0.975; L=8: c=0.3 1.012, c=0.4 1.000 (c=0.5 0.88, noisy: only 200 correlated measurements). Statistical errors on single points 0.4–2%, so agreement is at the 1–3% level; the L=4 excess is plausibly the unmodelled lattice zero-mode correction in N_hat. Small run (200 meas, sep 5), not a precision test.
* **Free U(1) limit** (beta = 40, 300 meas): t^2<E> beta/N_hat_U(1) = 1.012(7), 1.012(10), 1.010(12) (L=4, c=0.3/0.4/0.5); 1.001(6), 0.993(9), 0.987(13) (L=8).
* **Flow step size**: max relative difference of E(t) between eps = 0.01 and 0.02 over the sampled configurations: <= 3.5e-5 (L=4), <= 6.3e-6 (L=8) in every production ensemble (column below). Also lattice tree-level N_hat/N(cont) = 0.591, 0.788 (L=4, c=0.3, 0.4) and 0.929, 0.961 (L=8): L=4 has 40% / 21% tree-level cutoff effect in the continuum-normalised coupling.
* Plaquette against independent Metropolis (same staple) at beta=2.3, L=4: 0.6096(15) vs 0.612–0.617(3). Staple-vs-direct-plaquette identity checked to 1e-12.

## SU(2) results, 4 -> 8 (statistical + interpolation errors only)
**Tree-improved normalisation (the meaningful one at a/L = 1/4):**

| c | u | beta*(L=4) | Sigma (M=2) | Sigma (M=3) | 1/u-1/Sigma (M=3) | one-loop 2 b0 ln2 | Sigma 1-loop | Sigma 2-loop ref |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 1.30 | 4.525 | 1.4448(22e-4) | 1.4445(22e-4) | 0.0769(11e-4) | 0.0644 | 1.4187 | 1.4234 |
| 0.3 | 1.60 | 3.944 | 1.8355(22e-4) | 1.8411(29e-4) | 0.0818(9e-4) | 0.0644 | 1.7837 | 1.7921 |
| 0.3 | 2.00 | 3.447 | 2.4084(31e-4) | 2.4133(34e-4) | 0.0856(6e-4) | 0.0644 | 2.2956 | 2.3108 |
| 0.3 | 2.40 | 3.123 | 3.0562(47e-4) | 3.0514(49e-4) | 0.0889(5e-4) | 0.0644 | 2.8386 | 2.8630 |
| 0.4 | 1.30 | 4.590 | 1.4327(38e-4) | 1.4307(39e-4) | 0.0703(19e-4) | 0.0644 | 1.4187 | 1.4234 |
| 0.4 | 1.60 | 4.031 | 1.8048(37e-4) | 1.8107(46e-4) | 0.0727(14e-4) | 0.0644 | 1.7837 | 1.7921 |
| 0.4 | 2.00 | 3.553 | 2.3374(46e-4) | 2.3456(56e-4) | 0.0737(10e-4) | 0.0644 | 2.2956 | 2.3108 |
| 0.4 | 2.40 | 3.240 | 2.9220(68e-4) | 2.9227(68e-4) | 0.0745(8e-4) | 0.0644 | 2.8386 | 2.8630 |

**Continuum normalisation (cutoff effects dominate; shown for completeness, do not read as running):**

| c | u | beta*(L=4) | Sigma (M=2) | Sigma (M=3) | 1/u-1/Sigma (M=3) | one-loop 2 b0 ln2 | Sigma 1-loop | Sigma 2-loop ref |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 1.00 | 3.809 | 1.8294(21e-4) | 1.8267(28e-4) | 0.4526(8e-4) | 0.0644 | 1.0688 | 1.0710 |
| 0.3 | 1.30 | 3.272 | 2.5219(34e-4) | 2.5240(35e-4) | 0.3730(5e-4) | 0.0644 | 1.4187 | 1.4234 |
| 0.3 | 1.60 | 2.942 | 3.3332(52e-4) | 3.3458(70e-4) | 0.3261(6e-4) | 0.0644 | 1.7837 | 1.7921 |
| 0.3 | 2.00 | 2.667 | 4.7452(142e-4) | 4.7467(138e-4) | 0.2893(6e-4) | 0.0644 | 2.2956 | 2.3108 |
| 0.4 | 1.00 | 4.663 | 1.3396(37e-4) | 1.3380(39e-4) | 0.2526(22e-4) | 0.0644 | 1.0688 | 1.0710 |
| 0.4 | 1.30 | 3.958 | 1.7997(36e-4) | 1.8021(46e-4) | 0.2143(14e-4) | 0.0644 | 1.4187 | 1.4234 |
| 0.4 | 1.60 | 3.526 | 2.2895(45e-4) | 2.2931(54e-4) | 0.1889(10e-4) | 0.0644 | 1.7837 | 1.7921 |
| 0.4 | 2.00 | 3.157 | 3.0092(73e-4) | 3.0101(75e-4) | 0.1678(8e-4) | 0.0644 | 2.2956 | 2.3108 |

Reading, without overclaiming:
* Sigma > u in all cases, as asymptotic freedom requires, but with L/a = 4 -> 8 the lattice artifacts are of the same order as the effect. The continuum-N Sigma exceeds the one-loop value by factors 1.3–2 because g^2_GF(L=4) is depressed by the tree-level cutoff factor 0.59 (c=0.3) / 0.79 (c=0.4). With tree-level improvement the measured shift 1/u - 1/Sigma = 0.070–0.090 is 9–40% above the one-loop 0.0644, with a clear trend: c=0.3 rises with u (0.077 -> 0.089), c=0.4 is flatter (0.070 -> 0.075).
* **c = 0.3 and c = 0.4 disagree beyond the statistical errors** (e.g. u = 2.0: Sigma = 2.413(3) vs 2.346(6); shifts 0.0856(6) vs 0.0737(10)). Per plan check 6 this is a discretisation/finite-volume systematic, not noise. The scatter between the two schemes (about 0.01–0.015 in the shift) is the honest uncertainty at this a/L; it is larger than the statistical errors by an order of magnitude and comparable to the difference between the measured shift and the one-loop value.
* The two-loop line (Sigma_2loop) differs from one-loop by < 1.1% and is indicative only (see plan changelog). Data cannot discriminate.
* **Verdict for this pair: consistent in sign and rough size with one-loop asymptotic freedom (shift 0.07–0.09 vs 0.064), but not a quantitative confirmation; the continuum limit has not been taken. Inconclusive on size, no claim of running from a single pair.**
* Beta interpolation: chi^2/dof of the fits 0.2–3.1 (M=2) / 0.3–0.6 (M=3); M=2 for L=8 is marginal for c=0.3 (3.1), M=3 fine. Targets u = 1.3, 1.6, 2.0, 2.4 lie inside the measured u range (L=4 tree-impr. u from 1.14 to 4.2); beta* = 3.1–4.6 (L=4).

## Autocorrelation, thermalisation, topology
Per-ensemble table (L=4 and 8; errors in last digits; `tau_int g2` is the Gamma-method value for the g^2_GF series sampled every 5 sweeps):

| run | nmeas | g2_GF c=0.3 (cont N) | g2_GF c=0.3 (tree-impr. N) | g2_GF c=0.4 (cont N) | g2_GF c=0.4 (tree-impr.) | tau_int g2 [sweeps] | plaq tau_int [sweeps] | half-sample z | max rel dE (eps .01 vs .02) | max abs Q (c=0.4) | rounded-Q changes |
|---|---|---|---|---|---|---|---|---|---|---|---|
| su2_L4_b2.60 | 4000 | 2.1351(36e-4) | 3.6109(61e-4) | 3.3316(87e-4) | 4.2270(110e-4) | <= 2.5 (unresolved) | 1.02 | +1.3 | 9.5208e | 0.169 | 0 |
| su2_L4_b2.80 | 4000 | 1.7844(28e-4) | 3.0178(47e-4) | 2.6752(64e-4) | 3.3942(81e-4) | <= 2.5 (unresolved) | 0.92 | +0.3 | 1.23868 | 0.0628 | 0 |
| su2_L4_b3.00 | 4000 | 1.5378(25e-4) | 2.6008(41e-4) | 2.2445(54e-4) | 2.8478(68e-4) | <= 2.8 (unresolved) | 0.90 | +0.2 | 1.52593 | 0.0232 | 0 |
| su2_L4_b3.20 | 4000 | 1.3527(20e-4) | 2.2877(34e-4) | 1.9408(43e-4) | 2.4625(55e-4) | <= 2.5 (unresolved) | 0.79 | +1.2 | 1.68538 | 0.0162 | 0 |
| su2_L4_b3.40 | 4000 | 1.2125(18e-4) | 2.0506(30e-4) | 1.7179(37e-4) | 2.1797(48e-4) | <= 2.5 (unresolved) | 0.82 | +0.4 | 2.18815 | 0.0131 | 0 |
| su2_L4_b3.40_cold | 1500 | 1.2071(32e-4) | 2.0415(54e-4) | 1.7063(61e-4) | 2.1649(77e-4) | <= 3.2 (unresolved) | 0.74 | -2.1 | 1.83658 | 0.0108 | 0 |
| su2_L4_b3.60 | 4000 | 1.0972(16e-4) | 1.8556(26e-4) | 1.5360(31e-4) | 1.9489(40e-4) | <= 2.5 (unresolved) | 0.80 | -0.3 | 1.91401 | 0.0131 | 0 |
| su2_L4_b3.90 | 4000 | 0.9630(13e-4) | 1.6287(23e-4) | 1.3345(28e-4) | 1.6932(36e-4) | <= 2.5 (unresolved) | 0.73 | -1.6 | 2.34973 | 0.00793 | 0 |
| su2_L4_b4.30 | 4000 | 0.8294(11e-4) | 1.4027(19e-4) | 1.1357(23e-4) | 1.4410(29e-4) | <= 2.5 (unresolved) | 0.74 | -0.4 | 2.35378 | 0.0072 | 0 |
| su2_L4_b5.00 | 4000 | 0.6667(9e-4) | 1.1276(15e-4) | 0.9012(18e-4) | 1.1435(23e-4) | <= 2.6 (unresolved) | 0.69 | +2.7 | 3.48793 | 0.00459 | 0 |
| su2_L8_b2.60 | 1200 | 5.3334(169e-4) | 5.7436(182e-4) | 6.4451(373e-4) | 6.7079(388e-4) | <= 2.5 (unresolved) | 1.03 | +2.1 | 1.97586 | 1.25 | 26 |
| su2_L8_b2.80 | 1200 | 3.9365(102e-4) | 4.2393(110e-4) | 4.4854(201e-4) | 4.6683(209e-4) | <= 2.5 (unresolved) | 0.94 | +0.5 | 2.14299 | 0.00688 | 0 |
| su2_L8_b3.00 | 1200 | 3.1616(73e-4) | 3.4047(79e-4) | 3.5012(144e-4) | 3.6440(150e-4) | <= 2.5 (unresolved) | 0.85 | -0.5 | 2.4576e | 0.00637 | 0 |
| su2_L8_b3.20 | 1200 | 2.6553(58e-4) | 2.8596(63e-4) | 2.8898(111e-4) | 3.0077(115e-4) | <= 2.5 (unresolved) | 0.79 | -0.0 | 2.35795 | 0.00368 | 0 |
| su2_L8_b3.40 | 1200 | 2.3140(52e-4) | 2.4920(56e-4) | 2.4970(95e-4) | 2.5989(99e-4) | <= 2.5 (unresolved) | 0.69 | +0.9 | 2.28542 | 0.00266 | 0 |
| su2_L8_b3.40_cold | 600 | 2.2990(67e-4) | 2.4758(73e-4) | 2.4692(126e-4) | 2.5699(131e-4) | <= 2.5 (unresolved) | 0.64 | -0.8 | 2.29665 | 0.00317 | 0 |
| su2_L8_b3.60 | 1200 | 2.0437(48e-4) | 2.2009(52e-4) | 2.1877(81e-4) | 2.2769(84e-4) | <= 2.8 (unresolved) | 0.79 | -1.0 | 2.0871e | 0.00228 | 0 |
| su2_L8_b3.90 | 1200 | 1.7468(37e-4) | 1.8812(40e-4) | 1.8580(75e-4) | 1.9338(78e-4) | <= 2.5 (unresolved) | 0.75 | -0.6 | 1.78918 | 0.00156 | 0 |
| su2_L8_b4.30 | 1200 | 1.4645(32e-4) | 1.5772(35e-4) | 1.5456(58e-4) | 1.6086(60e-4) | <= 2.5 (unresolved) | 0.71 | +0.7 | 3.27988 | 0.00119 | 0 |
| su2_L8_b5.00 | 1200 | 1.1397(23e-4) | 1.2274(25e-4) | 1.1894(44e-4) | 1.2379(46e-4) | <= 2.5 (unresolved) | 0.70 | +0.1 | 6.33641 | 0.000964 | 0 |

* **tau_int**: the g^2_GF series at 5-sweep spacing is uncorrelated within errors (tau_int <= 0.5 measurements = 2.5 sweeps, unresolved). The per-sweep plaquette (HB + 4 OR sweeps) gives tau_int = 0.6–1.0 sweeps at L=4 and 0.7–1.0 at L=8 (decreasing with beta). A dedicated sep = 1 run for g^2 itself (jobs `*_tau`) was queued but **not run**; so tau_int for g^2 is an upper bound from the sampling, not a measurement.
* **Thermalisation**: 500 sweeps discarded from hot start; first-half vs second-half z-scores of g^2(c=0.3) lie in -2.2..+2.7 over the L=4/8 ensembles and both c (40 tests, 5 with |z|>2; extremes: su2_L4_b3.40_cold c=0.4, su2_L4_b5.00 c=0.3) — 5 of 40 exceed 2 sigma where ~2 are expected for independent Gaussian noise: mildly more than chance (possible slowly-relaxing zero-mode sector or slightly underestimated errors; not resolved). Errors quoted may therefore be somewhat optimistic. Hot vs cold start at beta = 3.4: L=4 g^2(c=0.3) 1.2125(18) hot vs 1.2071(32) cold (1.5 sigma); L=8 2.3140(52) vs 2.2990(67) (1.8 sigma): both cold values low by 0.5–0.7%, marginal; if real it is a ~0.5% effect, well below the 2–4% fit-form/c systematic.
* **Topology**: L=4: Q (clover, flowed at c=0.4/0.5) stays at Q ~ 0 in every ensemble (max |Q| = 0.17 at beta=2.6 down to 0.005 at beta=5.0, **0 changes of rounded Q**): no Q != 0 configurations occur; this is *absence of weight* (instanton action ~ 2 pi^2 beta >= 50), not algorithmic freezing, but also means the Q != 0 sectors are not sampled and not tested. L=8: Q = 0 for beta >= 2.8 (max |Q| < 0.007); at beta = 2.6 (outside the beta* window, entering only the fit) 13 of 1200 measurements have |Q| ~ 1 (histogram {-1: 9, 0: 1187, +1: 4}), 26 rounded-Q changes, so tunnelling is alive there. Q is not near-integer-valued for flow this short on L=4 (the number is not a calibrated charge); treat "Q ~ 0" as a statement about small-field configurations only. Periodic untwisted torus: no topology freezing problem seen at these couplings and volumes; this will have to be re-checked at 8->16 and larger g^2.
* Step-ratio: s = 2 (L -> 2L) at the same beta.

## Compact U(1) Coulomb-phase control (4 -> 8)
Wilson action S = beta sum(1 - cos theta_p), g0^2 = 1/beta, abelian normalisation N_U(1)(c) (no zero-mode quartic term). beta = 1.2, 1.4, 1.7, 2.2, 3.0 (all > beta_T = 1.0111; plaquette distributions unimodal, excess kurtosis within -0.1..+0.13, no two-state flip-flop seen, L=4 beta=1.2: 4000 measurements; L=4 other: 2000, L=8: 800). Expected: no running, Sigma/u = 1 up to cutoff effects. Table (both c; Sigma/u shown with continuum N and tree-level-improved N; "(Sigma-u)/err" is for continuum N):

| pair | beta | c | u=g2(L) cont-N | g2(2L) cont-N | Sigma/u (cont-N) | Sigma/u (tree-impr. N) | (Sigma-u)/err | g2*beta (L, cont-N) | tau_sw L / 2L |
|---|---|---|---|---|---|---|---|---|---|
| 4->8 | 1.20 | 0.3 | 0.7721(16e-4) | 1.2227(47e-4) | 1.5837(70e-4) | 0.9724(43e-4) | +83.8 | 0.926 | 2.5 / 2.5 |
| 4->8 | 1.20 | 0.4 | 1.0836(35e-4) | 1.2096(71e-4) | 1.1162(75e-4) | 0.8691(59e-4) | +15.5 | 1.300 | 2.5 / 2.5 |
| 4->8 | 1.40 | 0.3 | 0.5824(16e-4) | 0.9137(32e-4) | 1.5689(69e-4) | 0.9634(42e-4) | +82.4 | 0.815 | 2.5 / 2.5 |
| 4->8 | 1.40 | 0.4 | 0.7857(30e-4) | 0.9243(52e-4) | 1.1765(79e-4) | 0.9160(62e-4) | +22.2 | 1.100 | 2.5 / 2.5 |
| 4->8 | 1.70 | 0.3 | 0.4331(11e-4) | 0.6887(27e-4) | 1.5902(74e-4) | 0.9764(45e-4) | +80.2 | 0.736 | 2.5 / 3.1 |
| 4->8 | 1.70 | 0.4 | 0.5748(22e-4) | 0.6975(46e-4) | 1.2136(92e-4) | 0.9450(72e-4) | +23.1 | 0.977 | 3.0 / 3.5 |
| 4->8 | 2.20 | 0.3 | 0.3121(8e-4) | 0.4957(20e-4) | 1.5884(76e-4) | 0.9753(47e-4) | +77.3 | 0.687 | 2.5 / 3.2 |
| 4->8 | 2.20 | 0.4 | 0.4122(14e-4) | 0.5041(32e-4) | 1.2231(89e-4) | 0.9523(69e-4) | +25.1 | 0.907 | 2.5 / 2.8 |
| 4->8 | 3.00 | 0.3 | 0.2162(5e-4) | 0.3449(13e-4) | 1.5953(69e-4) | 0.9796(43e-4) | +86.0 | 0.649 | 2.5 / 2.5 |
| 4->8 | 3.00 | 0.4 | 0.2842(9e-4) | 0.3510(21e-4) | 1.2352(83e-4) | 0.9618(65e-4) | +28.2 | 0.853 | 2.5 / 2.5 |

| L | beta | nmeas | plaq mean | plaq tau_int (sweeps) | plaq min | plaq max | excess kurtosis (bimodal if < ~ -1.2) |
|---|---|---|---|---|---|---|---|
| 4 | 1.20 | 4000 | 0.75314(12e-5) | 0.8 | 0.6902 | 0.7994 | +0.03 |
| 8 | 1.20 | 800 | 0.75165(7e-5) | 0.8 | 0.7373 | 0.7623 | +0.07 |
| 4 | 1.40 | 2000 | 0.79761(12e-5) | 0.7 | 0.7599 | 0.8337 | -0.02 |
| 8 | 1.40 | 800 | 0.79643(5e-5) | 0.7 | 0.7854 | 0.8070 | +0.13 |
| 4 | 1.70 | 2000 | 0.83884(10e-5) | 0.7 | 0.8076 | 0.8722 | -0.10 |
| 8 | 1.70 | 800 | 0.83797(4e-5) | 0.7 | 0.8300 | 0.8451 | +0.06 |
| 4 | 2.20 | 2000 | 0.87864(7e-5) | 0.6 | 0.8532 | 0.9006 | +0.04 |
| 8 | 2.20 | 800 | 0.87826(3e-5) | 0.7 | 0.8731 | 0.8845 | -0.07 |
| 4 | 3.00 | 2000 | 0.91285(5e-5) | 0.6 | 0.8949 | 0.9286 | +0.02 |
| 8 | 3.00 | 800 | 0.91258(2e-5) | 0.6 | 0.9079 | 0.9174 | +0.11 |

Result: with **tree-improved N the ratio Sigma/u is 0.96–0.98 (c = 0.3) and 0.87–0.96 (c = 0.4)**, i.e. not exactly 1: deviations of 2–4% (c=0.3) and 4–13% (c=0.4, worst at beta=1.2, near the transition) are many sigma (errors 0.4–1%). With continuum N the ratio is 1.57–1.60 (c=0.3), 1.12–1.24 (c=0.4) purely from the tree-level cutoff factors. Interpretation: **at a/L = 1/4 the cutoff effects of this observable in a theory with no running are 2–13% in Sigma/u, the same order as the 9–18% effect that one-loop running predicts for Sigma/u - 1 at u = 1.3–2.4**. The U(1) control therefore says the 4->8 SU(2) numbers cannot by themselves be attributed to running; the SU(2) excess Sigma/u - 1 (one-loop: +9% at u = 1.3 ... +18% at u = 2.4; measured tree-improved: +11% ... +27%) is larger than the U(1) artifact, which has the opposite sign (U(1): Sigma/u < 1), but the artifacts of the two theories need not coincide. The control does not fail catastrophically (no spurious running of the SU(2) size), and it does not confirm the pipeline at the percent level at this a/L. Remember also the free-field U(1) check at beta = 40 gave Sigma/u = 0.99 +- 0.01 (consistent with 1), and note the U(1) beta-dependence of the deficit is not simply ~1/beta.

## Resources (Mac darthurtron.local, strict rules)
* hw.ncpu = 16, hw.memsize = 64 GiB. Before runs: load averages 33.2/32.2/25.9 (first check 01:05 PDT; higher than ncpu all session because of other tenants' jobs: Pantheon python workers), memory_pressure "free percentage" 66%, `vm_stat` pages free 4351 (page 16 KiB; free+inactive ~ 22 GiB), AC power, battery 80%.
* Our processes: single-threaded, `nice -n 19`, at most 3 alive; `run_guard.sh` (30 s samples; log `results/resource_guard_log_stage1.log`) SIGSTOPs all but the oldest one process whenever load1 > ncpu (throttle) and all if free memory < 15%. Over the 130 guard samples (01:18–02:23 PDT) load1 ranged **14.4–85.9** (min 14.4 at the very end), free-memory percentage **63–73%** (never < 15%), state throttled-to-1-process in 118/130 samples, running freely in 12. RAM per process: estimated from the data structures (links 32 B x 4 V plus flow arrays; 8^4 ~ 2 MB), not measured with ps; certainly well below the 2 GB cap, total < 0.2 GB. Peak concurrent running processes: 1 (throttled) or up to 3 at load <= 16.
* Disclosure: the initial development tests (compile, tiny self-tests, tree-level and U(1) validation, ~8 min nice-19 CPU in total) and the first 3 minutes of the scout/production jobs ran before/while the guard had started at load 30–40 without the throttle (the first queue was killed when the shell exited, restarted detached with the guard). No Pantheon or other processes were touched.
* Run time: 4 -> 8 production: L=4 ~40 s CPU per beta, L=8 ~4–8 min wall per beta under throttle (about 0.2 s CPU per measurement incl. flow to c=0.4); wall clock for all of stage 1 ~65 min (01:18–02:23 PDT).

## Files
* Code: `simulations/gf_step_scaling/src/{lib.rs,bin/su2gf.rs,bin/u1gf.rs}` (no external crates; build with `CARGO_TARGET_DIR=/Users/darthur/ym_numerics_runs/target cargo build --release --offline`), `analysis/*.py`, `run_guard.sh`, `run_queue.py`.
* Small result tables: `simulations/gf_step_scaling/results/` (ensemble tables, step-scaling CSVs/logs, U(1) control, resource log, stage-1 job list with all seeds/parameters). Raw ensembles (csv per ensemble, per-sweep plaquette series, checkpoints with configs and RNG state) are outside git in `/Users/darthur/ym_numerics_runs/prod/` (reproducible: seeds in `jobs_stage1.txt`; deterministic given binary).

## What remains
1. **6 -> 12** (job list `prod/jobs_stage2.txt` written and partly started: L=6 beta 3.0..5.0, L=12 beta 3.0..5.0 with 600 measurements at sep 10, plus U(1) 6->12): not done; L=12 costs ~1.5 s CPU per measurement-cycle (about 15 min per beta).
2. 8 -> 16 (est. 10 s CPU per measurement-cycle at L=16; ~5 h for 6 betas) — only if headroom allows; needed for a constrained (a/L)^2 extrapolation (two pairs fit exactly: no check).
3. Dedicated sep = 1 tau_int runs for g^2 (jobs `*_tau`).
4. Continuum extrapolation (code in `analysis/stepscale.py`, `run_all`) once >= 2, preferably 3, pairs exist.
