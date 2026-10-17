# SU(2) 4D torus step scaling — results, stages 1–2 (L/a = 4->8, 6->12, 8->16) — 2026-10-17

**Status: Monte Carlo measurement only. Not a proof, not a bound, no Lean consequence.** `docs/4D_STEP_SCALING_PLAN.md` (rev. 2): formula verification, pipeline validation, SU(2) 4->8, compact U(1) control 4->8 (stage 1, sections below); **stage 2 (at the end): 6->12, 8->16 (three pairs, constrained (a/L)^2 check with 1 dof), sep=1 tau_int, U(1) 6->12.** The stage-1 sections state 'one pair, no continuum claim': that remains true for stage 1 only; see stage 2 for what the three-pair check does and does not show.

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
* Our processes: single-threaded, `nice -n 19`, at most 3 alive; `run_guard.sh` (30 s samples; log `results/resource_guard_log_stage1.log`) SIGSTOPs all but the oldest one process whenever load1 > ncpu (throttle) and all if free memory < 15%. Over the 130 guard samples (01:18–02:23 PDT) load1 ranged **14.4–85.9** (min 14.4 at the very end), free-memory percentage **63–73%** (never < 15%), state throttled-to-1-process in 118/130 samples, running freely in 12. RAM per process (stage 1, L<=8): estimated, not measured; stage-2 `ps` measurements show the true footprint is larger than my stage-1 estimate (~380–420 MB RSS per process at L=16, see Stage 2), still under the 2 GB cap for all 3 processes together. Peak concurrent running processes: 1 (throttled) or up to 3 at load <= 16.
* Disclosure: the initial development tests (compile, tiny self-tests, tree-level and U(1) validation, ~8 min nice-19 CPU in total) and the first 3 minutes of the scout/production jobs ran before/while the guard had started at load 30–40 without the throttle (the first queue was killed when the shell exited, restarted detached with the guard). No Pantheon or other processes were touched.
* Run time: 4 -> 8 production: L=4 ~40 s CPU per beta, L=8 ~4–8 min wall per beta under throttle (about 0.2 s CPU per measurement incl. flow to c=0.4); wall clock for all of stage 1 ~65 min (01:18–02:23 PDT).

## Files
* Code: `simulations/gf_step_scaling/src/{lib.rs,bin/su2gf.rs,bin/u1gf.rs}` (no external crates; build with `CARGO_TARGET_DIR=/Users/darthur/ym_numerics_runs/target cargo build --release --offline`), `analysis/*.py`, `run_guard.sh`, `run_queue.py`.
* Small result tables: `simulations/gf_step_scaling/results/` (ensemble tables, step-scaling CSVs/logs, U(1) control, resource log, stage-1 job list with all seeds/parameters). Raw ensembles (csv per ensemble, per-sweep plaquette series, checkpoints with configs and RNG state) are outside git in `/Users/darthur/ym_numerics_runs/prod/` (reproducible: seeds in `jobs_stage1.txt`; deterministic given binary).

<!-- STAGE2 BEGIN -->
## Stage 2 (2026-10-17, 06:32–09:29 PDT): 6 -> 12 and 8 -> 16 (SU(2)); U(1) control 6 -> 12; sep = 1 tau_int
**MC measurement only; not a proof, not a bound, no Lean consequence. All production runs finished; this section is final for stage 2.**

Data added: **L = 6**: beta = 3.0, 3.2, 3.4, 3.6, 3.8, 4.1, 4.5, 5.0, 4000 measurements (sep 5; 500 therm), plus a cold start at beta = 3.6 (1500 meas). **L = 12**: the same 8 betas, 600 meas, sep 10 sweeps, 300 therm. **L = 16**: beta = 3.4, 3.6, 3.9, 4.3, 5.0 (same betas as the L = 8 ensembles), 400 meas, sep 10, 300 therm, c in {0.3, 0.4} only. Dedicated **sep = 1** runs for tau_int: SU(2) L=4 (beta 3.2, 4000 meas), L=6 (3.6, 3000), L=8 (3.2, 2500), L=12 (3.6, 500); U(1) L=4/6/8/12 (beta 1.7, 4000/3000/2500/600). U(1) 6->12 control at beta = 1.2, 1.4, 1.7, 2.2, 3.0 (L=6: 1500 meas, L=12: 400 meas). Same action, flow, observable, fits and error analysis as stage 1. Reproduce: `analysis/stepscale.py RUNDIR OUT --pairs 4:8,6:12,8:16 --norm lat|cont`, `analysis/make_tables.py`, `analysis/continuum_check.py`, `analysis/ensemble_table.py`, `analysis/u1_control.py` (outputs in `results/stage2_6to12/` (interim) and `results/stage3_8to16/` (final)).

### Step scaling with the tree-improved normalisation: 4->8, 6->12, 8->16
Notation: (xx) = error in the last digits (statistical + beta-interpolation bootstrap; Gamma-method errors per ensemble); M = fit order of the beta interpolation (M=2 vs M=3 spread = fit-form systematic). For 8->16 the solved beta* are 4.82/4.86 (u = 1.3), 4.26/4.31 (1.6), 3.78/3.84 (2.0), 3.46/3.52 (2.4) for c = 0.3/0.4; the lowest L=16 beta is 3.4, so u = 2.4 is at the lower edge of the fitted beta range (no extrapolation, but little room). 8->16 uses **5 betas, 400 measurements each (errors 2x larger than 6->12)**.

| c | pair | u | beta* (L) | Sigma (M=2) | 1/u-1/Sigma (M=2) | 1/u-1/Sigma (M=3) | one-loop 0.0644 ratio (M=2) | chi2/dof L, 2L (M=2) |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 4->8 | 1.3 | 4.525 | 1.4448(23) | 0.0771(11) | 0.0769(11) | 1.20 | 0.2, 3.1 |
| 0.3 | 4->8 | 1.6 | 3.944 | 1.8355(21) | 0.0802(6) | 0.0818(8) | 1.25 | 0.2, 3.1 |
| 0.3 | 4->8 | 2.0 | 3.447 | 2.4084(30) | 0.0848(5) | 0.0856(6) | 1.32 | 0.2, 3.1 |
| 0.3 | 4->8 | 2.4 | 3.123 | 3.0562(45) | 0.0895(5) | 0.0889(5) | 1.39 | 0.2, 3.1 |
| 0.3 | 6->12 | 1.3 | 4.715 | 1.4195(28) | 0.0648(14) | 0.0648(14) | 1.01 | 1.4, 0.4 |
| 0.3 | 6->12 | 1.6 | 4.148 | 1.7883(26) | 0.0658(8) | 0.0657(11) | 1.02 | 1.4, 0.4 |
| 0.3 | 6->12 | 2.0 | 3.664 | 2.3119(38) | 0.0674(7) | 0.0674(7) | 1.05 | 1.4, 0.4 |
| 0.3 | 6->12 | 2.4 | 3.345 | 2.8777(49) | 0.0692(6) | 0.0693(8) | 1.07 | 1.4, 0.4 |
| 0.3 | 8->16 | 1.3 | 4.824 | 1.4205(54) | 0.0653(27) | 0.0649(27) | 1.01 | 0.4, 0.1 |
| 0.3 | 8->16 | 1.6 | 4.262 | 1.7851(50) | 0.0648(16) | 0.0637(22) | 1.01 | 0.4, 0.1 |
| 0.3 | 8->16 | 2.0 | 3.778 | 2.3039(69) | 0.0660(13) | 0.0666(15) | 1.02 | 0.4, 0.1 |
| 0.3 | 8->16 | 2.4 | 3.458 | 2.8699(96) | 0.0682(12) | 0.0684(12) | 1.06 | 0.4, 0.1 |
| 0.4 | 4->8 | 1.3 | 4.591 | 1.4327(39) | 0.0713(19) | 0.0703(20) | 1.11 | 0.4, 2.4 |
| 0.4 | 4->8 | 1.6 | 4.030 | 1.8048(36) | 0.0709(11) | 0.0727(14) | 1.10 | 0.4, 2.4 |
| 0.4 | 4->8 | 2.0 | 3.552 | 2.3374(45) | 0.0722(8) | 0.0737(10) | 1.12 | 0.4, 2.4 |
| 0.4 | 4->8 | 2.4 | 3.241 | 2.9220(65) | 0.0744(8) | 0.0745(8) | 1.16 | 0.4, 2.4 |
| 0.4 | 6->12 | 1.3 | 4.748 | 1.4279(50) | 0.0689(25) | 0.0689(25) | 1.07 | 1.2, 0.3 |
| 0.4 | 6->12 | 1.6 | 4.195 | 1.7954(45) | 0.0680(14) | 0.0677(19) | 1.06 | 1.2, 0.3 |
| 0.4 | 6->12 | 2.0 | 3.722 | 2.3161(63) | 0.0682(12) | 0.0681(13) | 1.06 | 1.2, 0.3 |
| 0.4 | 6->12 | 2.4 | 3.413 | 2.8784(86) | 0.0693(10) | 0.0695(12) | 1.08 | 1.2, 0.3 |
| 0.4 | 8->16 | 1.3 | 4.856 | 1.4340(95) | 0.0719(46) | 0.0716(46) | 1.12 | 0.5, 0.0 |
| 0.4 | 8->16 | 1.6 | 4.308 | 1.7997(86) | 0.0694(27) | 0.0684(39) | 1.08 | 0.5, 0.0 |
| 0.4 | 8->16 | 2.0 | 3.835 | 2.3215(124) | 0.0692(23) | 0.0696(25) | 1.08 | 0.5, 0.0 |
| 0.4 | 8->16 | 2.4 | 3.519 | 2.8944(147) | 0.0712(18) | 0.0716(22) | 1.11 | 0.5, 0.0 |
Two-loop reference (the u^3-truncated series in `stepscale.py`) (indicative only; b2 is not universal in this scheme): 1/u - 1/Sigma = 0.0667, 0.0670, 0.0673, 0.0674 for u = 1.3, 1.6, 2.0, 2.4 (one-loop: 0.0644 independent of u).

Reading:
* **The shift converges with increasing L and approaches the one-loop value.** 4->8: 0.071–0.090; 6->12: 0.065–0.069; 8->16: 0.064–0.072 (c=0.3: 0.0653(27), 0.0648(16), 0.0660(13), 0.0682(12); c=0.4: 0.0719(46), 0.0694(27), 0.0692(23), 0.0712(18)). At c=0.3 the 6->12 and 8->16 shifts agree within <= 1 sigma at every u (e.g. u=2.0: 0.0674(7) vs 0.0660(13)), i.e. no visible change between a/L = 1/6 and 1/8 at the 2–3% level; for c=0.4 likewise (0.0682(12) vs 0.0692(23)).
* **c = 0.3 vs c = 0.4 scheme difference** (a pure discretisation/finite-volume effect for the universal one-loop shift): u=2.0: 4->8 0.0126 (0.0848 vs 0.0722), 6->12 0.0008, 8->16 0.0032(26) (0.0660(13) vs 0.0692(23), 1.2 sigma).
* The u dependence of the shift (rising slowly with u, ~0.065 -> 0.068–0.071 for u=1.3 -> 2.4 at the finest pair) is of the size of the (indicative) two-loop term (0.0667 -> 0.0674) within errors. **The data are consistent with one-loop asymptotic freedom plus a small two-loop-like term and cannot discriminate between them; the statistical errors of the finest pair (2–4% at c=0.3, 2.5–6% at c=0.4) are of the size of the one-/two-loop difference (3.6–4.7%).**

### (a/L)^2 continuum check (tree-improved normalisation)
Weighted linear fit of the shift 1/u - 1/Sigma in (a/L)^2 over **three pairs (a/L = 1/4, 1/6, 1/8 of the smaller lattice; the "2L" lattices are 8, 12, 16)**: 3 points, 2 parameters, **1 degree of freedom**: this is the first constrained (a/L)^2 check; the chi2 listed is for 1 dof. The 2-pair fit (6->12, 8->16) is exact (no dof) and unchecked; shown for completeness. L=8 enters two pairs (4->8 and 8->16), so the pair errors are slightly correlated; ignored. (The weighted fit here differs slightly from the unweighted least-squares extrapolation written by `stepscale.py` into `continuum_lat.csv` (e.g. c=0.3, u=1.3: 0.0571(21) weighted vs 0.0592(27) unweighted); both are shown in the CSVs and give the same qualitative picture. Fit uses the bootstrap errors; the errors of the fitted continuum value are therefore statistical + interpolation only; no a/L systematic, no higher-order (a/L)^4 / log terms.)

| c | M | u | shift 4->8 | 6->12 | 8->16 | 3-pair fit a/L->0 | chi2 (1 dof) | slope | 2 finest pairs (exact) | one-loop |
|---|---|---|---|---|---|---|---|---|---|---|
| 0.3 | 2 | 1.3 | 0.0771(11) | 0.0648(14) | 0.0653(27) | 0.0571(21) | 2.2 | 0.32 | 0.0659(63) | 0.0644 |
| 0.3 | 2 | 1.6 | 0.0802(6) | 0.0658(8) | 0.0648(16) | 0.0561(13) | 4.4 | 0.38 | 0.0635(37) | 0.0644 |
| 0.3 | 2 | 2.0 | 0.0848(5) | 0.0674(7) | 0.0660(13) | 0.0558(11) | 7.8 | 0.46 | 0.0641(31) | 0.0644 |
| 0.3 | 2 | 2.4 | 0.0895(5) | 0.0692(6) | 0.0682(12) | 0.0557(9) | 18.6 | 0.54 | 0.0670(28) | 0.0644 |
| 0.3 | 3 | 1.3 | 0.0769(11) | 0.0648(14) | 0.0649(27) | 0.0571(22) | 1.8 | 0.32 | 0.0651(63) | 0.0644 |
| 0.3 | 3 | 1.6 | 0.0818(8) | 0.0657(11) | 0.0637(22) | 0.0543(17) | 1.9 | 0.44 | 0.0611(52) | 0.0644 |
| 0.3 | 3 | 2.0 | 0.0856(6) | 0.0674(7) | 0.0666(15) | 0.0551(12) | 9.1 | 0.49 | 0.0655(36) | 0.0644 |
| 0.3 | 3 | 2.4 | 0.0889(5) | 0.0693(8) | 0.0684(12) | 0.0572(11) | 14.3 | 0.50 | 0.0674(29) | 0.0644 |
| 0.4 | 2 | 1.3 | 0.0713(19) | 0.0689(25) | 0.0719(46) | 0.0688(38) | 0.4 | 0.04 | 0.0757(110) | 0.0644 |
| 0.4 | 2 | 1.6 | 0.0709(11) | 0.0680(14) | 0.0694(27) | 0.0668(22) | 0.5 | 0.06 | 0.0711(63) | 0.0644 |
| 0.4 | 2 | 2.0 | 0.0722(8) | 0.0682(12) | 0.0692(23) | 0.0662(18) | 0.7 | 0.10 | 0.0705(55) | 0.0644 |
| 0.4 | 2 | 2.4 | 0.0744(8) | 0.0693(10) | 0.0712(18) | 0.0671(15) | 2.7 | 0.11 | 0.0736(42) | 0.0644 |
| 0.4 | 3 | 1.3 | 0.0703(20) | 0.0689(25) | 0.0716(46) | 0.0694(38) | 0.3 | 0.01 | 0.0750(110) | 0.0644 |
| 0.4 | 3 | 1.6 | 0.0727(14) | 0.0677(19) | 0.0684(39) | 0.0647(30) | 0.3 | 0.13 | 0.0693(92) | 0.0644 |
| 0.4 | 3 | 2.0 | 0.0737(10) | 0.0681(13) | 0.0696(25) | 0.0652(20) | 1.2 | 0.13 | 0.0714(59) | 0.0644 |
| 0.4 | 3 | 2.4 | 0.0745(8) | 0.0695(12) | 0.0716(22) | 0.0674(18) | 2.0 | 0.11 | 0.0743(52) | 0.0644 |

What is and isn't tested:
* **c = 0.4**: the linear (a/L)^2 form is acceptable (chi2 = 0.3–2.7 for 1 dof, p >= 0.10) and the continuum shifts are 0.0647(30) – 0.0694(38) (M = 2 and 3 agree; u = 2.0: 0.0662(18) / 0.0652(20); u = 2.4: 0.0671(15) / 0.0674(18)), i.e. 0.1–1.8 sigma above the one-loop 0.0644 and equal to the indicative two-loop reference within errors. Acceptable fit quality with 1 dof is weak evidence only.
* **c = 0.3**: the linear (a/L)^2 fit **fails** (chi2 = 1.8–18.6 for 1 dof, >= 7.8 at u = 2.0 and 2.4 (p < 0.006); the 4->8 pair (a/L = 1/4) is outside the linear regime for this scheme) and its extrapolated values (0.054–0.057, i.e. 11–16% **below** one-loop) must not be quoted. Using only the two finest pairs (exact fit) gives 0.0611(52) – 0.0674(29), consistent with 0.0644 but with no check of the form.
* **Not tested**: any systematic from the neglected higher-order terms, the zero-mode/finite-volume dependence beyond c = 0.3/0.4, the one extrapolation form (linear in (a/L)^2 only; no (a/L)^2 log terms, no tree-level-improved vs unimproved comparison of the extrapolated value other than the continuum-N table below), the fixed 400-meas L=16 statistics, and Q != 0 sectors (not populated, see topology). The conclusion is therefore: **consistent with one-loop asymptotic freedom in the range u = 1.3–2.4 at the 5–10% level for the finest pairs; not a precision measurement; scheme c = 0.3 and c = 0.4 3-pair extrapolations disagree (0.0558(11) vs 0.0662(18) at u = 2.0, ~5 sigma) because the c = 0.3 three-pair fit is not a good description .** The honest summary of the continuum extrapolation is **inconclusive at the level of the two-loop effect (~4%), indicative at the 10% level**.

### Continuum-normalised N (scheme-defining N(c)): 4->8, 6->12, 8->16 (for completeness; cutoff effects dominate)
| c | pair | u | beta* (L) | Sigma (M=2) | 1/u-1/Sigma (M=2) | 1/u-1/Sigma (M=3) | one-loop 0.0644 ratio (M=2) | chi2/dof L, 2L (M=2) |
|---|---|---|---|---|---|---|---|---|
| 0.3 | 4->8 | 1.3 | 3.272 | 2.5219(36) | 0.3727(6) | 0.3730(6) | 5.79 | 15.9, 5.1 |
| 0.3 | 4->8 | 1.6 | 2.951 | 3.3332(52) | 0.3250(5) | 0.3261(6) | 5.05 | 15.9, 5.1 |
| 0.3 | 4->8 | 2.0 | 2.668 | 4.7452(138) | 0.2893(6) | 0.2893(6) | 4.49 | 15.9, 5.1 |
| 0.3 | 6->12 | 1.3 | 4.283 | 1.6317(25) | 0.1564(9) | 0.1557(12) | 2.43 | 2.5, 0.4 |
| 0.3 | 6->12 | 1.6 | 3.803 | 2.0657(33) | 0.1409(8) | 0.1406(9) | 2.19 | 2.5, 0.4 |
| 0.3 | 6->12 | 2.0 | 3.394 | 2.6890(48) | 0.1281(7) | 0.1285(8) | 1.99 | 2.5, 0.4 |
| 0.3 | 6->12 | 2.4 | 3.124 | 3.3788(74) | 0.1207(6) | 0.1210(7) | 1.87 | 2.5, 0.4 |
| 0.3 | 8->16 | 1.3 | 4.609 | 1.5143(47) | 0.1089(21) | 0.1076(25) | 1.69 | 0.6, 0.0 |
| 0.3 | 8->16 | 1.6 | 4.089 | 1.9077(58) | 0.1008(16) | 0.1002(18) | 1.57 | 0.6, 0.0 |
| 0.3 | 8->16 | 2.0 | 3.641 | 2.4723(69) | 0.0955(11) | 0.0965(16) | 1.48 | 0.6, 0.0 |
| 0.4 | 4->8 | 1.3 | 3.951 | 1.7997(35) | 0.2136(11) | 0.2143(14) | 3.32 | 3.5, 3.0 |
| 0.4 | 4->8 | 1.6 | 3.521 | 2.2895(45) | 0.1882(9) | 0.1889(10) | 2.92 | 3.5, 3.0 |
| 0.4 | 4->8 | 2.0 | 3.160 | 3.0092(68) | 0.1677(8) | 0.1678(8) | 2.60 | 3.5, 3.0 |
| 0.4 | 4->8 | 2.4 | 2.923 | 3.8354(96) | 0.1559(7) | 0.1557(9) | 2.42 | 3.5, 3.0 |
| 0.4 | 6->12 | 1.3 | 4.529 | 1.5267(46) | 0.1142(20) | 0.1139(21) | 1.77 | 1.4, 0.3 |
| 0.4 | 6->12 | 1.6 | 4.019 | 1.9246(48) | 0.1054(13) | 0.1049(18) | 1.64 | 1.4, 0.3 |
| 0.4 | 6->12 | 2.0 | 3.585 | 2.4910(73) | 0.0986(12) | 0.0986(12) | 1.53 | 1.4, 0.3 |
| 0.4 | 6->12 | 2.4 | 3.301 | 3.1085(93) | 0.0950(10) | 0.0954(13) | 1.48 | 1.4, 0.3 |
| 0.4 | 8->16 | 1.3 | 4.741 | 1.4833(88) | 0.0951(40) | 0.0944(43) | 1.48 | 0.6, 0.0 |
| 0.4 | 8->16 | 1.6 | 4.215 | 1.8644(93) | 0.0886(27) | 0.0878(36) | 1.38 | 0.6, 0.0 |
| 0.4 | 8->16 | 2.0 | 3.761 | 2.4106(126) | 0.0852(22) | 0.0857(26) | 1.32 | 0.6, 0.0 |
| 0.4 | 8->16 | 2.4 | 3.457 | 3.0154(179) | 0.0850(20) | 0.0852(20) | 1.32 | 0.6, 0.0 |
With the continuum-N normalisation the 8->16 shifts are still 48–69% (c=0.3: 0.0955–0.1089) and 32–48% (c=0.4: 0.0850–0.0951) above the one-loop 0.0644 and still decrease with L (tree-level factor N_hat/N = 0.93 / 0.96 at L=8, 0.97 / 0.98 at L=12, 0.98 / 0.99 at L=16 for c = 0.3 / 0.4), so the 3-pair (a/L)^2 fit is a bad description (chi2 = 85–270 for 1 dof; the extrapolated shifts are unstable under the fit weighting: -0.14 ... -0.16 (unweighted) or -0.007 ... +0.013 (weighted) for c = 0.3, 0.030–0.043 for c = 0.4 — all far from the tree-improved result and from one-loop: **meaningless**). The scheme-defining N(c) gives results only in the limit a/L -> 0; at a/L <= 1/8 the tree-level cutoff effect on this normalisation is still ~4–7% (L=8) and ~1–2% (L=16), and is the reason for the tree-improved normalisation as the primary analysis. This is a statement about the observable's lattice artefacts, not about running.

### Compact U(1) control, 4->8 and 6->12 (no running expected: Sigma/u = 1)
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
| 6->12 | 1.20 | 0.3 | 1.1920(36e-4) | 1.1978(61e-4) | 1.0049(60e-4) | 0.8826(52e-4) | +0.8 | 1.430 | 2.5 / 2.5 |
| 6->12 | 1.20 | 0.4 | 1.2252(62e-4) | 1.1842(90e-4) | 0.9666(88e-4) | 0.8982(82e-4) | -3.8 | 1.470 | 2.7 / 2.5 |
| 6->12 | 1.40 | 0.3 | 0.8690(22e-4) | 0.9300(43e-4) | 1.0702(57e-4) | 0.9401(50e-4) | +12.4 | 1.217 | 2.5 / 2.5 |
| 6->12 | 1.40 | 0.4 | 0.9000(38e-4) | 0.9397(77e-4) | 1.0441(96e-4) | 0.9703(89e-4) | +4.6 | 1.260 | 2.6 / 2.5 |
| 6->12 | 1.70 | 0.3 | 0.6494(16e-4) | 0.7016(39e-4) | 1.0805(65e-4) | 0.9491(57e-4) | +12.3 | 1.104 | 2.5 / 2.6 |
| 6->12 | 1.70 | 0.4 | 0.6815(26e-4) | 0.7033(62e-4) | 1.0321(100e-4) | 0.9591(93e-4) | +3.2 | 1.158 | 2.5 / 2.8 |
| 6->12 | 2.20 | 0.3 | 0.4655(12e-4) | 0.5112(26e-4) | 1.0983(62e-4) | 0.9647(54e-4) | +15.9 | 1.024 | 2.5 / 2.5 |
| 6->12 | 2.20 | 0.4 | 0.4938(20e-4) | 0.5172(42e-4) | 1.0473(95e-4) | 0.9733(88e-4) | +5.0 | 1.086 | 2.5 / 2.5 |
| 6->12 | 3.00 | 0.3 | 0.3217(8e-4) | 0.3573(22e-4) | 1.1108(73e-4) | 0.9757(64e-4) | +15.1 | 0.965 | 2.5 / 3.5 |
| 6->12 | 3.00 | 0.4 | 0.3412(14e-4) | 0.3589(36e-4) | 1.0517(114e-4) | 0.9774(106e-4) | +4.5 | 1.024 | 2.5 / 3.5 |
* With the tree-improved normalisation **6->12 does not look better than 4->8**: Sigma/u = 0.88–0.98 (c = 0.3) and 0.90–0.98 (c = 0.4) for 6->12 vs 0.96–0.98 and 0.87–0.96 for 4->8; the deficit is largest at beta = 1.2 (near the first-order transition at beta_T = 1.0111) and at large beta both pairs give the same ~2% deficit (e.g. beta = 3.0: 0.976(6), 0.977(11) for 6->12 vs 0.980(4), 0.962(7) for 4->8), i.e. **it does not shrink with a/L**, so it is not (only) an (a/L)^2 effect of the tree-level normalisation. With the continuum N the ratio is 0.97–1.11 (6->12) and 1.12–1.60 (4->8).
* **Conclusion for the control: the U(1) theory shows no running-like growth of Sigma (Sigma/u <= 1.11 with continuum N and <= 1 with tree-improved N in all 6->12 cases), but the control does not reach Sigma/u = 1 to the percent level, with residual 2–12% deviations that are not understood** (candidates: non-tree-level (one-loop-like) finite-volume effect of the compact theory at beta <= 3, the treatment of the zero mode in the lattice N, near-transition effects at beta = 1.2). It therefore does not validate the SU(2) pipeline beyond a ~2–5% level at large beta: the SU(2) results above should be read with that uncertainty (it is smaller than the 4->8 SU(2) excess but comparable to the 6->12 and 8->16 uncertainties).
* Plaquette histograms unimodal (excess kurtosis within -0.1 .. +0.17) at all beta and L, no flip-flop in the Coulomb phase (full table in `results/stage3_8to16/u1_control_4to8_6to12.md`).
* U(1) 8->16 was **not run**.

### tau_int, thermalisation, topology
* **tau_int of g^2_GF at sep = 1 sweep** (sweep = 1 heatbath + 4 overrelaxation; units: sweeps; Gamma method, S=1.5). **SU(2)**: L=4 (beta=3.2) 0.75 (c=0.3) / 0.72 (c=0.4); L=6 (3.6) 0.71 / 0.68; L=8 (3.2) 0.69 / 0.75; L=12 (3.6, 500 meas only) 0.82 / 0.93; plaquette 0.7–0.85. tau_int < 1 sweep for all L <= 12 tested: no critical slowing down visible; production series at sep 5/10 are uncorrelated (reported as the 2.5 / 5 floor; for L=16 at beta = 5.0 tau = 7.8 / 7.1 sweeps at sep 10 = 0.78 / 0.71 samples, i.e. consistent with 0.5 within errors of 400 meas). One beta per L only. **U(1)** at beta = 1.7: L=4 0.60 / 0.61, L=6 0.73 / 0.73, L=8 0.86 / 0.91, L=12 1.76 / 2.14 (600 meas; larger statistical error): **tau_int grows with L in the abelian theory (0.6 -> 1.8–2.1 sweeps from L=4 to L=12 at beta = 1.7); statistics too small to give an exponent**. The U(1) production series at sep 5 are still essentially uncorrelated (tau_int ~ 0.5 samples; L=12 beta = 1.7: 2.6–2.8 sweeps vs the 2.5 floor) and the Gamma-method errors account for it.
* **Thermalisation**: L=6 beta=3.6 g^2(c=0.3): hot 1.77936(210), cold-start 1.77506(387), sep-1 hot run 1.77493(291): 0.4–1.0 sigma. For L=16 the first-half/second-half z-scores are -1.8, -1.2, -1.3, -1.2, +0.4 (c=0.3): same sign in 4 of 5 (and -1.9, -0.8, -1.2, -1.3, +0.7 at c=0.4); **checked by discarding the first 100 measurements (1000 sweeps) in addition to the 300 thermalisation sweeps**: g^2(c=0.3) shifts by -0.0007, -0.0048, -0.0001, +0.0050, -0.0047 (0.0–0.8 sigma of the full-sample error, no systematic direction; quarter means fluctuate without trend), so there is no evidence of a thermalisation bias, but the same-sign z-scores are a mild warning and the L=16 errors could be slightly underestimated. Over all 42 SU(2) ensembles (L=4–16, incl. cold starts and the sep-1 runs), the first-half/second-half z-scores satisfy |z| < 2.8; 9 of 84 tests (c = 0.3 and 0.4 counted separately, but highly correlated, so roughly 5 of 42 distinct ensembles) have |z| > 2 where ~2–4 are expected: a mild excess, no clear drift pattern; errors may be slightly optimistic.
* **Topology**: L=6, 12, 16: flowed clover charge Q (c=0.4) stays at zero in every ensemble (max |Q| = 0.013 (L=6, beta=3.0), <= 0.0034 (L=12), <= 0.0007 (L=16)); **no Q != 0 configurations and no tunnelling observed, so no frozen-topology issue arises and the Q != 0 sectors are neither sampled nor tested** (action cost of a charge-1 instanton ~ 2 pi^2 beta >> kT at beta >= 3.4). Same conclusion as stage 1 (the only |Q| ~ 1 configurations occurred at L=8, beta=2.6 outside the target window).
* eps = 0.01 vs 0.02 flow-step check: max relative difference of E(t) <= 1.4e-5 (L=6), <= 6.1e-6 (L=12), <= 5.9e-6 (L=16), all at the measured configurations.

### Resources, stage 2 (Mac darthurtron.local, strict rules)
* **Cores / memory**: hw.ncpu = 16, hw.memsize = 64 GiB; at the start (06:32 PDT) load averages 6.20/6.53/7.07, free memory 77–78%, pages free 211297 (16 KiB pages), AC power, battery 80%.
* **Guard thresholds** (log `results/stage3_8to16/resource_guard_stage2_final.log`): throttle to one process if load1 > 16 (= ncpu), pause all if free memory < 15%. **358 samples (06:32–09:31 PDT): load1 min 4.62, max 26.02, mean 11.5; free-memory 76–80% (never near the 15% floor); 343 samples at full speed, 15 throttled to 1 process (load1 > 16, mostly other processes on the machine); never paused**. Our process count 3 in 317 samples.
* **RAM (measured with `ps` RSS)**: L=16 su2gf 373–418 MB per process (~1.2 GB for 3 concurrent) at peak, L <= 12 smaller; total <= 1.3 GB, under the 2 GB cap. (Corrects the stage-1 'unmeasured estimate <0.2 GB'.)
* **All our processes**: single-threaded, `nice -n 19`, <= 3 alive, detached with `launch_detached.py` (new session), checkpointed (`--ckpt-every`) and resumable; the agent session was interrupted several times, the detached queue/guard survived each time (two L=6 jobs had been resumed once or twice from checkpoints earlier). The guard and queue were stopped at 09:31 (GUARD_STOP): nothing of ours is running now.
* **Wall time** (3 concurrent): L=6 4000 meas ~8 min/beta; L=12 600 meas ~13.5 min/beta; L=16 400 meas ~48–50 min/beta (CPU ~29 min per 225 meas); SU(2) 6->12 data complete ~07:20; 8->16 production 07:44–09:22 (two batches of 3 jobs); U(1) and tau runs ran concurrently; the whole stage-2 queue finished at 09:29 (≈ 3.0 h wall; the sum of per-job elapsed times is 8.8 h, an upper bound on CPU time because of throttling).
* Files: ensemble CSVs (`results/stage3_8to16/su2_ensembles_all.csv`, `u1_ensembles_all.csv`), step-scaling logs/CSVs for both normalisations, job lists with seeds (`results/stage2_6to12/jobs_stage2_ordered.txt`, `jobs_stage3b.txt`), queue log.
<!-- STAGE2 END -->

## What remains / not done
1. **U(1) control at 8->16** and the U(1) tau_int growth with L (600 meas at L=12, one beta) — not run; U(1) is only a sanity control.
2. **More statistics for 8->16** (400 meas/beta, 5 betas): errors 2–4% at u = 1.3–2.4; the one- vs two-loop difference (~4%) cannot be resolved. A 3-pair check exists (this document) but is dominated by the 6->12 and 8->16 errors; a 12->24 pair (not affordable here: 24^4 lattice, extrapolated from the L=16 timing ~7 h per beta per process) or 4x statistics at L=16 would be needed.
3. A c-by-c analysis with tree-level plus one-loop improved normalisation, an (a/L)^2 + (a/L)^2 log fit, and a joint (correlated) fit of the three pairs (L=8 is shared) — not done.
4. Q != 0 sectors (not populated at beta >= 3.4); a dedicated run at smaller beta with topology-resolving observables was not done.
5. Nothing in this study is a proof or a bound; it is a numerical check of the gradient-flow step-scaling function against the perturbative one-loop value.
