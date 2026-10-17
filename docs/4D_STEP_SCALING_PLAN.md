# 4D torus step-scaling plan (SU(2)) — formulas verified against the literature 2026-10-17 (rev. 2); first stage run, see `docs/4D_STEP_SCALING_RESULTS.md`
Written 2026-10-17 by YM Bot at darthur's request; formulas checked and corrected by YM Numerics the same day (see Changelog at the end). Numerical measurement plan only; Monte Carlo / literature only, never a proof or bound; no Lean claim follows from it.

## Purpose
Measure the SU(2) running coupling on the periodic 4D torus (the same Z4 torus the Lean files use) and compare it with one-loop asymptotic freedom. This gives a measured schedule for how fast g^2 changes with scale, to compare against the RG error budgets. It does not prove asymptotic freedom, a continuum limit, or a mass gap.

## Observable
Gradient-flow coupling on the periodic 4D torus (Fodor–Holland–Kuti–Nógrádi–Wong, arXiv:1208.1051; flow definition and E(t) as in Lüscher arXiv:1006.4518):

    g^2_GF(L) = t^2 <E(t)> / N(c),   t = c^2 L^2 / 8   (i.e. c = sqrt(8t)/L),   mu = 1/L.

* Flow: Wilson flow, dV/dt = -g0^2 (d S_w / dV) V with S_w the Wilson plaquette action (so beta = 4/g0^2 for SU(2)); integrated with Lüscher's 3rd-order Runge–Kutta (arXiv:1006.4518; same integrator as Fritzsch–Ramos 1301.4388 App. D, eqs. (147)–(151)).
* E(t) = (1/4) G^a_{mu nu} G^a_{mu nu} = -(1/2) tr G_{mu nu} G_{mu nu}, with G the clover-leaf field strength of the flowed field (the plaquette definition is recorded as a cross-check).
* Normalisation (periodic torus, continuum, SU(N)): N(c) = 3 (N^2-1)/(128 pi^2) * (1 + delta(c)),  delta(c) = -pi^2 c^4/3 + theta_3(e^{-1/c^2})^4 - 1  [= -pi^2 c^4/3 + 8 e^{-1/c^2} + 24 e^{-2/c^2} + ...]  (Fodor et al. eqs. (2),(3),(31),(32); theta_3(q) = sum_n q^{n^2}). The (1+delta) factor contains the exact zero-mode (constant gauge field) integral, which gives the -pi^2 c^4/3 algebraic term. For SU(2): N(0.3) = 0.0069352, N(0.4) = 0.0066348 (infinite-volume value 9/(128 pi^2) = 0.0071240).
* "Tree level on the finite torus" is made precise in two ways, both reported: (i) the continuum-torus N(c) above (defines the scheme; this is what Fodor et al. use); (ii) a lattice tree-level N_hat(c, L/a) computed from the lattice momentum sum for Wilson flow + clover E over the non-zero modes, plus the continuum zero-mode term (N^2-1) c^4/64 (an approximation: the lattice zero-mode integral is not computed). The two differ only by O(a^2) and have the same continuum limit; (ii) removes the leading tree-level cutoff effect. See `simulations/gf_step_scaling/analysis/gfana.py`.
* Boundary conditions: periodic in all four directions, no twist, no background field. NOT the Schrödinger functional (Fritzsch–Ramos arXiv:1301.4388 is the SF version with Dirichlet time boundaries and a different N(c, rho, x0/T); its normalisation must not be used here), and not the twisted-periodic variant (Ramos arXiv:1308.4558: SU(2) pure gauge on a twisted torus, which removes the zero-mode complication; a natural follow-up scheme, not part of this plan).
* Consequences of the periodic torus: (a) the constant-mode (zero-mode) sector is non-perturbative and contributes at the same order as the non-zero modes (hence the exact (N^2-1) matrix integral in N(c)); (b) topological sectors are not frozen out by the boundary conditions and Q is defined only approximately for L/a this small (see results doc); (c) the centre symmetry is unbroken at these volumes but the scheme is a finite-volume scheme only: we measure no infinite-volume quantity.

## Step-scaling function
For scale factor s = 2: fix u = g^2_GF(L) at lattice size L/a, tune beta to hit u, then measure g^2_GF(2L) at the same beta on (2L/a)^4. This gives Sigma(2, u, a/L). The continuum step-scaling function is sigma(2, u) = lim_{a/L -> 0} Sigma.
- Lattice pairs: L/a = 4 -> 8, 6 -> 12, 8 -> 16 (a/L = 1/4, 1/6, 1/8). A 3rd pair is needed to extrapolate in (a/L)^2; add 10 -> 20 only if the first three leave the extrapolation unconstrained.
- Target couplings u: choose about 4 values spanning g^2_GF roughly 1.0–2.5 (final values set after the scouting scan, since the scale at beta is not known in advance).
- Tuning: scan beta on the small lattice, interpolate g^2_GF(beta) with a smooth fit, solve g^2_GF = u, then run the 2L lattice at that beta. Propagate the beta-interpolation error into Sigma.

## Checks (in order of priority)
1. Sanity: the Wilson flow at small t reproduces the known weak-coupling expansion; E(t) is independent of the flow integrator step (compare two step sizes).
2. Autocorrelation and topology: report integrated autocorrelation times for g^2_GF and the topological charge Q. If Q is frozen at the finer lattices, say so and do not average over a frozen sector without flagging it.
3. Asymptotic-freedom sign: Sigma(2,u) should be greater than u for SU(2). One loop (universal, scheme independent): mu dg/dmu = -b0 g^3 with b0 = 11 N/(48 pi^2) = 11/(24 pi^2) = 0.046439 for SU(2); in the g^2 convention L^2 dg^2/dL^2 = b_1 g^4/(16 pi^2) with b_1 = 22/3 (= 16 pi^2 b0), so d(1/g^2)/d ln L = -2 b0 and for s = 2:  1/Sigma = 1/u - 2 b0 ln 2,  2 b0 ln 2 = 0.064378  (equivalently Sigma = u + 2 b0 ln2 u^2 + ...). Compare the measured shift 1/u - 1/Sigma with 0.064378 at each u. Two-loop reference (Fodor et al. eq. (35) with b_1 = 22/3, b_2 = 34 N^2/3 = 136/3):  (Sigma - u)/ln(s^2) = b_1 u^2/(16 pi^2) + (b_1^2 ln(s^2) + b_2) u^3/(16 pi^2)^2.  CAUTION: b_2 is universal only under scheme changes g' = g (1 + O(g^2)); the periodic-torus GF scheme is related to MSbar by g'^2 = g^2 (1 + a_1(c) g + ...), with odd powers from the zero-mode sector (Fodor et al. Sect. 4), so b_2 is NOT guaranteed to be the coefficient of this scheme. The two-loop line is an indicative reference, not a prediction; only the one-loop coefficient is a clean test.
4. Continuum limit: extrapolate Sigma in (a/L)^2 at fixed u. Report whether the extrapolation is stable between the three-pair and two-pair fits.
5. Negative control: compact U(1) on the same torus in the Coulomb phase (Wilson action, first-order confined/Coulomb transition at beta_T = 1.0111331(21) in infinite volume, arXiv:hep-lat/0210010; use beta >= ~1.2 and look at the plaquette history for two-state flip-flops, which are larger on small L). Pure U(1) has no running (no charged matter), so Sigma(2,u) - u should be consistent with 0 up to cutoff effects. This applies the project's U(1) rule: anything U(1) also does is not evidence for non-abelian behavior. Normalisation for the abelian theory (S = beta sum_p (1 - cos theta_p), g0^2 = 1/beta, one "colour", no quartic zero-mode term because [B,B] = 0): N_U(1)(c) = 3/(128 pi^2) (theta_3(e^{-1/c^2})^4 - pi^2 c^4) (non-zero modes only), NOT the SU(2) N(c). A free-field check of the whole pipeline (flow + clover E + normalisation) is the large-beta limit, where g^2_GF must equal 1/beta times the lattice tree-level factor.
6. Compare the two values of c: if sigma(2,u) differs between c = 0.3 and 0.4 beyond errors, the difference is a discretization or finite-volume systematic and goes in the error budget.

## What would count as a result
- Positive: statistically clear Sigma > u for SU(2) with measured shifts within error of the one-loop/two-loop prediction and an (a/L)^2 extrapolation that is stable; U(1) control flat.
- Negative or inconclusive: shifts inconsistent with perturbation theory, or extrapolation unconstrained. Report that plainly. Do not claim running from a single lattice pair.
Either way, label it a Monte Carlo measurement with error bars, never a bound.

## Resources and process (standing rules)
- Run on the Mac, not the box (the box has ~2.3 GiB free). 16^4 with SU(2) is ~65,536 sites; start with 4 -> 8 and 6 -> 12 only.
- Cap CPU threads and memory, run targeted jobs, and log free CPU and RAM periodically. Throttle if headroom drops. Put those numbers in every update.
- Save ensembles, configs, seeds, flow parameters and the tuned betas, so any number can be reproduced.
- Output: a table of beta, u, Sigma, error, tau_int, Q statistics, plus a short note (`docs/4D_STEP_SCALING_RESULTS.md`, code and small tables under `simulations/gf_step_scaling/`). Committed locally on the codex branch only; NOT pushed (a push needs darthur's separate confirmation).

## Open choices for darthur
- Confirm gradient-flow coupling (recommended) versus another scheme.
- Confirm U(1) control is wanted.
- Confirm that YM Numerics should run it, to be told directly in its chat (the Prover would not act on an approval relayed by me). [darthur confirmed in chat on 2026-10-17: run 4->8 and 6->12, commit locally, do not push.]


## Changelog
### rev. 2 — 2026-10-17, YM Numerics (formula verification against the literature)
Verified: t = c^2 L^2/8 with c = sqrt(8t)/L (Fodor et al. 1208.1051, Fritzsch–Ramos 1301.4388 eq. (9),(10) for the same relation); b0 = 11/(24 pi^2) for SU(2) (cross-check: Fodor et al. eq. (34) b_1 = 11N/3 - 4 T(R) N_f/3 gives 22/3 for N = 2, N_f = 0, and 22/3/(16 pi^2) = 11/(24 pi^2)); 1/Sigma = 1/u - 2 b0 ln 2 with u = g^2 (equivalent to Fodor et al. eq. (35) at one loop; the u^3 term (2 b0 ln 2)^2 of the geometric series is exactly their b_1^2 ln(s^2)^2 term); Sigma > u for asymptotic freedom.
Corrections / additions:
1. The plan named no explicit N(c). Added the periodic-torus N(c) = 3(N^2-1)/(128 pi^2)(1 + delta(c)) with delta(c) = -pi^2 c^4/3 + theta_3(e^{-1/c^2})^4 - 1 (Fodor et al. 1208.1051), numerical values for SU(2), and the lattice tree-level variant N_hat.
2. Fritzsch–Ramos 1301.4388 is the Schrödinger-functional gradient-flow coupling (Dirichlet in time, N(c, rho, x0/T) eq. (59)); it is NOT the periodic-torus coupling of this plan. Its normalisation must not be used; it is only cited for the flow/E(t) conventions and the c in [0.3, 0.5] cutoff-effect discussion. The twisted-periodic variant (Ramos 1308.4558) is likewise a different scheme.
3. The two-loop comparison in check 3 was presented as the universal two-loop result. Corrected: b_2 = 34 N^2/3 is universal only for g' = g(1 + O(g^2)); the torus scheme has odd-power terms from the zero modes (Fodor et al. Sect. 4), so the two-loop line is indicative only; one-loop is the clean test.
4. The U(1) control needs its own normalisation N_U(1)(c) (abelian, no zero-mode quartic term) and g0^2 = 1/beta; with the SU(2) N(c) the control would be mis-normalised. Added the infinite-volume transition value beta_T = 1.0111331(21) (hep-lat/0210010) and the warning on small-L flip-flops.
5. Flow integrator, E definition (clover; plaquette as cross-check) and the boundary-condition consequences were not stated; added. Numerical value of 2 b0 ln 2 = 0.064378 added.
6. Status line: draft -> run (first stage). Output location changed from "uncommitted" to "committed locally, not pushed", per darthur's instruction of 2026-10-17.
