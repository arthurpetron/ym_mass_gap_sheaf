# 4D torus step-scaling plan (SU(2)) — DRAFT, not run, not committed
Written 2026-10-17 by YM Bot at darthur's request. Numerical measurement plan only; no Lean claim follows from it.

## Purpose
Measure the SU(2) running coupling on the periodic 4D torus (the same Z4 torus the Lean files use) and compare it with one-loop asymptotic freedom. This gives a measured schedule for how fast g^2 changes with scale, to compare against the RG error budgets. It does not prove asymptotic freedom, a continuum limit, or a mass gap.

## Observable
Gradient-flow coupling with periodic boundary conditions (Fodor–Holland–Kuti–Nógrádi–Wong style):
g^2_GF(L) = N(c) * t^2 <E(t)> at t = c^2 L^2 / 8, with E the Wilson-flow action density, c in {0.3, 0.4} (two values as a systematic check), N(c) fixed so g^2_GF = g^2 at tree level on the finite torus. Use the Wilson plaquette action for the ensemble and the Wilson flow action for the flow. Do NOT use the Schrödinger functional (needs non-periodic boundaries, different from the Lean torus).

## Step-scaling function
For scale factor s = 2: fix u = g^2_GF(L) at lattice size L/a, tune beta to hit u, then measure g^2_GF(2L) at the same beta on (2L/a)^4. This gives Sigma(2, u, a/L). The continuum step-scaling function is sigma(2, u) = lim_{a/L -> 0} Sigma.
- Lattice pairs: L/a = 4 -> 8, 6 -> 12, 8 -> 16 (a/L = 1/4, 1/6, 1/8). A 3rd pair is needed to extrapolate in (a/L)^2; add 10 -> 20 only if the first three leave the extrapolation unconstrained.
- Target couplings u: choose about 4 values spanning g^2_GF roughly 1.0–2.5 (final values set after the scouting scan, since the scale at beta is not known in advance).
- Tuning: scan beta on the small lattice, interpolate g^2_GF(beta) with a smooth fit, solve g^2_GF = u, then run the 2L lattice at that beta. Propagate the beta-interpolation error into Sigma.

## Checks (in order of priority)
1. Sanity: the Wilson flow at small t reproduces the known weak-coupling expansion; E(t) is independent of the flow integrator step (compare two step sizes).
2. Autocorrelation and topology: report integrated autocorrelation times for g^2_GF and the topological charge Q. If Q is frozen at the finer lattices, say so and do not average over a frozen sector without flagging it.
3. Asymptotic-freedom sign: Sigma(2,u) should be greater than u for SU(2), and the one-loop prediction is 1/sigma = 1/u - 2 b0 ln 2 with b0 = 11/(24 pi^2) (SU(2), 1/g^2 convention). Compare the measured shift 1/u - 1/Sigma with 2 b0 ln 2 at each u, and with the two-loop version.
4. Continuum limit: extrapolate Sigma in (a/L)^2 at fixed u. Report whether the extrapolation is stable between the three-pair and two-pair fits.
5. Negative control: compact U(1) on the same torus in the Coulomb phase (beta > ~1.01 for the Wilson action; avoid the first-order transition). Pure U(1) has no running at this order, so Sigma(2,u) - u should be consistent with 0. This applies the project's U(1) rule: anything U(1) also does is not evidence for non-abelian behavior.
6. Compare the two values of c: if sigma(2,u) differs between c = 0.3 and 0.4 beyond errors, the difference is a discretization or finite-volume systematic and goes in the error budget.

## What would count as a result
- Positive: statistically clear Sigma > u for SU(2) with measured shifts within error of the one-loop/two-loop prediction and an (a/L)^2 extrapolation that is stable; U(1) control flat.
- Negative or inconclusive: shifts inconsistent with perturbation theory, or extrapolation unconstrained. Report that plainly. Do not claim running from a single lattice pair.
Either way, label it a Monte Carlo measurement with error bars, never a bound.

## Resources and process (standing rules)
- Run on the Mac, not the box (the box has ~2.3 GiB free). 16^4 with SU(2) is ~65,536 sites; start with 4 -> 8 and 6 -> 12 only.
- Cap CPU threads and memory, run targeted jobs, and log free CPU and RAM periodically. Throttle if headroom drops. Put those numbers in every update.
- Save ensembles, configs, seeds, flow parameters and the tuned betas, so any number can be reproduced.
- Output: a table of beta, u, Sigma, error, tau_int, Q statistics, plus a short note. Under docs/ or a numerics folder, uncommitted until darthur approves.

## Open choices for darthur
- Confirm gradient-flow coupling (recommended) versus another scheme.
- Confirm U(1) control is wanted.
- Confirm that YM Numerics should run it, to be told directly in its chat (the Prover would not act on an approval relayed by me).
