# Scope: the (r,d) theta-asymptotics build (2026-06-22)

The genuine open frontier of the matched-retune leaf (`GenuineResidualBound`): prove the sharp
discrete local CLT — the box inequalities `DOM` (all k) and `DER` (windowed k≤S) — via the
asymptotics of the `(r,d)` self-fusion theta sums. This document scopes it honestly.

## What must be proved (recap)

With `g_s = bondMovedCoeff N w 2 s` (the p=2 self-fusion), `ρ³=g₁/2g₀`, `u=1−w`, `y_s=u·C₄(s)`:
- **DOM** ⟺ `(Δ²log g)_k ≥ 2logρ + log(1−1/(k+1)²)` (all k; SHARP — near-equality at k=1).
- **DER** ⟺ `δ_k ≤ ½u³(2k+3)` on the active window `k ≤ S(τ)≍τ^{−1/2}` (false in the tail).
Both reduce to sharp control of the consecutive ratio `g_{s+1}/g_s`, hence of the `(r,d)` theta sums
`R_m(k)=∑_{r≥k+1,r≡k+1(2)} r^m σ^{r²}` and `D_m(k)=∑_{|d|≤k−1,d≡k+1(2)} d^m σ^{d²}` (`σ=√w`).

## Hard constraints

1. **No CReal integration** in the substrate — asymptotics must be DISCRETE (sum↔sum, telescoping,
   dyadic), extending the existing `geom_beats_pow` / `Zsum`-partition machinery, NOT Gaussian
   integrals or Euler–Maclaurin-with-∫.
2. **Sharp margins required** — DOM is near-equality (O(u³) margin), so crude two-sided bounds are
   insufficient for DOM; the *second-order* discrete structure is needed. (DER has headroom on the
   window, so it is the easier of the two.)
3. **Parity interleaving** — consecutive modes `s, s+1` sum over OPPOSITE-parity `(r,d)` lattices, so
   the increment `g_{s+1}−g_s` is NOT a single term; this is the deep structural obstacle.
4. **Separated `R_m·D_m` product is exactly false at finite N** (folding + truncation; the
   `ClebschRDReindex` finding); valid only asymptotically/untruncated. The box form
   `bondMovedCoeff_p2_rd` is the exact object; the separation is an asymptotic device.

## Layered decomposition

- **Layer 1 (foundational, PARALLEL, reusable):** two-sided DISCRETE bounds for the theta sums
  `R_m(k)`, `D_m(k)` (m=0,2) — leading order + an explicit error term, via the existing partition /
  `geom_beats_pow` machinery. Reusable Gaussian-theta-sum infrastructure regardless of the CLT.
- **Layer 2 (sequential, HARD):** the consecutive-mode ratio `g_{s+1}/g_s` and the SECOND difference
  `Δ²log g` from Layer 1, handling the parity interleaving. This is where the sharpness lives.
- **Layer 3 (sequential):** assemble DOM (all k) and DER (windowed) from Layer 2; discharge
  `BoxRatioDominance`/`BoxRatioDerivative` ⇒ inhabit `GenuineResidualBound`.

## Honest cost/benefit

- This is a LARGE constructive-analysis build (sharp discrete Gaussian-theta asymptotics, no
  integration, parity interleaving). Layer 1 is bankable reusable infrastructure; Layers 2–3 are
  genuinely hard and uncertain — full DOM/DER closure may take several waves and may not close.
- Per the full Clay audit (`docs/clay-requirements-audit-2026-06-21.md`): even FULLY closing this is
  ONE leaf of ONE oracle (`GenuineResidualBound`) on the honest path. The other three oracles
  (`TrueRGComparison`, `ContinuumLimitData`, `ContinuumOSCarrier`) carry R1 construction, O(4)
  restoration, and non-triviality — the BULK of the Clay distance — and are untouched by this build.
  This build improves the *model-RG* leaf, not the continuum-construction distance.

## Wave 1 (launched): Layer-1 foundation, parallel

- **θR** — tail theta sums `R_m(k)=∑_{r≥k} r^m σ^{r²}` (m=0,2): two-sided bounds (leading + error),
  extending `geom_beats_pow` + the tail modulus. (`RDThetaTail.lean`)
- **θD** — centered theta partial sums `D_m(k)=∑_{|d|≤k} d^m σ^{d²}` (m=0,2): two-sided bounds,
  extending the `Zsum` partition / sum-of-squares machinery to general moment m. (`RDThetaCentered.lean`)

Subsequent waves (Layer 2, then Layer 3) are gated on Wave 1 and on whether the sharp discrete route
is tractable — to be reassessed after Wave 1.
