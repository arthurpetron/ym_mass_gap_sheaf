# P8: the exact Lean anchor Y_j (read-only from the repo on the Mac, branch codex/full-workspace-snapshot-2026-07-24, HEAD at read time 63ffd6e9; Lean files last touched in 0011f759)

All paths are under `lean/YMGap/Continuum/`.

## Trajectory data (`BF4WilsonAllNomeDyadicSmoothedTrajectory.lean`)
- `side j = 2^j` (`BF4DyadicWilsonSquare.lean:37`). Lattice spacing `2^-j`, so side_j is the same physical length at every scale.
- `M_j = radiusFactor * side j` (`trajRadius`, l.307; `radius`, l.345).
- `trajWidth j = side_j^2 + 1` (l.310). This is the spatial width of the carrier at scale j.
- `DyadicSmoothedTrajectory` (l.329) holds `faces j : List Z4Plaq` (spatial faces in `spatialFaces (trajWidth j)`, no duplicates), coefficients `coeff j : Z4Plaq → Q'`, and the nome schedule.
- `familyVector j` (l.348) = `familyExcitation(... faces j, coeff j)`.
- `state j = Y_j = smoothedCoherentVector (faces, coeff) (M_j)` (l.354).
- `response j n = R_j(n) = B(Y_j, T(n) Y_j)` (l.360).

## The concrete anchor actually used (`paddedZeroMomentumTrajectory`, `BF4WilsonAllNomeShiftedPaddedNondegenerate.lean:251`; AF version `afPaddedZeroMomentumTrajectory`, `BF4WilsonAllNomeAFPaddedTrajectory.lean:303`, same faces/coeff/radius, only `schedule := afNomeSchedule`)
- **radiusFactor = 1, so M_j = side_j.**
- **Faces:** ALL faces of `spatialFaces (side_j^2)`. `spatialFaces_mem_iff` (`BF4ExactSlabFixedSpatialFacePlacement.lean:98`) gives base point (x0,x1,x2) ∈ [0, side_j^2)^3, time coordinate x3 = 0, and plane not containing the time direction x3 (planes 01, 02, 12).
  - That is every spatial plaquette of one timeslice inside a cube of side side_j^2.
  - **Padding:** the cube sits one layer inside the carrier width side_j^2 + 1 (`PathFacesPadded`, l.171).
- **Coefficients:** all **+1** (unit, no signs) (l.255-257: `coeff := fun _ _ => 1`).
- **Observable:** `familyExpression` (`BF4WilsonPlaquetteFamilySourcePin.lean:51`) is the literal sum Σ_p c_p · loop(radius 0, plaquetteLoop p, rep 1): the fundamental Wilson-loop trace of each unsmoothed plaquette. There is no spatial smearing (radius 0).
- **Vacuum subtraction:** `familyExcitation = centeredExcitation x` (`BF4WilsonAllNomePlaquetteFamilyVariance.lean:147`; `BF4WilsonAllNomeCenteredVector.lean:129,152`). The centered vector is x − ⟨x, U⟩U, which lies in `VacuumComplement = {x // B U x = 0}` (`BF4WilsonAllNomeCompletedTime.lean:171`). So **R_x(n) = B(x, T(n) x) is the connected (vacuum-subtracted) correlator** of the zero-momentum plaquette sum.
- **Time box** (`BF4WilsonAllNomeSmoothedCoherentState.lean:164,183,285`):
  - Y = orbitSum(x, timeKernel M), with `timeKernel M` = weights `1/(M+1)` at lags 0..M. It is ONE-SIDED: Y = (M+1)^-1 Σ_{k=0}^{M} T(k) x.
  - Because T is self-adjoint, R_Y(n) = (M+1)^-2 Σ_{a,b=0}^{M} R_x(n+a+b) (`smoothedResponse_orbit_expand`, l.326). The lags add; the maximal lag is 2M+n.
- **The open input** is `PathShiftedWindowSurvival tr θ` (`BF4WilsonAllNomeShiftedWindowSurvival.lean:313`): for all j ≥ 1, θ·R_j(side_j/2) ≤ R_j(side_j+1), with Nat division side/2.

## What is computed here (MC translation)
- **x(t):** the zero-momentum sum over ALL spatial plaquettes (3 planes) on timeslice t of the periodic L^3 lattice (normalization irrelevant). Its connected correlator R_x(n) uses vacuum subtraction (single stream, so E1 is per-stream subtraction); E3d is the subtraction-free check.
- **R_Y(n)** = (M+1)^-2 Σ_{a,b≤M} R_x(n+a+b) with M = side.
- **W** = R_Y(side+1)/R_Y(side//2).

## Ambiguities / mismatches (flagged)
1. **Spatial volume.** Lean's family covers a cube of side side_j^2 inside a carrier of width side_j^2+1 (slab carrier, own boundary). Here the sum runs over the full periodic L^3: L=16 at the beta=2.5 check (Lean would want 4^3/9^3/16^3 for side 2/3/4), and L=48 at beta=2.95 (Lean would want 64^3 for side 8). For a zero-momentum sum the ground-state overlap fraction is volume-independent at large volume, so W should be insensitive. The Lean box with boundaries is not exactly zero momentum.
2. **Time extent.** The Lean carrier has an unbounded semigroup T(n); the lattice is periodic in time. The box needs R_x up to lag 3·side+1 = 25 at side 8, which exceeds Lt/2 = 24 on Lt=48. There R_x(25) := R_x(23) (the periodic image) is used; it enters with weight 1/81 and only in the largest-lag term.
3. **Scale identification.** side_j is tied to the scale j (lattice spacing 2^-j). The MC fixes beta (one spacing) and evaluates several sides on it, so "per supported side" means sides on one lattice, not a true trajectory. The physically matched combinations are beta 2.5 ↔ side 2 and beta 2.95 ↔ side 8 (P4/P5 matching side ≈ 1.5 sqrt(t0)).
4. **Nome schedule.** Irrelevant for the MC: the Wilson action at fixed beta is used. The carrier is heat-kernel (see HEATKERNEL_PLAN.md).
