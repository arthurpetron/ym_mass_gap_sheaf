# Quadratic source correction in the original plaquette energy

Date: 2026-10-01 UTC. A second explicit test now retains quadratic source
information in the original Young energy estimate. The complete projected
terminal source, plaquette, product heat and odd partition are unchanged.
This supplies a finite estimate under explicit cutoff guards, not the
missing comparison with interacting variance along a physical scaling family.

## Checked estimate

Let f be the fundamental plaquette character, q the complete projected
terminal source, H product quaternion Haar integration, K the original
two-slice product heat, and P its one-slice action. Define

    A = H[q^2],  F = H[q^2*f^2],  R = (1-w^32)*(F-A),
    D = H_xy[K*(Delta q*Delta f)^2],
    E = original energy,  C = original plaquette channel cost.

The source mass declaration uses H[(q*q)*1]; its equality with H[q^2]
is proved explicitly in the new argument. The heat image of f^2 is
1+w^32*(f^2-1) in the supported Haar pairings. For
s=(q_x+q_y)*(f_x+f_y), exact multiplication gives

    Delta q*Delta f*s = Delta(q^2)*Delta(f^2),
    H_xy[K*Delta q*Delta f*s] = 2*R,
    H_xy[K*s^2] <= 64*A.

Cauchy--Schwarz gives R^2<=16*A*D. Combining this with the existing
identity 4*E+D=2*C proves

    64*A*E + R^2 <= 32*A*C.

The final theorem multiplies by the square of the reciprocal of the SAME
positive original odd partition Z:

    64*(A/Z)*(E/Z) + (R/Z)^2 <= 32*(A/Z)*(C/Z).

No reciprocal of A or R, positivity of R, or stationary-source equation
is assumed. The guards include 0<w<1, K>=2, headCutoff(w)<=K,
strict spatial padding and membership of the face in the smaller box.
The constants 16, 32 and 64 are numerical; the actual moments, Z and
the cutoff guard still depend on the original parameters.

## Declaration map

- `SU2QuaternionProductHeatSumTest.sumCopy` and `sumTest`:
  `lean/YMGap/Continuum/SU2QuaternionProductHeatSumTest.lean:42` and
  `lean/YMGap/Continuum/SU2QuaternionProductHeatSumTest.lean:45`.
  Their support theorems are at lines 72 and 77.
- `SU2QuaternionProductHeatSumTest.sumTest_square_le_rawSourceMass`:
  `lean/YMGap/Continuum/SU2QuaternionProductHeatSumTest.lean:161`.
  This is the generic test bound given a supplied square cap 4 for f.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.evenResponse`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:73`.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.square_heat_moment`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:77`.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.quadratic_jump_mean`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:111`.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.sourceIncrement_even_square`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:154`.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.padded_terminal_even_square`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:199`.
- `BF4ExactSlabFixedSpatialSourceEvenCancellation.padded_terminal_normalized_even_square`:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceEvenCancellation.lean:239`.

## Remaining mathematical input

The test detects F-A, so the retained square vanishes when F=A.
No theorem here proves a nonzero response for the actual complete terminal
source or a useful fraction of the original channel cost. Moreover, q^2
Haar moments are not the interacting q*Pq moments, and A/Z is not one.
Controlling those actual source moments and their relation to the SAME
centered variance is the next input; additional scalar tests alone do not
supply it. The physical scaling family is still to be justified.

Subsequent checkpoint: the resulting even-only scalar upper budget has a
proved floor 31*(1-w)^2/64 for every raw moment ratio in [0,4]. Source
concentration alone cannot make that formula cubic; see
`audits/AUDIT-EVEN-CORRECTED-BUDGET-FLOOR-2026-10-01.md`. This is not a
lower bound on actual energy.

The preceding odd test and this even test each bound the SAME D. Their
retained squares cannot be added without a joint Gram or orthogonalization
estimate. Neither this bound nor the previous one supplies spatial/spacing
control, continuum survival, a physical mass calibration, or Clay closure.

## Verification boundary

Two final focused checks passed eight printed gates, all exactly
{propext, Quot.sound}. No sorry, new axiom, Classical dependency,
native_decide, noncomputable declaration or canonical field was introduced.
A parallel source reviewer checked the constants, original source and
normalization; only the main agent compiled.

The monitored checks used one worker, a 20 GiB worker ceiling, a 12 GiB
OS reserve and dynamic pressure monitoring. Preflight found no competing
compiler/runner and reported 90 percent memory free. No full root build,
tree audit or guard was run. Root imports were registered but not checked
as an aggregate. The canonical chart state is unchanged and was not printed.

Final log SHA-256 values, under `/tmp/`:

- `ym-product-heat-sum-test-20261001.log`:
  `4130116c5923b99f28a43720c20673d704c60a377cc0d281f5d1f7bf3eb42125`.
- `ym-source-even-cancellation-20261001.log`:
  `7de8fb04f393c1fe6c9117252c05ba88eb13ced79a334e9eb722124c151395f4`.
