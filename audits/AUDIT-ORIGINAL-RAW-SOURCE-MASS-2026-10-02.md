# Original raw source mass and explicit cutoff control

## Result and remaining frontier

For every nome 0<w<1, spatial width, K>=headCutoff(w) and positive terminal
depth n+1, the ACTUAL projected source q=P_fringe(V*g_(n+1)) satisfies

    H[q^2] <= B(w,width)*Z,
    B = sourceCapScale/sourceFloorScale,
    sourceCapScale = (spatialCeiling*kineticCap)^2,
    sourceFloorScale = spatialFloor^2*kineticFloor^3.

Z is the SAME original odd partition at depth n+1, not the raw source mass.
All coefficients are explicit rational data with nome/width parameters and
no cutoff or terminal-depth argument. The source cap and partition floor
contain the SAME predecessor mass squared. Scaled substitution cancels that
factor; only the fixed positive floor coefficient is inverted. No predecessor
mass or observable variance is inverted, and H[q^2]=Z is not asserted.

The computed modulus

    max(headCutoff(w), geometricCutoff(w,B,epsilon))

proves rho*H[q^2]/(2Z)<=epsilon/2 for every later K and every positive
depth, where rho=w^((K+1)*(K+3)) and epsilon>0. This is the raw-mass
component of `BF4DyadicWilsonSquareHaarProjection.haarCenteredDebt`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareHaarProjection.lean:101`).
Applying it with the full energy theorem still requires that theorem's
separate sufficientCutoff and loop-width guards; neither is silently removed.

The result is ADDITIVE cutoff control at fixed nome/width. It is not
OWN-variance-relative, coupling/width-uniform or physical scaling control.
The COMPLETE signed cubic/angular/Ward/centering debt minus retained gain
still needs a useful estimate on a physically justified changing family.
Physical mass calibration, nonzero continuum survival, full QFT axioms,
every actual compact simple group and the Clay theorem remain OPEN.

## Checked declarations

All entries below are in
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRawSourceMassBound.lean`.

| Declaration | Line | Content |
| --- | --- | --- |
| `rawSourceInterval` | 92 | Constructed Type-level interval for the actual positive-depth source |
| `rawSourceMass_le_capSquare` | 113 | Source cap with matching predecessor square |
| `marginalMass_floor` | 138 | Original partition floor with the same square |
| `rawSourceMass_cleared` | 158 | Scaled cancellation without predecessor inversion |
| `rawSourceMassConstant` | 179 | Computed cap/floor ratio |
| `rawSourceMassConstant_positive` | 184 | Positive fixed-parameter coefficient |
| `rawSourceMass_bound` | 190 | H[q^2]<=B*Z uniformly in positive depth and late cutoff |
| `rawSourceMassCutoff` | 214 | Explicit rational-tolerance cutoff modulus |
| `omitted_rawSourceMass_bound` | 223 | Unhalved normalized contribution <=epsilon |
| `omitted_half_rawSourceMass_bound` | 265 | Actual halved contribution <=epsilon/2 |

The geometric comparison uses the existing
`PositiveContractionResidual.geometric_bound`
(`lean/YMGap/Continuum/PositiveContractionResidual.lean:126`) and
`BF4ExactSlabFixedSpatialJointOrbitTailBound.rg_qpow_eqv_pow`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialJointOrbitTailBound.lean:73`).
K<=(K+1)*(K+3) and power antitonicity keep the original omitted exponent.

## Verification and resource boundary

Final accepted focused check, exit zero:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 \
  --check lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRawSourceMassBound.lean \
  --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRawSourceMassBound.olean \
  --log-file /tmp/ym-raw-source-mass-20261002-accepted.log
```

All ten printed gates contain only propext and Quot.sound. The final run
took about three seconds. Fresh process inspection found no competing
compiler or runner. Memory pressure reported 85 percent free with zero swap;
the launcher retained a 12-GiB OS reserve and the mandatory 20-GiB worker cap.
No new sorry, axiom, analytic premise or weakened frontier was introduced.
The earlier draft logs were unsuccessful and are not accepted verification.
Explicitly unfolding the large existing raw-mass definition before transport
resolved the elaboration timeout without raising a limit.

Source SHA256:
`f1568f4a958fabfa5fbfdc091bf4670b75e38c8b9730449c31e3986c2276d4a5`.
Accepted log SHA256:
`474171baca94ff7fe96701f1ec24b678749b456c3b302560e6c41f595977acb4`.

A parallel Sol math review checked the shared source/floor factor, depth,
normalization and modulus. Its wording correction distinguishes the
unhalved theorem from the exact halved consumer; the latter is now separately
proved. The documentation skill kept this report within the existing
repository audit convention, preserving the additive versus relative scope.
Independent Luna QA confirmed source/log hashes, all declaration anchors,
allowed gates, clean diff and unchanged canonical chart fences.
One semantic-root import was added. Root/full-tree build, broad audit,
guards and progress-metric script were NOT run. CI remains unchanged and
all existing canonical chart fences remain unchanged; no ASCII reprint.

The separately requested parallel seven-paper version check found all seven
records still v1 at 2026-10-02 09:27 UTC. It reused the cached theorem screen
and found methods, not the missing original scaling producer. See
`audits/RESEARCH-MATH-PH-2026-09-30.md`. Literature review is not proof progress.
