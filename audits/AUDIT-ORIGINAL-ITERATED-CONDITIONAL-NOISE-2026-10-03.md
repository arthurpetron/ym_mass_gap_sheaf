# Original iterated conditional-noise certificate and variance-loss identity

The continuum Yang--Mills/Clay target remains OPEN. This checkpoint proves
positivity of an actual finite original-action component that the preceding
noise-minus-drift join left unproved. It does not bound the complete signed
cost, produce a response reserve, or justify a changing physical family.

## Mathematical increment and causal consumer

For h integrated quaternion blocks and an arbitrary shared surviving tail,
write A_h for the EXISTING ordered partial Haar integral. Two copies of the
same positive W, with the tail shared, multiply the literal difference square.
Integration of both copies gives

    A_(2h)[W(x,z) W(y,z) (f(x,z)-f(y,z))^2]
      = 2*(A_h(W)*A_h(W f^2)-A_h(W f)^2).

The identity is coefficientwise, hence holds under EVERY surviving Haar
insertion. The certificate is constructed by copying the actual W certificate,
multiplying its copies and the supported difference square, integrating,
scaling by 1/2 and transporting the equality. Zero integrated or surviving
blocks are included. No pointwise-positivity inference or reciprocal is used.

The physical consumer uses the EXISTING half-open original action for t
transitions. Put N=length(baseLinks width), h=t*N and W=g*halfOpenAction(t).
Exactly t kinetic factors and t lower/intermediate spatial weights occur.
The final spatial weight is inserted ONCE by weightedMass, after integration.
Existing window contraction identifies the three moments coefficientwise:

    A=T^t g, b=T^t(g f), H=T^t(g f^2), Delta=A H-b^2.

The new certificate constructs Delta>=0 on the original surviving N carrier
for every supported signed f and supported certified g. In particular g=g_n
and f equal to the actual OWN-centered test are admissible without positivity
of that signed test, a source eigenpin or finite stationarity.

Actual weighted transfer symmetry and exact time composition give

    ell(Delta)=ell[g*T^(2t)(g f^2)]-ell(b^2),
    ell(b^2)<=ell[g*T^(2t)(g f^2)].

The first square is the actual longer-horizon endpoint square, not a square
under an assumed stationary finite marginal. At t=1 and g=g_n, the certificate
proves nonnegativity of the EXISTING `FilteredNoiseDrift.noise`. The original
radius-two numerator is still noise MINUS the separately nonnegative drift
square. Nothing here proves its sign or a useful relative signed bound.

## Declaration anchors

- `lean/YMGap/Continuum/SU2QuaternionMultiHeadVarianceReplica.lean:142`:
  `partial_copy`; :157: `replica_product`; :371: `replica_identity`;
  :403: `replica_certificate`; :425: `determinant_certificate`;
  :438: `spectator_nonnegative`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalNoise.lean:96`:
  `blockNoise_certificate`; :128: `blockNoise_nonnegative`;
  :138: `blockNoise_variance_loss`; :177: `filteredSquare_le_endpointSquare`;
  :192: `original_noise_nonnegative`.
- Existing action and exact contraction:
  `lean/YMGap/Continuum/SU2QuaternionHeadWindowBounds.lean:58`,
  `halfOpenAction_certificate`;
  `lean/YMGap/Continuum/SU2QuaternionHeadWindowContraction.lean:201`,
  `windowMessage_iterate`; :209: `windowMessage_one`.
- Existing chronological symmetry/composition:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialTransferSymmetry.lean:128`,
  `iterateStep_weighted_symmetric`;
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialMiddlePairing.lean:47`,
  `iterateStep_add`.
- Existing complete signed consumer:
  `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFilteredNoiseDrift.lean:82`,
  `noise`; :217: `filtered_loop_numerator`; :333: `driftSquare_nonnegative`.

## Forward/backward strategy consequence

The checked finite identity shows that a proposed bound
ell(Delta)<=C*ell(b^2) requires the filtered square to retain a fixed fraction
of its SAME longer-horizon endpoint square: that square must be at most
(1+C)*ell(b^2). Such a comparison, if proved from the actual action, is useful;
it is NOT supplied by Gram positivity or terminal-message regularity, and is
not a weaker independent input that can be assumed to produce survival.

Keep the complete signed score/commutator pairing as the next analytical
target. Do not replace it automatically by total-noise control or apply the
positive-message relative derivative bound to the signed b. No new derivative
covariance estimate or completed block-noise limit was proved in this check.
The original relative budget s*D<=C*Z1*ell(b^2), justified family, spatial and
spacing control, physical calibration, full SAME QFT and every-group route
remain OPEN.

## Accepted verification and exact scope

Two serialized focused checks used `scripts/safe_lean_build.py`, one worker,
12 GiB reserve and 20 GiB hard check-worker limit. Fresh preflights reported
85--86 percent memory free, zero swap and no competing Lean/Lake build.
All eleven distinct printed gates have only {propext, Quot.sound}; final
accepted logs contain no errors or warnings. Initial development logs are
NOT accepted evidence. No full build, root aggregate check, broad audit,
axiom baseline regeneration or progress-metric run was performed.

| Artifact | SHA-256 |
| --- | --- |
| `SU2QuaternionMultiHeadVarianceReplica.lean` | `eefb7b2a73e51301428953d54f5dcbcf01a63820d58d486aafbdb5c297018f28` |
| `BF4ExactSlabFixedSpatialBlockConditionalNoise.lean` | `d87b40b8f9510a0d655b070e1a965b1a4244b6ca2edad39202dc5112cf21098e` |
| `/tmp/ym-multihead-noise-20261003-b.log` | `4881c676912f7e4dbdcf59f635fa7a110859a19e60757cfbe8bbeb08ff9aca09` |
| `/tmp/ym-original-block-noise-20261003-b.log` | `12fc8512189c065803230fbbc56cb79cb3f3d72dfc614201b7313266acb02afe` |

Independent Sol mathematical/source review and Luna declaration, hash,
log, whitespace and unchanged-chart checks passed. The six generic replica
gates and five original-consumer gates are new.
Root imports are registered only. No exact canonical chart claim changed;
the chart is unchanged and was not reprinted. GitHub CI remains disabled.
