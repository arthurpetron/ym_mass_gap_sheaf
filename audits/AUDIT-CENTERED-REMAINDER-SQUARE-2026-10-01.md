# Square completion in the original signed energy bound

Date: 2026-10-01 UTC. PROGRESS after `68bf46e`: a constructed negative
square bounds the JOINT raw angular/commutator term without a score cap or
Casimir eigenpin. Its concrete original-family consumer has leading rate
12*h+h^2/8, h=1-w. The complete remaining error is explicit, not proved small.
This does not close the changing-coupling, spatial or continuum frontier.

## Exact mathematical argument

Use the existing original Haar functional H, supported source q and observable
f, positive Casimir C, and angular product Gamma. Put

    v = q*f, B = q*Cf-2*Gamma(q,f),
    A = sourceFirstOrder, S = H[B^2], Q = H[v^2].

Literal Casimir pairing and its product rule prove A=H[v*B]. Thus

    A-S = Q/4-H[(B-v/2)^2] <= Q/4.

The completed square comes with Type-level supported polynomial certificate
data. Neither source positivity nor a bare-heat eigenpin is required. Apply
this to the preceding exact complete-remainder cancellation, keeping its
cubic, omitted-mode and angular-pair terms. Only the constructed nonnegative
square is dropped in the upper bound.

For the ACTUAL original source at depth n, center f by its OWN odd-marginal
mean, giving psi. The marginal is not replaced by q^2. Instead the exact pin is

    H[(q*psi)^2] = Z*Var_odd(f)-sourceCorrection(q,psi).

Here Z is the SAME positive oddMass. The source correction remains signed.
Original energy and marginal angular cost are invariant under this constant
shift; the complete remainder is evaluated on psi, not declared shift-invariant.
The original whole-family Ward identity then yields

    E_original(f) <= (12*h+h^2/8)*Var_odd(f)+completeCenteredError(f),
    completeCenteredError =
      [sourceErrorBudget(q,psi)+h^3*pairBudget(q,q*Gamma(psi,psi))
        -(h^2/8)*sourceCorrection(q,psi)]/Z
      -h*normalizedWardResidual(f).

Every original source factor, own mean and normalization remains. No sign or
smallness of the displayed error is asserted. Arbitrary rational coefficients,
repeated faces, zero coefficients and zero variance are permitted.

## Declaration chain

- `lean/YMGap/Continuum/SU2QuaternionCompleteRemainderSquare.lean:106`,
  `sourceFirstOrder_commutator_pair`, gives A=H[v*B].
  `sourceFirstOrder_sub_square_complete` (:165) gives the exact square identity;
  `completedSquareCertificate` (:87) and `squareCompletionMass_nonnegative`
  (:98) provide its constructive sign. `sourceFirstOrder_sub_square_le_quarter`
  (:227), `completeRemainder_square_completion` (:252) and
  `completeRemainder_le_squareCeiling` (:273) supply the exact remainder and
  source-dependent ceiling.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:109`,
  `blockSquare_shifted`, and `marginalAngular_shifted` (:116) justify centering.
  `normalizedEnergy_centered_taylor` (:124) preserves original energy.
  `centered_sourceSquare_pin` (:157) uses the existing
  `BF4ExactSlabFixedSpatialSourceVarianceGram.centered_source_square`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialSourceVarianceGram.lean:89`).
  `quadraticRate` (:201) is h^2/8. `centeredError` (:206) and
  `completeCenteredError` (:285) expose the remaining debts.
  `normalizedRemainder_centered_square_bound` (:231) cancels ONLY Z;
  `padded_family_energy_centered_square` (:292) is the concrete whole-family
  consumer, using original `family_normalized_ward`
  (`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFamilyVarianceWard.lean:144`).

The generic identity requires supported q,f on tail+1 blocks. Its ceiling uses
0<=w<1 and K>=sufficientCutoff(w). The physical bound uses 0<w<1,
K>=headCutoff(w), K>=sufficientCutoff(w), base<width, and every listed face
in spatialFaces(base). It needs no endpoint-relative score cutoff or density
minimum. The leading coefficient has no width, depth, family or cutoff factor;
the error and its existing budgets do depend on the changing source/regulators.

## Remaining causal frontier

The former raw-angular/SAME-variance comparison is no longer separately needed
for this quadratic ceiling: completing A-S supplies its joint estimate directly.
Useful control of the COMPLETE centered error relative to SAME Var on a
justified coupling/spatial/spacing family remains OPEN. Existing Ward bounds
have no useful near-one calibration, and the cyclic budgets do not supply a
terminal-source estimate relative to Z*Var. The displayed h powers do not
establish an O(h^2) complete error. No limit for that changing error is built.

The existing completed source consumer `relative_derivative_bound`
(`lean/YMGap/Continuum/BF4WilsonAllNomeSectorSourceTransfer.lean:116`) still
requires an actual sufficiently small energy/SAME-norm bound; this checkpoint
does not supply it. Nonzero continuum survival, spatial/spacing control,
physical time and mass, full same-theory continuum OS/QFT, Yang--Mills field/UV
identification, every compact simple group and the Clay target remain OPEN.
No canonical frontier field or displayed chart claim changes; no chart reprint.

## Focused verification and independent review

Both final focused checks exited zero and emitted target oleans. All 17+11=28
printed gates passed: four empty, one {propext}, twenty-three
{propext,Quot.sound}. No sorry, new axiom, Classical, native_decide,
noncomputable declaration, analytic premise or weakened frontier was introduced.
Sol independently reviewed the math/source signs and next-input boundary;
Luna checked every gate, final sources and log hashes. A review paraphrase
confusing raw Q with the commutator square S was corrected before acceptance.

Main repaired a missing namespace open and a default-heartbeat reduction
timeout by keeping four existing scalar definitions locally irreducible.
Failed draft logs are not accepted proof evidence. Main alone compiled with
the safe-build skill and monitored launcher: one worker, 20 GiB ceiling,
unchanged 12 GiB OS reserve and automatic telemetry. Preflight found 82 percent
pressure-free memory and zero swap; user-owned reliability-study jobs were left
untouched. No memory/worker/heartbeat limit was raised. No full-root/tree build,
broad audit, guard, progress-metric script or CI change ran. Root imports are
registered only, not aggregate-checked. The documentation skill kept the
verified finite result and open scaling obligation distinct.

Accepted logs and SHA-256:

- `/tmp/ym-complete-remainder-square-second-20261001.log`:
  `0358b451e29a67ef9eb85ed7bc4a2a9320ff80a2d6af0c1c93ac6f1bb02402b8`.
- `/tmp/ym-original-centered-remainder-square-second-20261001.log`:
  `3ad15197b4c45f093110c8d045cb5ba31f92db087be5c867a64dcb2c682b3cc1`.
