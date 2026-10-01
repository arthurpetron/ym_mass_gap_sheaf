# Exact cancellation in the original signed remainder

Date: 2026-10-01 UTC. PROGRESS after `0703b83`: the quadratic source-curvature
flux cancels against the first Taylor coefficient of the ORIGINAL angular
weight defect. This is a checked finite identity and original-source ceiling,
not the missing useful signed scaling estimate or continuum Clay closure.

## Mathematical result

Set h=1-w, N=length(baseLinks width), and
q=projectedEndpointSource(w,K,width,terminalMessage(w,K,width,n)). The depth is
n in EVERY term. Let G=Gamma_range(N)(f,f), Phi=H[q*(Cq)*G], A=sourceFirstOrder,
and S=H[(q*Cf-2*Gamma(q,f))^2]. The previous source identity gives
D2=-2*Phi-S. The new finite-cutoff pairing identity gives

    angularWeightDefect = -h*Phi + pairRemainder(q,q*G).

The complete original signedRemainder is the source mixed-minus-diagonal
remainder minus h*angularWeightDefect. Thus its two flux terms cancel:

    signedRemainder = (h^2/2)*(A-S)
      + sourceCubic - sourceOmitted - h*pairRemainder(q,q*G).

This cancellation is performed before normalization or absolute estimates.
The signed observable is never split facewise. S has a constructed Type-level
supported square certificate and is nonnegative without positivity of q or f.
The exact formula keeps the signed angular pair remainder and actual cutoff
debt. Neither term has an assigned favorable sign.

At K>=sufficientCutoff(w), the existing sourceError_bound and negative pair
remainder bound give the explicit retained-square ceiling

    signedRemainder <= (h^2/2)*(A-S) + sourceErrorBudget
      + h*(h^2*pairBudget(q,q*G)).

The omitted-mode part of sourceErrorBudget has no asserted uniformly quadratic
bound. q, its degree and all leaf budgets change with w,K,width,n. No uniform
O(h^2), smallness versus variance or continuum schedule follows from this form.

## Concrete original consumers

All paths below are relative to the repository root.

- `lean/YMGap/Continuum/SU2QuaternionCompleteRemainderCancellation.lean:72`,
  `squareMassCertificate`, constructs the supported commutator square.
  `squareMass_nonnegative` (:88) gives its actual original-Haar sign.
  `angularWeightChange_taylor` (:112) and `completeRemainder_cancellation`
  (:174) prove the finite-cutoff identity. `completeRemainder_le_retained`
  (:250) proves the ceiling without assuming any source estimate.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialRemainderCancellation.lean:85`,
  `angularWeightDefect_generic`, collects the literal finite block sum using
  `BF4ExactSlabFixedSpatialFamilyBareHaar.weighted_gamma_finSum` (:80 in its
  own module). Collection needs no support, positivity or independence.
  `signedRemainder_cancellation` (:113) pins the exact formula to the ORIGINAL
  depth-n projected source and complete remainder.
- `normalizedRemainder_cancellation` (:128) divides ONLY by the SAME positive
  oddMass. `varianceRemainder_cancellation` (:145) retains the COMPLETE-weight
  Ward correction and own mean. `padded_family_energy_cancellation` (:157)
  proves E=12*h*Var+(cancelledRemainder-h*Ward)/Z for arbitrary signed and
  repeated interior families, with strict padding and original normalization.
- `cancellationCutoff` (:174) computes max(endpointRelativeCutoff(w),
  sufficientCutoff(w)). `normalizedRemainder_le_retained` (:186) supplies the
  actual-source ceiling. `padded_family_energy_le_cancelled` (:204) consumes
  the preceding whole-family angular/SAME-variance producer and proves
  E<=h*familyLengthAngularVarianceFactor(w,qs)*Var+retainedCeiling/Z.

Exact generic guards: supported q,f on tail+1 blocks, any rational w and K.
Normalized original guards: 0<w<1, K>=headCutoff(w); the family identity also
uses base<width and every listed face in spatialFaces(base). The final ceiling
consumer uses the computed joined cutoff. Zero/repeated coefficients and zero
variance are allowed. No source or variance inverse is introduced.

## Remaining causal frontier

The source-curvature flux is no longer an uncancelled term of the complete
remainder. What remains is useful JOINT control of the raw q^2 angular cost,
retained negative square, signed angular pair debt, cubic/omitted budgets and
original Ward correction relative to SAME Z*Var on a justified changing-
coupling/spatial/spacing family. A is NOT the previously bounded q*Pq marginal
angular cost. That comparison cannot be substituted without proof.

The existing marginal score coefficient remains coupling-dependent and lacks
useful near-one calibration. No completed remainder/angular limit or changing-
width map is constructed. Nontrivial continuum survival, physical time and
mass, full same-theory continuum OS/QFT, Yang--Mills field/UV identification,
every compact simple group and the Clay target remain OPEN. No canonical
frontier field or displayed chart claim changes; no ASCII chart is reprinted.

## Verification boundary

Both final focused checks exited zero and emitted target oleans. All 11+13=24
printed gates pass: one empty, one {propext}, twenty-two {propext,Quot.sound}.
No sorry, new axiom, Classical, native_decide, noncomputable declaration, new
analytic premise or weakened frontier appears in the final modules.

Sol independently reviewed the signs, original depth, defect collection,
normalization and concrete consumer. Luna checked final sources, every gate
and both hashes; an aggregate gate-count arithmetic typo was corrected before
recording this report. Main repaired namespace opens, integer-only reflection
of the rational half, a multiline match and the tail+1 Gamma unfold. Failed
draft logs are not accepted proof evidence.

Main alone compiled serially through the safe-build skill/monitored launcher:
one worker, 20 GiB ceiling, unchanged 12 GiB OS reserve and dynamic telemetry.
Preflight found 84 percent pressure-free memory and zero swap; final swap was
zero. Separate user-owned reliability-study jobs were left untouched. No worker,
memory or heartbeat limit was raised. No full root/tree build, broad audit,
guard or CI change ran. Root imports are registered, not aggregate-checked.
The historical progress-metric script invokes a broad guard and was not run.
The documentation skill preserved the verified finite versus open scaling
boundary in the proof record and existing repository documents.

Accepted logs and SHA-256:

- `/tmp/ym-complete-remainder-cancellation-second-20261001.log`:
  `2a086797789e60f6c4a664d98c0e31df7e509507f48a13ccfebd5abebdd34496`.
- `/tmp/ym-original-remainder-cancellation-second-20261001.log`:
  `43e78d8f42fec57fe3568b6be0069b1ba0542dba599f23224e0310ca548cff7d`.
