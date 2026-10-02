# Retained projection gain for the original growing Wilson loop

## Result and scope

The existing finite-loop energy ceiling now retains a computed nonnegative
part of its negative completed square. It uses the ORIGINAL positive partition
for both regularization and normalization. All signed centering, Ward, cubic,
omitted-mode and angular-pair debts remain. The gain may be zero; no useful
scaling margin or continuum theorem is established.

## Constructed gain and proof

Write H for raw product Haar integration, psi for the ORIGINAL-centered
observable, v=q*psi and T for the existing completed commutator. Define
B=H[v^2], S=H[T^2], d=H[v*T]. These are raw source quantities, not an
alternative interacting measure.

`projectionOverlap`
(`lean/YMGap/Continuum/SU2QuaternionCompleteRemainderProjection.lean:47`)
constructs d. `projection_overlap_pin` (same file, line 84) proves
d=sourceFirstOrder-B/2. `projectionDenom_pos` (line 61) and `projectionGain`
(line 74) construct g=d^2/(B+epsilon) for supplied epsilon>0, even if B=0.
`projectionGain_nonnegative` (line 114) proves g>=0.
`projectionGain_le_squareCompletionMass` (line 126) uses unweighted Haar
Cauchy--Schwarz d^2<=B*S and S>=0 to prove g<=S. No nonzero vector or
positive variance is assumed.

`completeRemainder_le_projectionCeiling` (line 169) therefore proves
completeRemainder <= squareCeiling-(h^2/2)*g, h=1-w. It starts from the
existing retained ceiling and its exact square completion; every previous
explicit error budget is unchanged. Its cutoff guard is
K>=sufficientCutoff(w), with 0<=w<1 and supported q,psi.

## Original loop and actual energy consumer

For the literal strictly padded loop put L=4*side(scale), original partition
Z>0, U0=H[q^2] and U2=H[q^2*chi2(loop)]. `rawSourceMass` and
`rawSecondCharacterMass`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean:100` and
line 105) construct these RAW quantities. U2 is NOT Z times the original
label-two moment. The original centered-square pin is
B=Z*OWNVar-C, where C is the signed `centeredCorrection`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialCenteredRemainderSquare.lean:150`,
`centered_sourceSquare_pin`, line 157).

`paddedSquare_firstOrder` (ProjectionGain, line 134) uses the checked literal
loop curvature and f^2=1+chi2 to prove sourceFirstOrder=L*(3*U0-U2).
`paddedSquare_overlap_moments` (line 190) proves exactly
d=L*(3*U0-U2)-(Z*OWNVar-C)/2, retaining the signed correction.

`normalizedProjectionGain` (line 201) chooses epsilon=ORIGINAL Z and divides
g by this SAME Z, giving G=d^2/((B+Z)*Z). Its nonnegativity is proved in
`normalizedProjectionGain_nonnegative` (line 206).
`paddedSquare_remainder_projection_bound` (line 227) reaches the original
normalized remainder, not merely an auxiliary square.
`paddedSquare_energy_projection_bound` (line 279) then proves

    E <= (3*L*h+h^2/8)*OWNVar + completeCenteredError - (h^2/2)*G.

This weakly sharpens `paddedSquare_energy_centered_square`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean:290`).
The complete error still includes the ORIGINAL Ward term and centering
correction, not only source cutoff costs. All w, K, width, n and scale
parameters remain explicit, with 0<w<1, K>=headCutoff(w),
K>=sufficientCutoff(w) and side(scale)<width. No uniformity over a changing
family is asserted.

## Verification

Both accepted focused checks on 2026-10-02 UTC exited 0 without warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/SU2QuaternionCompleteRemainderProjection.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionCompleteRemainderProjection.olean --log-file /tmp/ym-complete-remainder-projection-20261002-second.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareProjectionGain.olean --log-file /tmp/ym-dyadic-square-projection-gain-20261002-third.log
```

All sixteen printed gates report only {propext,Quot.sound}. Independent Sol
source/math review passed. Earlier elaboration failures were corrected; their
logs are not accepted evidence. The last correction explicitly recodes constant
polynomials before coefficient reflection. The local notation quotation
precheck is disabled, not elaboration or kernel checking. No sorry, new axiom,
analytic premise, erased witness, heartbeat or resource-limit change entered.

| Artifact | SHA256 |
| --- | --- |
| CompleteRemainderProjection source | `7475d9df20dc07f4fc2e955c82dba4a78783f615d5a3986d25ab285f63cac854` |
| DyadicWilsonSquareProjectionGain source | `701a0c4ae396a7d81f3b4fa02a03356c77fcb4c8f8392cc3a2f6f8d395a54e41` |
| CompleteRemainderProjection accepted log | `725f0e127db512dc6bc90ec309d9a0cc1a77cdafbf1d96c1ecdb45850361c040` |
| DyadicWilsonSquareProjectionGain accepted log | `844cd302221d86d1c85bac2e9884641a80baeca36636a9548e559c6b00eaa084` |

Checks were serialized with one 20 GiB capped worker and a 12 GiB OS reserve.
Memory reported 86 percent free before and after the final physical check;
swap was zero before it, and the monitored launcher reported no safety stop.
Process inspection found no competing compiler/runner. Two root imports were
added; full-root/tree/audit/guard/progress checks were NOT run. CI and the
exact canonical chart block remain unchanged.

## Remaining mathematical input

A useful target rate rho requires the actual estimate
completeCenteredError-(h^2/2)*G <= (rho-3*L*h-h^2/8)*OWNVar on a justified
changing family. The gain may vanish; the new bound supplies no quantitative
lower gain or uniform debt ceiling. It does not satisfy the required relative
energy premise merely by being nonnegative.
Physical coupling/time/spacing calibration, nontrivial continuum survival,
full SAME-theory QFT and every compact simple group remain OPEN. The parallel
seven-paper applicability review in `RESEARCH-MATH-PH-2026-09-30.md` supplies
methods, not this missing original-theory estimate. No exact chart claim closed.
