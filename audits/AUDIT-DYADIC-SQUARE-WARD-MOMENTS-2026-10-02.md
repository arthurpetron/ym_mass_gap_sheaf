# Growing Wilson square curvature and original Ward moments

## Result and scope

The literal padded dyadic Wilson loop now has exact full-slice angular
curvature and a COMPLETE differentiated-weight Ward term expressed in two
moments of its original interacting measure. This supplies a missing geometric
input to the existing growing-loop variance/Taylor consumer. It does not
bound the complete signed error or establish a physical scaling trajectory.

Write L=4*side(scale), h=1-w and f=chi1(loop). The marginal is exactly
`marginalWeight=spatialWeight*g_n*g_(n+1)`
(`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActualMarginalDual.lean:75`,
`marginalWeight`), with its OWN positive partition, not a q^2 auxiliary law.

## Geometric proof

`linear_angularSquare_norm`
(`lean/YMGap/Continuum/SU2QuaternionIndependentTailAngularSquare.lean:274`)
proves Gamma_block(f,f)=4*norm(coordinate)*norm(tail)-f^2, where norm here
denotes the sum of four component squares. It uses the six unordered angular
planes and a reflective eight-variable Lagrange identity.
The tail has degree zero on the selected block; both norms remain intact.

`fundamental_angularSquare` (same file, line 310) then applies the explicit
arbitrary-insertion Haar-unit laws to obtain Gamma_block(f,f)=4-f^2.
It requires no heat eigenvalue or extra tail-support hypothesis.

`paddedSquare_block_gamma`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:203`)
cyclically moves the original prefix past the selected letter. Link
distinctness leaves the tail independent of that block. Conjugation handles
reversed edges without changing unit norms.
`paddedSquare_gamma` (same file, line 280) uses the actual observable/spectator
partition: each of the L distinct loop links contributes 4-f^2, and every
spectator contributes zero. Thus full Gamma=L*(4-f^2), with arbitrary
polynomial insertions retained. This is SU(2) quaternion geometry, not an
interacting-transfer eigenidentity or a group-independent mass bound.

## Original moments and consumer

`squareMoment` (WardMoments, line 310) uses the original `middleRatio` at
depths (n+1,n). Put m1=E[chi1]=E[f] and m2=E[chi2]. Character fusion gives
E[f^2]=1+m2; m2 is NOT the scalar second moment. The exact new formulas are:

- `paddedSquare_variance` (line 351): OWNVar=1+m2-m1^2.
- `paddedSquare_angular` (line 359): Angular=L*(3-m2).
- `paddedSquare_ward` (line 385): COMPLETE Ward=L*(4*m2-3*m1^2).
- `paddedSquare_varianceRemainder` (line 413): the existing complete
  varianceRemainder equals normalizedRemainder-h*L*(4*m2-3*m1^2).

All these moments retain w, cutoff K, width, time depth and loop scale in
their types, with 0<w<1, K>=headCutoff(w) and side(scale)<width. Neither the
Ward term nor the remainder is assigned a sign. No term of the density,
mean or common normalization is dropped.

The actual consumer is `paddedSquare_energy_variance`
(`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean:257`):
E=3*L*h*OWNVar+varianceRemainder. Its existing `finiteSquare_energy_variance`
(same file, line 334) reaches the original finite energy/variance schedule;
the new moment formula specifies its COMPLETE error, not a bound for it.
`finite_reference_ratio`
(`lean/YMGap/Continuum/BF4WilsonAllNomeTerminalReferenceEnergyRatio.lean:52`)
still requires a useful supplied relative-energy estimate.

## Verification

Both final focused checks on 2026-10-02 UTC exited 0 without warnings:

```sh
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/SU2QuaternionIndependentTailAngularSquare.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/SU2QuaternionIndependentTailAngularSquare.olean --log-file /tmp/ym-independent-tail-angular-20261002-second.log
python3 scripts/safe_lean_build.py --jobs 1 --check-worker-limit-gib 20 --check lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean --check-output lean/.lake/build/lib/lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.olean --log-file /tmp/ym-dyadic-square-ward-moments-20261002-second.log
```

All nine printed gates report only {propext,Quot.sound}. Independent Sol
mathematical review passed for both files; a separate Luna arithmetic/source
review passed for the moment formulas. Initial namespace, syntax and inference
errors were corrected. A local notation quotation precheck was disabled;
actual elaboration and kernel checks remained in force. No resource or
heartbeat limit changed, and no sorry, new axiom or analytic premise entered.

| Artifact | SHA256 |
| --- | --- |
| WardMoments source | `d45f2d9932c3786db0d0d0ae919741c754161bd098542e6d8117e5554b399f25` |
| IndependentTailAngularSquare source | `e8267c96caa9fbe9cbabc148d7cb2d71ac23d71761fe7ed772dc178f096c0bcd` |
| WardMoments final log | `7ad2ddb763d9e42abe975a00e9ca431a2a631a4b2fdaacd5e2f4a7e1da8be706` |
| IndependentTailAngularSquare final log | `dc23fa362fd06223c9c559fd38b1b024fa7d53923714e94e18aa67aa38c8c5c9` |

Verification used one serialized 20 GiB capped worker with a 12 GiB OS
reserve. Memory reported 86 percent free before and after; swap remained zero,
and no competing or surviving compiler/runner process was found. Two root
imports were added; full-root/tree/audit/guard/progress checks were NOT run.
CI and the exact canonical chart block are unchanged.

## Remaining mathematical input

A useful target rate rho still needs COMPLETE signed control
`varianceRemainder <= (rho-3*L*h)*OWNVar` on a justified changing family.
The new identities expose its original moment content; they do not supply
this estimate or permit a favorable sign by deletion. Generic positive-source
examples are not replacements for the actual Wilson density.
Physical coupling/time/spacing calibration, nontrivial continuum survival,
full SAME-theory QFT and every compact simple group remain OPEN. The finite
geometric identities close no exact displayed chart claim.
