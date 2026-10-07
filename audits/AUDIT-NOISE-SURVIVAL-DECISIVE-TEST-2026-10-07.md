# Original full-noise versus surviving-square test (2026-10-07)

Whole-project goal unchanged and OPEN: construct nontrivial continuum
Yang--Mills on R^4 for every compact simple group, with SAME-theory QFT
axioms and a strictly positive physical Hamiltonian mass gap, under the
repository's constructive axiom gate.

Continuation from `cd27aec4`. This is a decision record, not a claim of a
completed test until the verification section below records its evidence.

## Prediction and decisive test

Consumer: the optional conditional-noise ceiling for the original direct
score, and the retained source payment in the cap-free innovation comparison.
The primary combined exact-score/signed-remainder estimate is distinct.

Before invoking an abstract norm comparison, test the proposed bound

```
H[Lambda * Nfull(psi)] <= C * ell[B(psi)^2]
B=T^(t+1)(g_n*psi), ell[p]=H[V*p],
Lambda=Vbar^2*Gout^2.
```

Prediction: a blanket bound over all supported sources and widths fails on
an actual inactive plaquette, because the transfer can kill its centered
source while the historical conditional variance remains positive. In
contrast, the literal output score and signed bulk should respect that
transmitted null class and vanish. This would reject a loose ceiling, not
the actual exact-score route or the Clay target.

Decisive finite case: width one, the origin face, one original transfer,
`psi=chi_origin-coeffW(w,1)`, and the SAME finite original K*V action, with
`0<w<1` and the existing cutoff guards. Use output reciprocal degree one:
degree zero is zero and makes the multiplier vanish. No heat-only action,
stationary normalization or completed-kernel surrogate is substituted.

Available inputs:

- `lean/YMGap/Continuum/BF4WilsonAllNomeFringeTimeKernel.lean:76`,
  `originFace_not_fully_active`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialFringeFaceTransfer.lean:163`,
  `inactive_fundamental_transfer_pair`: every supported Haar probe of the
  original transfer pair, not merely a zero mean.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPlaquetteHaar.lean:80`,
  `shifted_square_floor`: every rational center retains unit bare square mass.
- `lean/YMGap/Continuum/SU2QuaternionHaarCertificateReindex.lean:38`,
  `carrier_of_supported`: supported tested equality becomes equality under
  arbitrary insertions when both compared sources are supported.
- `lean/YMGap/Continuum/SU2QuaternionHaarAngularIBPAt.lean:133`,
  `angularDerivative_carrier_at`: tangential differentiation preserves the
  SAME Haar carrier class in an in-range block.

Implementation and independent mathematical review are separate bounded
tasks. Verification budget: serialized focused leaf checks, one monitored
20-GiB worker and 12-GiB OS reserve, fresh process/memory/swap preflight.
No full build/audit or expensive numerical parameter sweep.

Kill/revise criterion: if strict noise positivity and zero surviving square
are proved, prune the universal full-noise-to-surviving-square payment. If
the exact score also vanishes, retain the primary exact signed producer and
seek its quantitative bound without enlarging it to historical noise.

## Literal weight mismatch already found by source review

The retained B^2 payment in the innovation comparison is

```
H[Vbar^2 * Gout^2 * B^2] = H[(Vbar * phi_out)^2].
```

It is NOT the square bounded by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockConditionalDrift.lean:81`,
`blockConditionalRatio_surviving_square_le`, whose left side is
`ell[A^2*phi_out^2]`. The missing terminal A^2 factor cannot be cancelled
or inserted without a proved comparison. Projection does not remove the
remaining Vbar factor. This is a source finding, not an axiom-gated closure.

The existing scalar physical consumers stay separate:
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockWindowPin.lean:140`,
`normalized_block_window_pin`, retains the actual even-horizon norm;
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighWindow.lean:89`,
`clearedRayleighCost_window_pin`, retains both original partition factors
and the distinct odd horizon. No ordinary marginal bound supplies the
changing-action all-vector comparison by itself.

## Observed mathematical result

The finite SAME-action obstruction is now proved for every rational nome
`0<w<1`, every finite input depth n, and every K satisfying the actual heat
positivity guard and K>=1:

```
psi=chi_origin-coeffW(w,1), B=T(g_n*psi), width=1,
ell[B^2] = 0,
H[Vbar^2*Gout^2*Nfull(psi)] > 0,  Gout at output n+1, degree 1.
```

Thus no rational C, however large or parameter-dependent, pays this literal
full noise by C*ell[B^2]. At n=1 the existing innovation depth guard is met.
This is a positive-action proof, not a numerical fit or a completed-kernel
re-export.

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialNoiseSurvivalObstruction.lean:107`,
  `originSource`, is the actual source; `:110`, `originSource_supported`.
- Same file `:133`, `origin_transmitted_pair_zero`; `:165`,
  `origin_transmitted_surviving_square_zero`, retain the original transfer
  and V-weighted square.
- Same file `:253`, `origin_weighted_noise_positive`, uses the literal
  spatial/reciprocal multiplier, original spatial and terminal floors and
  the one-step transfer floor certificate. `:309`,
  `origin_no_noise_survival_bound`, excludes every rational C.

The direct score passes the same test: tangent differentiation preserves
the transmitted Haar-null class. The squared score integral is zero, and
BOTH Taylor remainders vanish through their fixed null test polynomials.
No linearity of the adaptive cyclic degree tree is asserted or needed.
The score statements retain `relativeCutoff w 32 <= K`, with `1 <= K`
for the concrete specialization; this implies the head-cutoff guard used
by the standalone noise obstruction.

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepNullScore.lean:119`,
  `exactScoreAngularBudget_zero`; `:146`, `exactScoreSignedBulk_zero`, use
  Haar-nullity of the ACTUAL transmitted numerator, not a zero-bulk premise.
- Same file `:181`, `origin_transmitted_null`, derives that input from the
  original supported-test identity. `:198`,
  `origin_exactScoreAngularBudget_zero`; `:208`,
  `origin_exactScoreSignedBulk_zero`, apply to the SAME obstruction source
  with all n, reciprocal degrees and sigma retained.

## Verification and decision

Final verification 2026-10-07, 18:15 UTC: two serialized focused checks
passed all 6+12 printed gates within {propext, Quot.sound}, with no errors
or sorryAx. One monitored 20-GiB worker, 12-GiB OS reserve, fresh capacity
preflights, no competing compiler and zero swap. Earlier elaboration failures
were repaired, not counted as evidence. No raised heartbeat, new hole/axiom,
classical input, frontier-field change, full-root/tree build/audit or hashed
baseline refresh. Root imports are registered but not whole-root checked.

Final logs and SHA-256:

- `/private/tmp/ym-oct7-noise-survival-obstruction.log`:
  `3f498177e7c6a91b5369cad188211cebc15bc75e21fd49a3baee1472cc9c0757`.
- `/private/tmp/ym-oct7-null-score.log`:
  `01cddfda10a3f12e8f87e62aa674867117992b65618781ce37f56f7f0cfb3a11`.

PRUNE: the blanket full-historical-noise-to-transmitted-square payment.
CONTINUE: the combined literal direct score and signed remainder, preserving
their exact cancellation before estimating. A proof on a narrower guarded
source family is not excluded by this example. The retained Lambda*B^2
payment itself is also NOT refuted; the earlier weight mismatch only says
the existing A^2-weighted theorem cannot be used unchanged.

This is not a counterexample to Yang--Mills, selected strictly padded AF
excitation survival, or every legitimate completed cross-action comparison.
AF survival, a useful combined signed estimate along the justified family,
the actual changing-action comparison, physical calibration, spatial/spacing
control, continuum QFT and every-group realization stay OPEN. The broad
canonical chart does not change and is not reprinted.
