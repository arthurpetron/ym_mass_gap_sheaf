# Original cap-free finite prediction and comparison (2026-10-07)

Whole-project goal unchanged and OPEN: nontrivial constructive continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms and
a strictly positive physical Hamiltonian mass gap.

Continuation from `cbd93ff3`. The October 5--7 review and live direct-score
route are in `AUDIT-RECENT-COMMITS-AND-CENTERED-SIGNED-PRODUCER-2026-10-07.md`.
The original nonunit tower and geometric covariance are recorded in
`AUDIT-ORIGINAL-INNOVATION-COVARIANCE-2026-10-07.md`.

## Vacuum-preserving prediction without exact density inversion

Use the SAME original transfer and terminal message:

```
g=g_n, a=T^t g=g_(n+t), b=T^t(g*psi), H=T^t(g*psi^2),
G=existing finite reciprocal, r=1-aG,
P psi=G*b+r*psi_out, F psi=G*H+r*psi_out^2.
```

The output-slice source is the same polynomial, not a stationary substitution
or a free-heat action. The existing positive window gives G>=0, r>=0,
r<=rho^k, rho=mixRate(w,width), under depth/cutoff guards. Structural aG+r=1
restores constants exactly. Jensen is the exact positive-cone decomposition

```
F-(P psi)^2 = G^2*(a*H-b^2)
                + G*r*Iold[W*(psi-lift(psi_out))^2].
```

Generic construction and actual consumer:

- `lean/YMGap/Continuum/QuaternionHaarUnitalReciprocalPrediction.lean:61`,
  `reciprocal_certificate`; `:92`, `reciprocalResidual_certificate`, construct
  the positive witnesses. `:126`, `prediction_certificate`, constructs the
  positive-map certificate. `:133`, `prediction_one`, proves unitality from
  structural cancellation. `:176`, `jensen_pin`; `:220`, `jensen_certificate`.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockUnitalPrediction.lean:184`,
  `blockUnitalPrediction`; `:196`, `blockMarginalSquare`, is literal
  mu=Haar[V*g*a*(-)], not the completed OS form. `:200`,
  `blockUnitalPrediction_one`; `:215`,
  `blockUnitalPrediction_jensen_certificate`, use the actual window.

Actual weighted transfer symmetry gives the integrated signed adjoint defect
g*(a*r-T^t(g*r)). The upper proof retains this defect rather than assuming
stationarity, and drops only the favorable nonpositive term. Consequently

```
||P psi||_mu^2 <= (1+rho^k)*||psi||_mu^2.
```

This is proved for EVERY supported source, with no source cap, by
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockUnitalPrediction.lean:273`,
`blockUnitalSecondMoment_upper`, and `:371`,
`blockUnitalPrediction_square_upper`. Generic Jensen is consumed by this
actual finite bound. No completed OS map, centered-mean preservation,
cross-action intertwining or strict contraction is inferred.

## Cap-free original innovation comparison with the leakage visible

Write Nfull for the old (t+1)-step noise, Nlast for the last-step noise of
phi=G*b, C for their actual signed reconstruction covariance, and
B=T^(t+1)(g*psi). Put m=1-aG. The joined source is
eta*lift(phi)+psi*lift(m), eta>0 an explicit rational.
Its determinant and the multiplier square interval give, with E the actual
joined-source error determinant,

```
Nfull-Nlast-2*C >= 0              (historical determinant retained),
eta^2*Nlast+2*eta*C+E >= 0,
E <= rho^(2k)*(Nfull+B^2).

nu=rho^(2k)/eta,
(1-eta)*Nlast <= (1+nu)*Nfull+nu*B^2.
```

Only eta is newly inverted in this argument; inherited G is the explicit
finite reciprocal polynomial using a positive scalar upper window, not an
exact pointwise conditional-density inverse. No source interval, conditional
unit mass, variance inverse or historical-smallness premise is introduced.

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockInnovationRelativeComparison.lean:289`,
  `innovationRelativeLoss`, returns nu with nome/width/k/eta explicit.
- Same file `:296`, `original_innovation_relativeComparison_certificate`,
  constructs the displayed polynomial positivity witness from the actual
  signed tower, two-copy determinant and multiplier interval.
- Same file `:585`, `original_innovation_relativeComparison_weighted_bound`,
  integrates against literal Lambda=Vbar^2*Gout^2. Output reciprocal degree
  kout is independent of k; output time is n+t+1. The B^2 payment remains.

This scalar estimate can pay last-noise contributions without a global
observable cap. A useful positive left coefficient needs eta<1. The SAME
centered surviving-form bound on its B^2 payment is not supplied. On psi=1,
Nfull=0 but C=-Nlast; hence dropping the leakage would be invalid. For k=0,
phi=0 and Nlast=0. For kout=0 the weighted statement has Lambda=0. These
endpoint checks were independently source-reviewed, not additional theorem
closures. The completed two-step/cross-action comparison is still OPEN.

## Completion viewpoint: reuse the theorem, do not assume its hypotheses

The user's Lawvere-enrichment viewpoint usefully separates a dense map from
its extension. Here the existing constructive API is
`lean/YMGap/Continuum/CRealSeminormCompletion.lean:340`,
`SquaredSeminorm.ModulusContinuous`: an actual dense endomap, positive
tolerance function and squared-distance implication for EVERY pair.
`:353`, `mapCauchy`, composes the supplied input modulus with that tolerance;
`:362`, `mapClose`; `:371`, `map_completionRel`; `:377`, `completionMap`,
transport representative closeness and descend without choosing quotient
representatives. This is a source review, not a new theorem or fresh build.

The actual original Wilson instance is
`lean/YMGap/Continuum/BF4WilsonAllNomeCompletedTime.lean:54`,
`timeNonexpansive`, using
`lean/YMGap/Continuum/BF4WilsonAllNomeTimeContraction.lean:167`,
`distSq_advance_contraction`. `BF4WilsonAllNomeCompletedTime.lean:73`,
`completedTime`; `:86`, `completedTime_embed`; `:93`, `time_cauchy_modulus`,
already construct the time extension and retain its modulus. Its source
distance is `lean/YMGap/Continuum/BF4WilsonAllNomeSeminorm.lean:38`, `distSq`,
the intrinsic reflected difference form; `:151`, `seminorm`, supplies the
symmetric squared-seminorm datum. The general continuity API also has the
actual instance `lean/YMGap/Continuum/BF4WilsonAllNomeTimeZeroOperator.lean:53`,
`multiplierContinuous`.

Two caveats prevent importing the proposed categorical account wholesale:

- A squared seminorm satisfies d(x,z)<=2d(x,y)+2d(y,z), not the literal
  additive Lawvere metric triangle. See `CRealSeminormCompletion.lean:39`,
  `SquaredSeminorm`. No new square-root metric or enrichment is constructed.
- Asymmetric forward-Cauchy completion is not automatically adjoint-weight
  Cauchy completion. [Hofmann--Tholen, Remark 3.4, Example 3.9 and section 4](https://link.springer.com/article/10.1007/s10485-026-09865-z)
  distinguish the self-dual Lawvere notion from forward completeness. For a
  direct mathematical check, set d(m,n)=0 when m<=n, otherwise 1, on Nat.
  The increasing sequence is forward-Cauchy, but its presheaf weight
  phi(m)=lim_n d(m,n)=0 is not adjoint: a partner would have to satisfy
  d(m,n)<=phi(m)+psi(n), forcing psi(n)>=1 for every n, while the unit
  requires inf_n(phi(n)+psi(n))=0. This prose example is NOT a Lean certificate.

For the new P, the missing input is an ACTUAL intrinsic/coarse map and a
quantitative reflected difference-form bound, compatible with the original
charts and normalization. The ordinary mu bound above does not supply it.
An ordinary weighted-Haar bounded-map completion is possible via existing
`lean/YMGap/Continuum/SU2QuaternionHaarBoundedCompletion.lean:39`, `BoundedMap`,
after a difference pin, but that would still be the wrong form for this join.
No such wrapper is added. Completion is not the unsolved analytic producer.

## Verification and next decision

Final verification recorded 2026-10-07, 17:43 UTC. Three serialized focused
checks succeeded, emitting local oleans and passing 13+8+3 printed gates,
all within {propext, Quot.sound}. Independent read-only reviews checked action,
norm, covariance direction, vacuum and boundary degrees. One monitored
20-GiB worker/12-GiB reserve, dynamic preflight before every launch, no competing
compiler and zero swap. Earlier failed elaboration is not proof evidence.
No full root/tree build/audit, hashed-baseline refresh, raised heartbeat,
new hole/axiom/classical input or canonical field change.

Final logs and SHA-256:

- `/private/tmp/ym-oct7-unital-reciprocal-prediction.log`:
  `d008aa79484f0a0061ddfc554da439a16e95fb4bd7e6edff52a7723b5557ef3d`.
- `/private/tmp/ym-oct7-block-unital-prediction.log`:
  `41d172497914f4582787faada17a141125b851a26e0b3eb35bbe8cbe26861811`.
- `/private/tmp/ym-oct7-innovation-relative-comparison.log`:
  `c1817b7a753d21e54b194b37a091df3eba9a490dce00d32b84f962fe70dcdd6f`.

NEXT: useful centered surviving-form payment of the weighted source term or
an actual dense OS realization with quantitative form continuity, alongside
the primary combined direct-score/signed-remainder estimate. Generic extension
does not solve action comparison, selective retention, ordinary delta budget,
independent AF survival or a uniform changing-family modulus. Physical
calibration/volume control, SAME continuum OS/QFT, every group and Clay remain
OPEN. Broad canonical chart unchanged; no reprint. Research-loop adaptation:
`AUDIT-RESEARCH-PIPELINE-TASTEVAL-2026-10-07.md`.
