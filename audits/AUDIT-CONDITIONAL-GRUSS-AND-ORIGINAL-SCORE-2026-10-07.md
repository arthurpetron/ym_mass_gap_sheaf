# Conditional Gruss correction on the original score (2026-10-07)

Whole-project goal unchanged and OPEN: constructive nontrivial continuum
Yang--Mills on R^4 for every compact simple group, SAME-theory QFT axioms
and a positive physical Hamiltonian mass gap.

Continuation from `c71f9eb4`. The recent-commit source review and previous
signed cancellation are recorded in
`AUDIT-RECENT-COMMITS-AND-CENTERED-SIGNED-PRODUCER-2026-10-07.md`.
This increment does not re-audit the entire recent history.

## Sharper finite mathematical argument

Let I be the same partial Haar integral and define

```
A=I(W), D=I(d), b=I(W*f), e=I(d*f), H=I(W*f^2), S=A*e-b*D.
U=L*W+d, V=L*W-d, u=I(U), v=I(V), L>0.
det(W,f)=A*H-b^2.
```

Actual positive certificates for U and V produce their masses and variance
determinants. The kernel-checked polynomial identity is

```
(u+v)*(v*det(U,f)+u*det(V,f))
  = 4*L^2*[(L^2*A^2-D^2)*det(W,f)-S^2].
```

The signed second moment I(d*f^2) cancels exactly. The left side has a
constructed positive certificate, so division ONLY by the positive rational
4*L^2 gives the sharper estimate. No inverse of W, A, a terminal source or
an excitation norm is taken. Zero mass/determinant and signed observables
require no additional hypothesis.

- `lean/YMGap/Continuum/SU2QuaternionConditionalGrussSquare.lean:70`,
  `centeredRelativeCoefficient`, names the literal corrected coefficient.
- Same file `:76`, `conditionalGrussSquare_certificate`, returns the
  positive certificate as Type-level data, including shared tail variables.

This is conditional scalar/positive-cone algebra, not a non-abelian
coercivity argument or a physical spectral estimate.

## Join to the original full window and existing consumer

- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockScoreVariance.lean:249`,
  `original_block_centered_scoreVariance_certificate`, applies the new
  certificate to the same blockWindowWeight and its output angular derivative.
  For every n,r and active direction, A=g_(n+r+1),
  b=T^(r+1)(g_n*(f-c)), it constructs
  `(L^2*A^2-(dA)^2)*blockNoise-S^2` with L=relativeCap(w,32).
  All original intermediate spatial factors and the original input center
  are retained. The cutoff premise remains `relativeCutoff w 32 <= K`.
- Same file `:346`, `original_block_scoreVariance_certificate`, preserves
  the previous public signature. Its proof adds back the positive product
  `(dA)^2*blockNoise`, using the existing full-window noise certificate.
- `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise.lean:74`,
  `centeredScoreNoiseAngularBudget`, keeps the exact Vbar^2*G^2 multiplier
  of the existing direct score, its reciprocal degree and every active plane.
- Same file `:99`, `exactScoreAngularBudget_le_centeredNoise`, integrates
  the certificate with the identical multiplier represented as (Vbar*G)^2,
  then sums with nonnegative 1+sigma. No independence or new analytic premise
  is introduced. This is an alternative ceiling on the exact score, not a
  claim that replacing the exact score by a ceiling improves its estimate.

## Verification boundary

Completed by 2026-10-07 16:57:04 UTC. Five serialized focused checks passed:

| Checked module | Printed gates | Log in /private/tmp | SHA256 |
| --- | ---: | --- | --- |
| SU2QuaternionConditionalGrussSquare | 2 | ym-oct7-conditional-gruss.log | c937fe9e15fb0cc1338110394090c8fce9983c164f20ff09d86b6ed3551db817 |
| BF4ExactSlabFixedSpatialBlockScoreVariance | 5 | ym-oct7-block-centered-score.log | 4697ae6806509286e55562d61bad09d82ccbc2bd277b2f4cbd78065d1307d33a |
| BF4ExactSlabFixedSpatialLastStepCenteredScoreNoise | 2 | ym-oct7-centered-score-noise.log | a69b137fdddd2fcfbc84c9165c7ffc83596e72eebdfaa41791f8aa3e212c45e5 |
| BF4ExactSlabFixedSpatialBlockConditionalScoreGradient (regression) | 5 | ym-oct7-centered-score-gradient-regression.log | fb51a79293054e3105a1ff56bfc3aa656b0d1b93a309a054086e742cb88db4e8 |
| BF4ExactSlabFixedSpatialLastStepRatioNoise (regression) | 4 | ym-oct7-centered-score-ratio-regression.log | 63cfe8a9e084e0c8d6d122dec7230a6754d9d96b069d4a3556ffa9a18c71aacd |

All 18 reported gates depend only on {propext, Quot.sound}; five declarations
are new. No sorry, new axiom, classical shortcut, native_decide or canonical
field change. Two independent read-only reviewers verified the determinant
identity, zero cases, original-window pins and weighted consumer.

Each launch used the safe-build procedure, one compiler, 20-GiB worker cap,
12-GiB OS reserve and a fresh process/pressure/swap preflight. Swap was zero.
No full-root/tree build, full axiom audit, or hashed-baseline regeneration.
The umbrella import edit is not represented as a checked umbrella build.

## Residue and next actual analytic task

The new coefficient is not uniformly strictly better: dA=0 recovers the
previous cap. L still depends explicitly on the nome through relativeCap;
there is no spacing-, volume- or AF-uniform smallness claim. The correction
does not supply conditional-noise versus surviving-form control.

Keep the primary exact-score/signed-remainder route. Use the new ceiling
only where the actual full-window noise and correction admit useful bounds.
The combined cost in SAME surviving-form units along a justified scaling
family, quantitative AF survival, actual interacting coarse action/map and
every-vector two-step relative comparison remain OPEN. One-step Rayleigh
cost is not identified with that two-step squared-norm dissipation.
Physical calibration, SAME continuum OS/QFT construction, all groups and
Clay closure remain OPEN. The broad canonical chart has no status change
and is not reprinted.
