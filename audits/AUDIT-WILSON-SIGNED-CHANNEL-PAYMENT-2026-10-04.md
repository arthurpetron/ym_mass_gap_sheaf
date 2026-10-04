# Actual long-Wilson variance credit in the complete signed energy

Two final focused checks and independent frozen-source semantic/evidence
reviews passed. The unchanged whole-project target remains OPEN:
nontrivial continuum Yang--Mills on R^4 for EVERY compact simple group,
SAME-theory full QFT axioms and a finite positive physical Hamiltonian gap.
This increment is an original finite SU(2) comparison, not scaling closure.

## Forward/backward meet

The backward macro consumer uses the long padded Wilson square, not the
elementary plaquette-family sum: `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
Forward, the new producer uses that literal square's sourceCharacter F,
the actual q=fringeProject(V*g_(n+1)), and its original partition Z.
Selected links have proved length 4*side(scale). Both source bands use
one actual projected spectator R, with proved active independence:

```
l*R <= q <= u*R,
l = localLower(w,4*side), u = localUpper(w,4*side), rho = l/u.
Q = squareChannelMoment(actual g_(n+1)).
```

Keeping q*F^2 unchanged in the first source leg and comparing only the
second leg gives l*rawSecond<=u*Q. The actual raw second moment bounds
Z*OWNVar(F), hence Q>=rho*Z*OWNVar(F). Only the mixed pair with the
active-independent R is identified with full heat. Q is NOT replaced by
a partial productMap moment; shared unselected coordinates are retained.
Only the positive scalar u is inverted; zero variance is included.

The complete existing signed moment bound is
`paddedSquare_energy_exact_channel_moment_bound`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelMomentBalance.lean:350`.
With h=1-w, t=h^2/2, P=perimeter(scale), and the actual channel mass M,
it bounds normalized original energy E by

```
[(h+t)*P*(4*M-Q) + t*P^2*(5*Q-8*M) + Err] / Z.
```

Err is the ENTIRE `activeChannelSobolevBudget`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareActiveChannelSobolev.lean:96`,
including its original OWN-centered active error and omitted-mode budget.
Combine all opposite signs FIRST:

```
alpha = (h+t)*P - 5*t*P^2,
beta  = 4*(h+t)*P - 8*t*P^2,
numerator = beta*M - alpha*Q + Err.
```

For explicit alpha>=0, the actual credit now proves

```
E + alpha*rho*OWNVar(F) <= (beta*M + Err)/Z.
```

No favorable sign of curvature alone is claimed or discarded. Scalar
arithmetic proves alpha>=t*P>0 in the sufficient window h*P<=2/5:
x=h*P satisfies x-(5/2)*x^2>=0 and alpha=t*P+x-(5/2)*x^2.
This numeric condition is NOT an inhabited physical scaling trajectory.

| Declaration | Source | Role |
| --- | --- | --- |
| `paddedSquare_channelMoment_rawSecond_linear` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceCredit.lean:193` | Actual long-square channel versus original raw second moment. |
| `paddedSquare_channelMoment_oddVariance_linear_cleared` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceCredit.lean:239` | SAME partition and OWN variance; no norm inversion. |
| `paddedSquare_channelMoment_oddVariance_credit` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceCredit.lean:261` | Computed rho=l/u pays the actual Q. |
| `signedSquareCoefficient` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedChannelPayment.lean:44` | Explicit alpha after complete signed combination. |
| `signedMassCoefficient` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedChannelPayment.lean:51` | Explicit beta for the SAME channel mass. |
| `signedSquareCoefficient_ge_quadratic_window` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedChannelPayment.lean:65` | h*P<=2/5 implies alpha>=t*P. |
| `signedSquareCoefficient_positive_window` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedChannelPayment.lean:101` | Strict positivity from the explicit numeric window. |
| `paddedSquare_energy_full_signed_variance_payment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareSignedChannelPayment.lean:133` | Original full signed energy consumer, with mass and error retained. |

## Exact remaining input

The actual beta*M+ENTIRE Err still needs useful control versus SAME surviving
variance. rho retains explicit nome/perimeter dependence through
`localLower` and `localUpper`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:44`
and `lean/YMGap/Continuum/BF4ExactSlabFixedSpatialUniformLocalBand.lean:47`.
No useful scaling-uniform credit or corrected energy ratio is proved.

Endpoint OWN variance is NOT the filtered starting norm in
`originalOwnBlockVariance`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`.
The macro consumer above still needs an eventual ORIGINAL aggregate bound
2*originalWindowCost(stage,u,u)<=(1-kappa)*originalOwnBlockVariance(stage,u).
It retains the common stage OWN center and separate lag partitions.
The existing exact original Rayleigh split also retains boundary drift and
signed multiplication cost:
`original_block_rayleigh_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`.
No new identity identifying these quantities is asserted.

NEXT: useful actual mass/error and joint chronological signed-cost control,
on an explicitly justified changing family. Nontrivial continuum survival,
physical mass, SAME OS/full QFT passage, every compact simple group and
Clay remain OPEN. Partial A03 only; the canonical chart's displayed claims
do not change, so no ASCII chart or paper list is reprinted.

## Verification boundary

Accepted final checks exited 0 without warnings/errors. Eight NEW printed
gates: two scalar definitions are axiom-free; all six theorems use only
{propext, Quot.sound}.

- `/private/tmp/ym-wilson-square-channel-credit-20261004-2.log`: three
  gates; SHA256 `dbe790321d6c68f21364054298a432e7dec0b6d8a7ee3c7ae427b9de789d9b5d`.
- `/private/tmp/ym-wilson-square-signed-payment-20261004-3.log`: five
  gates; SHA256 `9f7d129278df70f9a29d1a2e54e320805783cbeb7f99f80b6ec5db82489413f6`.

Frozen source SHA256:

- `BF4DyadicWilsonSquareChannelVarianceCredit.lean`:
  `81105c3b5ef3318e564a4e977c2e5e62aba722ac44aaababdf37c744f8e135a7`.
- `BF4DyadicWilsonSquareSignedChannelPayment.lean`:
  `661d54846eba07c2be69eb0d92dc8ce0ab719ffa86fb76f57f6142addbc73aac`.

First producer/consumer attempts failed on a namespace and rational
positivity repair; they are REJECTED evidence. The consumer's final replay
followed a comment-only nonpositive/negative wording correction; proof
bodies were unchanged from independent frozen review. No budget increase
was needed. Each run used ONE monitored worker capped at 20 GiB, a 12-GiB
reserve, and fresh process/pressure/swap checks; swap was zero.
No sorry, new axiom, Classical/native_decide/noncomputable declaration,
analytic budget premise, weakened frontier, CI/resource change or chart
closure. Root import registration is NOT root verification. No full/root
build, broad audit, guard or metrics run; CI stays off.
