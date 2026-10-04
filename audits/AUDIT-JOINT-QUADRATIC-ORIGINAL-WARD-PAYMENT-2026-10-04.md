# Quadratic scalar cancellation and the SAME original heat/Ward join

The unchanged whole-project target remains OPEN: constructive continuum
Yang--Mills on R^4 for EVERY compact simple group, with SAME-theory full QFT
axioms, nontrivial survival and finite positive physical Hamiltonian mass.
This milestone proves finite SU(2) inequalities, not that target.

## Mathematical contraction

Set ell=side(scale), a=w^(12*ell), beta=w^(32*ell), d=1-beta,
k=2*a-1-beta and h=1-w^(4*ell). For EVERY strict nome and every ell,

```
0 <= a*d-4*k <= 36*h^2.
```

These are `exactSquareCredit_massResidual_nonnegative` and
`exactSquareCredit_massResidual_quadratic_upper`,
`lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:368` and
`lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:409`.
The proof uses x=w^(4*ell) and exact finite polynomial factorizations
F=(1-x)^2*P(x), P(x)+(1-x)*B(x)=36. Both P and B are explicitly presented
as sums of nonnegative powers and power deficits on [0,1]. Thus the scalar
residue has no first-order term. No Taylor remainder or analytic assumption
is used. The constant 36 is independent of cutoff/width/depth/ell, but h
depends on nome AND ell; this is not a uniform physical rate or trajectory.

The actual original raw second moment U and partition Z satisfy

```
per*(4-U/Z) = Angular,         per=4*ell.
```

Here Angular is `normalizedAngular` of the SAME original odd marginal.
`paddedSquare_rawSecond_deficit_angular_pin`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareJointQuadraticDebt.lean:75`,
proves this using literal character fusion, original marginal normalization
and `paddedSquare_angular`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareWardMoments.lean:359`.
No foreign private declaration, substituted density, center or filtered
source is used. The heat and angular branches meet through this equality.

Keep the ENTIRE increment I from the preceding checked joint payment and
the ACTUAL channel loss L=M-Z. With E the normalized original energy,

```
per*((1+beta)*(4*E+I/Z)+(k/2)*(I/Z))
 <= 144*per*h^2 + 4*per*a*d*(L/Z) + 4*k*Angular.
```

This is `paddedSquare_energy_joint_quadratic_angular_payment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareJointQuadraticDebt.lean:120`.
It requires k>=0, K>=headCutoff and K>=2; arbitrary depth, including zero,
is allowed. It does NOT bound the remaining loss or angular cost by the
surviving variance. There is no universal numerical dominance claim over
previous ceilings.

## Actual chronological and signed Ward consumers

`originalOwnBlockCost_joint_quadratic_angular_boundary_paid`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareJointQuadraticDebt.lean:228`,
replaces E by the ACTUAL chronological Cost and adds
4*per*(1+beta)*(eta*RawRef+Signed) to the right. It preserves the stage OWN
center and BOTH original partitions. Only boundary drift is paid, by its
computed terminal tolerance; its raw endpoint reference square is not the
filtered-start norm. This variant additionally requires endpoint depth>=1.

The full original normalized OWN Ward identity is
`paddedSquare_normalized_ward`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareVarianceTaylor.lean:231`:
Angular+Ward_norm=3*per*endpointOWNVar. Keeping Ward's sign gives

```
per*((1+beta)*(4*Cost+I/Z)+(k/2)*(I/Z)) + 4*k*Ward_norm
 <= 144*per*h^2 + 4*per*a*d*(L/Z) + 12*per*k*endpointOWNVar
      + 4*per*(1+beta)*(eta*RawRef+Signed).
```

This is `originalOwnBlockCost_joint_quadratic_ward_boundary_paid`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareJointQuadraticDebt.lean:305`.
Ward uses the endpoint's OWN interacting mean; Signed and RawRef retain
the chronological STAGE mean. Their means and norms are not identified.
No sign is assigned to Ward or to Signed. Adding the same signed term to
both sides needs no positivity premise; the original k>=0 guard remains
needed for the upstream increment credit.

## Repointed next analytic frontier

The source-independent first-order scalar contribution is now cancelled.
The action-specific residue is the JOINT signed combination

```
per*a*d*(L/Z) - k*Ward_norm
```

alongside endpoint OWN variance, COMPLETE Signed, paid RAW-reference drift
and retained favorable increment. Estimate that combination against the
SAME surviving filtered-start norm; do not separately majorize Ward away
or identify endpoint OWN variance with the filtered norm. No such useful
changing-family/window estimate is supplied here. The actual backward
consumer remains `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`.
The new inequalities do not assume that consumer's conclusion or substitute
Signed=Cost-(energy+drift) as a circular proof.

Justified scaling, continuum survival, physical calibration, SAME OS/full
QFT/continuum and every group remain OPEN. Supporting A03 only; exact
canonical chart claims are unchanged, so no ASCII/paper-list reprint.

## Verification boundary

Two final serialized focused targets exited 0. All SIX new public gates
report exactly {propext, Quot.sound}; both final logs have no warnings or
errors. The earlier three-theorem version of the new target also passed.
Independent frozen mathematical and evidence reviews passed.

| Accepted log under `/private/tmp/` | SHA256 |
| --- | --- |
| `ym-joint-scalar-quadratic-20261004-1.log` | `cbe3da4a04bb1bf88c475bbae131e40912cd21491fbe9d91109e4a08a73ba5ea` |
| `ym-original-joint-quadratic-angular-20261004-2.log` | `83a4b8ef0880879bc0f3a93ed78484835588b9146c7e863d093a26d5ec97a615` |

Frozen source SHA256 in scalar / original-payment order:

```
fbc8fa67d1cf5efad30e3bb0afa6c42444fb9b15d71f99bac8ac3177cd969397
0df1073d7492383a0c8bfc9d6b7f93a6cc7f18b561f583ca1375303647e9c6a9
```

ONE monitored 20-GiB worker, 12-GiB OS reserve and a fresh process/pressure/
swap preflight were used for each run; no competing compiler, 76% free
memory and zero swap. No raised resources, new sorry/axiom/Classical/
native_decide, analytic budget, weakened frontier or CI change.
The new root import is registration ONLY, NOT root verification. No
full/root build, broad audit, guard or metrics run. The goal remains ACTIVE.
