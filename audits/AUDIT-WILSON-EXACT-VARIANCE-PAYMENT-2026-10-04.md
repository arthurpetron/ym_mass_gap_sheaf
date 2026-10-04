# Exact original long-Wilson variance payment

Two final focused checks and independent source/evidence review passed.
The unchanged whole-project target remains OPEN: nontrivial continuum
Yang--Mills on R^4 for EVERY compact simple group, SAME-theory full QFT
axioms and a finite positive physical Hamiltonian gap. This increment is
an actual finite SU(2) comparison, not an inhabited scaling trajectory.

## Mathematical meet

The exact heat identity already existed:
`paddedSquare_energy_exactChannel_increment`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:217`.
It uses the literal long padded Wilson square F and actual terminal source,
with both heat images evaluated exactly. At depth n+1, put

```
L = side(scale), a = w^(12*L), b = w^(32*L), k = 2*a-1-b,
Z = ORIGINAL oddMass(n+1), V = SAME OWN oddVariance(n+1,F),
E = normalized ORIGINAL energy(n+1,F),
M = actual squareChannelMass, Q = actual squareChannelMoment,
I = ENTIRE actual squareChannelIncrement, rho = computed localLower/localUpper.
```

The existing exact identity gives

```
E + I/(4*Z) = ((1-b)*M-k*Q)/(2*Z).
```

The new causal piece is to insert the already-constructed ACTUAL square
credit Q>=rho*Z*V from `paddedSquare_channelMoment_oddVariance_credit`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelVarianceCredit.lean:261`.
For explicit k>=0 this now proves

```
E + I/(4*Z) + (k*rho/2)*V <= ((1-b)/2)*M/Z.
```

The ENTIRE increment I is retained, not replaced by its weaker response-
square floor. Its sign is constructed by the existing
`squareChannelIncrement_nonnegative`,
`lean/YMGap/Continuum/BF4DyadicWilsonSquareChannelExactResponse.lean:139`.
There is no Taylor, cubic or omitted-mode error in this exact alternative.
No universal numerical ordering against the earlier Taylor ceiling is proved.
All original source/action factors, OWN variance and partition remain.
Only positive original Z and the computed positive local-band scalar u
are inverted; no excitation norm is inverted. K>=2 is explicit, separately
from K>=headCutoff(w). No centered heat eigenpin is asserted: constant
shifts preserve energy and I, not the false formula P(F-c)=a*(F-c).

## Short coefficient argument

Set x=w^(4*L), d=1-x. The existing
`BondMovingQuadratic.secondOrder_qpow`,
`lean/YMGap/Continuum/BondMovingQuadratic.lean:137`, at degree 8, and
`R1CornerAtoms.oneSub_qpow_le`,
`lean/YMGap/Continuum/R1CornerAtoms.lean:45`, at degree 3, give

```
8*d-(1-x^8) <= 64*d^2,       1-x^3 <= 3*d,
k >= 2*d-64*d^2.
```

The same linear deficit bound at degree 4*L supplies the explicit cleared
windows: (1-w)*(128*L)<=1 implies 32*d<=1 and k>=0;
(1-w)*(256*L)<=1 implies 64*d<=1 and k>=d. For L>0 and 0<w<1,
strict power contraction gives d>0. No finite polynomial expansion or
additional analytic dominance field is used.

| Declaration | Source | Role |
| --- | --- | --- |
| `exactSquareCredit` | `lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:24` | Explicit negative of the signed square coefficient. |
| `exactSquareCredit_nonnegative_window` | `lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:140` | Cleared 128*L numeric sign window. |
| `exactSquareCredit_ge_deficit_window` | `lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:177` | 256*L window gives k>=1-w^(4*L). |
| `exactSquareCredit_positive_window` | `lean/YMGap/Continuum/SU2HeatExactSquareCreditWindow.lean:213` | Strict positivity for nonempty side, not a uniform floor. |
| `paddedSquare_energy_exact_variance_payment` | `lean/YMGap/Continuum/BF4DyadicWilsonSquareExactVariancePayment.lean:50` | Actual SAME-variance consumer with full increment retained. |

## Backward residue and next action

The retained original mass/increment combination still needs useful JOINT
control against SAME surviving chronological filtered-start variance.
Do not majorize the mass and increment separately and lose this cancellation.
Endpoint V is NOT `originalOwnBlockVariance`,
`lean/YMGap/Continuum/BF4WilsonAllNomeDyadicOriginalRayleighLimit.lean:93`.
The actual aggregate input of `original_window_budget_macro_ratio`,
`lean/YMGap/Continuum/BF4WilsonAllNomeWindowSignedCost.lean:245`, is still
unfilled: eventual 2*originalWindowCost(stage,u,u)
<=(1-kappa)*originalOwnBlockVariance(stage,u), with the common stage OWN
center and each lag's distinct masses. The original Rayleigh split also
retains boundary drift and signed multiplication cost:
`original_block_rayleigh_split`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialBlockRayleighSplit.lean:244`.

Neither numeric window constructs or justifies physical spacing/coupling
calibration. rho and k retain explicit nome/loop-side dependence. Useful
changing-family/window control, nontrivial continuum survival, finite positive
physical mass, SAME OS/full QFT, every compact simple group and Clay remain
OPEN. Partial A03 only; exact canonical chart claims are unchanged, so no
ASCII chart or paper list is reprinted.

## Verification boundary

Accepted final logs exited 0 without warnings/errors. Five NEW public gates:
one scalar definition axiom-free; all four theorems use only
{propext, Quot.sound}.

- `/private/tmp/ym-exact-square-credit-window-20261004-3.log`: four gates;
  SHA256 `74155a5078d116dc5d7f9c1cb6cfe237d74a72a97f6c220d12a168a9b7ff5060`.
- `/private/tmp/ym-wilson-exact-variance-payment-20261004-2.log`: one gate;
  SHA256 `4d540e84b16c28ef00753681a9f0283666d8dd894a55a6186650d69112e46e8f`.

Frozen source SHA256:

- `SU2HeatExactSquareCreditWindow.lean`:
  `492092ed2d4b9817d428af0c435d3fed2bf680c8537de63c20bc8f807fb7c9bc`.
- `BF4DyadicWilsonSquareExactVariancePayment.lean`:
  `e3e81907c6bbcda239a93250443b76bbcaa3c8c14d1ab2d2f094f190e151fe78`.

The first two scalar attempts and first consumer attempt failed on lambda
layout, a missing existing positivity-helper import, and explicit unfolding;
they are REJECTED evidence. No budget increase was needed. Each run used ONE
monitored worker capped at 20 GiB, a 12-GiB reserve, and fresh process/memory-
pressure/swap checks; swap was zero. Independent frozen semantic/evidence
reviews passed. No sorry, new axiom, Classical/native_decide/noncomputable,
analytic budget premise, weakened frontier, CI/resource change or chart
closure. Root import registration is NOT root verification. No full/root
build, broad audit, guard or metrics run; CI stays off.
