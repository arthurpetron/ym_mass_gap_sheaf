# Original six-moment pilot: quantitative feasibility screen

Source review, exact scalar arithmetic and a small geometry diagnostic.
This feasibility screen involved no Lean edits or theorem checks, and no
Haar moment or auxiliary-state margin was evaluated. Subsequent scalar
proof work is recorded separately in
`AUDIT-ORIGINAL-CHEBYSHEV-SQRT-RATE-2026-09-30.md`. The scaling estimate
and same-theory continuum/Clay target remain open.

## Why this check changes the next action

The direct comparison needs six original raw moments, not six inexpensive
numbers. The existing all-nome canonical positivity cutoff is already at
least 627 at nome 1/2. A Cartesian spin-assignment expansion on even a
24-face core would therefore enumerate at least 628^24 assignments.
Do not launch that expansion. This does NOT exclude compressed integration,
alternative proved positivity cutoffs, or an analytic estimate.

The existing test is not being rebuilt. Its declarations are
`marginValue` and `reverse_energy_of_finite_test`,
`lean/YMGap/Continuum/BF4ExactSlabChebyshevFiniteTest.lean:79` and `:115`.
The weaker direct diagnostic follows algebraically from
`finite_covariance_cleared`,
`lean/YMGap/Continuum/BF4ExactSlabConnectedFaceResponse.lean:176`:
with `D(p,q)=Z*M(p*q)-M(p)*M(q)`, test
`D(p,q)^2 <= r^2*D(p,p)*D(q,q)` on the SAME action.
Success for one pair does not prove reverse energy, all-observable control,
or a parameter-uniform estimate.

## The canonical cutoff lower bound

Write `L=headFloor(w)`, `U=prefixCap(w)`, `Q=w*w`. Existing results give
`0<L<=1/32` and `U>=1`:

- `headFloor_positive`,
  `lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:52`;
- `headFloor_le_oneThirtySecond`,
  `lean/YMGap/Continuum/BF4ExactSlabSharedWindowFloorBound.lean:46`;
- `prefixCap_ge_one`,
  `lean/YMGap/Continuum/BF4ExactSlabStarRateObstruction.lean:32`.

The actual definitions, in ordinary rational-value notation, are

```
epsilon = weightTolerance(w,L) = L / (2*(U+1)) <= 1/128
A       = lossScale(Q)         = 2 / (1-Q)
delta   = lossTolerance(Q,epsilon) = epsilon / (A+1)
```

Sources: `weightTolerance`,
`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:51`;
`lossScale`, `lossTolerance`, and `lossCutoff`,
`lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean:36`, `:42`, `:60`.

`powBaseCutoff` takes the positive numerator of the rational
`1/((1-Q)*delta)`, not a logarithmic cutoff:
`lean/YMGap/Continuum/HeatKernelConvGen.lean:266`.
The quotient convention is `HKConv.divPos`,
`lean/YMGap/Continuum/HeatKernelConv.lean:126`, with denominator identity
`divPos_den_cast` at `:136`. Since a structural rational denominator is at
least one, this numerator is at least its rational value. Consequently

```
lossCutoff >= 128*(2/(1-Q)+1)/(1-Q).
w=1/2: Q=1/4, so lossCutoff >= 5632/9, hence lossCutoff >= 626.
headCutoff = bandSize + lossCutoff >= 1+626 = 627.
```

The last equality uses `bandSize` and `deficitCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabJacobiDeficitInterval.lean:49`, `:69`;
`centeredCutoff`,
`lean/YMGap/Continuum/FiniteJacobiWeightConvergence.lean:88`;
and `headCutoff`,
`lean/YMGap/Continuum/BF4ExactSlabRetainedHeatHeadComparison.lean:55`.
Main and Sol independently checked this derivation against source. Tiny
Python `Fraction` arithmetic checked 5632/9 and the integer ceiling. This
derived lower bound is not recorded as a new Lean theorem. Unreduced
rational representations can make the actual cutoff larger still.

## Small geometry diagnostic, not a reduced-action theorem

`boundaryCompleteSlabPlaquettes`,
`lean/YMGap/Continuum/Z4HalfTimeReflectionGeometry.lean:169`, retains
3(E+1)^4 spatial and 3E(E+1)^3 temporal faces. The existing executable
mirror is `boundary_complete_slab_plaquettes`,
`computations/dual_half_time_reflection_route.py:122`.
Luna inspected the definitions; main ran a bounded E=0,1,2,3 diagnostic
using this mirror and `edges_of` from
`computations/dual_positivity_geometry_bridge.py:57`.

The diagnostic repeatedly removes a face with a link incident to exactly
one remaining face. It handles finite incidence sets only: no characters,
heat polynomials, Haar contractions, representation sums or compiler.

| E | Full faces | Full links | Full vertices | Removed faces | Remaining faces | Remaining links |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 3 | 9 | 7 | 3 | 0 | 0 |
| 1 | 72 | 116 | 52 | 48 | 24 | 32 |
| 2 | 405 | 513 | 189 | 189 | 216 | 216 |
| 3 | 1344 | 1488 | 496 | 480 | 864 | 768 |

Extent zero has no temporal face. Extent one is NOT literally a 24-face
action; its 24-face remainder is the output of this graph diagnostic.
No equality of the original six moments with reduced moments was proved.
Such an equality must check that the observables avoid each removed link.
The existing fixed-spatial result `spatialWeight_haar_active`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialActiveSpatialWeight.lean:130`,
is a precedent with explicit independence hypotheses, not a pin for this
whole-slab diagnostic.

Even assuming that reduction is supplied, the naive 24-face label expansion
at K>=627 has at least

```
628^24 = 14158963092163953508691265632276558109170103555323872424556658425856
```

candidate assignments BEFORE admissibility and contraction. This is not a
lower bound on the runtime of every possible algorithm. No large run was
started and no successful six-moment instance is claimed.

## Targeted literature screen: finite groups are not compact SU(2)

Adhikari--Cao, [Correlation decay for finite lattice gauge theories at weak
coupling](https://arxiv.org/html/2202.10375v3), Theorem 1.1, treats finite
groups with a Wilson exponential action. Section 3 uses a weight-preserving
two-copy swapping map; Section 6 bounds the failure event. The decay uses
the positive nonidentity character defect Delta_G from Section 1.3 and
constants involving the finite group cardinality. This supplies no bound
for the repository's compact SU(2) heat action. No theorem was imported.

Our elementary obstruction to transplanting that defect assumption is
constructive: the rational unit quaternions
`q_N=((N^2-1)/(N^2+1), 2*N/(N^2+1), 0, 0)`, N>=1, are nonidentity and
have fundamental trace defect `2-2*(q_N).scalar=4/(N^2+1)`.
For epsilon=a/b>0, N=4*b+1 makes the defect smaller than epsilon.
Thus there is no positive uniform defect away from the identity on this
rational SU(2) subcarrier. This argument is not a mass-gap counterexample
and has not been formalized here. The paper's swapping idea alone does not
provide a compact-group replacement for its probability estimate.

The cached general math-ph listing was reused, not refreshed. This was a
targeted primary-source scope check. Next work remains the useful averaged
signed estimate on the original action, or a genuinely bounded compressed
calculation with its same-action pin; no further conditional compiler is
warranted by the present screen.
