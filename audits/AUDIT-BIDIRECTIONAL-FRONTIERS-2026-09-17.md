# Bidirectional construction: inputs available now and open meeting points

Date: 2026-09-17. Source baseline `843ac19`; the three new modules below
were implemented in parallel and checked serially by the parent.

WHOLE-PROJECT GOAL: constructive nontrivial continuum Yang--Mills on R^4
for every compact simple group, with the required same-theory QFT axioms,
isolated vacuum and finite positive physical Hamiltonian mass gap. **OPEN.**

## Decision

The forward-backward method is now explicit in `work_plan.md`. Work backward
from genuine physical requirements and forward from actual original-lattice
objects. A matching name or a conditional bundle is not a meeting point:
the action, carrier, observable, normalization, operator and physical time
must agree. No canonical frontier field has been modified in this checkpoint.

Several needed inputs are known and constructed; the full continuum inputs
are not all available. The independent proofs below consume existing data
and fill concrete algebraic or fixed-spacing subgoals. They do not assume
the missing changing-scale estimate, continuum survival or QFT reconstruction.

## 1. Nontrivial survival and physical calibration

Existing inputs are the actual vector `unitExcitation`, its norm one and
positive two-step response floor, in
`lean/YMGap/Continuum/BF4WilsonSpatialUnionNormalizedExcitation.lean:101`,
`:107`, `:151`. These concern the current Wilson union at nome 1/1024.

New `unitExcitation_response_square`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionDyadicResponse.lean:56`, uses
completed Cauchy--Schwarz, time balance and norm one to prove C(t)^2<=C(2t).
`unitExcitation_dyadic_lower`, `_upper`, `_band`, same file at
lines 69, 105, 121, give for every natural k:

    rho^(2^k) <= B(v,T(2*2^k)v) <= q^(2^k).

The vector, form and transfer are the SAME on both sides. This proves a
positive lower response envelope at arbitrarily late dyadic discrete times,
not continuum survival. In particular rho is fixed here: as a lattice time
index grows, the lower bound can approach zero. It supplies no uniform
positive lower bound at fixed physical time along decreasing spacing.

Backward inputs still missing on this current carrier:

- Actual changing-spacing/nome family, original observable comparisons
  and cross-scale Cauchy moduli. `ReferenceWeightStageFamily` and
  `CanonicalSchwingerLimit`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:84`
  and `:121`, specify stage/limit data; their spacing and two-limit moduli
  are not a supplied current-Wilson physical family.
- A nonzero same-limit norm and surviving correlations (or a compatible
  strongly continuous limiting semigroup supplying that survival).
  A producer is **NOT FOUND** in the current `BF4WilsonSpatialUnion*.lean`
  modules, `CanonicalOSRoot.lean` and the dynamic-vacuum modules inspected
  by the parallel review. `ofUniformNormFloor`,
  `lean/YMGap/Continuum/BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler.lean:180`,
  is a conditional construction on an older carrier with supplied variation
  and norm-floor inputs; it does not construct these inputs for this vector.
- Calibration to the SAME actual generator. `massRate`,
  `lean/YMGap/Continuum/PhysicalSeparatorLogRate.lean:212`, constructs
  -log(q)/spacing from supplied separator, spacing and logarithm data.
  For a two-step rate the time spacing is 2*a, not a. `marginRate` at
  line 218 is explicitly a rational lower proxy, not the exact logarithmic
  rate or a Hamiltonian identification. The checked small-nome estimate
  cannot simply be followed along the existing AF chart:
  `no_fine_guard_on_chart`, `no_blocked_guard_on_chart`,
  `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126`, `:133`.

## 2. Same-theory QFT observable algebra

The current completed multiplier, its symmetry and real linearity already
exist: `completedMultiply`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeZeroMultiplier.lean:140`,
and `completedInner_multiplier_balance`, `completedMultiply_realSmul`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeZeroOperator.lean:89`, `:119`.

New `completedMultiply_comm`,
`lean/YMGap/Continuum/BF4WilsonSpatialUnionTimeZeroCommutation.lean:160`,
proves commutation of these actual operators on every completed state,
with arbitrary source loops, spins and support bases. Its proof passes
the scalar-character identity through the original reflected form, common
finite bases and represented pairing limits. `completedInner_multiplier_product_balance`
at line 171 proves symmetry of their product. No arbitrary multiplication
of completed states or null representatives is postulated.

This supplies an equal-time observable algebra law, not continuum spacelike
locality. Detailed backward requirements and exact search scope are in
`AUDIT-PARALLEL-QFT-INPUTS-2026-09-17.md`: changing-spacing limiting fields,
correct scalar/complex-Hilbert interface, Euclidean covariance, regularity,
continuous time/generator, local-field identification and limiting locality
remain open. Older-carrier spatial translations and real-time semigroups
cannot fill current-carrier obligations without a proved bridge. Some
canonical predicates are too weak or scalar-incompatible and need a separate
reviewed statement repair, not a convenient inhabitant.

## 3. Every compact simple group and global forms

Known inputs include an actual constructive group of rational unit
quaternions (`group`,
`lean/YMGap/RepTheory/RationalQuaternionUnitNormGroup.lean:419`) and an
explicit finite-central-subgroup quotient/descent algorithm
(`CentralQuotientPresentation.descendRepresentation`,
`lean/YMGap/RepTheory/ConstructiveRepresentationDescent.lean:230`).
Previously the concrete quaternion sign-quotient example was the eight-point
fixture, `signLocatedQuotientPresentation`,
`lean/YMGap/RepTheory/RationalQuaternionQ8Fixture.lean:260`.

New `signCentralSubgroup`, `signLocator`, `signLocatedQuotientPresentation`,
`signCoset_iff`, `signQuotientWitness_ne_one`, `descendSignRepresentation`
and its pin, in
`lean/YMGap/RepTheory/RationalQuaternionSignQuotient.lean:111`, `:119`,
`:128`, `:134`, `:153`, `:165`, `:176`, construct the quotient of ALL
rational unit-quaternion points by the two scalar signs. The kernel is
exact, lifts are explicit, the quotient is nontrivial, and representation
descent needs just the actual negative-unit test in addition to the supplied
homomorphism. This is a real algebraic instance, not a group-name relabel.

It is not compact SO(3), a compact topology, Haar integration or a proof
that every rational rotation lifts to a rational unit quaternion. Those
identifications are not asserted. More generally `CompactSimpleGlobalFormCode`,
`lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:318`, records a finite
marked center code and explicitly contains no group realization. SU(3)
`dim` and `threeCasimir`, `lean/YMGap/RepTheory/SU3.lean:41`, `:45`,
are arithmetic data, not group/Haar constructions. The code-general bound
`cartanType_weylDimData_crude`, `lean/YMGap/RG/WeylDimGeneralData.lean:137`,
still consumes actual Weyl factors and their product estimate. Actual
per-group representation/Haar/action data and same-theory analytic/scaling
proofs are not supplied by these codes or by the new rational quotient.

## 4. Verification and next execution

All three final focused checks passed through `scripts/safe_lean_build.py`
with one worker and an explicit 20 GiB worker ceiling. All 24 printed gates
are within {propext, Quot.sound}; three quotient-module declarations are
axiom-free. Parent read the complete sources. No sorry introduced/discharged,
new analytic oracle, altered canonical field, resource configuration or CI
change. Three semantic-root imports were added; root/full-tree/full audit,
guard and progress runs were NOT performed.

The quotient check first lacked a dependency olean. A single dependency-
complete target supplied it; that invocation inherited the existing Lake
32 GiB ceiling and ended on elaboration errors without a pressure stop.
This was not the intended 20 GiB invocation. The corrected final check used
an explicit 20 GiB limit. Subsequent dependency targets must also pass
`--lake-worker-limit-gib 20` rather than relying on the current Lake default.

| Final log in `/tmp/` | SHA-256 |
| --- | --- |
| `ym-wilson-dyadic-response-20260917.log` | `a6222bbcf4e969a82ebf3bc53844c136f37e74930bb21439e5d65e95932dc434` |
| `ym-wilson-timezero-commutation-20260917.log` | `808ebee1e3c81738b41c25b370b6b407341a99f54a41ed349d1f39baf2ecd048` |
| `ym-rational-quaternion-sign-quotient-20260917.log` | `ff11bdee21fcd03f4a3bb81605e69adb1af9d0e907f4be3f6418729768f39f25` |

Continue the forward interacting estimate while selecting further independent
backward tasks only when a concrete supplied input and exact consumer are
identified. The missing signed bulk estimate, regulator-uniform Wilson orbit,
same-theory scaling/QFT and every-group endpoint remain OPEN. Parallel proof
progress neither bypasses those joins nor measures proximity to the Clay goal.
