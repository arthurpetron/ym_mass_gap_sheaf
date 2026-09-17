# Original spatial Wilson observables: parallel proof checkpoint

Date: 2026-09-17 UTC. Base: `eac824a`, committed and pushed before this work.
The preceding normalized-excitation goal turn is classified **PROGRESS**.

## Whole-project goal and current boundary

For EVERY compact simple gauge group, construct a nontrivial continuum
Yang--Mills theory on R^4 with the required QFT axioms, isolated vacuum and
strictly positive physical Hamiltonian mass gap. The action, observables,
limiting state and operators must belong to the SAME theory. Retain the
constructive, Mathlib-free MLTT/HoTT gate. **The Clay target remains OPEN.**

This checkpoint proves original-observable realization, not a new gap. The
existing strict bound is on the plaquette-generated spatial union. The new
finite Wilson algebra is NOT asserted to embed into that completion, and its
strict completed bound is NOT supplied by the old theorem.

## Why this is the next causal join

The existing carrier is already richer than single plaquettes: it contains
finite signed sums of arbitrary products of scheduled plaquette characters.
The exact syntax is `Span`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialReflectedForm.lean:54`, using
`FaceFactor`, `lean/YMGap/Continuum/BF4ExactSlabTemporalSweep.lean:52`;
`PhysicalSpan` is the physical subtype,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialIntrinsicSeminorm.lean:30`.

An existing finite obstruction prevents identifying every Wilson loop with
an expression in individual plaquette traces by mere pointwise recoding:
`SU2PlaquetteCharacterNonseparation.no_pointwise_plaquette_recoding`,
`lean/YMGap/Continuum/SU2PlaquetteCharacterNonseparation.lean:311`.
Its precise domain is the old `PlaquetteExpression 0`, not a theorem named
for current `Stage`, and it proves neither OS-norm nor dynamical nondensity.

Conversely, substantial analysis already applies to arbitrary supported
polynomials: `originalChain_finiteValue_nonnegative`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialChainReflectionPositive.lean:61`,
and `polynomialWindowCauchy`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWindowTimeLimit.lean:115`.
The missing original-loop interpretation of the source polynomial was a
separate finite algebraic/geometric join. The results below supply that join
for arbitrary closed spatial loop characters and their single-slice time
expectations, without re-proving completion or Cauchy--Schwarz.

## Proved arrows

All module paths in the table are under `lean/YMGap/Continuum/`.

| Mathematical arrow | Declaration and source |
| --- | --- |
| Arbitrary finite ordered path -> endpoint gauge conjugation | `SU2QuaternionHaarGaugeWord.gauge_word`, `SU2QuaternionHaarGaugeWord.lean:74` |
| Closed endpoint -> unchanged all-spin character under every spectator | `closed_character`, `SU2QuaternionHaarGaugeWord.lean:104` |
| Actual original oriented edges -> image under the ONE full temporal ledger | `ledger_word`, `BF4ExactSlabTemporalGaugeWilsonWord.lean:161`; `ledger_character`, same file:177 |
| Closed same-slice physical loop -> every-cut invariance with supported spectators | `ledger_invariant`, `BF4ExactSlabTemporalGaugeWilsonWord.lean:277` |
| Observable AND full action transformed together -> unchanged original observable with swept action | `invariant_step_haar`, `BF4ExactSlabTemporalInvariantSweep.lean:50`; `invariant_original_chain_pairing`, same file:94 |
| Signed products of actual loops at arbitrary individual times -> same original-chain identity | `Expression`, `BF4ExactSlabSpatialWilsonAlgebra.lean:49`; `evaluate_ledger_invariant`, same file:88; `original_chain_pairing`, same file:155 |
| Width-only loop -> literal physical time placement | `SourceLoop`, `BF4ExactSlabFixedSpatialWilsonProbe.lean:44`; `placeLoop`, same file:82 |
| Source character -> exact original slab character, coefficient-sensitively | `sourceCharacter_pin`, `BF4ExactSlabFixedSpatialWilsonProbe.lean:167` |
| Original loop + original selected action -> existing middle-message numerator | `original_loop_pairing`, `BF4ExactSlabFixedSpatialWilsonTimeLimit.lean:62` |
| Both reciprocals -> SAME partition normalization | `middleRatio_originalLoop`, `BF4ExactSlabFixedSpatialWilsonTimeLimit.lean:90` |
| Actual finiteValue diagonal -> computed Cauchy data and existing polynomial-state limit | `originalLoopCauchy`, `BF4ExactSlabFixedSpatialWilsonTimeLimit.lean:142`; `originalLoop_converges`, same file:167 |
| Existing dense presentations -> literal cross-product source/placed semantics | `sourceSpan_spanProduct`, `BF4ExactSlabFixedSpatialSpanProduct.lean:113`; `placedSpan_spanProduct`, same file:120 |
| Dense product -> compatible physical time/base inclusion | `physicalTime_mulSpan`, `BF4ExactSlabFixedSpatialSpanProduct.lean:149`; `inclusion_mulSpan`, same file:154 |

The cancellation proof never commutes quaternion factors. Invariance of a
product transforms BOTH factors first; cancellation of the first keeps the
transformed second factor in the supported spectator. No shared link or action
factor is dropped. The common-action consumer applies invariance with the
complete transformed action as spectator, not with the unit alone.

## Parameters and the actual time limit

`originalLoopScalar`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialWilsonTimeLimit.lean:124`, uses
ambient extent `width+(m+n)`, selected chain start `0`, length `m+n`, and the
literal loop shifted to time `m`. On the diagonal this is extent `width+2*t`
with the loop at `t`. The source polynomial
`sourceCharacter width loop.edges spin` remains fixed; the varying original
observable is identified with it BEFORE passing to the limit by
`originalLoopScalar_pin`, same file:130.

`originalLoopCauchy_modulus`, same file:158, displays exactly
`intervalMiddleModulus(hw0,hw1,width,polynomialCap(sourceCharacter),epsilon)`.
The defining `intervalMiddleModulus`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPolynomialMiddleTime.lean:155`,
is `geometricCutoff(mixRate(hw0,hw1,width), (c+c)+(c+c), epsilon)`.
It is independent of the retained stage in `K=headCutoff(w)+stage`, but
depends on nome, spatial width and the source polynomial. Width and cutoff
are fixed during this time limit. No spatial/heat-cutoff interchange or
spacing-uniform estimate follows.

The target is the pre-existing `expectation`,
`lean/YMGap/Continuum/BF4ExactSlabFixedSpatialPolynomialState.lean:73`, with
the same source polynomial and K. The new time theorem concerns one arbitrary
source-loop character, at every spin; a common multi-time source/limit pin for
all of `Expression` is not claimed by that theorem.

## Five-front parallel-work assessment

| Requested front | What can proceed independently | Required join still open |
| --- | --- | --- |
| Nonconstant excitation | Fixed-nome unit excitation and positive strict response are already constructed: `normalizedCertificate`, `lean/YMGap/Continuum/BF4SpatialUnionNormalizedExcitation.lean:160`. | Survival/nontriviality in the SAME continuum limit, not another finite witness. |
| Full Hilbert/OS/QFT | Actual observable algebra, placement, reflection and source identities can be developed in parallel; this checkpoint supplies several of them. | Enlarged reflected carrier/limit, coverage or computed approximation, strict bound on that carrier, scalar-compatible canonical OS realization, continuous-time QFT. |
| Spatial and spacing control | Full spatial group action and changing-coupling original-action estimates are independent investigations. | Existing positive diagonal semigroup is not the full spatial group; the small-nome AF obstruction remains (`no_fine_guard_on_chart` / `no_blocked_guard_on_chart`, `lean/YMGap/Continuum/BF4SmallNomeAFGuardObstruction.lean:126` / `:133`). |
| Positive physical mass | Reuse the scalar rate compiler, e.g. `fullMassRate`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogRate.lean:108`. | Actual SAME-transfer physical-length and finite-rate inputs, including the supplied `FullRangeLogRateCeiling`, `lean/YMGap/Continuum/PhysicalSeparatorFullLogComparison.lean:163`. Fixed-nome contraction is not that calibration. |
| Every compact simple group | Actual group/global-form representation, Haar and action producers can be built separately from SU(2) completion. | No new such producer in this checkpoint. The conditional `mass_gap_of_cartanType`, `lean/YMGap/MassGap/AllSimpleTypes.lean:280`, is not a physical all-group construction; `so3_spinHalf_rejected`, `lean/YMGap/RepTheory/CompactSimpleGlobalForm.lean:443`, precludes reusing the spin-half probe unchanged for SO(3). |

There is useful parallel work in all five areas, but they are NOT five
independent solutions whose endpoints can be combined by matching names.
The mathematically load-bearing joins are the common observables, action,
state, transfer, physical scale and group. This turn used parent plus three
agents for finite ordered algebra, source placement, action/time integration
and independent reviews. Compilation remained serialized.

The canonical scalar mismatch is unchanged: `PositiveTimeOSRoot.positive`
is `GNSData`, `lean/YMGap/Continuum/CanonicalOSRoot.lean:272`, whose `B` is
rational-valued (`lean/YMGap/Continuum/GNSQuotient.lean:102`).
`stateEssentiallySurjective`, `CanonicalOSRoot.lean:296`, quantifies over
the dense positive space; a normalized completed RC-valued vector does not
by itself fill it. No canonical field was weakened or declared closed.

## Next bounded consumer

Extend the original source/reflection realization to products of actual loop
characters in a fixed positive-time window, then use the existing finite
original-chain reflection positivity with those literal polynomials. The
cutoff/spatial limits and the estimate on the resulting SAME reflected
carrier remain separate proofs. An ordinary positive-state or weighted L2
bound is not an OS multiplier estimate. Dense multiplication above supplies
no radical-ideal or completed multiplication theorem.

No new beta-uniform physical-gap claim is made. The new change-of-variables
identities are finite SU(2) polynomial identities, not nonabelian coercivity.
The time modulus names its nome and width. No literature scan or CI change
was performed; no old proof, analytic guard, sorry, axiom or safety limit was
changed. Verification evidence and the concrete rectangle are recorded below.

## Concrete non-plaquette instance

`rectangle`, `lean/YMGap/Continuum/BF4ExactSlabSpatialWilsonRectangle.lean:47`,
supplies all finite geometric fields of `SpatialLoop 1 0` for the six-link
rectangle. `character_pin`, same file:80, proves coefficient equivalence with
the old original-slab rectangle polynomial by quaternion associativity and
terminal-unit removal. `rectangle_evaluation`, same file:103, transfers its
values -2 and 0 on the two old unit fields. `no_pointwise_plaquette_recoding`
and `no_coefficient_plaquette_recoding`, same file:111 and :121, transfer the
obstruction for the explicitly named old `PlaquetteExpression 0` algebra.
The example therefore belongs to the new physical word family. No claim
about current Stage pointwise recoding, almost-everywhere equality or
completed OS density is inferred from it.

## Verification and independent review

All eight focused final checks exited 0; all 78 public axiom gates reported
only {propext, Quot.sound} or no axioms. Final logs contain no errors, warnings,
`sorryAx`, classical choice or native reduction dependency. Earlier attempts
needed namespace/field elaboration fixes and a finite-list proof correction;
the rectangle identity uses symbolic quaternion laws without expanding the
large link carrier. No memory, worker, recursion or heartbeat limit was raised.

Every run used `scripts/safe_lean_build.py --jobs 1
--check-worker-limit-gib 20 --check <file> --check-output <its olean>` with
fresh process/swap inspection. Swap stayed at 6917.19 MiB during these checks.
Verification was paused while an unrelated user-owned pytest process ran;
that process was neither stopped nor modified. No root build, full audit or
full guard suite ran. Root imports are added, not claimed root-checked.

Final log names below are in `/tmp/`; hashes are SHA-256.

| Module | Public gates | Log | SHA-256 |
| --- | ---: | --- | --- |
| SU2QuaternionHaarGaugeWord | 9 | `ym-gauge-word-20260917.log` | `255a09391ed33a899a01a684aa4ee7da0b44ccd977290c6e3fc3ab1fdecf8ea1` |
| BF4ExactSlabTemporalGaugeWilsonWord | 22 | `ym-temporal-wilson-word-final-20260917.log` | `3ae0c0a939a4dc56d1c3390ed325339b18969971479995e884c711029ec39c90` |
| BF4ExactSlabTemporalInvariantSweep | 3 | `ym-invariant-sweep-final-20260917.log` | `2479ffb3c546255157d64271a246407412530d45824920bf6730dee157f4aeab` |
| BF4ExactSlabSpatialWilsonAlgebra | 5 | `ym-spatial-wilson-algebra-20260917.log` | `d95b03c22a06d86561ac7016dbed75352d13e92a07a7388092c0b64ff70d5cd8` |
| BF4ExactSlabSpatialWilsonRectangle | 6 | `ym-spatial-wilson-rectangle-final-20260917.log` | `0200ddcd43e0e6610f6a82bbb3c74b56ebe48373714e4cd934e975de9d84c089` |
| BF4ExactSlabFixedSpatialWilsonProbe | 15 | `ym-spatial-wilson-probe-20260917.log` | `1edc0f9102b350a6a67b3cf7a21bce4850c13cc1d6710853e0a398a6e1b98fe2` |
| BF4ExactSlabFixedSpatialWilsonTimeLimit | 7 | `ym-spatial-wilson-time-limit-20260917.log` | `aff65b2f3626d9d2964f7e9276d0035fbcd7cbffcfea57423dccb9311e3afd24` |
| BF4ExactSlabFixedSpatialSpanProduct | 11 | `ym-span-product-20260917.log` | `1e241b2c921b415f214ce66883b77d4c6c1458ade3cac24038c8618ad3882a7b` |

Independent source review checked the full-action spectator retention,
product cancellation, dense product scope, physical source placement,
same-partition cancellation and changing original-observable diagonal.
No substantive mathematical defect was identified. Scope distinctions in this
report are part of that review, not claims that the remaining joins are proved.
