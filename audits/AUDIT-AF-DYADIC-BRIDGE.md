# Physical dyadic bridge: checked arithmetic refutation

Date: 2026-09-15. Source review after `a912133`, followed by focused kernel
checks. This is a specification defect in one route, not a refutation of
Yang--Mills theory or of the separate original-action results.

## 1. What is refuted

`MatchedDyadicSameActionAFBridge` has no inhabitant for ANY of its supplied
families, laws, spacings or rational coupling trajectories. Its heat-time
equation alone requires `coupling(1)^2 = 1/2` in rational equivalence.
No rational satisfies that equation. Neither the AF remainder estimate nor
the spacing law nor the nome/cutoff fields enter the contradiction.

| Fact | Declaration and source |
| --- | --- |
| Exact physical square chart | `physicalTime`, `lean/YMGap/Continuum/BF4MatchedPhysicalAFBridge.lean:347`; `physicalAFEnvelope`, same file `:377`, assigns `t := physicalTime` |
| Exact dyadic requirement | `DyadicSameActionAFBridge.heat_time`, `lean/YMGap/Continuum/BF4FarautAFCutoffGrowth.lean:348`; `dyadicHeatArgument`, same file `:60`, is `1/2^scale` |
| Rational obstruction, independent of presentation | `Q'.square_ne_half`, `lean/YMGap/Constructive/RationalSquareHalfObstruction.lean:53` |
| General square-time envelope refutation | `squareTime_dyadicBridge_uninhabited`, `lean/YMGap/Continuum/BF4MatchedDyadicHeatObstruction.lean:43` |
| Exact matched bridge refutation | `matchedDyadicSameActionAFBridge_uninhabited`, `lean/YMGap/Continuum/BF4MatchedDyadicHeatObstruction.lean:55` |
| Matched window refutation | `matchedPhysicalPointwiseHeatWindows_uninhabited`, `lean/YMGap/Continuum/BF4MatchedDyadicHeatObstruction.lean:62` |

The arithmetic proof uses denominator-positive cross multiplication and
natural-number parity descent. It needs no lowest-terms representation,
classical selection, numerical experiment, or unproved analytic premise.
The old field definitions are unchanged. No contradiction has been installed
as an axiom: the checked result is an implication from the impossible bundle
to `False`.

## 2. Affected consumers

The central physical module now labels its impossible inputs explicitly:
`lean/YMGap/Continuum/BF4MatchedPhysicalFarautTrajectory.lean`.

| Consumer | Source | Consequence |
| --- | --- | --- |
| `matchedPhysicalFarautAFBitGrowth` | `BF4MatchedPhysicalFarautTrajectory.lean:92` | Its bridge premise is impossible; no physical instance is constructed. |
| `matchedPhysicalFarautCoreLength_uniform` | same file `:108` | Valid conditional inequality, not an instantiated physical core-length bound. |
| `MatchedPhysicalPointwiseHeatWindows` | same file `:133`; underlying `SameActionPointwiseHeatWindows.bridge`, `SU2PointwiseHeatDynamicWindow.lean:1025` | Also uninhabited; the window interface does not bypass the bridge. |
| `matchedPhysicalPointwiseAFWindowFamily` | `BF4MatchedPhysicalFarautTrajectory.lean:147` | Its source windows are impossible. |
| `MatchedFiniteHeatWindowCertificate` | `BF4MatchedPhysicalFiniteHeatWindow.lean:500`, bridge field `:509` | Contains the refuted bridge. |
| `MatchedFinitePhysicalHeatWindowCertificate` | same file `:581`, bridge field `:590` | Contains the refuted bridge. |
| `MatchedFixedFinitePhysicalHeatWindowCertificate` | same file `:659`, bridge field `:668` | Contains the refuted bridge. |
| `cubeActivityWeightFloor_le_matchedWeight` | `BF4DyadicCubeVacuumCalibration.lean:138` | Matched specialization requires the bridge, even though its proof uses only the nome field. |
| `MatchedDyadicLowSpinGrowingVolumeRayDomination` | `BF4LowSpinGrowingVolumeMatchedRayComparisonGate.lean:95` | Indexed by a bridge that cannot be supplied. |

All abbreviated paths in this table are under `lean/YMGap/Continuum/`.
A lexical scan for the two matched bridge/window type names finds 30
other existing consumer modules, beyond the defining module and the new
refutation. These include cube calibration, finite-window certificates,
matched low-spin/raw-partition repair gates, and matched central-face
mass/ray gates. This is a direct-reference inventory, NOT a complete
transitive dependency audit. The older generic algebra inside those files
is not declared false merely because a particular specialization is empty.

Reproduce the inventory with:

```sh
rg -l 'MatchedDyadicSameActionAFBridge|MatchedPhysicalPointwiseHeatWindows' lean/YMGap --glob '*.lean'
```

The concrete Padé envelope also has the same square heat chart:
`envelopeTime`, `lean/YMGap/Continuum/BF4AFInstantiation.lean:138`;
`bf4PadeData`, same file `:145`; `bf4AFEnvelope`, same file `:175`.
The general square-time refutation applies to that chart as well. This
does not refute `bf4AFEnvelope` itself, only the exact dyadic bridge to it.
Generic `AFEnvelope` permits other time functions; neither every generic
dyadic bridge nor every generic Padé envelope is refuted.

## 3. Unaffected results and remaining physics

The original-action all-nome normalization and determinant comparison do
not consume this bridge: `expectation_formula`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetExpectation.lean:94`, and
`comparison_bound_eventually`,
`lean/YMGap/Continuum/BF4ExactSlabAllNomeFaceSetComparison.lean:64`.
The fixed-nome original geometric OS result remains a different declaration:
`complement_twoStep_form_gap`,
`lean/YMGap/Continuum/BF4ExactSlabThermodynamicCompletedGap.lean:99`.
These sources were inspected, not recompiled in this diagnostic checkpoint.

The refutation does not supply spatial decay at changing coupling, original
OS transfer/physical-scale transport, a continuum QFT, or the all-group
Clay theorem. It also does not prove `CubicMarginLaw` or
`PhysicalSpacingEnvelope` uninhabited.

## 4. Separate RG-orientation calibration concern

The code's block map goes fine to coarse: `SlabScalePair`,
`lean/YMGap/Continuum/CompactDualFiniteBlockRemainder.lean:49`, and
`FiniteSlabKernel.blockedMass`, same file `:97`. Its selected output is
the coarse coupling by `observableMatchedScalePair_coupling`,
`lean/YMGap/Continuum/BF4ObservableMatchedOneStep.lean:408`.
But `CubicMarginLaw`,
`lean/YMGap/Continuum/BF4MatchedPhysicalAFBridge.lean:175`, uses
`1-w_fine = g^2` and `1-w_coarse = g^2-beta*g^4+O(g^6)`, with beta positive.
No physical equation `a_coarse=2*a_fine` is present in the inspected
`SlabScalePair`, matched trajectory, or `PhysicalSpacingEnvelope` (`:333`).

For comparison, Dalla Brida and Ramos define a step toward lower energy as
`sigma_s(u)=gbar^2(mu/s)` (Eq. 2.12), with positive leading correction
`sigma_2(u)=u+2*b0*log(2)*u^2+...` (Eqs. C.2--C.3).
[Primary paper, sections 2.2 and C](https://link.springer.com/article/10.1140/epjc/s10052-019-7228-z).
Inference: identifying the code's chart with that physical running coupling
requires an orientation/calibration argument; the stated minus sign is a
warning, not a kernel-checked refutation of `CubicMarginLaw`. No sign or
field was changed in this checkpoint. The rational-square contradiction
above is independent of this physical interpretation.

## 5. Next mathematical target, not yet implemented

The already existing consumer `FarautAFBitGrowth`,
`lean/YMGap/Continuum/BF4FarautJointCarrierAFBudget.lean:1058`, needs only
an actual schedule with `bits*(t/4) <= costCeiling`, not exact dyadic
identities. `PointwiseHeatAFWindowFamily`,
`lean/YMGap/Continuum/SU2PointwiseHeatDynamicWindow.lean:861`, accepts
that schedule directly and separately requires the actual local windows
and their `upper <= 4^bits*lower` bound.

A concrete proposed replacement argument is available without altering
these types. For delta=1-w in (0,1), take the computed integer
N=floor(8/delta)+1. Then 8 <= N*delta <= 9. The AF field t/8 <= delta
would give N*(t/4) <= 18. Existing constructive ingredients are
`DyadicTimeRationals.upper`, `.rational_le_upper`, and
`.upper_le_rational_add_unit`,
`lean/YMGap/Constructive/DyadicTimeRationals.lean:67`, `:74`, `:84`;
and `HKConvGen.bernoulli_pow` plus `ofNat_mul_le_bScale`,
`lean/YMGap/Continuum/HeatKernelConvGen.lean:190`, `:245`.
They also suggest the power-tail inequality w^N <= 1/8.

This paragraph is a paper-level next argument, NOT a checked new theorem.
A tail cutoff is NOT automatically a Harnack bit bound. The actual local
window/spread bound, retained interaction, original-action identification,
and physical scale remain separate obligations. Do not replace the
refuted type with a weaker field and claim those obligations solved.

## 6. Verification boundary

Three focused safe checks, each passing first run, serialized with one
worker and a 20 GiB ceiling. The five new public gates and seven unchanged
public gates in the comment-updated physical module are all within
{propext, Quot.sound}. No resource/heartbeat limit was raised. No literal
hole, custom axiom, canonical field or old theorem statement changed.
Own/direct artifacts were fresh. Root/full-tree audit unrun; CI manual-only.

- `/tmp/ym-rational-square-half-obstruction.log`:
  `4cfd8515559dee3f59a6b0ffdad5f0714c0cb26b2d6fab4885c1e62a4d7583d1`.
- `/tmp/ym-matched-dyadic-heat-obstruction.log`:
  `9555c8b5452960e56b1489ffa49f82dc2135434acf004b05f34994540cfdc23e`.
- `/tmp/ym-matched-faraut-refutation-docs.log`:
  `3bbb4a4d3c87834f588cdd778431654dea46de003c7a4c5c7b0ede9682620932`.
