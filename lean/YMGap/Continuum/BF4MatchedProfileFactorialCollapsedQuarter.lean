/-
# Matched BF4 quarter certificate from profile, factorial, and collapsed data

This module packages the smallest analytic inputs produced by the corrected
spectral decomposition:

1. a `1/16` rational prefix/image window for the calibrated empty feature;
2. a `1/16` factorial envelope for the nonempty feature words;
3. the conditionally integrated active-boundary `1/8` realization of the
   physical-minus-endpoint row.

The first two prove the physically recentered spectral `1/8`; the third
proves the comparison `1/8`.  The corrected matched Perron theorem then gives
the physical mean-zero `1/4` contraction at every scale.

At cross order zero the nonempty factorial field is inhabited
unconditionally, so a separate adapter exposes the remaining profile and
collapsed-boundary inputs without retaining a vacuous tail premise.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope
import YMGap.Continuum.BF4CalibratedProfileHarnack
import YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth

namespace YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4CalibratedEmptyProfileWindow
open YMGap.Continuum.BF4CalibratedNonemptyFeatureEnvelope
open YMGap.Continuum.BF4CalibratedProfileHarnack
open YMGap.Continuum.BF4FixedMagneticReferenceFiberCollapse
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalRecenteredEndpointRate
open YMGap.Continuum.BF4PhysicallyRecenteredMatchedEighth
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-! ## 1. Complete corrected analytic certificate -/

/-- Spacing-uniform physical inputs after the corrected empty/nonempty and
fixed-magnetic fiber decompositions. -/
structure MatchedProfileFactorialCollapsedQuarterData
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  profile_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        let w :=
          matchedAllSpinWeight family coupling scale
        let hw :=
          matchedAllSpinWeight_nonnegative
            family coupling scale
        let K :=
          matchedAllSpinCutoff family coupling scale
        let half := halfExtent scale
        calibratedEmptyLeftProfileMismatch
                w hw K half
                (diagonalOrder scale) (crossOrder scale)
                source *
              calibratedEmptyRightProfileAbsMass
                w hw K half (diagonalOrder scale) +
            centralPhysicalRowMarginal
                w hw K half source *
              calibratedEmptyRightProfileMismatchMass
                w hw K half (diagonalOrder scale) ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              w hw K half source
  factorial_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        let w :=
          matchedAllSpinWeight family coupling scale
        let hw :=
          matchedAllSpinWeight_nonnegative
            family coupling scale
        let K :=
          matchedAllSpinCutoff family coupling scale
        let half := halfExtent scale
        calibratedNonemptyFeatureFactorialRowEnvelope
            w hw K half
            (diagonalOrder scale) (crossOrder scale)
            source ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              w hw K half source
  collapsed :
    ∀ scale,
      CollapsedActiveFixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)

namespace MatchedProfileFactorialCollapsedQuarterData

/-- The three smallest analytic inputs inhabit the corrected
collapsed-active eighth realization. -/
def toCollapsedActiveRecenteredEighthRealization
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (data :
      MatchedProfileFactorialCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedCollapsedActiveRecenteredEighthRealization
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  spectral_centered_row_eighth := by
    intro scale source hsource
    exact
      physicalCenteredEndpointRowMass_le_eighth_of_profile_and_factorial
        (data.profile_sixteenth scale source hsource)
        (data.factorial_sixteenth scale source hsource)
  collapsed := data.collapsed

/-- The profile, factorial, and collapsed-boundary estimates inhabit both
literal row eighth fields. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (data :
      MatchedProfileFactorialCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedPhysicallyRecenteredRowwiseEighthEstimates
      family law spacing coupling halfExtent
      diagonalOrder crossOrder :=
  data.toCollapsedActiveRecenteredEighthRealization
    |>.toRowwiseEighthEstimates

/-- Complete corrected physical quarter contraction along the matched
trajectory. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (data :
      MatchedProfileFactorialCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable :=
  data.toRowwiseEighthEstimates.physical_quarter_uniform
    scale observable hmean

end MatchedProfileFactorialCollapsedQuarterData

/-! ## 2. Cross-order-zero specialization -/

/-- At cross order zero only the physical prefix/image window and collapsed
endpoint realization remain; the factorial field is a theorem. -/
structure MatchedCrossZeroProfileCollapsedQuarterData
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  profile_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        let w :=
          matchedAllSpinWeight family coupling scale
        let hw :=
          matchedAllSpinWeight_nonnegative
            family coupling scale
        let K :=
          matchedAllSpinCutoff family coupling scale
        let half := halfExtent scale
        calibratedEmptyLeftProfileMismatch
                w hw K half (diagonalOrder scale) 0 source *
              calibratedEmptyRightProfileAbsMass
                w hw K half (diagonalOrder scale) +
            centralPhysicalRowMarginal
                w hw K half source *
              calibratedEmptyRightProfileMismatchMass
                w hw K half (diagonalOrder scale) ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              w hw K half source
  collapsed :
    ∀ scale,
      CollapsedActiveFixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder (fun _ => 0) scale)

namespace MatchedCrossZeroProfileCollapsedQuarterData

/-- Fill the factorial field with the exact empty-carrier theorem. -/
def toProfileFactorialCollapsedQuarterData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedCrossZeroProfileCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder) :
    MatchedProfileFactorialCollapsedQuarterData
      family law spacing coupling halfExtent
      diagonalOrder (fun _ => 0) where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  profile_sixteenth := data.profile_sixteenth
  factorial_sixteenth := by
    intro scale source _
    exact
      calibratedNonemptyFeatureFactorialRowEnvelope_crossZero_le_sixteenth
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        source
  collapsed := data.collapsed

end MatchedCrossZeroProfileCollapsedQuarterData

/-! ## 3. Pointwise Harnack specialization -/

/-- Replace the global profile-sixteenth premise by the two pointwise
`1/64` Harnack windows proved sufficient above. -/
structure MatchedHarnackFactorialCollapsedQuarterData
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        (crossOrder scale)
  factorial_sixteenth :
    ∀ scale source,
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale) →
        let w :=
          matchedAllSpinWeight family coupling scale
        let hw :=
          matchedAllSpinWeight_nonnegative
            family coupling scale
        let K :=
          matchedAllSpinCutoff family coupling scale
        let half := halfExtent scale
        calibratedNonemptyFeatureFactorialRowEnvelope
            w hw K half
            (diagonalOrder scale) (crossOrder scale)
            source ≤
          Q'.mkPos 1 16 (by decide) *
            centralPhysicalRowMarginal
              w hw K half source
  collapsed :
    ∀ scale,
      CollapsedActiveFixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)

namespace MatchedHarnackFactorialCollapsedQuarterData

/-- The pointwise Harnack fields compute the profile `1/16`, yielding the
complete profile/factorial/collapsed certificate. -/
def toProfileFactorialCollapsedQuarterData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (data :
      MatchedHarnackFactorialCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder crossOrder) :
    MatchedProfileFactorialCollapsedQuarterData
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  profile_sixteenth := by
    intro scale source hsource
    exact (data.harnack scale).profile_sixteenth
      hsource
  factorial_sixteenth :=
    data.factorial_sixteenth
  collapsed := data.collapsed

/-- Pointwise Harnack, factorial Mehler, and collapsed-boundary estimates
give the corrected physical quarter contraction. -/
theorem physical_quarter_uniform
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (data :
      MatchedHarnackFactorialCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        observable) :
    Q'.abs
        (centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable
          (centralPhysicalMarkovApply
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)
            observable)) ≤
      Q'.mkPos 1 4 (by decide) *
        centralPhysicalWeightedInner
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale)
          observable observable :=
  data.toProfileFactorialCollapsedQuarterData
    |>.physical_quarter_uniform
      scale observable hmean

end MatchedHarnackFactorialCollapsedQuarterData

/-- At cross order zero, the exact factorial-zero theorem leaves only the
two pointwise Harnack windows and the collapsed endpoint realization. -/
structure MatchedCrossZeroHarnackCollapsedQuarterData
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  harnack :
    ∀ scale,
      CalibratedEmptyProfileHarnackData
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        0
  collapsed :
    ∀ scale,
      CollapsedActiveFixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder (fun _ => 0) scale)

namespace MatchedCrossZeroHarnackCollapsedQuarterData

/-- Fill the cross-zero factorial premise constructively. -/
def toHarnackFactorialCollapsedQuarterData
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder : Nat → Nat}
    (data :
      MatchedCrossZeroHarnackCollapsedQuarterData
        family law spacing coupling halfExtent
        diagonalOrder) :
    MatchedHarnackFactorialCollapsedQuarterData
      family law spacing coupling halfExtent
      diagonalOrder (fun _ => 0) where
  coupling_pos := data.coupling_pos
  coupling_le_window := data.coupling_le_window
  harnack := data.harnack
  factorial_sixteenth := by
    intro scale source _
    exact
      calibratedNonemptyFeatureFactorialRowEnvelope_crossZero_le_sixteenth
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (diagonalOrder scale)
        source
  collapsed := data.collapsed

end MatchedCrossZeroHarnackCollapsedQuarterData

end YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedProfileFactorialCollapsedQuarterData.toCollapsedActiveRecenteredEighthRealization
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedProfileFactorialCollapsedQuarterData.toRowwiseEighthEstimates
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedProfileFactorialCollapsedQuarterData.physical_quarter_uniform
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedCrossZeroProfileCollapsedQuarterData.toProfileFactorialCollapsedQuarterData
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedHarnackFactorialCollapsedQuarterData.toProfileFactorialCollapsedQuarterData
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedHarnackFactorialCollapsedQuarterData.physical_quarter_uniform
#print axioms YMGap.Continuum.BF4MatchedProfileFactorialCollapsedQuarter.MatchedCrossZeroHarnackCollapsedQuarterData.toHarnackFactorialCollapsedQuarterData
