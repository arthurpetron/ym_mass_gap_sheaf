/-
# Core/tail realization of the calibrated BF4 endpoint

This module connects the source-dependent cutoff theorem to the exact
calibrated endpoint used by the final physical Perron budget.  It replaces
the global `[7/8,9/8]` channel window by:

* a `1/16` relative comparison on a source-dependent core;
* a `1/32` physical tail row;
* a `1/32` reference tail row.

The Peter--Weyl identification is still exact on the complete common carrier;
only its quantitative proof is split into core and tails.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination
import YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility

namespace YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4FixedMagneticCoreTailRowCPDomination
open YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-- Exact same-carrier endpoint realization with a quantitative
source-dependent core/tail proof. -/
structure FixedMagneticCoreTailEndpointRealization
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint w hw K half) : Type where
  referenceWeight :
    CentralFixedMagneticIntertwinerChannel → Q'
  joint_identification :
    ∀ left,
      left ∈ centralPositiveHalfStates w hw K half →
        ∀ right,
          right ∈ centralPositiveHalfStates w hw K half →
            endpoint.joint left right ≈
              centralNormalizedFixedMagneticReferenceGram
                w hw K half referenceWeight left right
  coreTail :
    CentralFixedMagneticCoreTailEighthData
      hw K half referenceWeight

namespace FixedMagneticCoreTailEndpointRealization

/-- The complete physical-minus-calibrated-endpoint row estimate obtained
from the exact Peter--Weyl identification and the three cutoff payments. -/
theorem physicalNormalizedJointRowError_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint w hw K half}
    (realization :
      FixedMagneticCoreTailEndpointRealization
        hw K half endpoint)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates w hw K half) :
    physicalNormalizedJointRowError endpoint source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  have htransport :
      physicalNormalizedJointRowError endpoint source ≈
        finiteJointDifferenceAbsRowMass
          (centralPositiveHalfStates w hw K half)
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half realization.referenceWeight)
          source := by
    unfold physicalNormalizedJointRowError
      finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply YMGap.Constructive.Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_left
    exact Q'.neg_eqv_congr _ _
      (realization.joint_identification
        source hsource target htarget)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport)
    (realization.coreTail.normalized_row_error_le_eighth
      hsource)

end FixedMagneticCoreTailEndpointRealization

/-- Core/tail realizations of the exact calibrated endpoint on every matched
AF carrier. -/
structure MatchedFixedMagneticCoreTailEndpointRealization
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (_spacing : PhysicalSpacingEnvelope law.g₁)
    (coupling : Nat → Q')
    (halfExtent diagonalOrder crossOrder : Nat → Nat) : Type where
  coupling_pos :
    ∀ scale, (0 : Q') < coupling scale
  coupling_le_window :
    ∀ scale, coupling scale ≤ law.g₁
  realization :
    ∀ scale,
      FixedMagneticCoreTailEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)

namespace MatchedFixedMagneticCoreTailEndpointRealization

/-- The matched cutoff realization proves the second spacing-uniform eighth
field verbatim. -/
theorem comparison_row_eighth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (matched :
      MatchedFixedMagneticCoreTailEndpointRealization
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (scale : Nat)
    (source : EdgeLabelling)
    (hsource :
      source ∈
          centralPositiveHalfStates
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative
              family coupling scale)
            (matchedAllSpinCutoff family coupling scale)
            (halfExtent scale)) :
    physicalNormalizedJointRowError
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)
        source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative
            family coupling scale)
          (matchedAllSpinCutoff family coupling scale)
          (halfExtent scale) source :=
  (matched.realization scale).physicalNormalizedJointRowError_le_eighth
    hsource

/-- With the independent spectral eighth, the source-dependent cutoff
realization inhabits the complete final rowwise analytic certificate. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (matched :
      MatchedFixedMagneticCoreTailEndpointRealization
        family law spacing coupling halfExtent
        diagonalOrder crossOrder)
    (spectral_eighth :
      ∀ scale,
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
            family coupling halfExtent
            diagonalOrder crossOrder scale).rate ≤
          Q'.mkPos 1 8 (by decide)) :
    MatchedVacuumCalibratedRowwiseEighthEstimates
      family law spacing coupling halfExtent
      diagonalOrder crossOrder where
  coupling_pos := matched.coupling_pos
  coupling_le_window := matched.coupling_le_window
  spectral_eighth := spectral_eighth
  comparison_row_eighth := by
    intro scale source hsource
    exact matched.comparison_row_eighth
      scale source hsource

end MatchedFixedMagneticCoreTailEndpointRealization

end YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility.FixedMagneticCoreTailEndpointRealization.physicalNormalizedJointRowError_le_eighth
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility.MatchedFixedMagneticCoreTailEndpointRealization.comparison_row_eighth
#print axioms YMGap.Continuum.BF4FixedMagneticCoreTailEndpointCompatibility.MatchedFixedMagneticCoreTailEndpointRealization.toRowwiseEighthEstimates
