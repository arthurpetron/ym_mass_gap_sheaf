/-
# Fixed-magnetic realization of a BF4 Mehler endpoint

This module connects the fixed-magnetic CP-order theorem to the calibrated
Mehler endpoint interface used by the final spectral budget.

A realization consists of an actual weight on the enlarged physical carrier,
an equality identifying its normalized weighted Gram with the supplied
endpoint joint, and the quantitative `[7/8,9/8]` weight window.  From those
data Lean proves the literal normalized physical-minus-endpoint row eighth.

Thus the second final inequality no longer requires a separate all-row
estimate.  Its genuine analytic content is exactly:

1. the Peter--Weyl/Feynman--Kac realization on the enlarged carrier; and
2. its spacing-uniform two-sided channel-weight window.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
import YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget

namespace YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open YMGap.Constructive
open YMGap.Continuum.BF4AFUniformRowRelativeBudget
open YMGap.Continuum.BF4CanonicalFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalFixedMagneticRowCPDomination
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SameCarrierRowCPDomination
open YMGap.Continuum.BF4SU2FixedMagneticMehlerCarrier
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4VacuumCalibratedFiniteMehlerGramSpectralBudget
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-- A genuine same-carrier realization of a finite BF4 endpoint.

The `joint_identification` field is the missing Peter--Weyl transform:
it identifies the endpoint with a weighted Gram using the exact physical
fixed-magnetic half-amplitudes.  The last two fields are the quantitative
Yang--Mills/Mehler comparison. -/
structure FixedMagneticEndpointRealization
    {w : Q'} (hw : (0 : Q') ≤ w)
    (K half : Nat)
    (endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half) : Type where
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
  lower_window :
    ∀ channel,
      channel ∈
          centralFixedMagneticIntertwinerChannels K half →
        Q'.mkPos 7 8 (by decide) *
            centralFixedMagneticIntertwinerWeight
              w half channel ≤
          referenceWeight channel
  upper_window :
    ∀ channel,
      channel ∈
          centralFixedMagneticIntertwinerChannels K half →
        referenceWeight channel ≤
          Q'.mkPos 9 8 (by decide) *
            centralFixedMagneticIntertwinerWeight
              w half channel

namespace FixedMagneticEndpointRealization

/-- A realized endpoint satisfies the exact second calibrated eighth on
every retained row. -/
theorem physicalNormalizedJointRowError_le_eighth
    {w : Q'} {hw : (0 : Q') ≤ w}
    {K half : Nat}
    {endpoint :
      CentralPhysicalRawMehlerEndpoint
        w hw K half}
    (realization :
      FixedMagneticEndpointRealization
        hw K half endpoint)
    {source : EdgeLabelling}
    (hsource :
      source ∈ centralPositiveHalfStates
        w hw K half) :
    physicalNormalizedJointRowError
        endpoint source ≤
      Q'.mkPos 1 8 (by decide) *
        centralPhysicalRowMarginal
          w hw K half source := by
  have htransport :
      physicalNormalizedJointRowError
          endpoint source ≈
        finiteJointDifferenceAbsRowMass
          (centralPositiveHalfStates
            w hw K half)
          (centralNormalizedPhysicalReflectedKernel
            w hw K half)
          (centralNormalizedFixedMagneticReferenceGram
            w hw K half realization.referenceWeight)
          source := by
    unfold physicalNormalizedJointRowError
      finiteJointDifferenceAbsRowMass
    apply listQSum_congr_on
    intro target htarget
    apply Q'.abs_eqv_congr
    apply Q'.add_eqv_congr_left
    exact Q'.neg_eqv_congr _ _
      (realization.joint_identification
        source hsource target htarget)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv htransport)
    (centralNormalizedFixedMagneticReferenceGram_row_error_le_eighth
      realization.referenceWeight
      hsource
      realization.lower_window
      realization.upper_window)

end FixedMagneticEndpointRealization

/-- Same-carrier realizations of the calibrated endpoint at every matched
AF scale. -/
structure MatchedFixedMagneticEndpointRealization
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
      FixedMagneticEndpointRealization
        (matchedAllSpinWeight_nonnegative
          family coupling scale)
        (matchedAllSpinCutoff family coupling scale)
        (halfExtent scale)
        (matchedVacuumCalibratedMehlerGramRawEndpointAt
          family coupling halfExtent
          diagonalOrder crossOrder scale)

namespace MatchedFixedMagneticEndpointRealization

/-- The matched realization proves the second field of
`MatchedVacuumCalibratedRowwiseEighthEstimates` verbatim. -/
theorem comparison_row_eighth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (matched :
      MatchedFixedMagneticEndpointRealization
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
          (halfExtent scale) source := by
  exact
    (matched.realization scale).physicalNormalizedJointRowError_le_eighth
      hsource

/-- Once the independent calibrated spectral eighth is supplied, the
same-carrier realization fills the complete sharp rowwise certificate. -/
def toRowwiseEighthEstimates
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {halfExtent diagonalOrder crossOrder : Nat → Nat}
    (matched :
      MatchedFixedMagneticEndpointRealization
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

end MatchedFixedMagneticEndpointRealization

end YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility.FixedMagneticEndpointRealization.physicalNormalizedJointRowError_le_eighth
#print axioms YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility.MatchedFixedMagneticEndpointRealization.comparison_row_eighth
#print axioms YMGap.Continuum.BF4FixedMagneticMehlerEndpointCompatibility.MatchedFixedMagneticEndpointRealization.toRowwiseEighthEstimates
