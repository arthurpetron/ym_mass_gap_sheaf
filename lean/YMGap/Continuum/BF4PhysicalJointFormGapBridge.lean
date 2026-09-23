/-
# The central physical form gap on the reflected-joint comparison image

The reflected joint-form completion has a canonical comparison map from the
same physical completed carrier.  This module transports the existing strict
central form-gap contract to that comparison image.  The statement is only
for vectors in the comparison image: no density or range-extension claim is
made for arbitrary vectors of the joint completion.
-/

import YMGap.Continuum.BF4PhysicalJointFormTransfer
import YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalJointFormGapBridge

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PositiveContractionOneStepCompletion

/-- A central completed physical form gap transfers to the reflected-joint
form on every vector in the canonical comparison image.  The right side is
the joint-completion norm, not the untransported central norm. -/
theorem physicalJointComparison_form_gap_of_central_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (x : CentralPhysicalGNSCompletion w hw K half)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal w hw K half x) :
    CReal.RCle
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointTransfer w hw K half
          (physicalJointComparison w hw K half x))
        (physicalJointComparison w hw K half x))
      (CReal.RCscale rate
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointComparison w hw K half x)
          (physicalJointComparison w hw K half x))) := by
  have hcentral :=
    centralPhysicalCompletedMarkovTransfer_square_form_gap_of_form_gap
      hw K half gap x horthogonal
  have hleft :
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointTransfer w hw K half
            (physicalJointComparison w hw K half x))
          (physicalJointComparison w hw K half x) =
        (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half x)
          (centralPhysicalCompletedMarkovTransfer w hw K half x) := by
    calc
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointTransfer w hw K half
            (physicalJointComparison w hw K half x))
          (physicalJointComparison w hw K half x) =
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointComparison w hw K half
            (centralPhysicalCompletedMarkovTransfer w hw K half x))
          (physicalJointComparison w hw K half x) := by
            rw [physicalJointComparison_intertwines]
      _ = (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half x)
          (centralPhysicalCompletedMarkovTransfer w hw K half x) := by
            simpa only [actionIterate, Nat.zero_add] using
              (physicalJointComparison_moments w hw K half 0
                (centralPhysicalCompletedMarkovTransfer w hw K half x) x)
  have hright :
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointComparison w hw K half x)
          (physicalJointComparison w hw K half x) =
        (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half x) x := by
    calc
      (physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (physicalJointComparison w hw K half x)
          (physicalJointComparison w hw K half x) =
        (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl x
          (centralPhysicalCompletedMarkovTransfer w hw K half x) := by
            simpa only [actionIterate, Nat.zero_add] using
              (physicalJointComparison_moments w hw K half 0 x x)
      _ = (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer w hw K half x) x :=
        (centralPhysicalCompletedMarkovTransfer_selfAdjoint
          w hw K half x x).symm
  rw [hleft, hright]
  exact hcentral

/-- The producer-selected physical BF4 rate transfers to the reflected-joint
comparison image at every matched scale.  The conclusion still quantifies
only over the comparison image and remains finite-cutoff data. -/
theorem producer_physicalJointComparison_form_gap_sixteenth
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal : CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((physicalJointSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (physicalJointTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0
          (physicalJointComparison
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector))
        (physicalJointComparison
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (Q'.mkPos 1 16 (by decide))
        ((physicalJointSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          (physicalJointComparison
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector)
          (physicalJointComparison
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector))) :=
  physicalJointComparison_form_gap_of_central_form_gap
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer_completed_vacuum_form_gap_data producer scale)
    vector horthogonal

end YMGap.Continuum.BF4PhysicalJointFormGapBridge

#print axioms YMGap.Continuum.BF4PhysicalJointFormGapBridge.physicalJointComparison_form_gap_of_central_form_gap
#print axioms YMGap.Continuum.BF4PhysicalJointFormGapBridge.producer_physicalJointComparison_form_gap_sixteenth
