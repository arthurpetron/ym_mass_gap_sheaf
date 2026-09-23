/-
# Exact centered cylinders in the physical reflected-joint completion

The general reflected-joint completion passage is conditional on an explicit
exact-kernel range witness.  Finite observables with zero physical stationary
mean already supply such witnesses: their constant Cauchy representatives
are stagewise joint-vacuum orthogonal by the transported central vacuum
identity.  This module records that non-vacuous dense-cylinder fragment and
does not extend it to arbitrary completed vectors.
-/

import YMGap.Continuum.BF4PhysicalJointFormGapExtension
import YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap

namespace YMGap.Continuum.BF4PhysicalJointCenteredKernel

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.BF4PhysicalJointFormTransfer
open YMGap.Continuum.BF4PhysicalJointFormGapExtension
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedOperatorNormGap
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

/-- The exact rational central centering, viewed as a reflected-joint
observable.  The underlying finite carrier is the same `EdgeLabelling → Q'`.
-/
abbrev physicalJointCenteredObservable
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') : EdgeLabelling → Q' :=
  centralPhysicalCenteredObservable w hw K half observable

/-- Every finite observable becomes joint-vacuum orthogonal after exact
stationary centering. -/
theorem physicalJointCenteredObservable_vacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    PhysicalJointVacuumOrthogonal w hw K half
      (embedV (physicalJointSmulGNS w hw K half).toGNSData
        (physicalJointCenteredObservable w hw K half observable)) := by
  have hcentral : CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (embedV (centralPhysicalSmulGNS w hw K half).toGNSData
        (physicalJointCenteredObservable w hw K half observable)) :=
    centralPhysicalCompletedObservable_vacuumOrthogonal
      w hw K half (physicalJointCenteredObservable w hw K half observable)
      (centralPhysicalCenteredObservable_meanZero w hw K half observable)
  have hinner := physicalJointComparison_vacuum_inner w hw K half
    (embedV (centralPhysicalSmulGNS w hw K half).toGNSData
      (physicalJointCenteredObservable w hw K half observable))
  unfold PhysicalJointVacuumOrthogonal
  rw [physicalJointComparison_embed] at hinner
  exact hinner.trans hcentral

/-- The constant Cauchy representative of a centered cylinder is an explicit
exact-kernel replacement.  No choice or bare existence proposition is used. -/
def exactPhysicalJointVacuumComplementReplacement_constant
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q')
    :
    ExactPhysicalJointVacuumComplementReplacement hw K half
      (constCauchy
        (physicalJointSmulGNS w hw K half).toGNSData
        (physicalJointCenteredObservable w hw K half observable)) where
  representative :=
    constCauchy
      (physicalJointSmulGNS w hw K half).toGNSData
      (physicalJointCenteredObservable w hw K half observable)
  close := cauchyNull_refl _ _
  stageInKernel := fun _ =>
    physicalJointCenteredObservable_vacuumOrthogonal
      w hw K half observable

/-- The conditional completed form gap is now non-vacuously inhabited on every
finite centered cylinder. -/
theorem physicalJoint_centeredObservable_completed_form_gap
    {w rate : Q'} (hw : (0 : Q') ≤ w) (K half : Nat)
    (gap : CentralPhysicalCompletedVacuumFormGap w hw K half rate)
    (observable : EdgeLabelling → Q') :
    CReal.RCle
      ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
        (physicalJointTransfer w hw K half
          (embedV (physicalJointSmulGNS w hw K half).toGNSData
            (physicalJointCenteredObservable w hw K half observable)))
        (embedV (physicalJointSmulGNS w hw K half).toGNSData
          (physicalJointCenteredObservable w hw K half observable)))
      (CReal.RCscale rate
        ((physicalJointSmulGNS w hw K half).toGNSData.cinnerCompl
          (embedV (physicalJointSmulGNS w hw K half).toGNSData
            (physicalJointCenteredObservable w hw K half observable))
          (embedV (physicalJointSmulGNS w hw K half).toGNSData
            (physicalJointCenteredObservable w hw K half observable)))) := by
  exact physicalJoint_completed_form_gap_of_replacement
    hw K half gap
    (constCauchy
      (physicalJointSmulGNS w hw K half).toGNSData
      (physicalJointCenteredObservable w hw K half observable))
    (exactPhysicalJointVacuumComplementReplacement_constant
      w hw K half observable)

#print axioms physicalJointCenteredObservable
#print axioms physicalJointCenteredObservable_vacuumOrthogonal
#print axioms exactPhysicalJointVacuumComplementReplacement_constant
#print axioms physicalJoint_centeredObservable_completed_form_gap

end YMGap.Continuum.BF4PhysicalJointCenteredKernel
