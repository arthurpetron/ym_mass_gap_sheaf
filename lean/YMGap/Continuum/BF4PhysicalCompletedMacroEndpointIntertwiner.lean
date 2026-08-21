/-
# The corrected one-macro-step physical BF4 endpoint comparison

The finite physical BF4 carrier, completed transfer, vacuum complement, rate
probe, same-object matrix coefficient, and Cauchy--Schwarz handoff are now
constructed.  Consequently the remaining weak-to-strong operator input is
only an isometric map from that concrete physical completion to the concrete
strong endpoint, intertwining one already-composed physical macro transfer
with one strong two-step transfer and preserving the vacuum complement.

The Faraut depth constructs the physical slab kernel; it does not iterate that
macro kernel again.  This module therefore supersedes the older residual's
depth-fold physical transfer field.  No inhabitant of the comparison map is
claimed here.
-/

import YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
import YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The irreducible cross-model comparison datum -/

/-- The residual comparison map after constructing the physical BF4 GNS
completion and its one-macro-step same-object correlator.

There are no abstract physical-carrier, physical-transfer, probe, or
Cauchy--Schwarz fields: all of those are the concrete objects constructed in
`BF4PhysicalCompletedMacroCorrelator`. -/
structure CompletedBF4MacroEndpointIntertwiner
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {endpointCoupling : Q'}
    (hendpoint : (0 : Q') ≤ endpointCoupling)
    (hle : endpointCoupling ≤ anchorCoupling)
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P) : Type 1 where
  /-- The only new carrier map: physical weak-coupling GNS completion to the
  already-constructed strong endpoint. -/
  toStrong :
    (scale : Nat) →
      CentralPhysicalGNSCompletion
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 →
      StrictJointCylinderOSCompletion hendpoint hle
  /-- Exact preservation of the completed squared norm. -/
  normIdentification :
    ∀ scale vector,
      strictJointCylinderCompletedInner hendpoint hle
          (toStrong scale vector) (toStrong scale vector) =
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector
  /-- One physical slab macro step is one strong two-step endpoint step.  No
  Faraut-depth re-iteration appears here. -/
  macroTransferIntertwining :
    ∀ scale vector,
      toStrong scale
          (centralPhysicalCompletedMarkovTransfer
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector) =
        strictJointCylinderCompletedTwoStepTransfer hendpoint hle
          (toStrong scale vector)
  /-- The physical stationary vacuum complement maps into the endpoint vacuum
  complement on which the strict strong estimate is already proved. -/
  mapsVacuumOrthogonal :
    ∀ scale vector,
      CentralPhysicalCompletedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector →
        StrictJointCylinderCompletionVacuumOrthogonal hendpoint hle
          (toStrong scale vector)

namespace CompletedBF4MacroEndpointIntertwiner

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {endpointCoupling : Q'}
    {hendpoint : (0 : Q') ≤ endpointCoupling}
    {hle : endpointCoupling ≤ anchorCoupling}
    {producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P}

/-! ## 2. Strict completed physical macro gap -/

/-- A named uniform norm-gap statement on the actual physical completed
vacuum complement.  Its squared-norm rate is `separator^2`. -/
def CentralPhysicalCompletedMacroVacuumNormGap
    (_producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (separator : Q') : Prop :=
  (0 : Q') ≤ separator ∧ separator < (1 : Q') ∧
    ∀ scale vector,
      CentralPhysicalCompletedVacuumOrthogonal
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector →
        CReal.RCle
          ((centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
            (centralPhysicalCompletedMarkovTransfer
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0 vector)
            (centralPhysicalCompletedMarkovTransfer
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0 vector))
          (CReal.RCscale (separator * separator)
            ((centralPhysicalSmulGNS
              (matchedAllSpinWeight family coupling scale)
              (matchedAllSpinWeight_nonnegative family coupling scale)
              (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
              vector vector))

/-- One exact macro intertwining imports the already-proved endpoint operator
norm gap to every vector in the concrete physical vacuum complement. -/
theorem physicalMacroTransfer_norm_gap
    (intertwiner : CompletedBF4MacroEndpointIntertwiner
      hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal :
      CentralPhysicalCompletedVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        (centralPhysicalCompletedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate *
          anchorDecoratedDoubledTimeRate)
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
          vector vector)) := by
  rw [← intertwiner.normIdentification scale
    (centralPhysicalCompletedMarkovTransfer
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 vector)]
  rw [intertwiner.macroTransferIntertwining scale vector]
  rw [← intertwiner.normIdentification scale vector]
  exact anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
    hendpoint hle (intertwiner.toStrong scale vector)
      (intertwiner.mapsVacuumOrthogonal scale vector horthogonal)

/-- The corrected comparison datum closes the physical completed macro norm
gap at the common rate `1/16`, uniformly over the cutoff scale. -/
theorem physicalMacroVacuumNormGap
    (intertwiner : CompletedBF4MacroEndpointIntertwiner
      hendpoint hle producer) :
    CentralPhysicalCompletedMacroVacuumNormGap producer
      anchorDecoratedDoubledTimeRate := by
  exact ⟨anchorDecoratedDoubledTimeRate_nonnegative,
    anchorDecoratedDoubledTimeRate_lt_one,
    fun scale vector horthogonal =>
      intertwiner.physicalMacroTransfer_norm_gap
        scale vector horthogonal⟩

/-! ## 3. The rate-probe handoff is now derived -/

/-- For the same physical rate probe, completed Cauchy--Schwarz feeds directly
into the imported strict macro norm estimate.  Neither the probe nor this
correlation-square inequality is a field of the intertwiner. -/
theorem rateProbe_correlationSquare_le_strictMacroNorm
    (intertwiner : CompletedBF4MacroEndpointIntertwiner
      hendpoint hle producer)
    (scale : Nat) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let probe := completedRateProbe producer scale
    CReal.RCle
      (CReal.RCmul
        (physicalConstantRC
          (P.corrIface.connectedCorr scale
            (producer.sameObject.embed scale
              (producer.rateSharpness.probe scale))
            (producer.bf4.depth scale)))
        (physicalConstantRC
          (P.corrIface.connectedCorr scale
            (producer.sameObject.embed scale
              (producer.rateSharpness.probe scale))
            (producer.bf4.depth scale))))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate *
          anchorDecoratedDoubledTimeRate)
        ((centralPhysicalSmulGNS w hw K 0).toGNSData.cinnerCompl
          probe probe)) := by
  dsimp only
  exact CReal.RCle_trans
    (completedRateProbe_correlationSquare_le_transferredNorm producer scale)
    (intertwiner.physicalMacroTransfer_norm_gap scale
      (completedRateProbe producer scale)
      (completedRateProbe_vacuumOrthogonal producer scale))

end CompletedBF4MacroEndpointIntertwiner

end YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner

#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner.CompletedBF4MacroEndpointIntertwiner.physicalMacroTransfer_norm_gap
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner.CompletedBF4MacroEndpointIntertwiner.physicalMacroVacuumNormGap
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroEndpointIntertwiner.CompletedBF4MacroEndpointIntertwiner.rateProbe_correlationSquare_le_strictMacroNorm
