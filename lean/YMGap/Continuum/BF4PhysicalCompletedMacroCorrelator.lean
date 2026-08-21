/-
# The physical BF4 same-object macro correlator in the completed GNS carrier

This module identifies the already-proved finite physical BF4 joint quadratic
with an actual matrix coefficient of the completed physical macro transfer.
It also proves that every finite stationary-mean-zero observable embeds into
the completed vacuum complement.  Applied to a physical separator producer,
the selected rate probe is therefore the same completed vector on both sides
of the macro matrix coefficient.

The transfer here is one already-composed slab macro step.  The Faraut depth
indexes the construction of that slab and is not a further iterate of this
operator.  No cross-model blocking map or strict completed gap is asserted.
-/

import YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
import YMGap.Continuum.BF4PhysicalSeparatorProducer
import YMGap.Continuum.FCNormBoundLimit
import YMGap.Continuum.RCCauchySchwarz

namespace YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalLocalGluingAFCertificate
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Dense physical observables inside the completion -/

/-- A rational regarded as a constant in the completed real quotient. -/
def physicalConstantRC (value : Q') : CReal.RC :=
  Quotient.mk CReal.crealSetoid (CReal.ofQ' value)

/-- Rational order embeds into order on completed-real constants. -/
theorem physicalConstantRC_le_of_rat {left right : Q'}
    (h : left ≤ right) :
    CReal.RCle (physicalConstantRC left) (physicalConstantRC right) := by
  change CReal.leEv (CReal.ofQ' left) (CReal.ofQ' right)
  exact CReal.leEv_of_le (CReal.ofQ'_le_ofQ' h)

/-- Multiplication in the completed real quotient is monotone in the right
input when the left factor is nonnegative. -/
theorem physicalRCmul_mono_nonnegative_left
    {factor left right : CReal.RC}
    (hfactor : CReal.RCnonneg factor)
    (hle : CReal.RCle left right) :
    CReal.RCle (CReal.RCmul factor left) (CReal.RCmul factor right) := by
  refine Quotient.inductionOn₃ factor left right ?_ hfactor hle
  intro f a b hf hab
  exact CReal.leEv_mul_nonneg_left hf hab

/-- The rational constant one is the multiplicative unit in `RC`. -/
theorem physicalRCmul_constant_one_right (value : CReal.RC) :
    CReal.RCmul value (physicalConstantRC 1) = value := by
  refine Quotient.inductionOn value ?_
  intro representative
  exact Quotient.sound
    (YMGap.Constructive.CRealAlg.cmul_cone representative)

/-- The literal dense embedding of a finite physical BF4 observable. -/
def centralPhysicalCompletedObservable
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    CentralPhysicalGNSCompletion w hw K half :=
  embedV (centralPhysicalSmulGNS w hw K half).toGNSData observable

/-- Pairing a finite observable with the constant vacuum is exactly its
stationary mean. -/
theorem centralPhysicalWeightedInner_vacuum_right
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    centralPhysicalWeightedInner w hw K half
        observable centralPhysicalVacuumCarrier ≈
      centralPhysicalStationaryMean w hw K half observable := by
  unfold centralPhysicalWeightedInner centralPhysicalStationaryMean
    centralPhysicalVacuumCarrier
  apply listQSum_congr
  intro state
  exact Q'.mul_eqv_congr_left
    (centralPhysicalRowMarginal w hw K half state) _ _
    (Q'.mul_one_eqv (observable state))

/-- The completed inner product of two dense observables is their exact
rational physical weighted pairing. -/
theorem centralPhysicalCompletedObservable_inner
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (left right : EdgeLabelling → Q') :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedObservable w hw K half left)
        (centralPhysicalCompletedObservable w hw K half right) =
      physicalConstantRC
        (centralPhysicalWeightedInner w hw K half left right) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  change D.cinnerCompl
      (embedQuot D (D.qmk left))
      (embedQuot D (D.qmk right)) =
    Quotient.mk CReal.crealSetoid
      (CReal.ofQ' (centralPhysicalWeightedInner w hw K half left right))
  rw [D.cinnerCompl_embed]
  apply Quotient.sound
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_of_eq
      (centralPhysicalSmulGNS_B_eq w hw K half left right))

/-- A finite stationary-mean-zero observable embeds into the actual completed
vacuum complement. -/
theorem centralPhysicalCompletedObservable_vacuumOrthogonal
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q')
    (hmean : CentralPhysicalMeanZero w hw K half observable) :
    CentralPhysicalCompletedVacuumOrthogonal w hw K half
      (centralPhysicalCompletedObservable w hw K half observable) := by
  let D := (centralPhysicalSmulGNS w hw K half).toGNSData
  unfold CentralPhysicalCompletedVacuumOrthogonal
  change D.cinnerCompl
      (embedQuot D (D.qmk observable))
      (embedQuot D (D.qmk centralPhysicalVacuumCarrier)) =
    Quotient.mk CReal.crealSetoid CReal.czero
  rw [D.cinnerCompl_embed]
  apply Quotient.sound
  exact CReal.ofQ'_equiv_of_eqv
    (Q'.eqv_trans _ _ _
      (Q'.eqv_trans _ _ _
        (Q'.eqv_of_eq
          (centralPhysicalSmulGNS_B_eq
            w hw K half observable centralPhysicalVacuumCarrier))
        (centralPhysicalWeightedInner_vacuum_right
          w hw K half observable))
      hmean)

/-! ## 2. The completed macro matrix coefficient -/

/-- The dense autocorrelation matrix coefficient of the completed macro
transfer is exactly the finite symmetric BF4 joint quadratic. -/
theorem centralPhysicalCompletedObservable_macroCoefficient
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    (centralPhysicalSmulGNS w hw K half).toGNSData.cinnerCompl
        (centralPhysicalCompletedObservable w hw K half observable)
        (centralPhysicalCompletedMarkovTransfer w hw K half
          (centralPhysicalCompletedObservable w hw K half observable)) =
      physicalConstantRC
        (centralPhysicalJointQuadratic w hw K half observable) := by
  unfold centralPhysicalCompletedObservable
  rw [centralPhysicalCompletedMarkovTransfer_embed]
  exact Eq.trans
    (centralPhysicalCompletedObservable_inner
      w hw K half observable
        (centralPhysicalMarkovApply w hw K half observable))
    (Quotient.sound
      (CReal.ofQ'_equiv_of_eqv
        (centralPhysicalWeightedMarkovQuadratic_eq_joint
          w hw K half observable)))

/-- The finite physical joint quadratic is nonnegative because its completed
matrix coefficient comes from the positive physical macro transfer. -/
theorem centralPhysicalJointQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)
    (observable : EdgeLabelling → Q') :
    (0 : Q') ≤ centralPhysicalJointQuadratic w hw K half observable :=
  Q'.le_trans' _ _ _
    (centralPhysicalMarkovApply_positive w hw K half observable)
    (Q'.le_of_eqv
      (centralPhysicalWeightedMarkovQuadratic_eq_joint
        w hw K half observable))

/-- The same-object pin is not merely numerically compatible with the GNS
construction: its selected connected correlation is the completed physical
macro matrix coefficient of the very same finite observable. -/
theorem sameObject_macroCorrelation_eq_completedCoefficient
    {family : MatchedBlockFamily}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    {depth : Nat → Nat}
    (pin : BF4PhysicalSeparatorSameObjectPin family coupling P depth)
    (scale : Nat)
    (observable : EdgeLabelling → Q')
    (hmean :
      CentralPhysicalMeanZero
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable) :
    (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerCompl
      (centralPhysicalCompletedObservable
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 observable)
      (centralPhysicalCompletedMarkovTransfer
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0
        (centralPhysicalCompletedObservable
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable)) =
      physicalConstantRC
        (P.corrIface.connectedCorr scale
          (pin.embed scale observable) (depth scale)) := by
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  have hjoint0 : (0 : Q') ≤
      centralPhysicalJointQuadratic w hw K 0 observable :=
    centralPhysicalJointQuadratic_nonnegative w hw K 0 observable
  have hcorrJoint :
      P.corrIface.connectedCorr scale
          (pin.embed scale observable) (depth scale) ≈
        centralPhysicalJointQuadratic w hw K 0 observable :=
    Q'.eqv_trans _ _ _
      (pin.macroCorrelation scale observable hmean)
      (Q'.eqv_of_eq
        (YMGap.Constructive.ExpNeg.abs_of_nonneg hjoint0))
  exact (centralPhysicalCompletedObservable_macroCoefficient
    w hw K 0 observable).trans
      (Quotient.sound
        (CReal.ofQ'_equiv_of_eqv (Q'.eqv_symm hcorrJoint)))

/-! ## 3. The producer's selected rate probe -/

/-- The producer's exact finite rate probe, embedded into the physical GNS
completion at the same scale. -/
def completedRateProbe
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    CentralPhysicalGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0 :=
  centralPhysicalCompletedObservable
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer.rateSharpness.probe scale)

theorem completedRateProbe_vacuumOrthogonal
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    CentralPhysicalCompletedVacuumOrthogonal
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0
      (completedRateProbe producer scale) :=
  centralPhysicalCompletedObservable_vacuumOrthogonal
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0
    (producer.rateSharpness.probe scale)
    (producer.rateSharpness.probe_meanZero scale)

/-- The completed rate probe retains the finite weighted normalization
`||v||^2 <= 1`. -/
theorem completedRateProbe_norm_le_one
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    CReal.RCle
      ((centralPhysicalSmulGNS w hw K 0).toGNSData.cinnerCompl
        (completedRateProbe producer scale)
        (completedRateProbe producer scale))
      (physicalConstantRC 1) := by
  dsimp only
  unfold completedRateProbe
  rw [centralPhysicalCompletedObservable_inner]
  exact physicalConstantRC_le_of_rat
    (producer.rateSharpness.probe_inner_le_one scale)

/-- The same-object physical connected correlation selected by the producer is
literally the completed autocorrelation of its embedded rate probe after one
physical macro transfer. -/
theorem completedRateProbe_macroCorrelation
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    (centralPhysicalSmulGNS w hw K 0).toGNSData.cinnerCompl
        (completedRateProbe producer scale)
        (centralPhysicalCompletedMarkovTransfer w hw K 0
          (completedRateProbe producer scale)) =
      physicalConstantRC
        (P.corrIface.connectedCorr scale
          (producer.sameObject.embed scale
            (producer.rateSharpness.probe scale))
          (producer.bf4.depth scale)) := by
  dsimp only
  exact sameObject_macroCorrelation_eq_completedCoefficient
    producer.sameObject scale (producer.rateSharpness.probe scale)
      (producer.rateSharpness.probe_meanZero scale)

/-- Completed Cauchy--Schwarz and the probe normalization automatically supply
the one-macro-step correlation-square handoff.  This is therefore no longer
independent operator-realization data. -/
theorem completedRateProbe_correlationSquare_le_transferredNorm
    {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat → Q'}
    {P : PhysicalSeparator}
    (producer : BF4QuarterPhysicalSeparatorProducer
      family law spacing coupling P)
    (scale : Nat) :
    let w := matchedAllSpinWeight family coupling scale
    let hw := matchedAllSpinWeight_nonnegative family coupling scale
    let K := matchedAllSpinCutoff family coupling scale
    let probe := completedRateProbe producer scale
    let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 probe
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
      ((centralPhysicalSmulGNS w hw K 0).toGNSData.cinnerCompl
        transferred transferred) := by
  dsimp only
  let w := matchedAllSpinWeight family coupling scale
  let hw := matchedAllSpinWeight_nonnegative family coupling scale
  let K := matchedAllSpinCutoff family coupling scale
  let D := (centralPhysicalSmulGNS w hw K 0).toGNSData
  let probe := completedRateProbe producer scale
  let transferred := centralPhysicalCompletedMarkovTransfer w hw K 0 probe
  have hcs := D.RC_cauchy_schwarz probe transferred
  have hcorrelation := completedRateProbe_macroCorrelation producer scale
  change D.cinnerCompl probe transferred = _ at hcorrelation
  rw [hcorrelation] at hcs
  have hprobe := completedRateProbe_norm_le_one producer scale
  change CReal.RCle (D.cinnerCompl probe probe) (physicalConstantRC 1) at hprobe
  have htransferred0 := D.cinner_self_nonneg transferred
  have hmul := physicalRCmul_mono_nonnegative_left htransferred0 hprobe
  rw [CReal.RCmul_comm (D.cinnerCompl probe probe)
      (D.cinnerCompl transferred transferred)] at hcs
  rw [physicalRCmul_constant_one_right] at hmul
  exact CReal.RCle_trans hcs hmul

end YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator

#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.centralPhysicalWeightedInner_vacuum_right
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.centralPhysicalCompletedObservable_inner
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.centralPhysicalCompletedObservable_vacuumOrthogonal
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.centralPhysicalCompletedObservable_macroCoefficient
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.centralPhysicalJointQuadratic_nonnegative
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.sameObject_macroCorrelation_eq_completedCoefficient
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.completedRateProbe_vacuumOrthogonal
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.completedRateProbe_norm_le_one
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.completedRateProbe_macroCorrelation
#print axioms YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator.completedRateProbe_correlationSquare_le_transferredNorm
