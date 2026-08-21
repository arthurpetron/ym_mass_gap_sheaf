/-
# Choice-free dense comparison from modulated physical BF4 to the endpoint

The Type-modulated physical GNS carrier removes the sole completion-interface
obstruction found in the legacy route.  A finite-stage map preserving squared
distance now sends explicit physical null moduli directly to explicit strong
null moduli.  No selector field and no choice principle are needed.

Five dense analytic laws remain: the stage map itself, squared-distance and
full-inner identifications, the one-macro-step radical intertwining law, and
the vacuum radical law.  From these, this module constructs the completed map,
proves all four completed comparison laws, and imports the strict endpoint
operator norm gap to the physical modulated vacuum complement.

No inhabitant of the five dense analytic laws is claimed.
-/

import YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
import YMGap.Continuum.BF4PhysicalSeparatorProducer
import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap

namespace YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4PhysicalMarkovModulusCompletion
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4ReflectedAllSpinAFRowRelative
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.GNSModulusCompletion
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CouplingParametricSignedGeometricClustering
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedInner
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionBilinearOuter
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedTwoStepTransfer
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletedVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDirectLimitBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointVacuumComplement
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCompletedOperatorNormGap
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The five dense analytic laws -/

/-- Dense finite-stage comparison data on the Type-modulated physical carrier.
Unlike the legacy lift, this structure needs no null-modulus selector. -/
structure ModulatedBF4DenseEndpointData
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
  toStrongStage : (scale : Nat) →
    (EdgeLabelling → Q') → StrictJointCylinderStage
  distSqIdentification : ∀ scale left right,
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hendpoint hle
        (toStrongStage scale left) (toStrongStage scale right))
      (CReal.ofQ'
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.distSqQ
          left right))
  innerIdentification : ∀ scale left right,
    CReal.Equiv
      (strictJointCylinderStageReflectionBilinear hendpoint hle
        (toStrongStage scale left) (toStrongStage scale right))
      (CReal.ofQ'
        ((centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData.B
          left right))
  macroStageNull : ∀ scale observable,
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Null
      (toStrongStage scale
        (centralPhysicalMarkovApply
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 observable))
      ((toStrongStage scale observable).timeTranslate (1 + 1))
  vacuumStageNull : ∀ scale,
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Null
      (toStrongStage scale centralPhysicalVacuumCarrier)
      strictJointCylinderVacuumStage

namespace ModulatedBF4DenseEndpointData

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

private theorem czero_le_ofQ'_of_pos {epsilon : Q'}
    (hepsilon : (0 : Q') < epsilon) :
    CReal.leEv CReal.czero (CReal.ofQ' epsilon) :=
  CReal.leEv_of_le
    (CReal.ofQ'_le_ofQ' (Q'.le_of_lt hepsilon))

/-! ## 2. Automatic modulus transport and completion map -/

def mapPhysicalCauchy
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (X : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData) :
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Cauchy where
  seq := fun n => data.toStrongStage scale (X.seq n)
  modulus := X.modulus
  isCauchy := by
    intro epsilon hepsilon m n hm hn
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (data.distSqIdentification scale (X.seq m) (X.seq n)))
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ'
          (X.isCauchy epsilon hepsilon m n hm hn)))

/-- Exact squared-distance preservation transports a supplied physical null
modulus to the strong completion with the same modulus. -/
def mapNullModulus
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    {X Y : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData}
    (hXY : CauchyNullModulus
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData X Y) :
    (strictJointCylinderStageSquaredSeminorm hendpoint hle).Close
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y) where
  modulus := hXY.modulus
  close := by
    intro epsilon hepsilon n hn
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (data.distSqIdentification scale (X.seq n) (Y.seq n)))
      (CReal.leEv_of_le
        (CReal.ofQ'_le_ofQ'
          (hXY.close epsilon hepsilon n hn)))

def completedMap
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat) :
    CentralPhysicalModulatedGNSCompletion
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 →
      StrictJointCylinderOSCompletion hendpoint hle :=
  Quotient.lift
    (fun X => Quotient.mk
      (strictJointCylinderStageSquaredSeminorm hendpoint hle).completionSetoid
      (data.mapPhysicalCauchy scale X))
    (fun _ _ h => by
      rcases h with ⟨hdata⟩
      exact Quotient.sound ⟨data.mapNullModulus scale hdata⟩)

theorem completedMap_embed
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat) (observable : EdgeLabelling → Q') :
    data.completedMap scale
        (modulatedEmbedV
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData
          observable) =
      (strictJointCylinderStageSquaredSeminorm hendpoint hle).embedRep
        (data.toStrongStage scale observable) := by
  apply Quotient.sound
  exact ⟨{
    modulus := fun _ => 0
    close := by
      intro epsilon hepsilon n hn
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          ((strictJointCylinderStageSquaredSeminorm hendpoint hle).distSq_refl
            (data.toStrongStage scale observable)))
        (czero_le_ofQ'_of_pos hepsilon)
  }⟩

/-! ## 3. Full completed inner preservation -/

theorem mappedCauchy_inner_equiv
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (X Y : CauchyGNS
      (centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData) :
    CReal.Equiv
      (cauchyPairingLimit hendpoint hle
        (data.mapPhysicalCauchy scale X)
        (data.mapPhysicalCauchy scale Y))
      ((centralPhysicalSmulGNS
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0).toGNSData.cinnerRep
        X Y) := by
  let D := (centralPhysicalSmulGNS
    (matchedAllSpinWeight family coupling scale)
    (matchedAllSpinWeight_nonnegative family coupling scale)
    (matchedAllSpinCutoff family coupling scale) 0).toGNSData
  apply CReal.Equiv_of_limit_of_equal
    (aSeq := cauchyPairingSeq hendpoint hle
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y))
    (bSeq := fun n => CReal.ofQ' (D.cInnerSeq X Y n))
  · intro n
    exact data.innerIdentification scale (X.seq n) (Y.seq n)
  · exact cauchyPairingSeq_converges hendpoint hle
      (data.mapPhysicalCauchy scale X)
      (data.mapPhysicalCauchy scale Y)
  · exact CReal.convergesTo_ofQ'CauchySeq _ _

theorem completedMap_inner
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (left right : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0) :
    strictJointCylinderCompletedInner hendpoint hle
        (data.completedMap scale left) (data.completedMap scale right) =
      modulatedCinnerCompl
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData
        left right := by
  refine Quotient.inductionOn₂ left right ?_
  intro X Y
  apply Quotient.sound
  exact data.mappedCauchy_inner_equiv scale X Y

/-! ## 4. Macro, vacuum, and vacuum complement -/

theorem completedMap_macroTransferIntertwining
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0) :
    data.completedMap scale
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector) =
      strictJointCylinderCompletedTwoStepTransfer hendpoint hle
        (data.completedMap scale vector) := by
  refine Quotient.inductionOn vector ?_
  intro X
  apply Quotient.sound
  exact ⟨{
    modulus := fun _ => 0
    close := by
      intro epsilon hepsilon n hn
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          (data.macroStageNull scale (X.seq n)))
        (czero_le_ofQ'_of_pos hepsilon)
  }⟩

theorem completedMap_vacuum
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat) :
    data.completedMap scale
        (centralPhysicalModulatedVacuum
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0) =
      strictJointCylinderCompletionVacuum hendpoint hle := by
  unfold centralPhysicalModulatedVacuum
  rw [data.completedMap_embed]
  exact (strictJointCylinderStageSquaredSeminorm hendpoint hle).embedRep_eq_of_null
    (data.vacuumStageNull scale)

theorem completedMap_mapsVacuumOrthogonal
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal :
      CentralPhysicalModulatedVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 vector) :
    StrictJointCylinderCompletionVacuumOrthogonal hendpoint hle
      (data.completedMap scale vector) := by
  unfold StrictJointCylinderCompletionVacuumOrthogonal
  rw [← data.completedMap_vacuum scale]
  rw [data.completedMap_inner scale]
  exact horthogonal

/-! ## 5. Imported strict physical gap -/

/-- The five dense analytic laws imply the uniform strict operator norm gap on
the actual Type-modulated physical vacuum complement. -/
theorem physicalModulatedMacroTransfer_norm_gap
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer)
    (scale : Nat)
    (vector : CentralPhysicalModulatedGNSCompletion
      (matchedAllSpinWeight family coupling scale)
      (matchedAllSpinWeight_nonnegative family coupling scale)
      (matchedAllSpinCutoff family coupling scale) 0)
    (horthogonal :
      CentralPhysicalModulatedVacuumOrthogonal
        (matchedAllSpinWeight family coupling scale)
        (matchedAllSpinWeight_nonnegative family coupling scale)
        (matchedAllSpinCutoff family coupling scale) 0 vector) :
    CReal.RCle
      (modulatedCinnerCompl
        (centralPhysicalSmulGNS
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0).toGNSData
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector)
        (centralPhysicalModulatedMarkovTransfer
          (matchedAllSpinWeight family coupling scale)
          (matchedAllSpinWeight_nonnegative family coupling scale)
          (matchedAllSpinCutoff family coupling scale) 0 vector))
      (CReal.RCscale
        (anchorDecoratedDoubledTimeRate *
          anchorDecoratedDoubledTimeRate)
        (modulatedCinnerCompl
          (centralPhysicalSmulGNS
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0).toGNSData
          vector vector)) := by
  rw [← data.completedMap_inner scale]
  rw [data.completedMap_macroTransferIntertwining scale]
  rw [← data.completedMap_inner scale]
  exact anchorDecoratedDoubledTimeRate_completed_vacuum_operator_norm_gap
    hendpoint hle (data.completedMap scale vector)
      (data.completedMap_mapsVacuumOrthogonal scale vector horthogonal)

/-- The imported rate is uniformly strict. -/
theorem physicalModulatedMacroVacuumNormGap
    (data : ModulatedBF4DenseEndpointData hendpoint hle producer) :
    (0 : Q') ≤ anchorDecoratedDoubledTimeRate ∧
      anchorDecoratedDoubledTimeRate < (1 : Q') ∧
      ∀ scale vector,
        CentralPhysicalModulatedVacuumOrthogonal
            (matchedAllSpinWeight family coupling scale)
            (matchedAllSpinWeight_nonnegative family coupling scale)
            (matchedAllSpinCutoff family coupling scale) 0 vector →
          CReal.RCle
            (modulatedCinnerCompl
              (centralPhysicalSmulGNS
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative family coupling scale)
                (matchedAllSpinCutoff family coupling scale) 0).toGNSData
              (centralPhysicalModulatedMarkovTransfer
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative family coupling scale)
                (matchedAllSpinCutoff family coupling scale) 0 vector)
              (centralPhysicalModulatedMarkovTransfer
                (matchedAllSpinWeight family coupling scale)
                (matchedAllSpinWeight_nonnegative family coupling scale)
                (matchedAllSpinCutoff family coupling scale) 0 vector))
            (CReal.RCscale
              (anchorDecoratedDoubledTimeRate *
                anchorDecoratedDoubledTimeRate)
              (modulatedCinnerCompl
                (centralPhysicalSmulGNS
                  (matchedAllSpinWeight family coupling scale)
                  (matchedAllSpinWeight_nonnegative family coupling scale)
                  (matchedAllSpinCutoff family coupling scale) 0).toGNSData
                vector vector)) :=
  ⟨anchorDecoratedDoubledTimeRate_nonnegative,
    anchorDecoratedDoubledTimeRate_lt_one,
    fun scale vector horthogonal =>
      data.physicalModulatedMacroTransfer_norm_gap
        scale vector horthogonal⟩

end ModulatedBF4DenseEndpointData

end YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison

#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.mapNullModulus
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.completedMap
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.completedMap_inner
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.completedMap_macroTransferIntertwining
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.completedMap_vacuum
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.completedMap_mapsVacuumOrthogonal
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.physicalModulatedMacroTransfer_norm_gap
#print axioms YMGap.Continuum.BF4PhysicalModulatedDenseEndpointComparison.ModulatedBF4DenseEndpointData.physicalModulatedMacroVacuumNormGap
