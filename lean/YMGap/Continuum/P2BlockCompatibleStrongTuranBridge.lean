/-
Track 11.7-fusion / R3e -- schedule-wide strong-Turan frontier atoms.

# Result

The block-compatible physical bridge formerly accepted one adjacent-
coefficient inequality for every scale and every supported mode.  The
strong-Turan induction is a proof about that computation: at each fixed
scale it propagates the first open edge through the entire Clebsch support.

This module lifts that compiler over the complete replacement schedule.  It
also exposes the weighted-box form, so the all-scale coefficient carrier is
reduced to the existing ballot/interlacing coordinate rather than to fusion
convolution evaluation.  Bundled with the genuine normalized mode-one square
comparison, these are the two remaining honest atoms needed to reach the
genuine `BlockingStep.Phi` defect-power identity.

# Constructivity

Pure structure compilation and the existing Nat induction.  No `Classical`,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration.
-/

import YMGap.Continuum.P2BlockCompatibleModeOneCross
import YMGap.Continuum.P2RetunedStrongTuranCompiler

namespace YMGap.Continuum.P2BlockCompatibleStrongTuranBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleModeOneCross
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedStrongTuranCompiler

/-! ## 1. Lift the proof-about-computation compiler over all scales -/

/-- One strong-Turan family at every cutoff of the physical replacement
schedule.  The first open edge and the uniform Turan step replace a growing
adjacent-coefficient scan at each scale. -/
structure BlockCompatibleP2StrongTuranData : Type where
  strongTuran : forall k,
    P2RetunedStrongTuran (blockNcut k) (blockWeight k)
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)

/-- Compile the schedule-wide strong-Turan family to the exact raw
coefficient carrier consumed by `CanonicalBulkControl`. -/
def BlockCompatibleP2StrongTuranData.toCoeffTailData
    (T : BlockCompatibleP2StrongTuranData) :
    BlockCompatibleP2CoeffTailData where
  coeffTailRatio := fun k =>
    p2CoeffTailRatio_of_strongTuran
      (blockWeight_pos k) (blockWeight_le_one k) (T.strongTuran k)

/-- The canonical weighted Clebsch-box version of the all-scale residual. -/
structure BlockCompatibleP2BoxStrongTuranData : Type where
  boxStrongTuran : forall k,
    P2RetunedBoxStrongTuran (blockNcut k) (blockWeight k)
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)

/-- Exact Peter--Weyl reconstruction transports the weighted boxes to the
physical bond-moved strong-Turan family at every scale. -/
def BlockCompatibleP2BoxStrongTuranData.toStrongTuranData
    (T : BlockCompatibleP2BoxStrongTuranData) :
    BlockCompatibleP2StrongTuranData where
  strongTuran := fun k =>
    strongTuran_of_box
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)
      (T.boxStrongTuran k)

/-- The weighted-box family therefore constructs the reviewed all-scale
`CanonicalBulkControl` carrier without evaluating a fusion-power table. -/
def BlockCompatibleP2BoxStrongTuranData.toCoeffTailData
    (T : BlockCompatibleP2BoxStrongTuranData) :
    BlockCompatibleP2CoeffTailData :=
  T.toStrongTuranData.toCoeffTailData

/-! ## 2. The two canonical physical frontier atoms -/

/-- The complete remaining input boundary for the present p=2 physical
bridge: weighted-box strong Turan at every scale, and the division-free
normalized mode-one cross comparison.  The latter preserves cancellation
because the crude unnormalized endpoint-Lipschitz route is provably too
large. -/
structure BlockCompatibleP2PhysicalFrontierAtoms : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  modeOneCross : BlockCompatibleP2ModeOneCrossTail

def BlockCompatibleP2PhysicalFrontierAtoms.coeffTailData
    (A : BlockCompatibleP2PhysicalFrontierAtoms) :
    BlockCompatibleP2CoeffTailData :=
  A.coefficient.toCoeffTailData

def BlockCompatibleP2PhysicalFrontierAtoms.modeOneTailMonotonicity
    (A : BlockCompatibleP2PhysicalFrontierAtoms) :
    BlockCompatibleP2ModeOneTailMonotonicity :=
  A.modeOneCross.toModeOneTailMonotonicity

/-- The two frontier atoms compile all the way to the actual physical map:
`finePin` is spectrum-defined, `imagePin` is `BlockingStep.step`, and the
factor is the genuine two-fold quotient defect. -/
theorem BlockCompatibleP2PhysicalFrontierAtoms.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtoms)
    {B : BlockingStep
      (fusionSeparator A.coeffTailData.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.coeffTailData.toControlFamily modeOne) B.Φ
      (A.modeOneTailMonotonicity.toQuotientData A.coeffTailData
        (B := B)).toCrossMul.factor :=
  A.modeOneTailMonotonicity.blockDefectPowerOnTrajectory
    A.coeffTailData

/-- Every resulting physical quotient remains in the certified half-loss
window.  A summable sharper loss remains a later physical-margin atom. -/
theorem BlockCompatibleP2PhysicalFrontierAtoms.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtoms)
    {B : BlockingStep
      (fusionSeparator A.coeffTailData.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.modeOneTailMonotonicity.toQuotientData A.coeffTailData
          (B := B)).toCrossMul.factor k <=
      YMGap.Constructive.HalfPow.half :=
  A.modeOneTailMonotonicity.factorLossLeHalf A.coeffTailData k

#print axioms BlockCompatibleP2StrongTuranData.toCoeffTailData
#print axioms BlockCompatibleP2BoxStrongTuranData.toStrongTuranData
#print axioms BlockCompatibleP2BoxStrongTuranData.toCoeffTailData
#print axioms BlockCompatibleP2PhysicalFrontierAtoms.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtoms.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
