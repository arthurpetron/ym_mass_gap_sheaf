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

import YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit
import YMGap.Continuum.P2RetunedStrongTuranCompiler

namespace YMGap.Continuum.P2BlockCompatibleStrongTuranBridge

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.FusionKernelStatement
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleModeOneCross
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaCross
open YMGap.Continuum.P2BlockCompatibleThetaDeficit
open YMGap.Continuum.P2BlockCompatibleThetaParityEnergy
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaPathEnergy
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaNormalizedDeficit
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
bridge: weighted-box strong Turan at every scale, together with the additive
coarse-deficit and fine even-path-energy comparisons for the normalized
mode-one comparison.  Exact dyadic pairing and reflected polynomial
normalization compile those two local atoms to the cross-cutoff theta
half-contraction. -/
structure BlockCompatibleP2PhysicalFrontierAtoms : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  thetaEnergySandwich : BlockCompatibleP2ThetaPathEnergySandwich

/-- Reduced physical frontier after the exact `k=4`, `N=79 -> 159` path-
energy cell has been kernel-checked.  Only the coefficient sandwich from
`k=5` onward remains as an input. -/
structure BlockCompatibleP2PhysicalFrontierAtomsFromFive : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  thetaCoefficientTail : BlockCompatibleP2CoefficientSandwichFromFive

/-- Further reduced physical frontier after the exact `k=5`, `N=159 -> 319`
cell is also checked. -/
structure BlockCompatibleP2PhysicalFrontierAtomsFromSix : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  thetaCoefficientTail : BlockCompatibleP2CoefficientSandwichFromSix

/-- Physical frontier after the exact `k=6`, `N=319 -> 639` cell is checked. -/
structure BlockCompatibleP2PhysicalFrontierAtomsFromSeven : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  thetaCoefficientTail : BlockCompatibleP2CoefficientSandwichFromSeven

/-- Canonical analytic frontier after the checked prefix: weighted-box strong
Turan plus the two normalized-deficit inequalities from `k=7` onward. -/
structure BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  thetaNormalizedTail : BlockCompatibleP2NormalizedDeficitTailFromSeven

/-- Insert the checked `k=4` cell, compile the remaining coefficient cells to
path-energy cells, and recover the original physical frontier boundary. -/
def BlockCompatibleP2PhysicalFrontierAtomsFromFive.toPhysicalFrontierAtoms
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromFive) :
    BlockCompatibleP2PhysicalFrontierAtoms where
  coefficient := A.coefficient
  thetaEnergySandwich :=
    A.thetaCoefficientTail.toAllScale.toThetaPathEnergySandwich

/-- Insert both checked tail cells and recover the original physical frontier
boundary from a coefficient sandwich beginning only at `k=6`. -/
def BlockCompatibleP2PhysicalFrontierAtomsFromSix.toPhysicalFrontierAtoms
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSix) :
    BlockCompatibleP2PhysicalFrontierAtoms where
  coefficient := A.coefficient
  thetaEnergySandwich :=
    A.thetaCoefficientTail.toAllScale.toThetaPathEnergySandwich

/-- Insert all three checked tail cells and recover the original physical
frontier from a coefficient sandwich beginning at `k=7`. -/
def BlockCompatibleP2PhysicalFrontierAtomsFromSeven.toPhysicalFrontierAtoms
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSeven) :
    BlockCompatibleP2PhysicalFrontierAtoms where
  coefficient := A.coefficient
  thetaEnergySandwich :=
    A.thetaCoefficientTail.toAllScale.toThetaPathEnergySandwich

/-- Cancel the normalized ratios, insert the three checked prefix cells, and
recover the original physical frontier boundary. -/
def BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.toPhysicalFrontierAtoms
    (A : BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven) :
    BlockCompatibleP2PhysicalFrontierAtoms where
  coefficient := A.coefficient
  thetaEnergySandwich := A.thetaNormalizedTail.toCoefficientSandwich
    |>.toAllScale.toThetaPathEnergySandwich

def BlockCompatibleP2PhysicalFrontierAtoms.coeffTailData
    (A : BlockCompatibleP2PhysicalFrontierAtoms) :
    BlockCompatibleP2CoeffTailData :=
  A.coefficient.toCoeffTailData

def BlockCompatibleP2PhysicalFrontierAtoms.modeOneTailMonotonicity
    (A : BlockCompatibleP2PhysicalFrontierAtoms) :
    BlockCompatibleP2ModeOneTailMonotonicity :=
  A.thetaEnergySandwich.toPathEnergyTransport.toEnergyTransport
    |>.toDyadicParityTransport
    |>.toThetaDeficitHalfContraction.toThetaDeficitTail
    |>.toThetaCrossTail.toModeOneCrossTail
    |>.toModeOneTailMonotonicity

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

/-- The reduced frontier reaches the actual physical map, including the
checked first tail cell, without reintroducing an all-`k>=4` premise. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromFive.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromFive)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne) B.Φ
      (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
        A.toPhysicalFrontierAtoms.coeffTailData (B := B)).toCrossMul.factor :=
  A.toPhysicalFrontierAtoms.blockDefectPowerOnTrajectory

/-- The corresponding quotient factor still lies in the certified half-loss
window at every scale. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromFive.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromFive)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
          A.toPhysicalFrontierAtoms.coeffTailData
          (B := B)).toCrossMul.factor k <=
      YMGap.Constructive.HalfPow.half :=
  A.toPhysicalFrontierAtoms.factorLossLeHalf k

/-- The twice-reduced frontier reaches the genuine physical map with only a
`k>=6` theta coefficient tail left open. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromSix.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSix)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne) B.Φ
      (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
        A.toPhysicalFrontierAtoms.coeffTailData (B := B)).toCrossMul.factor :=
  A.toPhysicalFrontierAtoms.blockDefectPowerOnTrajectory

/-- The quotient factors generated from the twice-reduced frontier retain the
same uniform half-loss bound. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromSix.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSix)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
          A.toPhysicalFrontierAtoms.coeffTailData
          (B := B)).toCrossMul.factor k <=
      YMGap.Constructive.HalfPow.half :=
  A.toPhysicalFrontierAtoms.factorLossLeHalf k

/-- The three-anchor frontier reaches the genuine physical map with only a
`k>=7` theta coefficient tail left open. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromSeven.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSeven)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne) B.Φ
      (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
        A.toPhysicalFrontierAtoms.coeffTailData (B := B)).toCrossMul.factor :=
  A.toPhysicalFrontierAtoms.blockDefectPowerOnTrajectory

/-- The three-anchor quotient factors retain the uniform half-loss bound. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromSeven.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromSeven)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
          A.toPhysicalFrontierAtoms.coeffTailData
          (B := B)).toCrossMul.factor k <=
      YMGap.Constructive.HalfPow.half :=
  A.toPhysicalFrontierAtoms.factorLossLeHalf k

/-- The normalized-deficit tail reaches the actual `BlockingStep.Phi` map. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne) B.Φ
      (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
        A.toPhysicalFrontierAtoms.coeffTailData (B := B)).toCrossMul.factor :=
  A.toPhysicalFrontierAtoms.blockDefectPowerOnTrajectory

/-- The normalized-deficit route retains the quotient half-loss bound. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven)
    {B : BlockingStep
      (fusionSeparator
        A.toPhysicalFrontierAtoms.coeffTailData.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toPhysicalFrontierAtoms.modeOneTailMonotonicity.toQuotientData
          A.toPhysicalFrontierAtoms.coeffTailData
          (B := B)).toCrossMul.factor k <=
      YMGap.Constructive.HalfPow.half :=
  A.toPhysicalFrontierAtoms.factorLossLeHalf k

#print axioms BlockCompatibleP2StrongTuranData.toCoeffTailData
#print axioms BlockCompatibleP2BoxStrongTuranData.toStrongTuranData
#print axioms BlockCompatibleP2BoxStrongTuranData.toCoeffTailData
#print axioms BlockCompatibleP2PhysicalFrontierAtoms.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtoms.factorLossLeHalf
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromFive.toPhysicalFrontierAtoms
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromFive.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromFive.factorLossLeHalf
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSix.toPhysicalFrontierAtoms
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSix.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSix.factorLossLeHalf
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSeven.toPhysicalFrontierAtoms
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSeven.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromSeven.factorLossLeHalf
#print axioms BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.toPhysicalFrontierAtoms
#print axioms BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtomsNormalizedFromSeven.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
