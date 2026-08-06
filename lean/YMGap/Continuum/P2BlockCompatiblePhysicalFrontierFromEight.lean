/-
Track 11.7-fusion / R3y -- install the checked `k=7` fine-reserve head.

The terminal and radial fields are already proved for every `k>=7`, and the
preceding exact certificate closes the fine even/odd reserve at `k=7`.  This
module removes that discharged head cell from the honest physical input:

* trapezoid exchange remains for `k>=7`;
* fine reserve is requested only for `k>=8`;
* the weighted-box strong-Turan family remains the coefficient input.

The resulting carrier compiles to the all-cutoff `pGamma=2` canonical control
family, embeds in the general `pGamma>=2` family, and reaches the genuine
`BlockingStep.Phi` defect-power identity.  `finePin` and `imagePin` are filled
by the existing spectrum-defined theorems; no duplicate map hypothesis is
introduced.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenPhysical
import YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedBlock
import YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
import YMGap.Continuum.CanonicalFusionSpectrumFamily

namespace YMGap.Continuum.P2BlockCompatiblePhysicalFrontierFromEight

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenPhysical
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2BlockCompatibleThetaTerminalRadialFixedBlock
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.RGTransport

/-- Honest post-certificate theta frontier.  The exact `k=7` reserve is no
longer a caller-supplied premise. -/
structure BlockCompatibleP2PostRadialTailFromEight : Type where
  trapezoidExchange : forall k, 7 <= k ->
    let w0 := blockWeight k
    let w4 := qpow (blockWeight (k + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut k) <= (0 : Q')
  fineReserve : forall k, 8 <= k ->
    let w1 := blockWeight (k + 1)
    let w4 := qpow w1 4
    let D1 := coordNormSq w1 (blockNcut (k + 1))
    let D4 := coordNormSq w4 (blockNcut k)
    let T1 := coefficientDeficit w1 (blockNcut (k + 1))
    let T4 := coefficientDeficit w4 (blockNcut k)
    Q'.ofNat 2 * (D4 * T1) +
        blockParityDebt k * (D1 * D4) <= D1 * T4

/-- Insert the exact physical `k=7` reserve and recover the previous
post-radial carrier. -/
def BlockCompatibleP2PostRadialTailFromEight.toPostRadialTailFromSeven
    (T : BlockCompatibleP2PostRadialTailFromEight) :
    BlockCompatibleP2PostRadialTailFromSeven where
  trapezoidExchange := T.trapezoidExchange
  fineReserve := fun k hk => by
    by_cases h7 : k = 7
    · subst k
      exact blockFineReserve_seven
    · exact T.fineReserve k (by omega)

/-- The reduced theta frontier now yields the existing coefficient sandwich
with no `k=7` fine-reserve field. -/
def BlockCompatibleP2PostRadialTailFromEight.toCoefficientSandwich
    (T : BlockCompatibleP2PostRadialTailFromEight) :
    BlockCompatibleP2CoefficientSandwichFromSeven :=
  T.toPostRadialTailFromSeven.toCoefficientSandwich

/-- Complete current Bucket-1 analytic boundary after installing every checked
theta head cell: weighted-box strong Turan, trapezoid exchange from seven, and
fine reserve only from eight. -/
structure BlockCompatibleP2PhysicalFrontierAtomsFromEight : Type where
  coefficient : BlockCompatibleP2BoxStrongTuranData
  theta : BlockCompatibleP2PostRadialTailFromEight

/-- Recover the reviewed physical frontier.  This is a strict premise
reduction because the old `k=7` fine-reserve field is theorem-generated. -/
def BlockCompatibleP2PhysicalFrontierAtomsFromEight.toFrontierFromSeven
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight) :
    BlockCompatibleP2PhysicalFrontierAtomsFromSeven where
  coefficient := A.coefficient
  thetaCoefficientTail := A.theta.toCoefficientSandwich

/-- The weighted-box input constructs an actual all-cutoff `pGamma=2`
`CanonicalBulkControl` family. -/
def BlockCompatibleP2PhysicalFrontierAtomsFromEight.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight) :
    CanonicalBulkControlFamily :=
  CanonicalBulkControlFamily.ofP2Retuned
    A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData.toControlFamily

/-- The constructed family is literally in the reviewed positive-exponent
class. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromEight.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCanonicalFamily.pGamma_ge_two k

/-- On this reduced physical frontier the fine separator pin remains
definitionally generated by the selected canonical fusion spectrum. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromEight.finePin
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  canonicalFusionSeparator_finePin A.toCanonicalFamily mode k

/-- The image pin is the symmetric law of the actual physical blocking step,
not a separately assumed equality. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromEight.imagePin
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  canonicalFusionSeparator_imagePin A.toCanonicalFamily mode B k

/-- The reduced frontier reaches the genuine `BlockingStep.Phi` defect-power
identity through the existing mode-one quotient compiler. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromEight.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight)
    {B : BlockingStep
      (fusionSeparator
        A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator
        A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne) B.Φ
      (A.toFrontierFromSeven.toPhysicalFrontierAtoms.modeOneTailMonotonicity
        |>.toQuotientData
          A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData (B := B)
        |>.toCrossMul.factor) :=
  A.toFrontierFromSeven.blockDefectPowerOnTrajectory

/-- The same quotient factors retain the constructive half-loss gate. -/
theorem BlockCompatibleP2PhysicalFrontierAtomsFromEight.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierAtomsFromEight)
    {B : BlockingStep
      (fusionSeparator
        A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne)} (k : Nat) :
    (1 : Q') -
        (A.toFrontierFromSeven.toPhysicalFrontierAtoms.modeOneTailMonotonicity
          |>.toQuotientData
            A.toFrontierFromSeven.toPhysicalFrontierAtoms.coeffTailData (B := B)
          |>.toCrossMul.factor k) <=
      YMGap.Constructive.HalfPow.half :=
  A.toFrontierFromSeven.factorLossLeHalf k

#print axioms BlockCompatibleP2PostRadialTailFromEight.toPostRadialTailFromSeven
#print axioms BlockCompatibleP2PostRadialTailFromEight.toCoefficientSandwich
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromEight.toCanonicalFamily
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromEight.finePin
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromEight.imagePin
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromEight.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierAtomsFromEight.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatiblePhysicalFrontierFromEight
