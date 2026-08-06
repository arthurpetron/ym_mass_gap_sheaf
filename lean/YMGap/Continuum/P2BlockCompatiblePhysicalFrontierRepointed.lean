/-
Track 11.7-fusion / R4e -- physically repoint the strict frontier away from
the constructively empty schedule-wide strong-Turan carrier.

The coefficient input is now the fixed-power parity-strand family only from
`k>=4`: direct integral certificates discharge every supported mode at scales
zero through three, odd cells propagate by a two-step product law, and each
even cell is inserted from the preceding odd cell by the true odd-index Turan
law.  The theta input remains the honest post-certificate tail with both fields
requested only from `k>=8`.  These independent inputs compile directly to the
reviewed all-cutoff family, its spectrum pins, and the genuine
`BlockingStep.Phi` quotient defect without passing through either refuted
all-index strong-Turan carrier.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
import YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
import YMGap.Continuum.P2RetunedParityStrandCompiler

namespace YMGap.Continuum.P2BlockCompatiblePhysicalFrontierRepointed

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleIntegralTailCertificate
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleStrongTuranBridge
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.RGTransport

/-- Honest Bucket-1 boundary after removing both refuted sufficient premises.
The true parity-strand coefficient laws begin only at physical scale four. -/
structure BlockCompatibleP2PhysicalFrontierRepointed : Type where
  coefficient : BlockCompatibleP2BoxCoreParityStrandFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalFrontierRepointed.coeffTailData
    (A : BlockCompatibleP2PhysicalFrontierRepointed) :
    BlockCompatibleP2CoeffTailData :=
  A.coefficient.toCoeffTailData

/-- The checked theta prefix and the two post-certificate tails produce the
same physical mode-one monotonicity datum independently of the coefficient
compiler. -/
def BlockCompatibleP2PhysicalFrontierRepointed.modeOneTailMonotonicity
    (A : BlockCompatibleP2PhysicalFrontierRepointed) :
    BlockCompatibleP2ModeOneTailMonotonicity :=
  A.theta.toPostRadialTailFromEight.toCoefficientSandwich
    |>.toAllScale.toThetaPathEnergySandwich
    |>.toPathEnergyTransport.toEnergyTransport
    |>.toDyadicParityTransport
    |>.toThetaDeficitHalfContraction.toThetaDeficitTail
    |>.toThetaCrossTail.toModeOneCrossTail
    |>.toModeOneTailMonotonicity

/-- The repaired frontier constructs the reviewed all-cutoff `pGamma=2`
canonical family without passing through the empty carrier. -/
def BlockCompatibleP2PhysicalFrontierRepointed.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalFrontierRepointed) :
    CanonicalBulkControlFamily :=
  CanonicalBulkControlFamily.ofP2Retuned A.coeffTailData.toControlFamily

theorem BlockCompatibleP2PhysicalFrontierRepointed.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalFrontierRepointed) (k : Nat) :
    2 ≤ A.toCanonicalFamily.pGamma k :=
  A.toCanonicalFamily.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalFrontierRepointed.finePin
    (A : BlockCompatibleP2PhysicalFrontierRepointed)
    (mode : Nat → Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  canonicalFusionSeparator_finePin A.toCanonicalFamily mode k

theorem BlockCompatibleP2PhysicalFrontierRepointed.imagePin
    (A : BlockCompatibleP2PhysicalFrontierRepointed)
    (mode : Nat → Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  canonicalFusionSeparator_imagePin A.toCanonicalFamily mode B k

/-- The repaired frontier reaches the actual physical map on the selected
mode-one trajectory. -/
theorem BlockCompatibleP2PhysicalFrontierRepointed.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalFrontierRepointed)
    {B : BlockingStep
      (fusionSeparator A.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne) B.Φ
      (A.modeOneTailMonotonicity.toQuotientData A.coeffTailData (B := B)
        |>.toCrossMul.factor) :=
  A.modeOneTailMonotonicity.blockDefectPowerOnTrajectory A.coeffTailData

/-- The quotient factors retain the constructive half-loss gate. -/
theorem BlockCompatibleP2PhysicalFrontierRepointed.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalFrontierRepointed)
    {B : BlockingStep
      (fusionSeparator A.coeffTailData.toControlFamily
        P2RetunedFusionPhysicalMode.modeOne)} (k : Nat) :
    (1 : Q') -
        (A.modeOneTailMonotonicity.toQuotientData A.coeffTailData (B := B)
          |>.toCrossMul.factor k) ≤
      YMGap.Constructive.HalfPow.half :=
  A.modeOneTailMonotonicity.factorLossLeHalf A.coeffTailData k

#print axioms BlockCompatibleP2PhysicalFrontierRepointed.coeffTailData
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.modeOneTailMonotonicity
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.toCanonicalFamily
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.finePin
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.imagePin
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2PhysicalFrontierRepointed.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatiblePhysicalFrontierRepointed
