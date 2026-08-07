/-
Track 11.7-fusion / R4am -- centered-reserve refinement of the common
physical frontier.

The centered heat-successor argument and its rectangular corollary reduce
the coefficient campaign to a region-split residual with a fixed-width upper
prefix.  This module compiles that smaller carrier to the same reviewed all-scale
coefficient datum used by the physical spectrum, pairs it with the existing
post-radial theta carrier, and proves that the resulting data reach the
canonical `pGamma >= 2`, `finePin`, `imagePin`, and genuine
`BlockingStep.Phi` conclusions.

This is an implication, not an inhabitance claim.  The minimized coefficient
reserve and the post-radial theta tail remain explicit open inputs.  No
frontier bundle or Yang--Mills target is constructed here.

No `Classical`, `native_decide`, explicit proof hole, custom axiom, or
noncomputable declaration.
-/

import YMGap.Continuum.P2HalfTimeCenteredProfile
import YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier

namespace YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2HalfTimeCenteredProfile
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.RGTransport

/-! ## Centered coefficient refinement of the physical carrier -/

/-- The common physical frontier with the coefficient input sharpened to the
region-split centered/product-tail reserve.  The theta component is exactly
the existing strict post-radial tail; no second physical trajectory is made. -/
structure BlockCompatibleP2PhysicalCenteredReserveFrontier : Type where
  coefficient : BlockCompatibleP2CenteredRectangleResidualFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

/-- Compile the sharpened coefficient input to the single reviewed physical
carrier shared by all coefficient proof routes. -/
def BlockCompatibleP2PhysicalCenteredReserveFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

def BlockCompatibleP2PhysicalCenteredReserveFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier) :
    CanonicalBulkControlFamily :=
  A.toCompiled.toCanonicalFamily

/-- The sharpened residual supplies the physical exponent lower bound at
every cutoff once paired with the honest theta carrier. -/
theorem BlockCompatibleP2PhysicalCenteredReserveFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCompiled.pGamma_ge_two k

/-- Exact identification of the fine selected spectrum with the fusion-mode
real on the same canonical family. -/
theorem BlockCompatibleP2PhysicalCenteredReserveFrontier.finePin
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  A.toCompiled.finePin mode k

/-- Exact image identification under a genuine blocking map on the same
canonical trajectory. -/
theorem BlockCompatibleP2PhysicalCenteredReserveFrontier.imagePin
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  A.toCompiled.imagePin mode B k

/-- Exact quotient defect-power law on the genuine selected mode-one
trajectory supplied by the centered-reserve refinement. -/
theorem BlockCompatibleP2PhysicalCenteredReserveFrontier.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne) B.Φ
      (A.toCompiled.modeOneTailMonotonicity.toQuotientData
        A.toCompiled.coefficient (B := B) |>.toCrossMul.factor) :=
  A.toCompiled.blockDefectPowerOnTrajectory

/-- The same checked quotient data retain the uniform one-half factor-loss
bound after the centered coefficient refinement. -/
theorem BlockCompatibleP2PhysicalCenteredReserveFrontier.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalCenteredReserveFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toCompiled.modeOneTailMonotonicity.toQuotientData
          A.toCompiled.coefficient (B := B) |>.toCrossMul.factor k) <=
      YMGap.Constructive.HalfPow.half :=
  A.toCompiled.factorLossLeHalf k

end YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.toCompiled
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.toCanonicalFamily
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.pGamma_ge_two
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.finePin
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.imagePin
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2HalfTimeCenteredPhysicalFrontier.BlockCompatibleP2PhysicalCenteredReserveFrontier.factorLossLeHalf
