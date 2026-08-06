/-
Track 11.7-fusion / R4l -- common compiled physical frontier and the exact
half-time-reserve refinement.

The coefficient campaign has two sound sufficient routes: the original
heat-matched parity transitions and the exact half-time line-reserve.  They
must not create two physical Yang--Mills objects.  This module coarsens both
routes to one common carrier consisting of

  * the already reviewed all-scale `BlockCompatibleP2CoeffTailData`, and
  * the same post-radial theta tail beginning at `k = 8`.

All spectrum, `finePin`, `imagePin`, and genuine `BlockingStep.Phi` defect-
power statements are proved once on that common carrier.  The exact full
local-reserve numerator family then maps into it, so replacing the refuted
fixed-`w` strong-Turan premise does not fork the physical trajectory.

This is an honest refinement/compiler.  The all-scale reserve signs and the
theta tail remain named open inputs; no frontier bundle or Yang--Mills target
is inhabited here.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatiblePhysicalFrontierRepointed
import YMGap.Continuum.P2HalfTimeParityStrandCompiler
import YMGap.Continuum.P2HalfTimeShiftTail
import YMGap.Continuum.P2HalfTimeSixthShell
import YMGap.Continuum.P2HalfTimeFifthShell
import YMGap.Continuum.P2HalfTimeFourthShell
import YMGap.Continuum.P2HalfTimeAntepenultimateShell
import YMGap.Continuum.P2HalfTimePenultimateShell
import YMGap.Continuum.P2HalfTimeTerminalShell

namespace YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierRepointed
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.P2HalfTimeSixthShell
open YMGap.Continuum.P2HalfTimeFifthShell
open YMGap.Continuum.P2HalfTimeFourthShell
open YMGap.Continuum.P2HalfTimeAntepenultimateShell
open YMGap.Continuum.P2HalfTimePenultimateShell
open YMGap.Continuum.P2HalfTimeTerminalShell
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.RGTransport

/-! ## 1. One common compiled physical carrier -/

/-- The common physical boundary after coefficient proofs have been compiled
to the reviewed all-scale coefficient data.  It contains no choice of proof
route and therefore pins every downstream theorem to the same spectrum. -/
structure BlockCompatibleP2PhysicalCompiledFrontier : Type where
  coefficient : BlockCompatibleP2CoeffTailData
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

/-- The previously reviewed odd/even parity frontier coarsens to the common
compiled carrier without changing either physical input. -/
def BlockCompatibleP2PhysicalFrontierRepointed.toCompiled
    (A : BlockCompatibleP2PhysicalFrontierRepointed) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coeffTailData
  theta := A.theta

def BlockCompatibleP2PhysicalCompiledFrontier.modeOneTailMonotonicity
    (A : BlockCompatibleP2PhysicalCompiledFrontier) :
    BlockCompatibleP2ModeOneTailMonotonicity :=
  A.theta.toPostRadialTailFromEight.toCoefficientSandwich
    |>.toAllScale.toThetaPathEnergySandwich
    |>.toPathEnergyTransport.toEnergyTransport
    |>.toDyadicParityTransport
    |>.toThetaDeficitHalfContraction.toThetaDeficitTail
    |>.toThetaCrossTail.toModeOneCrossTail
    |>.toModeOneTailMonotonicity

/-- The common carrier constructs the reviewed all-cutoff `pGamma = 2`
canonical family. -/
def BlockCompatibleP2PhysicalCompiledFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalCompiledFrontier) :
    CanonicalBulkControlFamily :=
  CanonicalBulkControlFamily.ofP2Retuned A.coefficient.toControlFamily

theorem BlockCompatibleP2PhysicalCompiledFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalCompiledFrontier) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCanonicalFamily.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalCompiledFrontier.finePin
    (A : BlockCompatibleP2PhysicalCompiledFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  canonicalFusionSeparator_finePin A.toCanonicalFamily mode k

theorem BlockCompatibleP2PhysicalCompiledFrontier.imagePin
    (A : BlockCompatibleP2PhysicalCompiledFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  canonicalFusionSeparator_imagePin A.toCanonicalFamily mode B k

/-- The exact same compiled coefficient data enters the genuine quotient
defect power on the selected mode-one trajectory. -/
theorem BlockCompatibleP2PhysicalCompiledFrontier.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalCompiledFrontier)
    {B : BlockingStep
      (fusionSeparator A.coefficient.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.coefficient.toControlFamily modeOne) B.Φ
      (A.modeOneTailMonotonicity.toQuotientData A.coefficient (B := B)
        |>.toCrossMul.factor) :=
  A.modeOneTailMonotonicity.blockDefectPowerOnTrajectory A.coefficient

theorem BlockCompatibleP2PhysicalCompiledFrontier.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalCompiledFrontier)
    {B : BlockingStep
      (fusionSeparator A.coefficient.toControlFamily modeOne)} (k : Nat) :
    (1 : Q') -
        (A.modeOneTailMonotonicity.toQuotientData A.coefficient (B := B)
          |>.toCrossMul.factor k) <=
      YMGap.Constructive.HalfPow.half :=
  A.modeOneTailMonotonicity.factorLossLeHalf A.coefficient k

/-! ## 2. Exact full-local-reserve refinement -/

/-- Compile the exact one-integer-sign-per-channel reserve family to the same
all-scale coefficient data used by the parity route. -/
def BlockCompatibleP2FullLocalNumeratorFromFour.toCoeffTailData
    (T : BlockCompatibleP2FullLocalNumeratorFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    (((T.toLocal).toLineSumTail).tail k hk).toCoeff).toAllScale

/-- Residual proof-about-computation boundary after removing the physical
mode-one head at every scale.  Only channels `s >= 2` remain: the four early
heads and the entire symbolic `k >= 8` head family are kernel theorems. -/
structure BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour : Type where
  nonneg : forall k s, 4 <= k -> 2 <= s -> s < 2 * blockNcut k ->
    physicalFullLocalReserveAt k (blockNcut k) s

/-- Splice the checked physical head into the residual integer-sign family.
Every later channel is reconstructed pointwise from its exact numerator,
without evaluating a growing rational convolution in Lean. -/
def BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour.toLineSumTail
    (T : BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => {
    tail := fun s hs hsN => by
      by_cases h2 : 2 <= s
      · exact physicalFullLocalReserveAt_lineSum k (blockNcut k) s
          (T.nonneg k s hk h2 hsN)
      · have hs1 : s = 1 := by omega
        subst s
        exact physical_halfTime_lineSum_head_from_four k hk
  }

/-- Compile the strictly smaller residual family to the same reviewed
all-scale coefficient data. -/
def BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour.toCoeffTailData
    (T : BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-- Boundary-reduced reserve interface.  The physical head `s=1` and the
top six shells `s=2*N-6, ..., 2*N-1` are theorems, so only the deeper
interior channels remain as integer signs. -/
structure BlockCompatibleP2FullLocalNumeratorInteriorFromFour : Type where
  nonneg : forall k s, 4 <= k -> 2 <= s ->
    s + 6 < 2 * blockNcut k ->
    physicalFullLocalReserveAt k (blockNcut k) s

/-- Insert the seven proved boundary regions and reconstruct only the deeper
interior from the proof-about-computation signs. -/
def BlockCompatibleP2FullLocalNumeratorInteriorFromFour.toLineSumTail
    (T : BlockCompatibleP2FullLocalNumeratorInteriorFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => {
    tail := fun s hs hsN => by
      by_cases h2 : 2 <= s
      · by_cases hInterior : s + 6 < 2 * blockNcut k
        · exact physicalFullLocalReserveAt_lineSum k (blockNcut k) s
            (T.nonneg k s hk h2 hInterior)
        · by_cases hSixth : s + 5 < 2 * blockNcut k
          · have hsSixth : s = 2 * blockNcut k - 6 := by omega
            rw [hsSixth]
            simpa only [
              show (2 * blockNcut k - 6) + 1 = 2 * blockNcut k - 5 by
                have := blockNcut_pos k
                omega,
              show (2 * blockNcut k - 6) + 2 = 2 * blockNcut k - 4 by
                have := blockNcut_pos k
                omega] using
              physical_halfTime_lineSum_sixth_from_four k hk
          · by_cases hFifth : s + 4 < 2 * blockNcut k
            · have hsFifth : s = 2 * blockNcut k - 5 := by omega
              rw [hsFifth]
              simpa only [
                show (2 * blockNcut k - 5) + 1 = 2 * blockNcut k - 4 by
                  have := blockNcut_pos k
                  omega,
                show (2 * blockNcut k - 5) + 2 = 2 * blockNcut k - 3 by
                  have := blockNcut_pos k
                  omega] using
                physical_halfTime_lineSum_fifth_from_four k hk
            · by_cases hFourth : s + 3 < 2 * blockNcut k
              · have hsFourth : s = 2 * blockNcut k - 4 := by omega
                rw [hsFourth]
                simpa only [
                  show (2 * blockNcut k - 4) + 1 = 2 * blockNcut k - 3 by
                    have := blockNcut_pos k
                    omega,
                  show (2 * blockNcut k - 4) + 2 = 2 * blockNcut k - 2 by
                    have := blockNcut_pos k
                    omega] using
                  physical_halfTime_lineSum_fourth_from_four k hk
              · by_cases hAntepenultimate : s + 2 < 2 * blockNcut k
                · have hsAntepenultimate : s = 2 * blockNcut k - 3 := by omega
                  rw [hsAntepenultimate]
                  simpa only [
                  show (2 * blockNcut k - 3) + 1 = 2 * blockNcut k - 2 by
                    have := blockNcut_pos k
                    omega,
                  show (2 * blockNcut k - 3) + 2 = 2 * blockNcut k - 1 by
                    have := blockNcut_pos k
                    omega] using
                  physical_halfTime_lineSum_antepenultimate_from_four k hk
                · by_cases hPenultimate : s + 1 < 2 * blockNcut k
                  · have hsPenultimate : s = 2 * blockNcut k - 2 := by omega
                    rw [hsPenultimate]
                    simpa only [
                    show (2 * blockNcut k - 2) + 1 = 2 * blockNcut k - 1 by
                      have := blockNcut_pos k
                      omega,
                    show (2 * blockNcut k - 2) + 2 = 2 * blockNcut k by
                      have := blockNcut_pos k
                      omega] using
                    physical_halfTime_lineSum_penultimate_from_four k hk
                  · have hsTop : s = 2 * blockNcut k - 1 := by omega
                    rw [hsTop]
                    simpa only [
                      show (2 * blockNcut k - 1) + 1 = 2 * blockNcut k by
                        have := blockNcut_pos k
                        omega,
                      show (2 * blockNcut k - 1) + 2 = 2 * blockNcut k + 1 by
                        have := blockNcut_pos k
                        omega] using physical_halfTime_lineSum_terminal k
      · have hs1 : s = 1 := by omega
        subst s
        exact physical_halfTime_lineSum_head_from_four k hk
  }

def BlockCompatibleP2FullLocalNumeratorInteriorFromFour.toCoeffTailData
    (T : BlockCompatibleP2FullLocalNumeratorInteriorFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-- The live half-time-reserve frontier.  Its coefficient field is exactly
one integer numerator sign for every physical scale/channel, and its theta
field is definitionally the same post-radial tail as the reviewed route. -/
structure BlockCompatibleP2PhysicalHalfTimeReserveFrontier : Type where
  coefficient : BlockCompatibleP2FullLocalNumeratorFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

/-- Total coarsening into the common physical carrier.  In particular, this
proves that the reserve route uses the same canonical spectrum, pins, and
`BlockingStep.Phi` trajectory rather than a parallel surrogate. -/
def BlockCompatibleP2PhysicalHalfTimeReserveFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalHalfTimeReserveFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient :=
    BlockCompatibleP2FullLocalNumeratorFromFour.toCoeffTailData A.coefficient
  theta := A.theta

/-- Preferred live reserve frontier: no field remains for the already-proved
mode-one head. -/
structure BlockCompatibleP2PhysicalHalfTimeReserveAwayHeadFrontier : Type where
  coefficient : BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

/-- The residual reserve family reaches the identical compiled physical
carrier and therefore the identical spectrum, pins, and genuine `Phi`
defect-power theorem. -/
def BlockCompatibleP2PhysicalHalfTimeReserveAwayHeadFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalHalfTimeReserveAwayHeadFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

/-- Preferred live frontier after both coefficient-tail boundary channels
have been physically discharged. -/
structure BlockCompatibleP2PhysicalHalfTimeInteriorReserveFrontier : Type where
  coefficient : BlockCompatibleP2FullLocalNumeratorInteriorFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalHalfTimeInteriorReserveFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalHalfTimeInteriorReserveFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

end YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalFrontierRepointed.toCompiled
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalCompiledFrontier.toCanonicalFamily
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalCompiledFrontier.finePin
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalCompiledFrontier.imagePin
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalCompiledFrontier.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalCompiledFrontier.factorLossLeHalf
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorAwayHeadFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorInteriorFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorInteriorFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalHalfTimeReserveFrontier.toCompiled
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalHalfTimeReserveAwayHeadFrontier.toCompiled
#print axioms YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier.BlockCompatibleP2PhysicalHalfTimeInteriorReserveFrontier.toCompiled
