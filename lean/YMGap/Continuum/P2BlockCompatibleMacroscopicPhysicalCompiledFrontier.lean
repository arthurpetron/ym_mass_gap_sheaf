/-
Track 11.7-fusion / R4ac -- macroscopic physical reserve consumer.

`P2HalfTimeMacroscopicEndpointDescent` proves complete half-time cells on the
linearly growing endpoint band

    5 * (m + 1) <= N_k + 1,    s = 2*N_k - m.

This module installs that theorem in the real compiled physical carrier.  The
remaining coefficient field asks for exact full-local numerator signs only
outside the band (and only away from the already-proved head).  Unlike the old
fixed ten-shell splice, the theorem-provided region grows at every cutoff.

The coarsening lands in the existing common physical carrier, so its
`CanonicalBulkControl`, `finePin`, `imagePin`, and genuine `BlockingStep.Phi`
statements refer to exactly the same fusion spectrum and trajectory.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier
import YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent

namespace YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2HalfTimeMacroscopicEndpointDescent
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeShiftTail
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.RGTransport

/-! ## 1. The reduced exact-numerator frontier -/

/-- Residual coefficient signs after removing the physical head and the whole
macroscopic endpoint band.  The negated band guard is a pure-Nat condition;
there is no shell table and no fixed depth. -/
structure BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour : Type where
  nonneg : forall k s, 4 <= k -> 2 <= s -> s < 2 * blockNcut k ->
    ¬ (5 * (2 * blockNcut k - s + 1) <= blockNcut k + 1) ->
    physicalFullLocalReserveAt k (blockNcut k) s

/-- Splice the proved head and the growing endpoint band into a full physical
half-time line-sum family. -/
def BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour.toLineSumTail
    (T : BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => {
    tail := fun s hs hsN => by
      by_cases h2 : 2 <= s
      · let N := blockNcut k
        let m := 2 * N - s
        by_cases hband : 5 * (m + 1) <= N + 1
        · have hm : 0 < m := by
            dsimp only [m, N]
            omega
          have hline := physical_halfTime_lineSum_fifth_depth_from_four
            k m hk hm (by simpa only [N] using hband)
          simpa only [N, m,
            show 2 * blockNcut k - (2 * blockNcut k - s) = s by omega,
            show 2 * blockNcut k - (2 * blockNcut k - s) + 1 = s + 1 by
              omega,
            show 2 * blockNcut k - (2 * blockNcut k - s) + 2 = s + 2 by
              omega] using hline
        · exact physicalFullLocalReserveAt_lineSum k (blockNcut k) s
            (T.nonneg k s hk h2 hsN (by simpa only [N, m] using hband))
      · have hs1 : s = 1 := by omega
        subst s
        exact physical_halfTime_lineSum_head_from_four k hk
  }

def BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour.toCoeffTailData
    (T : BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-! ## 2. Coarsening to the genuine physical spectrum and Phi trajectory -/

structure BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier : Type where
  coefficient : BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

def BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier) :
    CanonicalBulkControlFamily :=
  A.toCompiled.toCanonicalFamily

theorem BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCompiled.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.finePin
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  A.toCompiled.finePin mode k

theorem BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.imagePin
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  A.toCompiled.imagePin mode B k

/-- The reduced macroscopic carrier reaches the exact quotient defect-power
law on the genuine selected mode-one trajectory. -/
theorem BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne) B.Φ
      (A.toCompiled.modeOneTailMonotonicity.toQuotientData
        A.toCompiled.coefficient (B := B) |>.toCrossMul.factor) :=
  A.toCompiled.blockDefectPowerOnTrajectory

/-- The same reduced carrier retains the physical half-loss estimate used by
the downstream blocking argument. -/
theorem BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toCompiled.modeOneTailMonotonicity.toQuotientData
          A.toCompiled.coefficient (B := B) |>.toCrossMul.factor k) <=
      YMGap.Constructive.HalfPow.half :=
  A.toCompiled.factorLossLeHalf k

end YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour.toLineSumTail
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2FullLocalNumeratorMacroscopicInteriorFromFour.toCoeffTailData
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.toCompiled
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.pGamma_ge_two
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.finePin
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.imagePin
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2BlockCompatibleMacroscopicPhysicalCompiledFrontier.BlockCompatibleP2PhysicalMacroscopicInteriorReserveFrontier.factorLossLeHalf
