/-
Track 11.7-fusion / R4ag -- splice the complete first physical cutoff into
the endpoint-aware parity compiler.

`P2HalfTimeScaleFourComplete` proves every supported half-time cell at
`k = 4`.  Consequently the residual transition family need only begin at
`k = 5`.  This module performs that dependent splice, transports the complete
scale-four row through the exact A1 reindex, and lands in the same common
physical carrier used by the reviewed canonical spectrum and genuine
`BlockingStep.Phi` trajectory.

The `k >= 5` off-cover transition family and the post-radial theta tail remain
honest open inputs.  No frontier bundle is inhabited here.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2HalfTimeScaleFourComplete

namespace YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CanonicalFusionSpectrumFamily
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatiblePhysicalCompiledFrontier
open YMGap.Continuum.P2BlockCompatiblePhysicalFrontierStrictFromEight
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2HalfTimeEndpointSplicedParityCompiler
open YMGap.Continuum.P2HalfTimeParityStrandCompiler
open YMGap.Continuum.P2HalfTimeScaleFourComplete
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact A1 transport of the complete scale-four row -/

/-- The complete `k = 4` coefficient row in exact lag-correlation coordinates. -/
def physicalScaleFourLineSumTail :
    P2HalfTimeLineSumTailRatio (blockNcut 4) (blockWeight 4) where
  tail := fun s hs hsN => by
    have hcoeff := physical_halfTime_scaleFour s hs hsN
    have hBondSucc :
        bondMovedCoeff (blockNcut 4) (blockWeight 4) 2 (s + 1) ≈
          lineSum (lagCorr (blockWeight 4) (blockNcut 4)) (s + 1) :=
      Q'.eqv_trans _ _ _
        (bondMovedCoeff_eq_boxSum (blockNcut 4) (s + 1))
        (boxSum_eq_lineSum_lagCorr
          (blockWeight 4) (blockNcut 4) (s + 1))
    have hBond :
        bondMovedCoeff (blockNcut 4) (blockWeight 4) 2 s ≈
          lineSum (lagCorr (blockWeight 4) (blockNcut 4)) s :=
      Q'.eqv_trans _ _ _
        (bondMovedCoeff_eq_boxSum (blockNcut 4) s)
        (boxSum_eq_lineSum_lagCorr (blockWeight 4) (blockNcut 4) s)
    have eleft :
        dimQ s * lineSum
            (lagCorr (blockWeight 4) (blockNcut 4)) (s + 1) ≈
          dimQ s * bondMovedCoeff
            (blockNcut 4) (blockWeight 4) 2 (s + 1) :=
      Q'.mul_eqv_congr_left _ _ _ (Q'.eqv_symm hBondSucc)
    have einner :
        dimQ (s + 1) * bondMovedCoeff
            (blockNcut 4) (blockWeight 4) 2 s ≈
          dimQ (s + 1) *
            lineSum (lagCorr (blockWeight 4) (blockNcut 4)) s :=
      Q'.mul_eqv_congr_left _ _ _ hBond
    have eright :
        qpow (blockWeight 4) (s + 2) *
            (dimQ (s + 1) * bondMovedCoeff
              (blockNcut 4) (blockWeight 4) 2 s) ≈
          qpow (blockWeight 4) (s + 2) *
            (dimQ (s + 1) *
              lineSum (lagCorr (blockWeight 4) (blockNcut 4)) s) :=
      Q'.mul_eqv_congr_left _ _ _ einner
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hcoeff (Q'.le_of_eqv eright))

/-! ## 2. Residual transition family beginning at scale five -/

/-- After the complete direct row at `k = 4`, transition atoms are requested
only at later cutoffs and only outside the exact endpoint cover. -/
structure BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive : Type where
  odd : forall k m, 5 <= k -> 2 * m + 3 < 2 * blockNcut k ->
    ¬ physicalEndpointCoverAt k (2 * m + 3) ->
    physicalHalfTimeBoxOddTransitionAt k m
  even : forall k m, 5 <= k -> 1 <= m -> 2 * m < 2 * blockNcut k ->
    ¬ physicalEndpointCoverAt k (2 * m) ->
    physicalHalfTimeBoxEvenTransitionAt k m

private def lineSumTailAt_of_offCoverTransitionsFromFive
    (T : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive)
    (k : Nat) (hk : 5 <= k) :
    P2HalfTimeLineSumTailRatio (blockNcut k) (blockWeight k) where
  tail := fun s hs hsN => by
    let A : AlternatingTailOutside
        (boxTailLeft (blockNcut k) (blockWeight k))
        (halfTimeBoxRight (blockNcut k) (blockWeight k))
        (physicalEndpointCoverAt k) (blockNcut k) := {
      head := physical_halfTime_box_head_from_four k (by omega)
      direct := fun t ht htN hcover =>
        physical_halfTime_box_of_endpointCoverAt
          k t (by omega) ht htN hcover
      oddStep := fun m hm houtside =>
        halfTimeBox_oddStep_of_core (blockWeight_nonneg k) m
          (physicalHalfTimeBoxOddTransitionAt_sound k m
            (T.odd k m hk hm houtside))
      evenBridge := fun m hm1 hm houtside =>
        halfTimeBox_evenBridge_of_core (blockWeight_nonneg k) m hm1
          (physicalHalfTimeBoxEvenTransitionAt_sound k m
            (T.even k m hk hm1 hm houtside))
    }
    have hbox := tail_of_alternating_outside
      (fun t ht => boxTailLeft_pos (blockWeight_pos k) t ht) A s hs hsN
    have eleft :
        dimQ s * lineSum
            (lagCorr (blockWeight k) (blockNcut k)) (s + 1) ≈
          boxTailLeft (blockNcut k) (blockWeight k) s := by
      unfold boxTailLeft
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm
          (boxSum_eq_lineSum_lagCorr
            (blockWeight k) (blockNcut k) (s + 1)))
    have ebase :
        boxTailBase (blockNcut k) (blockWeight k) s ≈
          dimQ (s + 1) *
            lineSum (lagCorr (blockWeight k) (blockNcut k)) s := by
      unfold boxTailBase
      exact Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr
          (blockWeight k) (blockNcut k) s)
    have eright :
        halfTimeBoxRight (blockNcut k) (blockWeight k) s ≈
          qpow (blockWeight k) (s + 2) *
            (dimQ (s + 1) *
              lineSum (lagCorr (blockWeight k) (blockNcut k)) s) := by
      unfold halfTimeBoxRight
      exact Q'.mul_eqv_congr_left _ _ _ ebase
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))

/-- Dependent scale splice: use the checked direct row at `k = 4`, and the
endpoint-aware alternating compiler with residual transitions for `k >= 5`. -/
def BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive.toLineSumTail
    (T : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk => by
    by_cases h4 : k = 4
    · subst k
      exact physicalScaleFourLineSumTail
    · exact lineSumTailAt_of_offCoverTransitionsFromFive T k (by omega)

def BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive.toCoeffTailData
    (T : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive) :
    BlockCompatibleP2CoeffTailData :=
  (BlockCompatibleP2HalfTimeCoeffTailFromFour.mk fun k hk =>
    ((T.toLineSumTail).tail k hk).toCoeff).toAllScale

/-! ## 3. Coarsening to the genuine physical spectrum and trajectory -/

structure BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier : Type where
  coefficient : BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive
  theta : BlockCompatibleP2PostRadialTailStrictFromEight

def BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.toCompiled
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier) :
    BlockCompatibleP2PhysicalCompiledFrontier where
  coefficient := A.coefficient.toCoeffTailData
  theta := A.theta

def BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.toCanonicalFamily
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier) :
    CanonicalBulkControlFamily :=
  A.toCompiled.toCanonicalFamily

theorem BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.pGamma_ge_two
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier) (k : Nat) :
    2 <= A.toCanonicalFamily.pGamma k :=
  A.toCompiled.pGamma_ge_two k

theorem BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.finePin
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier)
    (mode : Nat -> Nat) (k : Nat) :
    CReal.Equiv
      (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control (k + 1)) (mode (k + 1))) :=
  A.toCompiled.finePin mode k

theorem BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.imagePin
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier)
    (mode : Nat -> Nat)
    (B : BlockingStep (canonicalFusionSeparator A.toCanonicalFamily mode))
    (k : Nat) :
    CReal.Equiv
      (B.Φ (canonicalFusionSeparator A.toCanonicalFamily mode (k + 1)))
      (FusionSpectrumBlockingIdentification.fusionModeCReal
        (A.toCanonicalFamily.control k) (mode k)) :=
  A.toCompiled.imagePin mode B k

/-- Exact quotient defect-power law on the genuine selected mode-one
trajectory after discharging the complete `k = 4` coefficient row. -/
theorem BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.blockDefectPowerOnTrajectory
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne) B.Φ
      (A.toCompiled.modeOneTailMonotonicity.toQuotientData
        A.toCompiled.coefficient (B := B) |>.toCrossMul.factor) :=
  A.toCompiled.blockDefectPowerOnTrajectory

theorem BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.factorLossLeHalf
    (A : BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier)
    {B : BlockingStep
      (fusionSeparator A.toCompiled.coefficient.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (A.toCompiled.modeOneTailMonotonicity.toQuotientData
          A.toCompiled.coefficient (B := B) |>.toCrossMul.factor k) <=
      YMGap.Constructive.HalfPow.half :=
  A.toCompiled.factorLossLeHalf k

end YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.physicalScaleFourLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive.toLineSumTail
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2HalfTimeOffCoverTransitionsFromFive.toCoeffTailData
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.toCompiled
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.pGamma_ge_two
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.finePin
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.imagePin
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.blockDefectPowerOnTrajectory
#print axioms YMGap.Continuum.P2HalfTimeScaleFourSplicedParityCompiler.BlockCompatibleP2PhysicalScaleFourSplicedParityFrontier.factorLossLeHalf
