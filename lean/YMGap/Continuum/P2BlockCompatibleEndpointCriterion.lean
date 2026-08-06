/-
Track 11.7-fusion / R3c -- endpoint reduction of the replacement mode-one
tail.

The remaining normalized p=2 comparison is a quotient of finite character
sums.  The existing endpoint-continuity theorem replaces it by a scalar
budget involving only

    endpointRate(blockNcut k), vacLip(blockNcut k), blockMargin k.

The two expensive head cells remain discharged in
`P2BlockCompatibleScheduleCells`; this scalar carrier starts at `k = 2` and
compiles through the all-scale half-floor to the genuine `BlockingStep.Phi`
defect identity.  Proving the scalar budget is the next analytic task.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatiblePhysicalBridge
import YMGap.Continuum.P2DyadicFusionEndpointCriterion

namespace YMGap.Continuum.P2BlockCompatibleEndpointCriterion

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BlockingStepFrontier
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.EndpointCutoffTailClose
open YMGap.Continuum.EndpointCutoffTwoParameter
open YMGap.Continuum.FusionQuotientCollapse
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleCells
open YMGap.Continuum.P2DyadicFusionEndpointCriterion
open YMGap.Continuum.P2RetunedBlockingDictionary
open YMGap.Continuum.P2RetunedFusionDefectPower
open YMGap.Continuum.P2RetunedFusionPhysicalMode
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- Exact endpoint-continuity error on the replacement schedule. -/
def blockEndpointError (k : Nat) : Q' :=
  vacLip (blockNcut k) * blockMargin k

theorem blockRawModeOne_range (k : Nat) :
    ((0 : Q') <= blockRawModeOne k) /\
      (blockRawModeOne k <= (1 : Q')) := by
  have h0 := p2VacNorm_nonneg (blockNcut k)
    (blockWeight_nonneg k) (blockWeight_le_one k) 1
  have hret := p2VacNorm_one_le_retuned (blockNcut k)
    (blockWeight_nonneg k) (blockWeight_le_one k)
  have hret1 :
      qpow (p2RetunedWeight (blockWeight k)) (c4 1) <= (1 : Q') :=
    qpow_le_one
      (p2RetunedWeight_nonneg (blockWeight_nonneg k))
      (p2RetunedWeight_le_one (blockWeight_le_one k)) (c4 1)
  exact ⟨h0, Q'.le_trans' _ _ _ hret hret1⟩

/-- Specialization of finite-character endpoint continuity. -/
theorem blockRawModeOne_endpoint_error (k : Nat) :
    absQ (blockRawModeOne k + -(endpointRate (blockNcut k))) <=
      blockEndpointError k := by
  have h := vacNorm_fundamental_endpoint_continuity
    (blockWeight_nonneg k) (blockWeight_le_one k) (blockNcut k)
  have hmargin :
      vacLip (blockNcut k) * ((1 : Q') - blockWeight k) ≈
        blockEndpointError k :=
    Q'.mul_eqv_congr_left (vacLip (blockNcut k)) _ _
      (one_sub_blockWeight_eqv_margin k)
  exact Q'.le_trans' _ _ _ h (Q'.le_of_eqv hmargin)

/-- The normalized-amplitude tail reduced to an explicit scalar inequality.
No fusion convolution or rational quotient occurs in this data. -/
structure BlockCompatibleP2EndpointMonotonicityTail : Type where
  budget : forall k, 2 <= k ->
    endpointRate (blockNcut k) +
        (blockEndpointError k +
          Q'.ofNat 2 * blockEndpointError (k + 1)) <=
      endpointRate (blockNcut (k + 1)) *
        endpointRate (blockNcut (k + 1))

/-- The endpoint budget discharges the sole normalized mode-one tail used by
the physical bridge. -/
def BlockCompatibleP2EndpointMonotonicityTail.toModeOneTailMonotonicity
    (E : BlockCompatibleP2EndpointMonotonicityTail) :
    BlockCompatibleP2ModeOneTailMonotonicity where
  tail := fun k hk => by
    have hfine := blockRawModeOne_range (k + 1)
    have hrefFine := endpointRate_range (blockNcut (k + 1))
    have hsquare := coarse_le_fine_square_of_reference_budget
      hfine.1 hfine.2 hrefFine.1 hrefFine.2
      (blockRawModeOne_endpoint_error k)
      (blockRawModeOne_endpoint_error (k + 1)) (E.budget k hk)
    exact Q'.le_trans' _ _ _ hsquare
      (Q'.ge_of_eqv (P2DyadicFusionEndpointCriterion.qpow_two_eqv
        (blockRawModeOne (k + 1))))

/-- End-to-end endpoint-only input for the actual physical block map. -/
theorem BlockCompatibleP2EndpointMonotonicityTail.blockDefectPowerOnTrajectory
    (E : BlockCompatibleP2EndpointMonotonicityTail)
    (D : BlockCompatibleP2CoeffTailData)
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)} :
    IsBlockDefectPowerOnTrajectory 1
      (fusionSeparator D.toControlFamily modeOne) B.Φ
      ((E.toModeOneTailMonotonicity.toQuotientData D
        (B := B)).toCrossMul.factor) :=
  E.toModeOneTailMonotonicity.blockDefectPowerOnTrajectory D

/-- The endpoint-only route inherits the canonical half-loss window. -/
theorem BlockCompatibleP2EndpointMonotonicityTail.factorLossLeHalf
    (E : BlockCompatibleP2EndpointMonotonicityTail)
    (D : BlockCompatibleP2CoeffTailData)
    {B : BlockingStep (fusionSeparator D.toControlFamily modeOne)}
    (k : Nat) :
    (1 : Q') -
        (E.toModeOneTailMonotonicity.toQuotientData D
          (B := B)).toCrossMul.factor k <= HalfPow.half :=
  E.toModeOneTailMonotonicity.factorLossLeHalf D k

#print axioms blockRawModeOne_endpoint_error
#print axioms BlockCompatibleP2EndpointMonotonicityTail.toModeOneTailMonotonicity
#print axioms BlockCompatibleP2EndpointMonotonicityTail.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2EndpointMonotonicityTail.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatibleEndpointCriterion
