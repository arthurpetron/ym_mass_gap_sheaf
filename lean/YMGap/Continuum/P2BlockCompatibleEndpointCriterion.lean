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
import YMGap.Continuum.SpectralMarginBridge

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
open YMGap.Continuum.SpectralMarginBridge
open YMGap.Continuum.VacNormEigShift

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.mul_num_cast, Q'.mul_den_cast, Int.mul_one];
             ac_rfl))

private theorem divPos_eqv_divPos_of_cross {p q p' q' : Q'}
    (hq : (0 : Q') < q) (hq' : (0 : Q') < q')
    (hcross : p * q' ≈ p' * q) :
    Q'.divPos p q hq ≈ Q'.divPos p' q' hq' := by
  let c := Q'.divPos p' q' hq'
  have hright : (c * q) * q' ≈ p' * q := by
    refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv c q q') ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left c _ _ (Q'.mul_comm_eqv q q')) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv c q' q)) ?_
    exact Q'.mul_eqv_congr_right _ _ q (Q'.divPos_mul_eqv p' q' hq')
  have hmul : p * q' ≈ (c * q) * q' :=
    Q'.eqv_trans _ _ _ hcross (Q'.eqv_symm hright)
  have hcancel : p ≈ c * q := by
    apply Q'.mul_left_cancel_of_pos hq'
    refine Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv q' p) ?_
    refine Q'.eqv_trans _ _ _ hmul ?_
    exact Q'.mul_comm_eqv (c * q) q'
  exact divPos_eqv_of_eqv_mul hq hcancel

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

/-! ## Exact endpoint reserve -/

/-- Common positive denominator for the endpoint square at `N -> 2N+1`. -/
def endpointBlockCommonDen (N : Nat) : Q' :=
  let M := 2 * N + 1
  let D := Q'.ofNat (2 * M + 3)
  let d := Q'.ofNat (2 * N + 3)
  (D * D) * d

theorem endpointBlockCommonDen_pos (N : Nat) :
    (0 : Q') < endpointBlockCommonDen N := by
  dsimp only [endpointBlockCommonDen]
  exact Q'.mul_pos
    (Q'.mul_pos (endpointDen_pos (2 * N + 1))
      (endpointDen_pos (2 * N + 1)))
    (endpointDen_pos N)

/-- Closed endpoint reserve
`6(N+2)/((4N+5)^2(2N+3))`. -/
def endpointBlockSlack (N : Nat) : Q' :=
  Q'.divPos
    (Q'.ofNat 6 * (Q'.ofNat N + Q'.ofNat 2))
    (endpointBlockCommonDen N) (endpointBlockCommonDen_pos N)

/-- The endpoint square is the coarse endpoint plus the exact positive
reserve. -/
theorem endpointRate_add_endpointBlockSlack_eqv (N : Nat) :
    endpointRate N + endpointBlockSlack N ≈
      endpointRate (2 * N + 1) * endpointRate (2 * N + 1) := by
  let M := 2 * N + 1
  let a := Q'.ofNat (2 * N)
  let d := Q'.ofNat (2 * N + 3)
  let A := Q'.ofNat (2 * M)
  let D := Q'.ofNat (2 * M + 3)
  let den := (D * D) * d
  let coarseNum := a * (D * D)
  let fineNum := (A * A) * d
  let slackNum := Q'.ofNat 6 * (Q'.ofNat N + Q'.ofNat 2)
  have hd : (0 : Q') < d := by
    unfold d
    exact endpointDen_pos N
  have hD : (0 : Q') < D := by
    unfold D M
    exact endpointDen_pos (2 * N + 1)
  have hD2 : (0 : Q') < D * D := Q'.mul_pos hD hD
  have hden : (0 : Q') < den := Q'.mul_pos hD2 hd
  have hcoarse : endpointRate N ≈
      Q'.divPos coarseNum den hden := by
    unfold endpointRate
    apply divPos_eqv_divPos_of_cross (endpointDen_pos N) hden
    dsimp only [coarseNum, den, a, d, D]
    ring_qeqv
  have hsquare : Q'.divPos (A * A) (D * D) hD2 ≈
      endpointRate M * endpointRate M := by
    simpa only [endpointRate, A, D] using
      (P2BlockCompatibleSchedule.divPos_square_eqv A D hD)
  have hcommon : Q'.divPos (A * A) (D * D) hD2 ≈
      Q'.divPos fineNum den hden := by
    apply divPos_eqv_divPos_of_cross hD2 hden
    dsimp only [fineNum, den, A, D, d]
    ring_qeqv
  have hfine : endpointRate M * endpointRate M ≈
      Q'.divPos fineNum den hden :=
    Q'.eqv_trans _ _ _ (Q'.eqv_symm hsquare) hcommon
  have hslack : endpointBlockSlack N ≈
      Q'.divPos slackNum den hden := by
    rfl
  have hadd := Q'.add_eqv_congr' hcoarse hslack
  have hsame := add_divPos_eqv coarseNum slackNum den hden
  have hgap : fineNum ≈ coarseNum + slackNum := by
    simpa only [M, a, d, A, D, coarseNum, fineNum, slackNum] using
      (endpointBlockCrossGap_eqv N)
  have hnum : coarseNum + slackNum ≈ fineNum := Q'.eqv_symm hgap
  have hquot :
      Q'.divPos (coarseNum + slackNum) den hden ≈
        Q'.divPos fineNum den hden := by
    apply divPos_eqv_divPos_of_cross hden hden
    exact Q'.mul_eqv_congr_right _ _ den hnum
  exact Q'.eqv_trans _ _ _ hadd
    (Q'.eqv_trans _ _ _ hsame
      (Q'.eqv_trans _ _ _ hquot (Q'.eqv_symm hfine)))

/-- The normalized-amplitude tail reduced to an explicit scalar inequality.
No fusion convolution or rational quotient occurs in this data. -/
structure BlockCompatibleP2EndpointMonotonicityTail : Type where
  budget : forall k, 2 <= k ->
    endpointRate (blockNcut k) +
        (blockEndpointError k +
          Q'.ofNat 2 * blockEndpointError (k + 1)) <=
      endpointRate (blockNcut (k + 1)) *
        endpointRate (blockNcut (k + 1))

/-- Preferred scalar residual: the two continuity errors fit inside the exact
closed endpoint reserve. -/
structure BlockCompatibleP2EndpointReserveTail : Type where
  errorsLeSlack : forall k, 2 <= k ->
    blockEndpointError k + Q'.ofNat 2 * blockEndpointError (k + 1) <=
      endpointBlockSlack (blockNcut k)

/-- The exact endpoint identity compiles the reserve form to the budget form. -/
def BlockCompatibleP2EndpointReserveTail.toEndpointMonotonicityTail
    (R : BlockCompatibleP2EndpointReserveTail) :
    BlockCompatibleP2EndpointMonotonicityTail where
  budget := fun k hk => by
    have hadd := Q'.add_le_add_left
      (endpointRate (blockNcut k)) _ _ (R.errorsLeSlack k hk)
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (by
        simpa only [blockNcut_succ] using
          (endpointRate_add_endpointBlockSlack_eqv (blockNcut k))))

/-! ## The crude endpoint modulus is provably too large -/

private def qOneThirtySecond : Q' := Q'.mkPos 1 32 (by decide)

/-- Already at `k=2`, the unnormalized finite-character Lipschitz modulus is
larger than the exact endpoint reserve.  Thus the reserve compiler above is a
valid sufficient implication, but its premise cannot be the final physical
route.  A normalized cancellation estimate or a direct quotient comparison
is necessary. -/
theorem no_BlockCompatibleP2EndpointReserveTail :
    BlockCompatibleP2EndpointReserveTail -> False := by
  intro R
  have hv : Q'.ofNat 6 <= vacLip (blockNcut 2) :=
    vacLip_ge_six (by decide)
  have hscaled :
      Q'.ofNat 6 * blockMargin 2 <= blockEndpointError 2 := by
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hv (blockMargin_nonneg 2)
  have hquarter : qOneThirtySecond <= blockEndpointError 2 :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv (by decide :
      qOneThirtySecond ≈ Q'.ofNat 6 * blockMargin 2)) hscaled
  have herrFine : (0 : Q') <= Q'.ofNat 2 * blockEndpointError 3 :=
    Q'.mul_nonneg _ _ (by decide)
      (Q'.mul_nonneg _ _ (vacLip_nonneg _) (blockMargin_nonneg _))
  have herr : blockEndpointError 2 <=
      blockEndpointError 2 + Q'.ofNat 2 * blockEndpointError 3 :=
    Q'.add_le_self_of_nonneg _ _ herrFine
  have hle : qOneThirtySecond <= endpointBlockSlack (blockNcut 2) :=
    Q'.le_trans' _ _ _ hquarter
      (Q'.le_trans' _ _ _ herr (R.errorsLeSlack 2 (by decide)))
  have hlt : endpointBlockSlack (blockNcut 2) < qOneThirtySecond := by
    decide
  exact (by decide : Not (qOneThirtySecond < qOneThirtySecond))
    (Q'.lt_of_le_of_lt hle hlt)

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
#print axioms endpointRate_add_endpointBlockSlack_eqv
#print axioms BlockCompatibleP2EndpointReserveTail.toEndpointMonotonicityTail
#print axioms no_BlockCompatibleP2EndpointReserveTail
#print axioms BlockCompatibleP2EndpointMonotonicityTail.toModeOneTailMonotonicity
#print axioms BlockCompatibleP2EndpointMonotonicityTail.blockDefectPowerOnTrajectory
#print axioms BlockCompatibleP2EndpointMonotonicityTail.factorLossLeHalf

end YMGap.Continuum.P2BlockCompatibleEndpointCriterion
