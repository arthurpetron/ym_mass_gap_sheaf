/-
Track 11.7-fusion / R4b -- exact physical `k=7` trapezoid exchange.

The remaining trapezoid head is a comparison of two products of 639-term
theta sums.  Direct rational normalization is needlessly expensive and hides
the small physical margin.  This module instead uses the existing binary
fixed-point power intervals and 32-term blocked-sum compiler:

* `blockWeight 7` is represented exactly in the same fixed-point scale as the
  already-certified `blockWeight 8` base;
* outward coefficient intervals bound the two adjacent sums and the two
  trapezoid norms in the directions needed by the cross product;
* four generated natural numerators and one final integer comparison certify
  the sign.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
import YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange

namespace YMGap.Continuum.P2BlockCompatibleThetaTrapezoidSevenFixedPoint

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaDriftCross
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
open YMGap.Continuum.P2BlockCompatibleThetaTrapezoidExchange
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

/-- `blockWeight 7 = 786428/786432`, represented in the fixed-point scale
already used for the `k=8` fine-reserve tables. -/
def trapezoidSevenLowBase : Nat := 786428000000000000

theorem trapezoidSevenLowBase_eqv_weight :
    fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowBase ≈ blockWeight 7 := by
  have hscaled :
      fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowBase ≈
        Q'.mkPos 196607 196608 (by decide) := by
    show (fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowBase).num *
          ((Q'.mkPos 196607 196608 (by decide)).den : Int) =
      (Q'.mkPos 196607 196608 (by decide)).num *
        ((fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowBase).den : Int)
    rw [fixedPointVal_num, fixedPointVal_den, Q'.mkPos_num, Q'.mkPos_den]
    unfold fineSevenScale trapezoidSevenLowBase
    decide
  have hweight : blockWeight 7 ≈
      Q'.mkPos 196607 196608 (by decide) := by
    unfold blockWeight blockMargin SpectralLocalizationCrux.q112 blockQuarter
    decide
  exact Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm hweight)

theorem trapezoidSevenLowFloorPow_le (exponent : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (floorPow fineSevenScale trapezoidSevenLowBase exponent) <=
      qpow (blockWeight 7) exponent := by
  exact floorPow_le_qpow fineSevenScale fineSevenScale_pos
    trapezoidSevenLowBase (blockWeight 7) (blockWeight_nonneg 7)
    (Q'.le_of_eqv trapezoidSevenLowBase_eqv_weight) exponent

theorem trapezoidSevenLowPow_le_ceil (exponent : Nat) :
    qpow (blockWeight 7) exponent <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (ceilPow fineSevenScale trapezoidSevenLowBase exponent) := by
  exact qpow_le_ceilPow fineSevenScale fineSevenScale_pos
    trapezoidSevenLowBase (blockWeight 7) (blockWeight_nonneg 7)
    (Q'.ge_of_eqv trapezoidSevenLowBase_eqv_weight) exponent

def trapezoidSevenLowCoeff (s : Nat) : Q' :=
  Q'.ofNat (s + 1) * qpow (blockWeight 7) (c4 s)

def trapezoidSevenLowCoeffLower (s : Nat) : Nat :=
  (s + 1) * floorPow fineSevenScale trapezoidSevenLowBase (c4 s)

def trapezoidSevenLowCoeffUpper (s : Nat) : Nat :=
  (s + 1) * ceilPow fineSevenScale trapezoidSevenLowBase (c4 s)

theorem trapezoidSevenLowCoeff_nonneg (s : Nat) :
    (0 : Q') <= trapezoidSevenLowCoeff s := by
  unfold trapezoidSevenLowCoeff
  exact Q'.mul_nonneg _ _ (dimQ_nonneg s)
    (qpow_nonneg (blockWeight 7) (blockWeight_nonneg 7) _)

theorem trapezoidSevenLowCoeffLower_le (s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (trapezoidSevenLowCoeffLower s) <= trapezoidSevenLowCoeff s := by
  have hp := trapezoidSevenLowFloorPow_le (c4 s)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (s + 1)) hp
    (dimQ_nonneg s)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_natMul_eqv fineSevenScale fineSevenScale_pos
        (s + 1) (floorPow fineSevenScale trapezoidSevenLowBase (c4 s))))
    hmul

theorem trapezoidSevenLowCoeff_le_upper (s : Nat) :
    trapezoidSevenLowCoeff s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (trapezoidSevenLowCoeffUpper s) := by
  have hp := trapezoidSevenLowPow_le_ceil (c4 s)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (s + 1)) hp
    (dimQ_nonneg s)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.ge_of_eqv
      (fixedPointVal_natMul_eqv fineSevenScale fineSevenScale_pos
        (s + 1) (ceilPow fineSevenScale trapezoidSevenLowBase (c4 s))))

theorem trapezoidSevenLowCoeff_eqv (s : Nat) :
    trapezoidSevenLowCoeff s ≈ coeffW (blockWeight 7) s := by
  unfold trapezoidSevenLowCoeff coeffW dimQ
  exact Q'.eqv_refl _

/-- Adjacent product and trapezoid norm for an arbitrary coefficient row. -/
def coefficientAdj (coeff : Nat -> Q') (N : Nat) : Q' :=
  fsum (fun s => coeff s * coeff (s + 1)) N

def coefficientTrapezoidNorm (coeff : Nat -> Q') (N : Nat) : Q' :=
  (fsum (fun s => coeff s * coeff s) N + coeff N * coeff N) +
    fsum (fun s => coeff s * coeff s) N

theorem coefficientAdj_eqv
    (coeff : Nat -> Q') (w : Q')
    (hcoeff : forall s, coeff s ≈ coeffW w s) (N : Nat) :
    coefficientAdj coeff N ≈ adjCorr w N := by
  unfold coefficientAdj adjCorr
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.eqv_trans _ (coeffW w s * coeff (s + 1)) _
      (Q'.mul_eqv_congr_right _ _ _ (hcoeff s))
      (Q'.mul_eqv_congr_left _ _ _ (hcoeff (s + 1)))) N

theorem coefficientTrapezoidNorm_eqv
    (coeff : Nat -> Q') (w : Q')
    (hcoeff : forall s, coeff s ≈ coeffW w s) (N : Nat) :
    coefficientTrapezoidNorm coeff N ≈
      fixedCutoffTrapezoidNorm w N := by
  unfold coefficientTrapezoidNorm fixedCutoffTrapezoidNorm
    coordNormSq fixedCutoffDiagPrefix fixedCutoffDiagTerm
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.add_eqv_congr' ?_ ?_
    · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
        Q'.eqv_trans _ (coeffW w s * coeff s) _
          (Q'.mul_eqv_congr_right _ _ _ (hcoeff s))
          (Q'.mul_eqv_congr_left _ _ _ (hcoeff s))) N
    · exact Q'.eqv_trans _ (coeffW w N * coeff N) _
        (Q'.mul_eqv_congr_right _ _ _ (hcoeff N))
        (Q'.mul_eqv_congr_left _ _ _ (hcoeff N))
  · exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
      Q'.eqv_trans _ (coeffW w s * coeff s) _
        (Q'.mul_eqv_congr_right _ _ _ (hcoeff s))
        (Q'.mul_eqv_congr_left _ _ _ (hcoeff s))) N

def trapezoidSevenLowAdjUpperTerm (s : Nat) : Nat :=
  ceilMul fineSevenScale (trapezoidSevenLowCoeffUpper s)
    (trapezoidSevenLowCoeffUpper (s + 1))

def trapezoidSevenHighAdjLowerTerm (s : Nat) : Nat :=
  floorMul fineSevenScale (fineSevenCoeffLower 4 s)
    (fineSevenCoeffLower 4 (s + 1))

def trapezoidSevenLowMassLowerTerm (s : Nat) : Nat :=
  floorMul fineSevenScale (trapezoidSevenLowCoeffLower s)
    (trapezoidSevenLowCoeffLower s)

theorem trapezoidSevenLowAdj_le_upperTerm (s : Nat) :
    trapezoidSevenLowCoeff s * trapezoidSevenLowCoeff (s + 1) <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (trapezoidSevenLowAdjUpperTerm s) := by
  have hs := trapezoidSevenLowCoeff_le_upper s
  have ht := trapezoidSevenLowCoeff_le_upper (s + 1)
  have hmul := Q'.mul_le_mul_of_nonneg hs ht
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _)
    (trapezoidSevenLowCoeff_nonneg (s + 1))
  exact Q'.le_trans' _ _ _ hmul
    (ceilMul_sound fineSevenScale fineSevenScale_pos _ _)

theorem trapezoidSevenHighAdjLowerTerm_le (s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (trapezoidSevenHighAdjLowerTerm s) <=
      fineSevenCoeff 4 s * fineSevenCoeff 4 (s + 1) := by
  have hfloor := floorMul_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower 4 s) (fineSevenCoeffLower 4 (s + 1))
  have hs := fineSevenCoeffLower_le 4 s
  have ht := fineSevenCoeffLower_le 4 (s + 1)
  have hmul := Q'.mul_le_mul_of_nonneg hs ht
    (fineSevenCoeff_nonneg 4 s)
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _)
  exact Q'.le_trans' _ _ _ hfloor hmul

theorem trapezoidSevenLowMassLowerTerm_le (s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (trapezoidSevenLowMassLowerTerm s) <=
      trapezoidSevenLowCoeff s * trapezoidSevenLowCoeff s := by
  have hfloor := floorMul_sound fineSevenScale fineSevenScale_pos
    (trapezoidSevenLowCoeffLower s) (trapezoidSevenLowCoeffLower s)
  have hs := trapezoidSevenLowCoeffLower_le s
  have hmul := Q'.mul_le_mul_of_nonneg hs hs
    (trapezoidSevenLowCoeff_nonneg s)
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _)
  exact Q'.le_trans' _ _ _ hfloor hmul

def trapezoidSevenLowAdjUpperNum : Nat :=
  natBlockedSum trapezoidSevenLowAdjUpperTerm 32 19 31

def trapezoidSevenHighAdjLowerNum : Nat :=
  natBlockedSum trapezoidSevenHighAdjLowerTerm 32 19 31

def trapezoidSevenLowMassLowerNum : Nat :=
  natBlockedSum trapezoidSevenLowMassLowerTerm 32 19 31

def trapezoidSevenLowNormLowerNum : Nat :=
  trapezoidSevenLowMassLowerNum + trapezoidSevenLowMassLowerTerm 639 +
    trapezoidSevenLowMassLowerNum

def trapezoidSevenHighNormUpperNum : Nat :=
  fineSevenMassUpperBlockedNum 4 19 31 + fineSevenMassUpperTerm 4 639 +
    fineSevenMassUpperBlockedNum 4 19 31

def trapezoidSevenLowAdjUpperWitness : Nat :=
  10315341635047949146132453

def trapezoidSevenHighAdjLowerWitness : Nat :=
  10315368099349233375092900

def trapezoidSevenLowNormLowerWitness : Nat :=
  20630832217324667249238991

def trapezoidSevenHighNormUpperWitness : Nat :=
  20630885146029342435378479

theorem trapezoidSevenLowAdjUpper_generated :
    trapezoidSevenLowAdjUpperNum =
      trapezoidSevenLowAdjUpperWitness := by decide

theorem trapezoidSevenHighAdjLower_generated :
    trapezoidSevenHighAdjLowerNum =
      trapezoidSevenHighAdjLowerWitness := by decide

theorem trapezoidSevenLowNormLower_generated :
    trapezoidSevenLowNormLowerNum =
      trapezoidSevenLowNormLowerWitness := by decide

theorem trapezoidSevenHighNormUpper_generated :
    trapezoidSevenHighNormUpperNum =
      trapezoidSevenHighNormUpperWitness := by decide

theorem trapezoidSevenLowAdj_le_witness :
    adjCorr (blockWeight 7) 639 <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowAdjUpperWitness := by
  have hsum : coefficientAdj trapezoidSevenLowCoeff 639 <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowAdjUpperNum := by
    unfold coefficientAdj trapezoidSevenLowAdjUpperNum
    exact Q'.le_trans' _ _ _
      (Q'.ge_of_eqv
        (qBlockedSum_eqv_fsum
          (fun s => trapezoidSevenLowCoeff s *
            trapezoidSevenLowCoeff (s + 1)) 32 19 31))
      (qBlockedSum_le_fixedPointVal _ _
        trapezoidSevenLowAdj_le_upperTerm 32 19 31)
  have hactual : adjCorr (blockWeight 7) 639 <=
      coefficientAdj trapezoidSevenLowCoeff 639 :=
    Q'.le_of_eqv
      (Q'.eqv_symm
        (coefficientAdj_eqv trapezoidSevenLowCoeff (blockWeight 7)
          trapezoidSevenLowCoeff_eqv 639))
  rw [trapezoidSevenLowAdjUpper_generated] at hsum
  exact Q'.le_trans' _ _ _ hactual hsum

theorem trapezoidSevenHighAdj_witness_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighAdjLowerWitness <=
      adjCorr (qpow (blockWeight 8) 4) 639 := by
  have hsum : fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighAdjLowerNum <=
      coefficientAdj (fineSevenCoeff 4) 639 := by
    unfold coefficientAdj trapezoidSevenHighAdjLowerNum
    exact Q'.le_trans' _ _ _
      (fixedPointVal_natBlockedSum_le _ _
        trapezoidSevenHighAdjLowerTerm_le 32 19 31)
      (Q'.le_of_eqv
        (qBlockedSum_eqv_fsum
          (fun s => fineSevenCoeff 4 s * fineSevenCoeff 4 (s + 1))
          32 19 31))
  have hactual : coefficientAdj (fineSevenCoeff 4) 639 <=
      adjCorr (qpow (blockWeight 8) 4) 639 :=
    Q'.le_of_eqv
      (coefficientAdj_eqv (fineSevenCoeff 4)
        (qpow (blockWeight 8) 4) fineSevenCoeff_four_eqv 639)
  rw [trapezoidSevenHighAdjLower_generated] at hsum
  exact Q'.le_trans' _ _ _ hsum hactual

theorem trapezoidSevenLowNorm_witness_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowNormLowerWitness <=
      fixedCutoffTrapezoidNorm (blockWeight 7) 639 := by
  have hprefix : fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowMassLowerNum <=
      fsum (fun s => trapezoidSevenLowCoeff s *
        trapezoidSevenLowCoeff s) 639 := by
    unfold trapezoidSevenLowMassLowerNum
    exact Q'.le_trans' _ _ _
      (fixedPointVal_natBlockedSum_le _ _
        trapezoidSevenLowMassLowerTerm_le 32 19 31)
      (Q'.le_of_eqv
        (qBlockedSum_eqv_fsum
          (fun s => trapezoidSevenLowCoeff s *
            trapezoidSevenLowCoeff s) 32 19 31))
  have hterminal := trapezoidSevenLowMassLowerTerm_le 639
  have hsum : fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowNormLowerNum <=
      coefficientTrapezoidNorm trapezoidSevenLowCoeff 639 := by
    unfold trapezoidSevenLowNormLowerNum coefficientTrapezoidNorm
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          (fixedPointVal fineSevenScale fineSevenScale_pos
              (trapezoidSevenLowMassLowerNum +
                trapezoidSevenLowMassLowerTerm 639) +
            fixedPointVal fineSevenScale fineSevenScale_pos
              trapezoidSevenLowMassLowerNum) _
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _)
          (Q'.add_eqv_congr_right _ _ _
            (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))))
      (Q'.add_le_add (Q'.add_le_add hprefix hterminal) hprefix)
  have hactual : coefficientTrapezoidNorm trapezoidSevenLowCoeff 639 <=
      fixedCutoffTrapezoidNorm (blockWeight 7) 639 :=
    Q'.le_of_eqv
      (coefficientTrapezoidNorm_eqv trapezoidSevenLowCoeff (blockWeight 7)
        trapezoidSevenLowCoeff_eqv 639)
  rw [trapezoidSevenLowNormLower_generated] at hsum
  exact Q'.le_trans' _ _ _ hsum hactual

theorem trapezoidSevenHighNorm_le_witness :
    fixedCutoffTrapezoidNorm (qpow (blockWeight 8) 4) 639 <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighNormUpperWitness := by
  have hprefix : fineSevenMass 4 639 <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperBlockedNum 4 19 31) :=
    fineSevenMass_le_upperBlocked_at 4 19 31 639 (by decide)
  have hterminal := fineSevenMass_le_upperTerm 4 639
  have hprefix' :
      fsum (fun s => fineSevenCoeff 4 s * fineSevenCoeff 4 s) 639 <=
        fixedPointVal fineSevenScale fineSevenScale_pos
          (fineSevenMassUpperBlockedNum 4 19 31) := by
    simpa only [fineSevenMass] using hprefix
  have hsum : coefficientTrapezoidNorm (fineSevenCoeff 4) 639 <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighNormUpperNum := by
    unfold coefficientTrapezoidNorm trapezoidSevenHighNormUpperNum
    exact Q'.le_trans' _ _ _
      (Q'.add_le_add (Q'.add_le_add hprefix' hterminal) hprefix')
      (Q'.ge_of_eqv
        (Q'.eqv_trans _
          (fixedPointVal fineSevenScale fineSevenScale_pos
              (fineSevenMassUpperBlockedNum 4 19 31 +
                fineSevenMassUpperTerm 4 639) +
            fixedPointVal fineSevenScale fineSevenScale_pos
              (fineSevenMassUpperBlockedNum 4 19 31)) _
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _)
          (Q'.add_eqv_congr_right _ _ _
            (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))))
  have hactual : fixedCutoffTrapezoidNorm (qpow (blockWeight 8) 4) 639 <=
      coefficientTrapezoidNorm (fineSevenCoeff 4) 639 :=
    Q'.le_of_eqv
      (Q'.eqv_symm
        (coefficientTrapezoidNorm_eqv (fineSevenCoeff 4)
          (qpow (blockWeight 8) 4) fineSevenCoeff_four_eqv 639))
  rw [trapezoidSevenHighNormUpper_generated] at hsum
  exact Q'.le_trans' _ _ _ hactual hsum

/-- The single small integer comparison left after the four interval bounds. -/
theorem trapezoidSevenWitnessCross :
    fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowAdjUpperWitness *
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighNormUpperWitness <=
    fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenHighAdjLowerWitness *
      fixedPointVal fineSevenScale fineSevenScale_pos
        trapezoidSevenLowNormLowerWitness := by
  show (fixedPointVal fineSevenScale fineSevenScale_pos
      trapezoidSevenLowAdjUpperWitness *
        fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenHighNormUpperWitness).num *
      ((fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenHighAdjLowerWitness *
        fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowNormLowerWitness).den : Int) <=
    (fixedPointVal fineSevenScale fineSevenScale_pos
      trapezoidSevenHighAdjLowerWitness *
        fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowNormLowerWitness).num *
      ((fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowAdjUpperWitness *
        fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenHighNormUpperWitness).den : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast,
    fixedPointVal_num, fixedPointVal_den]
  unfold trapezoidSevenLowAdjUpperWitness
    trapezoidSevenHighNormUpperWitness
    trapezoidSevenHighAdjLowerWitness trapezoidSevenLowNormLowerWitness
  decide

private theorem sub_nonpos_of_le_local {a b : Q'} (h : a <= b) :
    a + -b <= (0 : Q') := by
  have hadd := Q'.add_le_add_right a b (-b) h
  exact Q'.le_trans' _ _ _ hadd
    (Q'.le_of_eqv (Q'.add_neg_self_eqv b))

private theorem trapezoidNorm_nonneg_local
    {w : Q'} (hw : (0 : Q') <= w) (N : Nat) :
    (0 : Q') <= fixedCutoffTrapezoidNorm w N := by
  unfold fixedCutoffTrapezoidNorm fixedCutoffDiagPrefix
  exact Q'.zero_le_add _ _ (coordNormSq_nonneg hw N)
    (fsum_nonneg (fun s => Q'.mul_nonneg _ _
      (coeffW_nonneg hw s) (coeffW_nonneg hw s)) N)

/-- Exact physical first cell of the remaining trapezoid-exchange family. -/
theorem blockTrapezoidExchange_seven :
    let w0 := blockWeight 7
    let w4 := qpow (blockWeight (7 + 1)) 4
    fixedCutoffTrapezoidCross w0 w4 (blockNcut 7) <= (0 : Q') := by
  dsimp only
  rw [show blockNcut 7 = 639 by decide]
  have hhigh0 : (0 : Q') <= qpow (blockWeight 8) 4 :=
    qpow_nonneg (blockWeight 8) (blockWeight_nonneg 8) 4
  have hleft :
      adjCorr (blockWeight 7) 639 *
          fixedCutoffTrapezoidNorm (qpow (blockWeight 8) 4) 639 <=
        fixedPointVal fineSevenScale fineSevenScale_pos
            trapezoidSevenLowAdjUpperWitness *
          fixedPointVal fineSevenScale fineSevenScale_pos
            trapezoidSevenHighNormUpperWitness := by
    exact Q'.mul_le_mul_of_nonneg trapezoidSevenLowAdj_le_witness
      trapezoidSevenHighNorm_le_witness
      (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _)
      (trapezoidNorm_nonneg_local hhigh0 639)
  have hright :
      fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenHighAdjLowerWitness *
        fixedPointVal fineSevenScale fineSevenScale_pos
          trapezoidSevenLowNormLowerWitness <=
      adjCorr (qpow (blockWeight 8) 4) 639 *
        fixedCutoffTrapezoidNorm (blockWeight 7) 639 := by
    exact Q'.mul_le_mul_of_nonneg trapezoidSevenHighAdj_witness_le
      trapezoidSevenLowNorm_witness_le
      (adjCorr_nonneg hhigh0 639)
      (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _)
  have hcross :
      adjCorr (blockWeight 7) 639 *
          fixedCutoffTrapezoidNorm (qpow (blockWeight 8) 4) 639 <=
        adjCorr (qpow (blockWeight 8) 4) 639 *
          fixedCutoffTrapezoidNorm (blockWeight 7) 639 :=
    Q'.le_trans' _ _ _ hleft
      (Q'.le_trans' _ _ _ trapezoidSevenWitnessCross hright)
  unfold fixedCutoffTrapezoidCross
  exact sub_nonpos_of_le_local hcross

#print axioms trapezoidSevenLowBase_eqv_weight
#print axioms trapezoidSevenLowAdjUpper_generated
#print axioms trapezoidSevenHighAdjLower_generated
#print axioms trapezoidSevenLowNormLower_generated
#print axioms trapezoidSevenHighNormUpper_generated
#print axioms trapezoidSevenWitnessCross
#print axioms blockTrapezoidExchange_seven

end YMGap.Continuum.P2BlockCompatibleThetaTrapezoidSevenFixedPoint
