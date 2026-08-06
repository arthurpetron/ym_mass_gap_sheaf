/-
Track 11.7-fusion / R3x -- the physical `k=7` fine-reserve certificate.

The fine even/odd reserve is checked in its positive path-energy form.  A
single exact fixed-point base represents `blockWeight 8`; binary floor and
ceiling powers enclose every coefficient.  The interval-energy kernel then
encloses both the squared norm and the boundary-plus-Dirichlet energy without
expanding a difference of two nearly equal theta sums.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.FixedPointIntervalEnergy
import YMGap.Continuum.P2BlockCompatibleThetaTerminalTheta

namespace YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FixedPointIntervalEnergy
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.FusionPositivity
open YMGap.Continuum.FusionCoreStepRoundH
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

def fineSevenScale : Nat := 786432000000000000

def fineSevenBase : Nat := 786431000000000000

theorem fineSevenScale_pos : 0 < fineSevenScale := by decide

theorem fineSevenBase_eqv_weight :
    fixedPointVal fineSevenScale fineSevenScale_pos fineSevenBase ≈
      blockWeight 8 := by
  have hscaled :
      fixedPointVal fineSevenScale fineSevenScale_pos fineSevenBase ≈
        Q'.mkPos 786431 786432 (by decide) := by
    show (fixedPointVal fineSevenScale fineSevenScale_pos fineSevenBase).num *
        ((Q'.mkPos 786431 786432 (by decide)).den : Int) =
      (Q'.mkPos 786431 786432 (by decide)).num *
        ((fixedPointVal fineSevenScale fineSevenScale_pos fineSevenBase).den : Int)
    rw [fixedPointVal_num, fixedPointVal_den, Q'.mkPos_num, Q'.mkPos_den]
    unfold fineSevenScale fineSevenBase
    decide
  have hweight : blockWeight 8 ≈
      Q'.mkPos 786431 786432 (by decide) := by
    unfold blockWeight blockMargin SpectralLocalizationCrux.q112 blockQuarter
    decide
  exact Q'.eqv_trans _ _ _ hscaled (Q'.eqv_symm hweight)

theorem fineSevenFloorPow_le (exponent : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (floorPow fineSevenScale fineSevenBase exponent) <=
      qpow (blockWeight 8) exponent := by
  exact floorPow_le_qpow fineSevenScale fineSevenScale_pos fineSevenBase
    (blockWeight 8) (blockWeight_nonneg 8)
    (Q'.le_of_eqv fineSevenBase_eqv_weight) exponent

theorem fineSevenPow_le_ceil (exponent : Nat) :
    qpow (blockWeight 8) exponent <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (ceilPow fineSevenScale fineSevenBase exponent) := by
  exact qpow_le_ceilPow fineSevenScale fineSevenScale_pos fineSevenBase
    (blockWeight 8) (blockWeight_nonneg 8)
    (Q'.ge_of_eqv fineSevenBase_eqv_weight) exponent

/-- The exact common-base coefficient for exponent multiplier `rate`. -/
def fineSevenCoeff (rate s : Nat) : Q' :=
  Q'.ofNat (s + 1) * qpow (blockWeight 8) (rate * c4 s)

def fineSevenCoeffLower (rate s : Nat) : Nat :=
  (s + 1) * floorPow fineSevenScale fineSevenBase (rate * c4 s)

def fineSevenCoeffUpper (rate s : Nat) : Nat :=
  (s + 1) * ceilPow fineSevenScale fineSevenBase (rate * c4 s)

theorem fineSevenCoeff_nonneg (rate s : Nat) :
    (0 : Q') <= fineSevenCoeff rate s := by
  unfold fineSevenCoeff
  exact Q'.mul_nonneg _ _ (dimQ_nonneg s)
    (qpow_nonneg (blockWeight 8) (blockWeight_nonneg 8) _)

theorem fineSevenCoeffLower_le (rate s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenCoeffLower rate s) <= fineSevenCoeff rate s := by
  have hp := fineSevenFloorPow_le (rate * c4 s)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (s + 1)) hp
    (dimQ_nonneg s)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_natMul_eqv fineSevenScale fineSevenScale_pos
        (s + 1) (floorPow fineSevenScale fineSevenBase (rate * c4 s))))
    hmul

theorem fineSevenCoeff_le_upper (rate s : Nat) :
    fineSevenCoeff rate s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenCoeffUpper rate s) := by
  have hp := fineSevenPow_le_ceil (rate * c4 s)
  have hmul := Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat (s + 1)) hp
    (dimQ_nonneg s)
  exact Q'.le_trans' _ _ _ hmul
    (Q'.ge_of_eqv
      (fixedPointVal_natMul_eqv fineSevenScale fineSevenScale_pos
        (s + 1) (ceilPow fineSevenScale fineSevenBase (rate * c4 s))))

def fineSevenMassLowerTerm (rate s : Nat) : Nat :=
  floorMul fineSevenScale (fineSevenCoeffLower rate s)
    (fineSevenCoeffLower rate s)

def fineSevenMassUpperTerm (rate s : Nat) : Nat :=
  ceilMul fineSevenScale (fineSevenCoeffUpper rate s)
    (fineSevenCoeffUpper rate s)

def fineSevenMassLowerNum (rate : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => fineSevenMassLowerNum rate n + fineSevenMassLowerTerm rate n

def fineSevenMassUpperNum (rate : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => fineSevenMassUpperNum rate n + fineSevenMassUpperTerm rate n

def fineSevenEdgeLowerTerm (rate s : Nat) : Nat :=
  let gap := intervalLowerGap
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
  floorMul fineSevenScale gap gap

def fineSevenEdgeUpperTerm (rate s : Nat) : Nat :=
  let gap := intervalUpperGap
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
  ceilMul fineSevenScale gap gap

def fineSevenEdgeLowerNum (rate : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => fineSevenEdgeLowerNum rate n + fineSevenEdgeLowerTerm rate n

def fineSevenEdgeUpperNum (rate : Nat) : Nat -> Nat
  | 0 => 0
  | n + 1 => fineSevenEdgeUpperNum rate n + fineSevenEdgeUpperTerm rate n

def fineSevenPathLowerNum (rate N : Nat) : Nat :=
  fineSevenMassLowerTerm rate 0 + fineSevenMassLowerTerm rate N +
    fineSevenEdgeLowerNum rate N

def fineSevenPathUpperNum (rate N : Nat) : Nat :=
  fineSevenMassUpperTerm rate 0 + fineSevenMassUpperTerm rate N +
    fineSevenEdgeUpperNum rate N

def fineSevenD1LowerWitness : Nat := 82532923972525583657992434
def fineSevenD1UpperWitness : Nat := 82532923972636621525084478
def fineSevenD4UpperWitness : Nat := 10317939662207656503538134
def fineSevenP1UpperWitness : Nat := 20274453954355112892688
def fineSevenP4LowerWitness : Nat := 5143125689043198422899

theorem fineSevenD1LowerGenerated :
    fineSevenMassLowerNum 1 1280 = fineSevenD1LowerWitness := by decide

theorem fineSevenD1UpperGenerated :
    fineSevenMassUpperNum 1 1280 = fineSevenD1UpperWitness := by decide

theorem fineSevenD4UpperGenerated :
    fineSevenMassUpperNum 4 640 = fineSevenD4UpperWitness := by decide

theorem fineSevenP1UpperGenerated :
    fineSevenPathUpperNum 1 1279 = fineSevenP1UpperWitness := by decide

theorem fineSevenP4LowerGenerated :
    fineSevenPathLowerNum 4 639 = fineSevenP4LowerWitness := by decide

def fineSevenMass (rate count : Nat) : Q' :=
  fsum (fun s => fineSevenCoeff rate s * fineSevenCoeff rate s) count

def fineSevenEdgeSquare (rate s : Nat) : Q' :=
  (fineSevenCoeff rate s + -fineSevenCoeff rate (s + 1)) *
    (fineSevenCoeff rate s + -fineSevenCoeff rate (s + 1))

def fineSevenPath (rate N : Nat) : Q' :=
  fineSevenCoeff rate 0 * fineSevenCoeff rate 0 +
    fineSevenCoeff rate N * fineSevenCoeff rate N +
      fsum (fineSevenEdgeSquare rate) N

/-! ## Bounded-depth block compiler

Specializing a linear proof at length 1,280 creates an unnecessarily deep
kernel term.  The following generic compiler groups terms into fixed-width
ranges.  Its specialization depth is `numberOfBlocks + blockWidth`, not the
total number of terms.
-/

def natRangeSum (term : Nat -> Nat) (start : Nat) : Nat -> Nat
  | 0 => 0
  | count + 1 => natRangeSum term start count + term (start + count)

def qRangeSum (term : Nat -> Q') (start count : Nat) : Q' :=
  fsum (fun i => term (start + i)) count

def natBlockSum (term : Nat -> Nat) (width : Nat) : Nat -> Nat
  | 0 => 0
  | blocks + 1 => natBlockSum term width blocks +
      natRangeSum term (blocks * width) width

def qBlockSum (term : Nat -> Q') (width : Nat) : Nat -> Q'
  | 0 => 0
  | blocks + 1 => qBlockSum term width blocks +
      qRangeSum term (blocks * width) width

def natBlockedSum (term : Nat -> Nat) (width blocks tail : Nat) : Nat :=
  natBlockSum term width blocks +
    natRangeSum term (blocks * width) tail

def qBlockedSum (term : Nat -> Q') (width blocks tail : Nat) : Q' :=
  qBlockSum term width blocks + qRangeSum term (blocks * width) tail

theorem fixedPointVal_natRangeSum_le
    (lower : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i,
      fixedPointVal fineSevenScale fineSevenScale_pos (lower i) <= exact i)
    (start : Nat) : forall count : Nat,
    fixedPointVal fineSevenScale fineSevenScale_pos
        (natRangeSum lower start count) <= qRangeSum exact start count
  | 0 => Q'.le_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change fixedPointVal fineSevenScale fineSevenScale_pos
          (natRangeSum lower start count + lower (start + count)) <=
        qRangeSum exact start count + exact (start + count)
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
        (Q'.add_le_add
          (fixedPointVal_natRangeSum_le lower exact hterm start count)
          (hterm (start + count)))

theorem qRangeSum_le_fixedPointVal
    (upper : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i, exact i <=
      fixedPointVal fineSevenScale fineSevenScale_pos (upper i))
    (start : Nat) : forall count : Nat,
    qRangeSum exact start count <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (natRangeSum upper start count)
  | 0 => Q'.ge_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change qRangeSum exact start count + exact (start + count) <=
        fixedPointVal fineSevenScale fineSevenScale_pos
          (natRangeSum upper start count + upper (start + count))
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add
          (qRangeSum_le_fixedPointVal upper exact hterm start count)
          (hterm (start + count)))
        (Q'.ge_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem fixedPointVal_natBlockSum_le
    (lower : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i,
      fixedPointVal fineSevenScale fineSevenScale_pos (lower i) <= exact i)
    (width : Nat) : forall blocks : Nat,
    fixedPointVal fineSevenScale fineSevenScale_pos
        (natBlockSum lower width blocks) <= qBlockSum exact width blocks
  | 0 => Q'.le_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | blocks + 1 => by
      change fixedPointVal fineSevenScale fineSevenScale_pos
          (natBlockSum lower width blocks +
            natRangeSum lower (blocks * width) width) <=
        qBlockSum exact width blocks + qRangeSum exact (blocks * width) width
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
        (Q'.add_le_add
          (fixedPointVal_natBlockSum_le lower exact hterm width blocks)
          (fixedPointVal_natRangeSum_le lower exact hterm
            (blocks * width) width))

theorem qBlockSum_le_fixedPointVal
    (upper : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i, exact i <=
      fixedPointVal fineSevenScale fineSevenScale_pos (upper i))
    (width : Nat) : forall blocks : Nat,
    qBlockSum exact width blocks <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (natBlockSum upper width blocks)
  | 0 => Q'.ge_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | blocks + 1 => by
      change qBlockSum exact width blocks +
          qRangeSum exact (blocks * width) width <=
        fixedPointVal fineSevenScale fineSevenScale_pos
          (natBlockSum upper width blocks +
            natRangeSum upper (blocks * width) width)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add
          (qBlockSum_le_fixedPointVal upper exact hterm width blocks)
          (qRangeSum_le_fixedPointVal upper exact hterm
            (blocks * width) width))
        (Q'.ge_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem fixedPointVal_natBlockedSum_le
    (lower : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i,
      fixedPointVal fineSevenScale fineSevenScale_pos (lower i) <= exact i)
    (width blocks tail : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (natBlockedSum lower width blocks tail) <=
      qBlockedSum exact width blocks tail := by
  unfold natBlockedSum qBlockedSum
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
    (Q'.add_le_add
      (fixedPointVal_natBlockSum_le lower exact hterm width blocks)
      (fixedPointVal_natRangeSum_le lower exact hterm
        (blocks * width) tail))

theorem qBlockedSum_le_fixedPointVal
    (upper : Nat -> Nat) (exact : Nat -> Q')
    (hterm : forall i, exact i <=
      fixedPointVal fineSevenScale fineSevenScale_pos (upper i))
    (width blocks tail : Nat) :
    qBlockedSum exact width blocks tail <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (natBlockedSum upper width blocks tail) := by
  unfold natBlockedSum qBlockedSum
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add
      (qBlockSum_le_fixedPointVal upper exact hterm width blocks)
      (qRangeSum_le_fixedPointVal upper exact hterm
        (blocks * width) tail))
    (Q'.ge_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem qBlockSum_eqv_fsum (term : Nat -> Q') (width : Nat) :
    forall blocks : Nat,
    qBlockSum term width blocks ≈ fsum term (blocks * width)
  | 0 => by
      simpa only [qBlockSum, Nat.zero_mul, fsum_zero] using
        (Q'.eqv_refl (0 : Q'))
  | blocks + 1 => by
      change qBlockSum term width blocks +
          qRangeSum term (blocks * width) width ≈
        fsum term ((blocks + 1) * width)
      have hcount : (blocks + 1) * width = blocks * width + width :=
        Nat.succ_mul blocks width
      rw [hcount]
      exact Q'.eqv_trans _
        (fsum term (blocks * width) +
          qRangeSum term (blocks * width) width) _
        (Q'.add_eqv_congr_right _ _ _
          (qBlockSum_eqv_fsum term width blocks))
        (Q'.eqv_symm
          (fsum_split_at term (blocks * width) width))

theorem qBlockedSum_eqv_fsum
    (term : Nat -> Q') (width blocks tail : Nat) :
    qBlockedSum term width blocks tail ≈
      fsum term (blocks * width + tail) := by
  unfold qBlockedSum
  exact Q'.eqv_trans _
    (fsum term (blocks * width) +
      qRangeSum term (blocks * width) tail) _
    (Q'.add_eqv_congr_right _ _ _
      (qBlockSum_eqv_fsum term width blocks))
    (Q'.eqv_symm (fsum_split_at term (blocks * width) tail))

private theorem fineSevenMassLowerTerm_le_block (rate s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerTerm rate s) <=
      fineSevenCoeff rate s * fineSevenCoeff rate s := by
  have hfloor := floorMul_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffLower rate s)
  have hterm := fineSevenCoeffLower_le rate s
  have hmul := Q'.mul_le_mul_of_nonneg hterm hterm
    (fineSevenCoeff_nonneg rate s)
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos
      (fineSevenCoeffLower rate s))
  exact Q'.le_trans' _ _ _ hfloor hmul

private theorem fineSevenMass_le_upperTerm_block (rate s : Nat) :
    fineSevenCoeff rate s * fineSevenCoeff rate s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperTerm rate s) := by
  have hterm := fineSevenCoeff_le_upper rate s
  have hmul := Q'.mul_le_mul_of_nonneg hterm hterm
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos
      (fineSevenCoeffUpper rate s))
    (fineSevenCoeff_nonneg rate s)
  have hceil := ceilMul_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffUpper rate s) (fineSevenCoeffUpper rate s)
  exact Q'.le_trans' _ _ _ hmul hceil

private theorem fineSevenEdgeLowerTerm_le_block (rate s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeLowerTerm rate s) <= fineSevenEdgeSquare rate s := by
  unfold fineSevenEdgeLowerTerm fineSevenEdgeSquare
  exact intervalLowerSquare_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
    (fineSevenCoeff rate s) (fineSevenCoeff rate (s + 1))
    (fineSevenCoeffLower_le rate s) (fineSevenCoeff_le_upper rate s)
    (fineSevenCoeffLower_le rate (s + 1))
    (fineSevenCoeff_le_upper rate (s + 1))

private theorem fineSevenEdge_le_upperTerm_block (rate s : Nat) :
    fineSevenEdgeSquare rate s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeUpperTerm rate s) := by
  unfold fineSevenEdgeUpperTerm fineSevenEdgeSquare
  exact intervalUpperSquare_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
    (fineSevenCoeff rate s) (fineSevenCoeff rate (s + 1))
    (fineSevenCoeffLower_le rate s) (fineSevenCoeff_le_upper rate s)
    (fineSevenCoeffLower_le rate (s + 1))
    (fineSevenCoeff_le_upper rate (s + 1))

def fineSevenMassLowerBlockedNum (rate blocks tail : Nat) : Nat :=
  natBlockedSum (fineSevenMassLowerTerm rate) 32 blocks tail

def fineSevenMassUpperBlockedNum (rate blocks tail : Nat) : Nat :=
  natBlockedSum (fineSevenMassUpperTerm rate) 32 blocks tail

def fineSevenEdgeLowerBlockedNum (rate blocks tail : Nat) : Nat :=
  natBlockedSum (fineSevenEdgeLowerTerm rate) 32 blocks tail

def fineSevenEdgeUpperBlockedNum (rate blocks tail : Nat) : Nat :=
  natBlockedSum (fineSevenEdgeUpperTerm rate) 32 blocks tail

def fineSevenPathLowerBlockedNum (rate blocks tail : Nat) : Nat :=
  let N := blocks * 32 + tail
  fineSevenMassLowerTerm rate 0 + fineSevenMassLowerTerm rate N +
    fineSevenEdgeLowerBlockedNum rate blocks tail

def fineSevenPathUpperBlockedNum (rate blocks tail : Nat) : Nat :=
  let N := blocks * 32 + tail
  fineSevenMassUpperTerm rate 0 + fineSevenMassUpperTerm rate N +
    fineSevenEdgeUpperBlockedNum rate blocks tail

theorem fineSevenMassLowerBlocked_le (rate blocks tail : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerBlockedNum rate blocks tail) <=
      fineSevenMass rate (blocks * 32 + tail) := by
  unfold fineSevenMassLowerBlockedNum fineSevenMass
  exact Q'.le_trans' _ _ _
    (fixedPointVal_natBlockedSum_le _ _
      (fineSevenMassLowerTerm_le_block rate) 32 blocks tail)
    (Q'.le_of_eqv
      (qBlockedSum_eqv_fsum _ 32 blocks tail))

theorem fineSevenMass_le_upperBlocked (rate blocks tail : Nat) :
    fineSevenMass rate (blocks * 32 + tail) <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperBlockedNum rate blocks tail) := by
  unfold fineSevenMassUpperBlockedNum fineSevenMass
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (qBlockedSum_eqv_fsum _ 32 blocks tail))
    (qBlockedSum_le_fixedPointVal _ _
      (fineSevenMass_le_upperTerm_block rate) 32 blocks tail)

theorem fineSevenEdgeLowerBlocked_le (rate blocks tail : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeLowerBlockedNum rate blocks tail) <=
      fsum (fineSevenEdgeSquare rate) (blocks * 32 + tail) := by
  unfold fineSevenEdgeLowerBlockedNum
  exact Q'.le_trans' _ _ _
    (fixedPointVal_natBlockedSum_le _ _
      (fineSevenEdgeLowerTerm_le_block rate) 32 blocks tail)
    (Q'.le_of_eqv (qBlockedSum_eqv_fsum _ 32 blocks tail))

theorem fineSevenEdge_le_upperBlocked (rate blocks tail : Nat) :
    fsum (fineSevenEdgeSquare rate) (blocks * 32 + tail) <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeUpperBlockedNum rate blocks tail) := by
  unfold fineSevenEdgeUpperBlockedNum
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (qBlockedSum_eqv_fsum _ 32 blocks tail))
    (qBlockedSum_le_fixedPointVal _ _
      (fineSevenEdge_le_upperTerm_block rate) 32 blocks tail)

theorem fineSevenPathLowerBlocked_le (rate blocks tail : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathLowerBlockedNum rate blocks tail) <=
      fineSevenPath rate (blocks * 32 + tail) := by
  unfold fineSevenPathLowerBlockedNum fineSevenPath
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _)) ?_
  refine Q'.add_le_add ?_ (fineSevenEdgeLowerBlocked_le rate blocks tail)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
    (Q'.add_le_add (fineSevenMassLowerTerm_le_block rate 0)
      (fineSevenMassLowerTerm_le_block rate (blocks * 32 + tail)))

theorem fineSevenPath_le_upperBlocked (rate blocks tail : Nat) :
    fineSevenPath rate (blocks * 32 + tail) <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathUpperBlockedNum rate blocks tail) := by
  unfold fineSevenPathUpperBlockedNum fineSevenPath
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add ?_ (fineSevenEdge_le_upperBlocked rate blocks tail))
    (Q'.ge_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (fineSevenMass_le_upperTerm_block rate 0)
      (fineSevenMass_le_upperTerm_block rate (blocks * 32 + tail)))
    (Q'.ge_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

/-- Opaque index transport: specialize this theorem instead of rewriting a
closed blocked table, which would make the rewriter traverse its body. -/
theorem fineSevenMassLowerBlocked_le_at
    (rate blocks tail count : Nat)
    (hcount : blocks * 32 + tail = count) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerBlockedNum rate blocks tail) <=
      fineSevenMass rate count := by
  subst count
  exact fineSevenMassLowerBlocked_le rate blocks tail

theorem fineSevenMass_le_upperBlocked_at
    (rate blocks tail count : Nat)
    (hcount : blocks * 32 + tail = count) :
    fineSevenMass rate count <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperBlockedNum rate blocks tail) := by
  subst count
  exact fineSevenMass_le_upperBlocked rate blocks tail

theorem fineSevenPathLowerBlocked_le_at
    (rate blocks tail N : Nat)
    (hN : blocks * 32 + tail = N) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathLowerBlockedNum rate blocks tail) <=
      fineSevenPath rate N := by
  subst N
  exact fineSevenPathLowerBlocked_le rate blocks tail

theorem fineSevenPath_le_upperBlocked_at
    (rate blocks tail N : Nat)
    (hN : blocks * 32 + tail = N) :
    fineSevenPath rate N <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathUpperBlockedNum rate blocks tail) := by
  subst N
  exact fineSevenPath_le_upperBlocked rate blocks tail

theorem fineSevenMassLowerBlocked_le_value_at
    (rate blocks tail count : Nat) (value : Q')
    (hcount : blocks * 32 + tail = count)
    (hvalue : value = fineSevenMass rate count) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerBlockedNum rate blocks tail) <= value := by
  subst value
  exact fineSevenMassLowerBlocked_le_at rate blocks tail count hcount

theorem fineSevenMass_value_le_upperBlocked_at
    (rate blocks tail count : Nat) (value : Q')
    (hcount : blocks * 32 + tail = count)
    (hvalue : value = fineSevenMass rate count) :
    value <= fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenMassUpperBlockedNum rate blocks tail) := by
  subst value
  exact fineSevenMass_le_upperBlocked_at rate blocks tail count hcount

theorem fineSevenPathLowerBlocked_le_value_at
    (rate blocks tail N : Nat) (value : Q')
    (hN : blocks * 32 + tail = N)
    (hvalue : value = fineSevenPath rate N) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathLowerBlockedNum rate blocks tail) <= value := by
  subst value
  exact fineSevenPathLowerBlocked_le_at rate blocks tail N hN

theorem fineSevenPath_value_le_upperBlocked_at
    (rate blocks tail N : Nat) (value : Q')
    (hN : blocks * 32 + tail = N)
    (hvalue : value = fineSevenPath rate N) :
    value <= fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenPathUpperBlockedNum rate blocks tail) := by
  subst value
  exact fineSevenPath_le_upperBlocked_at rate blocks tail N hN

theorem fineSevenD1LowerBlockedGenerated :
    fineSevenMassLowerBlockedNum 1 40 0 = fineSevenD1LowerWitness := by decide

theorem fineSevenD1UpperBlockedGenerated :
    fineSevenMassUpperBlockedNum 1 40 0 = fineSevenD1UpperWitness := by decide

theorem fineSevenD4UpperBlockedGenerated :
    fineSevenMassUpperBlockedNum 4 20 0 = fineSevenD4UpperWitness := by decide

theorem fineSevenP1UpperBlockedGenerated :
    fineSevenPathUpperBlockedNum 1 39 31 = fineSevenP1UpperWitness := by decide

theorem fineSevenP4LowerBlockedGenerated :
    fineSevenPathLowerBlockedNum 4 19 31 = fineSevenP4LowerWitness := by decide

theorem fineSevenMassLowerTerm_le (rate s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerTerm rate s) <=
      fineSevenCoeff rate s * fineSevenCoeff rate s := by
  have hfloor := floorMul_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffLower rate s)
  have hterm := fineSevenCoeffLower_le rate s
  have hmul := Q'.mul_le_mul_of_nonneg hterm hterm
    (fineSevenCoeff_nonneg rate s)
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos
      (fineSevenCoeffLower rate s))
  exact Q'.le_trans' _ _ _ hfloor hmul

theorem fineSevenMass_le_upperTerm (rate s : Nat) :
    fineSevenCoeff rate s * fineSevenCoeff rate s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperTerm rate s) := by
  have hterm := fineSevenCoeff_le_upper rate s
  have hmul := Q'.mul_le_mul_of_nonneg hterm hterm
    (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos
      (fineSevenCoeffUpper rate s))
    (fineSevenCoeff_nonneg rate s)
  have hceil := ceilMul_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffUpper rate s) (fineSevenCoeffUpper rate s)
  exact Q'.le_trans' _ _ _ hmul hceil

theorem fineSevenMassLowerNum_le (rate : Nat) : forall count : Nat,
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerNum rate count) <= fineSevenMass rate count
  | 0 => by
      unfold fineSevenMass
      exact Q'.le_of_eqv
        (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change fixedPointVal fineSevenScale fineSevenScale_pos
          (fineSevenMassLowerNum rate count +
            fineSevenMassLowerTerm rate count) <=
        fineSevenMass rate count +
          fineSevenCoeff rate count * fineSevenCoeff rate count
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
        (Q'.add_le_add (fineSevenMassLowerNum_le rate count)
          (fineSevenMassLowerTerm_le rate count))

theorem fineSevenMass_le_upperNum (rate : Nat) : forall count : Nat,
    fineSevenMass rate count <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperNum rate count)
  | 0 => by
      unfold fineSevenMass
      exact Q'.ge_of_eqv
        (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change fineSevenMass rate count +
          fineSevenCoeff rate count * fineSevenCoeff rate count <=
        fixedPointVal fineSevenScale fineSevenScale_pos
          (fineSevenMassUpperNum rate count +
            fineSevenMassUpperTerm rate count)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add (fineSevenMass_le_upperNum rate count)
          (fineSevenMass_le_upperTerm rate count))
        (Q'.ge_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem fineSevenEdgeLowerTerm_le (rate s : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeLowerTerm rate s) <= fineSevenEdgeSquare rate s := by
  unfold fineSevenEdgeLowerTerm fineSevenEdgeSquare
  exact intervalLowerSquare_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
    (fineSevenCoeff rate s) (fineSevenCoeff rate (s + 1))
    (fineSevenCoeffLower_le rate s) (fineSevenCoeff_le_upper rate s)
    (fineSevenCoeffLower_le rate (s + 1))
    (fineSevenCoeff_le_upper rate (s + 1))

theorem fineSevenEdge_le_upperTerm (rate s : Nat) :
    fineSevenEdgeSquare rate s <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeUpperTerm rate s) := by
  unfold fineSevenEdgeUpperTerm fineSevenEdgeSquare
  exact intervalUpperSquare_sound fineSevenScale fineSevenScale_pos
    (fineSevenCoeffLower rate s) (fineSevenCoeffUpper rate s)
    (fineSevenCoeffLower rate (s + 1)) (fineSevenCoeffUpper rate (s + 1))
    (fineSevenCoeff rate s) (fineSevenCoeff rate (s + 1))
    (fineSevenCoeffLower_le rate s) (fineSevenCoeff_le_upper rate s)
    (fineSevenCoeffLower_le rate (s + 1))
    (fineSevenCoeff_le_upper rate (s + 1))

theorem fineSevenEdgeLowerNum_le (rate : Nat) : forall count : Nat,
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeLowerNum rate count) <=
      fsum (fineSevenEdgeSquare rate) count
  | 0 => Q'.le_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change fixedPointVal fineSevenScale fineSevenScale_pos
          (fineSevenEdgeLowerNum rate count +
            fineSevenEdgeLowerTerm rate count) <=
        fsum (fineSevenEdgeSquare rate) count +
          fineSevenEdgeSquare rate count
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
        (Q'.add_le_add (fineSevenEdgeLowerNum_le rate count)
          (fineSevenEdgeLowerTerm_le rate count))

theorem fineSevenEdge_le_upperNum (rate : Nat) : forall count : Nat,
    fsum (fineSevenEdgeSquare rate) count <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenEdgeUpperNum rate count)
  | 0 => Q'.ge_of_eqv
      (fixedPointVal_zero_eqv fineSevenScale fineSevenScale_pos)
  | count + 1 => by
      change fsum (fineSevenEdgeSquare rate) count +
          fineSevenEdgeSquare rate count <=
        fixedPointVal fineSevenScale fineSevenScale_pos
          (fineSevenEdgeUpperNum rate count +
            fineSevenEdgeUpperTerm rate count)
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add (fineSevenEdge_le_upperNum rate count)
          (fineSevenEdge_le_upperTerm rate count))
        (Q'.ge_of_eqv
          (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem fineSevenPathLowerNum_le (rate N : Nat) :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathLowerNum rate N) <= fineSevenPath rate N := by
  unfold fineSevenPathLowerNum fineSevenPath
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _)) ?_
  refine Q'.add_le_add ?_ (fineSevenEdgeLowerNum_le rate N)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
    (Q'.add_le_add (fineSevenMassLowerTerm_le rate 0)
      (fineSevenMassLowerTerm_le rate N))

theorem fineSevenPath_le_upperNum (rate N : Nat) :
    fineSevenPath rate N <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathUpperNum rate N) := by
  unfold fineSevenPathUpperNum fineSevenPath
  refine Q'.le_trans' _ _ _
    (Q'.add_le_add ?_ (fineSevenEdge_le_upperNum rate N))
    (Q'.ge_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add (fineSevenMass_le_upperTerm rate 0)
      (fineSevenMass_le_upperTerm rate N))
    (Q'.ge_of_eqv
      (fixedPointVal_add_eqv fineSevenScale fineSevenScale_pos _ _))

theorem fineSevenCoeff_one_eqv (s : Nat) :
    fineSevenCoeff 1 s ≈ coeffW (blockWeight 8) s := by
  unfold fineSevenCoeff coeffW dimQ
  rw [Nat.one_mul]
  exact Q'.eqv_refl _

theorem fineSevenCoeff_four_eqv (s : Nat) :
    fineSevenCoeff 4 s ≈ coeffW (qpow (blockWeight 8) 4) s := by
  unfold fineSevenCoeff coeffW dimQ
  exact Q'.mul_eqv_congr_left _ _ _
    (Q'.eqv_symm (HeatKernelRGStep.qpow_qpow (blockWeight 8) 4 (c4 s)))

theorem fineSevenMass_eqv_coordNormSq
    (rate : Nat) (w : Q')
    (hcoeff : forall s, fineSevenCoeff rate s ≈ coeffW w s)
    (N : Nat) : fineSevenMass rate (N + 1) ≈ coordNormSq w N := by
  unfold fineSevenMass coordNormSq
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s =>
    Q'.eqv_trans _
      (coeffW w s * fineSevenCoeff rate s) _
      (Q'.mul_eqv_congr_right _ _ _ (hcoeff s))
      (Q'.mul_eqv_congr_left _ _ _ (hcoeff s))) _

theorem fineSevenMass_eqv_coordNormSq_at
    (rate : Nat) (w : Q')
    (hcoeff : forall s, fineSevenCoeff rate s ≈ coeffW w s)
    (N count : Nat) (hcount : N + 1 = count) :
    fineSevenMass rate count ≈ coordNormSq w N := by
  subst count
  exact fineSevenMass_eqv_coordNormSq rate w hcoeff N

theorem fineSevenMassValues_eqv_at
    (rate : Nat) (w : Q')
    (hcoeff : forall s, fineSevenCoeff rate s ≈ coeffW w s)
    (N count : Nat) (left right : Q')
    (hcount : N + 1 = count)
    (hleft : left = fineSevenMass rate count)
    (hright : right = coordNormSq w N) : left ≈ right := by
  subst left
  subst right
  exact fineSevenMass_eqv_coordNormSq_at rate w hcoeff N count hcount

theorem fineSevenPath_eqv_boundaryDirichlet
    (rate : Nat) (w : Q')
    (hcoeff : forall s, fineSevenCoeff rate s ≈ coeffW w s)
    (N : Nat) : fineSevenPath rate N ≈
      coeffW w 0 * coeffW w 0 + coeffW w N * coeffW w N +
        dirichletEnergy w N := by
  unfold fineSevenPath dirichletEnergy
  refine Q'.add_eqv_congr'
    (Q'.add_eqv_congr'
      (Q'.eqv_trans _ (coeffW w 0 * fineSevenCoeff rate 0) _
        (Q'.mul_eqv_congr_right _ _ _ (hcoeff 0))
        (Q'.mul_eqv_congr_left _ _ _ (hcoeff 0)))
      (Q'.eqv_trans _ (coeffW w N * fineSevenCoeff rate N) _
        (Q'.mul_eqv_congr_right _ _ _ (hcoeff N))
        (Q'.mul_eqv_congr_left _ _ _ (hcoeff N)))) ?_
  exact CubeRatioBounds.fsum_eqv_congr _ _ (fun s => by
    unfold fineSevenEdgeSquare
    have hsub : fineSevenCoeff rate s + -fineSevenCoeff rate (s + 1) ≈
        coeffW w s + -coeffW w (s + 1) :=
      Q'.add_eqv_congr' (hcoeff s)
        (Q'.neg_eqv_congr _ _ (hcoeff (s + 1)))
    exact Q'.eqv_trans _
      ((coeffW w s + -coeffW w (s + 1)) *
        (fineSevenCoeff rate s + -fineSevenCoeff rate (s + 1))) _
      (Q'.mul_eqv_congr_right _ _ _ hsub)
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hsub)
        (Q'.eqv_symm
          (AllWindowCorrDirichlet.dirichletTerm_eqv_sq
            (coeffW w s) (coeffW w (s + 1)))))) N

theorem fineSevenPathValues_eqv
    (rate : Nat) (w : Q')
    (hcoeff : forall s, fineSevenCoeff rate s ≈ coeffW w s)
    (N : Nat) (left right : Q')
    (hleft : left = fineSevenPath rate N)
    (hright : right =
      coeffW w 0 * coeffW w 0 + coeffW w N * coeffW w N +
        dirichletEnergy w N) : left ≈ right := by
  subst left
  subst right
  exact fineSevenPath_eqv_boundaryDirichlet rate w hcoeff N

#print axioms fineSevenFloorPow_le
#print axioms fineSevenPow_le_ceil
#print axioms fineSevenCoeffLower_le
#print axioms fineSevenCoeff_le_upper
#print axioms fineSevenD1LowerGenerated
#print axioms fineSevenP4LowerGenerated
#print axioms fineSevenMassLowerNum_le
#print axioms fineSevenPathLowerNum_le
#print axioms fineSevenMass_eqv_coordNormSq
#print axioms fineSevenPath_eqv_boundaryDirichlet

end YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
