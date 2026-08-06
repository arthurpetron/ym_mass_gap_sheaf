/-
Track 11.7-fusion / R4i -- heat-matched alternating strands.

The half-time coefficient target has the exact growing power `w^(s+2)`.
Along the odd strand its exponent grows by two, and from the preceding odd
cell to an even cell it grows by one.  Consequently the whole supported
family is compiled from one `w^3` head and the two fixed transition factors
`w^2` and `w`.

This file connects that finite-state proof principle to the exact weighted
Clebsch box, the A1 strand reindex, and the symbolic physical head proved for
every scale `k >= 8`.  Sparse exact certificates close the four earlier heads
`k=4,5,6,7`, so the remaining honest input is only the fixed-power parity
transition family.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedParityStrandCompiler
import YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
import YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose
import YMGap.Continuum.P2BlockCompatibleParityTransitionCertificate

namespace YMGap.Continuum.P2HalfTimeParityStrandCompiler

set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
set_option exponentiation.threshold 60000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingRelResidual
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionCoreStepRoundD
open YMGap.Continuum.FusionStrandExactReindex
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatibleHalfTimeRatioCompiler
open YMGap.Continuum.P2BlockCompatibleHeadPhysicalEnergyClose
open YMGap.Continuum.P2BlockCompatibleHeadLinearCertificate
open YMGap.Continuum.P2BlockCompatibleParityTransitionCertificate
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleScheduleClosed
open YMGap.Continuum.P2RetunedFenceIntegralCertificate
open YMGap.Continuum.P2RetunedParityStrandCompiler
open YMGap.Continuum.P2VacNormIntegralCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The heat-matched two-state automaton -/

/-- Right state of the exact half-time box inequality. -/
def halfTimeBoxRight (N : Nat) (w : Q') (s : Nat) : Q' :=
  qpow w (s + 2) * boxTailBase N w s

/-- Complete alternating certificate for the heat-matched box family. -/
abbrev P2HalfTimeBoxParityStrands (N : Nat) (w : Q') : Type :=
  AlternatingTailStrands
    (boxTailLeft N w) (halfTimeBoxRight N w) N

/-- Fixed-power core of the heat-matched parity certificate.  The exponent
increments are exactly two on the odd strand and one across the even bridge. -/
structure P2HalfTimeBoxCoreParityStrands (N : Nat) (w : Q') : Type where
  head : boxTailLeft N w 1 <= halfTimeBoxRight N w 1
  oddStep : forall m, 2 * m + 3 < 2 * N ->
    boxTailBase N w (2 * m + 1) *
        boxTailLeft N w (2 * m + 3) <=
      (qpow w 2 * boxTailBase N w (2 * m + 3)) *
        boxTailLeft N w (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N ->
    boxTailBase N w (2 * m - 1) *
        boxTailLeft N w (2 * m) <=
      (w * boxTailBase N w (2 * m)) *
        boxTailLeft N w (2 * m - 1)

/-- Head-free form of the two transition schemas. -/
structure P2HalfTimeBoxCoreParityTransitions (N : Nat) (w : Q') : Type where
  oddStep : forall m, 2 * m + 3 < 2 * N ->
    boxTailBase N w (2 * m + 1) *
        boxTailLeft N w (2 * m + 3) <=
      (qpow w 2 * boxTailBase N w (2 * m + 3)) *
        boxTailLeft N w (2 * m + 1)
  evenBridge : forall m, 1 <= m -> 2 * m < 2 * N ->
    boxTailBase N w (2 * m - 1) *
        boxTailLeft N w (2 * m) <=
      (w * boxTailBase N w (2 * m)) *
        boxTailLeft N w (2 * m - 1)

/-- Insert a separately proved head into the fixed transition automaton. -/
def halfTimeBoxCoreStrands_of_head_transitions {N : Nat} {w : Q'}
    (head : boxTailLeft N w 1 <= halfTimeBoxRight N w 1)
    (T : P2HalfTimeBoxCoreParityTransitions N w) :
    P2HalfTimeBoxCoreParityStrands N w where
  head := head
  oddStep := T.oddStep
  evenBridge := T.evenBridge

/-- Reinsert the growing heat powers.  This is the proof about computation:
the unbounded exponent family is discharged once and for all by `qpow_add`. -/
def halfTimeParityStrands_of_core {N : Nat} {w : Q'}
    (hw0 : (0 : Q') <= w) (T : P2HalfTimeBoxCoreParityStrands N w) :
    P2HalfTimeBoxParityStrands N w where
  head := T.head
  oddStep := fun m hm => by
    let e := (2 * m + 1) + 2
    let qe := qpow w e
    let q2 := qpow w 2
    let qnext := qpow w ((2 * m + 3) + 2)
    let Bprev := boxTailBase N w (2 * m + 1)
    let Bnext := boxTailBase N w (2 * m + 3)
    let Lprev := boxTailLeft N w (2 * m + 1)
    let Lnext := boxTailLeft N w (2 * m + 3)
    have hscaled : qe * (Bprev * Lnext) <=
        qe * ((q2 * Bnext) * Lprev) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (T.oddStep m hm)
        (qpow_nonneg w hw0 e)
    have hexp : (2 * m + 3) + 2 = e + 2 := by omega
    have hpow : qe * q2 ≈ qnext := by
      dsimp only [qe, q2, qnext]
      rw [hexp]
      exact Q'.eqv_symm (qpow_add w e 2)
    have hleft :
        halfTimeBoxRight N w (2 * m + 1) * Lnext ≈
          qe * (Bprev * Lnext) := by
      unfold halfTimeBoxRight
      dsimp only [e, qe, Bprev]
      exact Q'.mul_assoc_eqv _ _ _
    have hright : qe * ((q2 * Bnext) * Lprev) ≈
        halfTimeBoxRight N w (2 * m + 3) * Lprev := by
      have hregroup : qe * ((q2 * Bnext) * Lprev) ≈
          ((qe * q2) * Bnext) * Lprev := by
        refine Q'.eqv_trans _ (qe * (q2 * Bnext) * Lprev) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe (q2 * Bnext) Lprev)) ?_
        exact Q'.mul_eqv_congr_right _ _ Lprev
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe q2 Bnext))
      have hreplace : ((qe * q2) * Bnext) * Lprev ≈
          (qnext * Bnext) * Lprev :=
        Q'.mul_eqv_congr_right _ _ Lprev
          (Q'.mul_eqv_congr_right _ _ Bnext hpow)
      refine Q'.eqv_trans _ _ _ hregroup ?_
      refine Q'.eqv_trans _ _ _ hreplace ?_
      unfold halfTimeBoxRight
      dsimp only [qnext, Bnext]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
  evenBridge := fun m hm1 hm => by
    let e := (2 * m - 1) + 2
    let qe := qpow w e
    let qnext := qpow w (2 * m + 2)
    let Bodd := boxTailBase N w (2 * m - 1)
    let Beven := boxTailBase N w (2 * m)
    let Lodd := boxTailLeft N w (2 * m - 1)
    let Leven := boxTailLeft N w (2 * m)
    have hscaled : qe * (Bodd * Leven) <=
        qe * ((w * Beven) * Lodd) :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ (T.evenBridge m hm1 hm)
        (qpow_nonneg w hw0 e)
    have hexp : 2 * m + 2 = e + 1 := by
      dsimp only [e]
      omega
    have hpow : qe * w ≈ qnext := by
      dsimp only [qe, qnext]
      rw [hexp]
      exact Q'.eqv_refl _
    have hleft :
        halfTimeBoxRight N w (2 * m - 1) * Leven ≈
          qe * (Bodd * Leven) := by
      unfold halfTimeBoxRight
      have hindex : 2 * m - 1 + 2 = e := by rfl
      rw [hindex]
      dsimp only [qe, Bodd]
      exact Q'.mul_assoc_eqv _ _ _
    have hright : qe * ((w * Beven) * Lodd) ≈
        halfTimeBoxRight N w (2 * m) * Lodd := by
      have hregroup : qe * ((w * Beven) * Lodd) ≈
          ((qe * w) * Beven) * Lodd := by
        refine Q'.eqv_trans _ (qe * (w * Beven) * Lodd) _
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe (w * Beven) Lodd)) ?_
        exact Q'.mul_eqv_congr_right _ _ Lodd
          (Q'.eqv_symm (Q'.mul_assoc_eqv qe w Beven))
      have hreplace : ((qe * w) * Beven) * Lodd ≈
          (qnext * Beven) * Lodd :=
        Q'.mul_eqv_congr_right _ _ Lodd
          (Q'.mul_eqv_congr_right _ _ Beven hpow)
      refine Q'.eqv_trans _ _ _ hregroup ?_
      refine Q'.eqv_trans _ _ _ hreplace ?_
      unfold halfTimeBoxRight
      dsimp only [qnext, Beven]
      exact Q'.eqv_refl _
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))

/-! ## 2. Compile to the reviewed half-time consumer -/

theorem boxTailLeft_pos {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (s : Nat) (hs : s < 2 * N) :
    (0 : Q') < boxTailLeft N w s :=
  lt_of_lt_of_le (coeffTailLeft_pos hwpos s hs)
    (Q'.le_of_eqv (coeffTailLeft_eqv_boxTailLeft N w s))

/-- The heat-matched box automaton proves every half-time box cell. -/
theorem halfTimeBoxTail_of_parityStrands {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (T : P2HalfTimeBoxParityStrands N w) :
    forall s, 1 <= s -> s < 2 * N ->
      boxTailLeft N w s <= halfTimeBoxRight N w s :=
  tail_of_alternating_strands
    (fun s hs => boxTailLeft_pos hwpos s hs) T

/-- Transport all proved box cells through the exact A1 strand reindex. -/
def halfTimeLineSumTail_of_boxParity {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (T : P2HalfTimeBoxParityStrands N w) :
    P2HalfTimeLineSumTailRatio N w where
  tail := fun s hs hsN => by
    have hbox := halfTimeBoxTail_of_parityStrands hwpos T s hs hsN
    have eleft :
        dimQ s * lineSum (lagCorr w N) (s + 1) ≈
          boxTailLeft N w s := by
      unfold boxTailLeft
      exact Q'.mul_eqv_congr_left _ _ _
        (Q'.eqv_symm (boxSum_eq_lineSum_lagCorr w N (s + 1)))
    have ebase :
        boxTailBase N w s ≈
          dimQ (s + 1) * lineSum (lagCorr w N) s := by
      unfold boxTailBase
      exact Q'.mul_eqv_congr_left _ _ _
        (boxSum_eq_lineSum_lagCorr w N s)
    have eright : halfTimeBoxRight N w s ≈
        qpow w (s + 2) *
          (dimQ (s + 1) * lineSum (lagCorr w N) s) := by
      unfold halfTimeBoxRight
      exact Q'.mul_eqv_congr_left _ _ _ ebase
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
      (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))

/-- Fixed-power box laws compile directly to the half-time line-sum input. -/
def halfTimeLineSumTail_of_boxCore {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (T : P2HalfTimeBoxCoreParityStrands N w) :
    P2HalfTimeLineSumTailRatio N w :=
  halfTimeLineSumTail_of_boxParity hwpos
    (halfTimeParityStrands_of_core (Q'.le_of_lt hwpos) T)

/-! ## 3. Sparse finite head certificates -/

/-- Cleared exact half-time cell in common-denominator coordinates. -/
def halfTimeIntegralTailAt (num den N s : Nat) : Prop :=
  (s + 1) * scaledCoeffAt num den N (s + 1) * den ^ (s + 2) <=
    num ^ (s + 2) * ((s + 2) * scaledCoeffAt num den N s)

instance halfTimeIntegralTailAtDecidable (num den N s : Nat) :
    Decidable (halfTimeIntegralTailAt num den N s) := by
  unfold halfTimeIntegralTailAt
  infer_instance

private theorem scaleHalfTimeDimCoeffAt_reconstruct
    (num den : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (N s : Nat) :
    Q'.ofNat (den ^ (2 * c4 N)) *
        (qpow w (s + 2) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s)) ≈
      qpow w (s + 2) *
        Q'.ofNat ((s + 2) * scaledCoeffAt num den N s) := by
  refine Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.mul_comm_eqv _ _)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv _ _ _) ?_
  exact Q'.mul_eqv_congr_left _ _ _
    (scaledDimCoeffAt_reconstruct num den hden w hw N (s + 1) s)

/-- Soundness of one sparse exact half-time cell. -/
theorem halfTimeIntegralTailAt_sound
    (num den N s : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (h : halfTimeIntegralTailAt num den N s) :
    dimQ s * bondMovedCoeff N w 2 (s + 1) <=
      qpow w (s + 2) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  let scale := Q'.ofNat (den ^ (2 * c4 N))
  let k := s + 2
  have hcross :
      (s + 1) * scaledCoeffAt num den N (s + 1) * den ^ k <=
        num ^ k * ((s + 2) * scaledCoeffAt num den N s) := by
    simpa only [k] using h
  have hrat := ofNat_le_mkPos_mul_of_cross
    ((s + 1) * scaledCoeffAt num den N (s + 1))
    ((s + 2) * scaledCoeffAt num den N s)
    (num ^ k) (den ^ k) (Nat.pow_pos hden) hcross
  have hqpow : qpow w k ≈
      Q'.mkPos ((num ^ k : Nat) : Int) (den ^ k)
        (Nat.pow_pos hden) :=
    Q'.eqv_trans _ _ _
      (qpow_eqv_congr_base hw k)
      (qpow_mkPosNat_eqv num den hden k)
  have hcore :
      Q'.ofNat ((s + 1) * scaledCoeffAt num den N (s + 1)) <=
        qpow w k *
          Q'.ofNat ((s + 2) * scaledCoeffAt num den N s) :=
    Q'.le_trans' _ _ _ hrat (Q'.le_of_eqv
      (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hqpow)))
  have hl := scaledDimCoeffAt_reconstruct
    num den hden w hw N s (s + 1)
  have hr := scaleHalfTimeDimCoeffAt_reconstruct
    num den hden w hw N s
  have hscaled :
      scale * (dimQ s * bondMovedCoeff N w 2 (s + 1)) <=
        scale * (qpow w k *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s)) :=
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hl)
      (Q'.le_trans' _ _ _ hcore (Q'.le_of_eqv (Q'.eqv_symm hr)))
  have hscale : (0 : Q') < scale := by
    show (0 : Int) * (1 : Int) <
      ((den ^ (2 * c4 N) : Nat) : Int) * (1 : Int)
    simp only [Int.mul_one]
    exact_mod_cast (Nat.pow_pos hden)
  exact Q'.le_of_mul_le_mul_left hscaled hscale

/-- Linear-size form of the isolated `s=1` half-time head. -/
def linearHalfTimeHeadAt (num den N : Nat) : Prop :=
  2 * scaledHeadTwoAt num den N * den ^ 3 <=
    num ^ 3 * (3 * scaledHeadOneAt num den N)

instance linearHalfTimeHeadAtDecidable (num den N : Nat) :
    Decidable (linearHalfTimeHeadAt num den N) := by
  unfold linearHalfTimeHeadAt
  infer_instance

theorem halfTimeIntegralTailAt_one_of_linear
    (num den N : Nat) (hden : 0 < den)
    (w : Q') (hw : w ≈ Q'.mkPos num den hden)
    (h : linearHalfTimeHeadAt num den N) :
    halfTimeIntegralTailAt num den N 1 := by
  unfold linearHalfTimeHeadAt at h
  unfold halfTimeIntegralTailAt
  rw [scaledCoeffAt_one_eq_headOne num den hden w hw N,
    scaledCoeffAt_two_eq_headTwo num den hden w hw N]
  simpa only using h

/-- Schedule-native sparse head atom. -/
def physicalLinearHalfTimeHeadAt (k : Nat) : Prop :=
  linearHalfTimeHeadAt
    (physicalWeightNum k) (physicalWeightDen k) (blockNcut k)

instance physicalLinearHalfTimeHeadAtDecidable (k : Nat) :
    Decidable (physicalLinearHalfTimeHeadAt k) := by
  unfold physicalLinearHalfTimeHeadAt
  infer_instance

theorem physical_halfTime_box_head_of_linear (k : Nat)
    (h : physicalLinearHalfTimeHeadAt k) :
    boxTailLeft (blockNcut k) (blockWeight k) 1 <=
      halfTimeBoxRight (blockNcut k) (blockWeight k) 1 := by
  have hatom : halfTimeIntegralTailAt
      (physicalWeightNum k) (physicalWeightDen k) (blockNcut k) 1 :=
    halfTimeIntegralTailAt_one_of_linear _ _ _
      (physicalWeightDen_pos k) (blockWeight k)
      (blockWeight_eqv_closed k) h
  have hcoeff := halfTimeIntegralTailAt_sound
    (physicalWeightNum k) (physicalWeightDen k) (blockNcut k) 1
    (physicalWeightDen_pos k) (blockWeight k)
    (blockWeight_eqv_closed k) hatom
  have eright :
      qpow (blockWeight k) 3 *
          (dimQ 2 * bondMovedCoeff
            (blockNcut k) (blockWeight k) 2 1) ≈
        halfTimeBoxRight (blockNcut k) (blockWeight k) 1 := by
    unfold halfTimeBoxRight
    exact Q'.mul_eqv_congr_left _ _ _
      (coeffTailBase_eqv_boxTailBase
        (blockNcut k) (blockWeight k) 1)
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (coeffTailLeft_eqv_boxTailLeft
      (blockNcut k) (blockWeight k) 1))
    (Q'.le_trans' _ _ _ hcoeff (Q'.le_of_eqv eright))

theorem physicalLinearHalfTimeHeadCheck_four :
    physicalLinearHalfTimeHeadAt 4 := by decide

theorem physicalLinearHalfTimeHeadCheck_five :
    physicalLinearHalfTimeHeadAt 5 := by decide

set_option maxRecDepth 300000 in
set_option exponentiation.threshold 300000 in
theorem physicalLinearHalfTimeHeadCheck_six :
    physicalLinearHalfTimeHeadAt 6 := by decide

set_option maxRecDepth 1000000 in
set_option exponentiation.threshold 900000 in
theorem physicalLinearHalfTimeHeadCheck_seven :
    physicalLinearHalfTimeHeadAt 7 := by decide

/-! ## 4. Physical schedule and the symbolic `k >= 8` seed -/

/-- Restatement of the symbolic Dirichlet-energy head in the automaton's
exact box coordinates. -/
theorem physical_halfTime_box_head_from_eight (r : Nat) :
    boxTailLeft (blockNcut (r + 8)) (blockWeight (r + 8)) 1 <=
      halfTimeBoxRight
        (blockNcut (r + 8)) (blockWeight (r + 8)) 1 := by
  unfold boxTailLeft halfTimeBoxRight boxTailBase
  simpa only using physical_box_halfTime_head r

/-- The physical half-time head is closed at every scale used by the
coefficient tail: four sparse exact cells followed by the symbolic
Dirichlet-energy family.  Naming this assembled theorem lets alternative
tail compilers reuse the discharged head without importing the parity
transition hypotheses. -/
theorem physical_halfTime_box_head_from_four (k : Nat) (hk : 4 <= k) :
    boxTailLeft (blockNcut k) (blockWeight k) 1 <=
      halfTimeBoxRight (blockNcut k) (blockWeight k) 1 := by
  by_cases h8 : 8 <= k
  · simpa only [Nat.sub_add_cancel h8] using
      physical_halfTime_box_head_from_eight (k - 8)
  · have hkCases : k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
    rcases hkCases with h4 | h5 | h6 | h7
    · subst k
      exact physical_halfTime_box_head_of_linear 4
        physicalLinearHalfTimeHeadCheck_four
    · subst k
      exact physical_halfTime_box_head_of_linear 5
        physicalLinearHalfTimeHeadCheck_five
    · subst k
      exact physical_halfTime_box_head_of_linear 6
        physicalLinearHalfTimeHeadCheck_six
    · subst k
      exact physical_halfTime_box_head_of_linear 7
        physicalLinearHalfTimeHeadCheck_seven

/-- Exact A1 transport of the already-closed physical head into the line-sum
coordinates used by the local-reserve normal form. -/
theorem physical_halfTime_lineSum_head_from_four (k : Nat) (hk : 4 <= k) :
    dimQ 1 * lineSum (lagCorr (blockWeight k) (blockNcut k)) 2 <=
      qpow (blockWeight k) 3 *
        (dimQ 2 * lineSum (lagCorr (blockWeight k) (blockNcut k)) 1) := by
  have hbox := physical_halfTime_box_head_from_four k hk
  have eleft :
      dimQ 1 * lineSum (lagCorr (blockWeight k) (blockNcut k)) 2 ≈
        boxTailLeft (blockNcut k) (blockWeight k) 1 := by
    unfold boxTailLeft
    exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (boxSum_eq_lineSum_lagCorr (blockWeight k) (blockNcut k) 2))
  have ebase :
      boxTailBase (blockNcut k) (blockWeight k) 1 ≈
        dimQ 2 * lineSum
          (lagCorr (blockWeight k) (blockNcut k)) 1 := by
    unfold boxTailBase
    exact Q'.mul_eqv_congr_left _ _ _
      (boxSum_eq_lineSum_lagCorr (blockWeight k) (blockNcut k) 1)
  have eright :
      halfTimeBoxRight (blockNcut k) (blockWeight k) 1 ≈
        qpow (blockWeight k) 3 *
          (dimQ 2 * lineSum
            (lagCorr (blockWeight k) (blockNcut k)) 1) := by
    unfold halfTimeBoxRight
    exact Q'.mul_eqv_congr_left _ _ _ ebase
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv eleft)
    (Q'.le_trans' _ _ _ hbox (Q'.le_of_eqv eright))

/-! ## 5. Pure-natural transition certificates -/

/-- Cleared heat-matched odd two-step transition. -/
def physicalHalfTimeBoxOddTransitionAt (k m : Nat) : Prop :=
  integralBoxCrossAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 2 (2 * m + 1) (2 * m + 3)
      (2 * m + 3) (2 * m + 1)

/-- Cleared heat-matched preceding-odd to even transition. -/
def physicalHalfTimeBoxEvenTransitionAt (k m : Nat) : Prop :=
  integralBoxCrossAt
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 1 (2 * m - 1) (2 * m)
      (2 * m) (2 * m - 1)

instance physicalHalfTimeBoxOddTransitionAtDecidable (k m : Nat) :
    Decidable (physicalHalfTimeBoxOddTransitionAt k m) := by
  unfold physicalHalfTimeBoxOddTransitionAt
  infer_instance

instance physicalHalfTimeBoxEvenTransitionAtDecidable (k m : Nat) :
    Decidable (physicalHalfTimeBoxEvenTransitionAt k m) := by
  unfold physicalHalfTimeBoxEvenTransitionAt
  infer_instance

theorem physicalHalfTimeBoxOddTransitionAt_sound (k m : Nat)
    (h : physicalHalfTimeBoxOddTransitionAt k m) :
    boxTailBase (blockNcut k) (blockWeight k) (2 * m + 1) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m + 3) <=
      (qpow (blockWeight k) 2 *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m + 3)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m + 1) :=
  integralBoxCrossAt_sound_of_base
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 2 (2 * m + 1) (2 * m + 3)
      (2 * m + 3) (2 * m + 1)
    (physicalWeightDen_pos k) (physicalWeightDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockWeight k) (blockWeight_eqv_closed k) h

theorem physicalHalfTimeBoxEvenTransitionAt_sound (k m : Nat)
    (h : physicalHalfTimeBoxEvenTransitionAt k m) :
    boxTailBase (blockNcut k) (blockWeight k) (2 * m - 1) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m) <=
      (blockWeight k *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m - 1) := by
  have hraw := integralBoxCrossAt_sound_of_base
    (physicalWeightNum k) (physicalWeightDen k)
    (physicalWeightNum k) (physicalWeightDen k)
    (blockNcut k) 1 (2 * m - 1) (2 * m)
      (2 * m) (2 * m - 1)
    (physicalWeightDen_pos k) (physicalWeightDen_pos k)
    (blockWeight k) (blockWeight_eqv_closed k)
    (blockWeight k) (blockWeight_eqv_closed k) h
  have hone : qpow (blockWeight k) 1 ≈ blockWeight k := by
    unfold qpow
    exact Q'.one_mul_eqv _
  have hright :
      (qpow (blockWeight k) 1 *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m - 1) ≈
      (blockWeight k *
          boxTailBase (blockNcut k) (blockWeight k) (2 * m)) *
        boxTailLeft (blockNcut k) (blockWeight k) (2 * m - 1) :=
    Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_eqv_congr_right _ _ _ hone)
  exact Q'.le_trans' _ _ _ hraw (Q'.le_of_eqv hright)

/-- Head-free wrapper for the fixed-power `w^2` / `w` transition family.
Every physical head at `k >= 4` is already a theorem, so the carrier asks
only for the genuinely open transition schemas. -/
structure BlockCompatibleP2HalfTimeTransitionsFromFour : Type where
  transitions : forall k, 4 <= k ->
    P2HalfTimeBoxCoreParityTransitions (blockNcut k) (blockWeight k)

/-- Fully arithmetic form of the remaining frontier.  Every field is a
natural-number comparison and the only infinite family consists of the two
fixed transition schemas. -/
structure BlockCompatibleP2HalfTimeIntegralTransitionsFromFour : Type where
  odd : forall k m, 4 <= k -> 2 * m + 3 < 2 * blockNcut k ->
    physicalHalfTimeBoxOddTransitionAt k m
  even : forall k m, 4 <= k -> 1 <= m ->
    2 * m < 2 * blockNcut k ->
    physicalHalfTimeBoxEvenTransitionAt k m

/-- The generic soundness theorem turns the pure-natural carrier into the
rational box automaton. -/
def BlockCompatibleP2HalfTimeIntegralTransitionsFromFour.toBox
    (T : BlockCompatibleP2HalfTimeIntegralTransitionsFromFour) :
    BlockCompatibleP2HalfTimeTransitionsFromFour where
  transitions := fun k hk => {
    oddStep := fun m hm =>
      physicalHalfTimeBoxOddTransitionAt_sound k m (T.odd k m hk hm)
    evenBridge := fun m hm1 hm =>
      physicalHalfTimeBoxEvenTransitionAt_sound k m
        (T.even k m hk hm1 hm)
  }

/-- Assemble the complete physical head with the two transition schemas. -/
def BlockCompatibleP2HalfTimeTransitionsFromFour.toLineSumTail
    (T : BlockCompatibleP2HalfTimeTransitionsFromFour) :
    BlockCompatibleP2HalfTimeLineSumTailFromFour where
  tail := fun k hk =>
    halfTimeLineSumTail_of_boxCore (blockWeight_pos k)
      (halfTimeBoxCoreStrands_of_head_transitions
        (physical_halfTime_box_head_from_four k hk)
        (T.transitions k hk))

/-- End-to-end compiler from the two fixed heat-matched transition schemas
to the reviewed all-cutoff physical control family. -/
def BlockCompatibleP2HalfTimeTransitionsFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeTransitionsFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toLineSumTail.toControlFamily

/-- End-to-end proof-about-computation compiler from pure-natural heat-matched
transition certificates to the reviewed all-cutoff control family. -/
def BlockCompatibleP2HalfTimeIntegralTransitionsFromFour.toControlFamily
    (T : BlockCompatibleP2HalfTimeIntegralTransitionsFromFour) :
    P2RetunedBlockingDictionary.P2RetunedControlFamily :=
  T.toBox.toControlFamily

#print axioms halfTimeParityStrands_of_core
#print axioms halfTimeBoxTail_of_parityStrands
#print axioms halfTimeLineSumTail_of_boxParity
#print axioms halfTimeLineSumTail_of_boxCore
#print axioms halfTimeIntegralTailAt_sound
#print axioms halfTimeIntegralTailAt_one_of_linear
#print axioms physical_halfTime_box_head_of_linear
#print axioms physicalLinearHalfTimeHeadCheck_four
#print axioms physicalLinearHalfTimeHeadCheck_five
#print axioms physicalLinearHalfTimeHeadCheck_six
#print axioms physicalLinearHalfTimeHeadCheck_seven
#print axioms physical_halfTime_box_head_from_eight
#print axioms physical_halfTime_box_head_from_four
#print axioms physical_halfTime_lineSum_head_from_four
#print axioms physicalHalfTimeBoxOddTransitionAt_sound
#print axioms physicalHalfTimeBoxEvenTransitionAt_sound
#print axioms BlockCompatibleP2HalfTimeIntegralTransitionsFromFour.toBox
#print axioms BlockCompatibleP2HalfTimeTransitionsFromFour.toLineSumTail
#print axioms BlockCompatibleP2HalfTimeTransitionsFromFour.toControlFamily
#print axioms BlockCompatibleP2HalfTimeIntegralTransitionsFromFour.toControlFamily

end YMGap.Continuum.P2HalfTimeParityStrandCompiler
