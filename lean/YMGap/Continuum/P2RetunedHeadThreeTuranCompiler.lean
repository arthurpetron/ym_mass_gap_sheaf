/-
Track 11.7-fusion / R2l -- a weaker replacement for the refuted
schedule-wide strong-Turan carrier.

The physical block schedule violates the strengthened Turan inequality at
`k=2,s=2`.  The adjacent coefficient tail itself is not refuted there.  This
module isolates the minimal repair: supply the first three adjacent tail
inequalities directly, and use strong Turan only from `s=3` onward.  Nat
induction then propagates the third head through the rest of the support.

This is a proof about computation: the unbounded coefficient scan is reduced
to a fixed three-cell head and one uniform interior recurrence.  No claim is
made here that the new analytic carrier is inhabited; unlike its predecessor,
it does not demand the known-false `s=2` Turan atom.

No `Classical`, `native_decide`, `sorry`, custom axiom, or noncomputable
declaration.
-/

import YMGap.Continuum.P2RetunedStrongTuranCompiler
import YMGap.Continuum.P2BlockCompatiblePhysicalBridge

namespace YMGap.Continuum.P2RetunedHeadThreeTuranCompiler

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FusionResidualBound
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.P2BlockCompatiblePhysicalBridge
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2RetunedRatioCompiler
open YMGap.Continuum.P2RetunedStrongTuranCompiler
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SelfFusionLogConcave

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ b ha)
    (Q'.mul_eqv_congr_left a' _ _ hb)

/-- The repaired coefficient carrier: three explicit adjacent heads followed
by strong-Turan propagation only at indices `s >= 3`. -/
structure P2RetunedHeadThreeTuran (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  head : forall s, 1 ≤ s -> s ≤ 3 -> s < 2 * N ->
    dimQ s * bondMovedCoeff N w 2 (s + 1) ≤
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 s)
  turan : forall s, 3 ≤ s -> s + 2 ≤ 2 * N ->
    (dimQ (s + 1) * bondMovedCoeff N w 2 s) *
        (dimQ (s + 1) * bondMovedCoeff N w 2 (s + 2)) ≤
      (qpow (p2RetunedWeight w) 2 *
          (dimQ (s + 2) * bondMovedCoeff N w 2 (s + 1))) *
        (dimQ s * bondMovedCoeff N w 2 (s + 1))

/-- Weighted Clebsch-box coordinate for the repaired carrier. -/
structure P2RetunedBoxHeadThreeTuran (N : Nat) (w : Q')
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) : Type where
  head : forall s, 1 ≤ s -> s ≤ 3 -> s < 2 * N ->
    dimQ s * boxSum w N (s + 1) ≤
      qpow (p2RetunedWeight w) (2 * s + 3) *
        (dimQ (s + 1) * boxSum w N s)
  turan : forall s, 3 ≤ s -> s + 2 ≤ 2 * N ->
    (dimQ (s + 1) * boxSum w N s) *
        (dimQ (s + 1) * boxSum w N (s + 2)) ≤
      (qpow (p2RetunedWeight w) 2 *
          (dimQ (s + 2) * boxSum w N (s + 1))) *
        (dimQ s * boxSum w N (s + 1))

/-- Exact Peter--Weyl reconstruction transports the repaired weighted-box
carrier to physical bond-moved coefficients. -/
def headThreeTuran_of_box {N : Nat} {w : Q'}
    (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (B : P2RetunedBoxHeadThreeTuran N w hw0 hw1) :
    P2RetunedHeadThreeTuran N w hw0 hw1 where
  head := fun s hs hs3 hsupport => by
    have hs0 : bondMovedCoeff N w 2 s ≈ boxSum w N s :=
      bondMovedCoeff_eq_boxSum N s
    have hs1 : bondMovedCoeff N w 2 (s + 1) ≈ boxSum w N (s + 1) :=
      bondMovedCoeff_eq_boxSum N (s + 1)
    have hleft :
        dimQ s * bondMovedCoeff N w 2 (s + 1) ≈
          dimQ s * boxSum w N (s + 1) :=
      Q'.mul_eqv_congr_left _ _ _ hs1
    have hright :
        qpow (p2RetunedWeight w) (2 * s + 3) *
            (dimQ (s + 1) * bondMovedCoeff N w 2 s) ≈
          qpow (p2RetunedWeight w) (2 * s + 3) *
            (dimQ (s + 1) * boxSum w N s) :=
      Q'.mul_eqv_congr_left _ _ _
        (Q'.mul_eqv_congr_left _ _ _ hs0)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (B.head s hs hs3 hsupport)
        (Q'.ge_of_eqv hright))
  turan := fun s hs hsupport => by
    have hs0 : bondMovedCoeff N w 2 s ≈ boxSum w N s :=
      bondMovedCoeff_eq_boxSum N s
    have hs1 : bondMovedCoeff N w 2 (s + 1) ≈ boxSum w N (s + 1) :=
      bondMovedCoeff_eq_boxSum N (s + 1)
    have hs2 : bondMovedCoeff N w 2 (s + 2) ≈ boxSum w N (s + 2) :=
      bondMovedCoeff_eq_boxSum N (s + 2)
    have hleft :
        (dimQ (s + 1) * bondMovedCoeff N w 2 s) *
            (dimQ (s + 1) * bondMovedCoeff N w 2 (s + 2)) ≈
          (dimQ (s + 1) * boxSum w N s) *
            (dimQ (s + 1) * boxSum w N (s + 2)) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _ hs0)
        (Q'.mul_eqv_congr_left _ _ _ hs2)
    have hright :
        (qpow (p2RetunedWeight w) 2 *
            (dimQ (s + 2) * bondMovedCoeff N w 2 (s + 1))) *
              (dimQ s * bondMovedCoeff N w 2 (s + 1)) ≈
          (qpow (p2RetunedWeight w) 2 *
            (dimQ (s + 2) * boxSum w N (s + 1))) *
              (dimQ s * boxSum w N (s + 1)) :=
      mul_eqv_both
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_eqv_congr_left _ _ _ hs1))
        (Q'.mul_eqv_congr_left _ _ _ hs1)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
      (Q'.le_trans' _ _ _ (B.turan s hs hsupport)
        (Q'.ge_of_eqv hright))

/-- Three fixed head cells plus the interior recurrence imply every adjacent
coefficient inequality in the complete two-fold support. -/
theorem coeffTailRatio_of_headThreeTuran {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (T : P2RetunedHeadThreeTuran N w (Q'.le_of_lt hwpos) hw1) :
    forall s, 1 ≤ s -> s < 2 * N ->
      dimQ s * bondMovedCoeff N w 2 (s + 1) ≤
        qpow (p2RetunedWeight w) (2 * s + 3) *
          (dimQ (s + 1) * bondMovedCoeff N w 2 s) := by
  intro s
  induction s with
  | zero =>
      intro hs
      exact absurd hs (by decide)
  | succ k ih =>
      intro hs hsupport
      by_cases hk : k < 3
      · exact T.head (k + 1) hs (by omega) hsupport
      · have hk3 : 3 ≤ k := by omega
        have hprev := ih (by omega) (by omega)
        have ht := T.turan k hk3 (by omega)
        let q2 := qpow (p2RetunedWeight w) 2
        let qk := qpow (p2RetunedWeight w) (2 * k + 3)
        let qnext := qpow (p2RetunedWeight w) (2 * (k + 1) + 3)
        let g0 := bondMovedCoeff N w 2 k
        let g1 := bondMovedCoeff N w 2 (k + 1)
        let g2 := bondMovedCoeff N w 2 (k + 2)
        let d0 := dimQ k
        let d1 := dimQ (k + 1)
        let d2 := dimQ (k + 2)
        have hscale0 : (0 : Q') ≤ q2 * (d2 * g1) := by
          exact Q'.mul_nonneg _ _
            (qpow_nonneg _ (p2RetunedWeight_nonneg (Q'.le_of_lt hwpos)) 2)
            (Q'.mul_nonneg _ _ (dimQ_nonneg (k + 2))
              (bondMovedCoeff_nonneg N (Q'.le_of_lt hwpos) 2 (k + 1)))
        have hscaled :
            (q2 * (d2 * g1)) * (d0 * g1) ≤
              (q2 * (d2 * g1)) * (qk * (d1 * g0)) :=
          Q'.mul_le_mul_of_nonneg_left _ _ _ hprev hscale0
        have hpow : q2 * qk ≈ qnext := by
          unfold q2 qk qnext
          have hexp : 2 * (k + 1) + 3 = 2 + (2 * k + 3) := by omega
          rw [hexp]
          exact Q'.eqv_symm
            (qpow_add (p2RetunedWeight w) 2 (2 * k + 3))
        have hright :
            (q2 * (d2 * g1)) * (qk * (d1 * g0)) ≈
              (d1 * g0) * (qnext * (d2 * g1)) := by
          refine Q'.eqv_trans _ _ _
            (mul_four_regroup q2 (d2 * g1) qk (d1 * g0)) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left (q2 * qk) _ _
              (Q'.mul_comm_eqv (d2 * g1) (d1 * g0))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.eqv_symm
              (Q'.mul_assoc_eqv (q2 * qk) (d1 * g0) (d2 * g1))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_right _ _ (d2 * g1)
              (Q'.mul_comm_eqv (q2 * qk) (d1 * g0))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv (d1 * g0) (q2 * qk) (d2 * g1)) ?_
          exact Q'.mul_eqv_congr_left (d1 * g0) _ _
            (Q'.mul_eqv_congr_right _ _ (d2 * g1) hpow)
        have hmul :
            (d1 * g0) * (d1 * g2) ≤
              (d1 * g0) * (qnext * (d2 * g1)) :=
          Q'.le_trans' _ _ _ ht
            (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hright))
        have hfactor : (0 : Q') < d1 * g0 :=
          Q'.mul_pos (Q'.ofNat_succ_pos (k + 1))
            (bondMovedCoeff_p2_pos_full_support hwpos (by omega))
        exact Q'.le_of_mul_le_mul_left hmul hfactor

def p2CoeffTailRatio_of_headThreeTuran {N : Nat} {w : Q'}
    (hwpos : (0 : Q') < w) (hw1 : w ≤ (1 : Q'))
    (T : P2RetunedHeadThreeTuran N w (Q'.le_of_lt hwpos) hw1) :
    P2RetunedCoeffTailRatio N w (Q'.le_of_lt hwpos) hw1 where
  tail := coeffTailRatio_of_headThreeTuran hwpos hw1 T

/-- Schedule-wide repaired coefficient carrier. -/
structure BlockCompatibleP2HeadThreeTuranData : Type where
  headThreeTuran : forall k,
    P2RetunedHeadThreeTuran (blockNcut k) (blockWeight k)
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)

def BlockCompatibleP2HeadThreeTuranData.toCoeffTailData
    (T : BlockCompatibleP2HeadThreeTuranData) :
    BlockCompatibleP2CoeffTailData where
  coeffTailRatio := fun k =>
    p2CoeffTailRatio_of_headThreeTuran
      (blockWeight_pos k) (blockWeight_le_one k) (T.headThreeTuran k)

/-- Weighted-box predecessor for the repaired schedule-wide carrier. -/
structure BlockCompatibleP2BoxHeadThreeTuranData : Type where
  boxHeadThreeTuran : forall k,
    P2RetunedBoxHeadThreeTuran (blockNcut k) (blockWeight k)
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)

def BlockCompatibleP2BoxHeadThreeTuranData.toHeadThreeTuranData
    (T : BlockCompatibleP2BoxHeadThreeTuranData) :
    BlockCompatibleP2HeadThreeTuranData where
  headThreeTuran := fun k =>
    headThreeTuran_of_box
      (Q'.le_of_lt (blockWeight_pos k)) (blockWeight_le_one k)
      (T.boxHeadThreeTuran k)

def BlockCompatibleP2BoxHeadThreeTuranData.toCoeffTailData
    (T : BlockCompatibleP2BoxHeadThreeTuranData) :
    BlockCompatibleP2CoeffTailData :=
  T.toHeadThreeTuranData.toCoeffTailData

#print axioms headThreeTuran_of_box
#print axioms coeffTailRatio_of_headThreeTuran
#print axioms p2CoeffTailRatio_of_headThreeTuran
#print axioms BlockCompatibleP2HeadThreeTuranData.toCoeffTailData
#print axioms BlockCompatibleP2BoxHeadThreeTuranData.toCoeffTailData

end YMGap.Continuum.P2RetunedHeadThreeTuranCompiler
