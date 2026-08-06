/-
Track 11.7-fusion / R4a -- physical `k=7` fine-reserve closure.

This module converts the certified boundary-plus-Dirichlet energies back to
coefficient deficits through `P = 2*T`, cancels the positive factor two, and
identifies the fixed rational debt with `blockParityDebt 7`.
-/

import YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenNumerals

namespace YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenPhysical

set_option maxHeartbeats 4000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaClearedCertificate
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveSeven
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenNumerals
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Int.add_mul, Int.mul_add, Int.one_mul,
               Int.mul_one];
             ac_rfl))

def fineSevenT1ExactAtom : Q' :=
  coefficientDeficit (blockWeight 8) 1279

def fineSevenT4ExactAtom : Q' :=
  coefficientDeficit (qpow (blockWeight 8) 4) 639

theorem fineSevenT1ExactAtom_eq : fineSevenT1ExactAtom =
    coefficientDeficit (blockWeight 8) 1279 := rfl

theorem fineSevenT4ExactAtom_eq : fineSevenT4ExactAtom =
    coefficientDeficit (qpow (blockWeight 8) 4) 639 := rfl

attribute [irreducible] fineSevenT1ExactAtom fineSevenT4ExactAtom

private theorem twiceDeficitValues_eqv
    (w : Q') (N : Nat) (T P : Q')
    (hT : T = coefficientDeficit w N)
    (hP : P = coeffW w 0 * coeffW w 0 + coeffW w N * coeffW w N +
      dirichletEnergy w N) : Q'.ofNat 2 * T ≈ P := by
  subst T
  subst P
  exact twice_norm_sub_corr_eq_boundary_dirichlet w N

theorem fineSevenTwiceT1_eqv_P1 :
    Q'.ofNat 2 * fineSevenT1ExactAtom ≈ fineSevenP1ExactAtom :=
  twiceDeficitValues_eqv (blockWeight 8) 1279 _ _
    fineSevenT1ExactAtom_eq fineSevenP1ExactAtom_eq

theorem fineSevenTwiceT4_eqv_P4 :
    Q'.ofNat 2 * fineSevenT4ExactAtom ≈ fineSevenP4ExactAtom :=
  twiceDeficitValues_eqv (qpow (blockWeight 8) 4) 639 _ _
    fineSevenT4ExactAtom_eq fineSevenP4ExactAtom_eq

private theorem reserve_of_doubled_path
    (D1 D4 T1 T4 P1 P4 debt : Q')
    (hP1 : Q'.ofNat 2 * T1 ≈ P1)
    (hP4 : Q'.ofNat 2 * T4 ≈ P4)
    (hbalance :
      Q'.ofNat 2 * (D4 * P1) +
          Q'.ofNat 2 * (debt * (D1 * D4)) <= D1 * P4) :
    Q'.ofNat 2 * (D4 * T1) + debt * (D1 * D4) <= D1 * T4 := by
  have hleftRing :
      Q'.ofNat 2 *
          (Q'.ofNat 2 * (D4 * T1) + debt * (D1 * D4)) ≈
        Q'.ofNat 2 * (D4 * (Q'.ofNat 2 * T1)) +
          Q'.ofNat 2 * (debt * (D1 * D4)) := by
    ring_qeqv
  have hleftSub :
      Q'.ofNat 2 * (D4 * (Q'.ofNat 2 * T1)) +
          Q'.ofNat 2 * (debt * (D1 * D4)) ≈
        Q'.ofNat 2 * (D4 * P1) +
          Q'.ofNat 2 * (debt * (D1 * D4)) := by
    exact Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
        (Q'.mul_eqv_congr_left D4 _ _ hP1))
      (Q'.eqv_refl _)
  have hrightRing : Q'.ofNat 2 * (D1 * T4) ≈
      D1 * (Q'.ofNat 2 * T4) := by
    ring_qeqv
  have hrightSub : D1 * (Q'.ofNat 2 * T4) ≈ D1 * P4 :=
    Q'.mul_eqv_congr_left D1 _ _ hP4
  have hscaled :
      Q'.ofNat 2 *
          (Q'.ofNat 2 * (D4 * T1) + debt * (D1 * D4)) <=
        Q'.ofNat 2 * (D1 * T4) := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.eqv_trans _ _ _ hleftRing hleftSub))
      (Q'.le_trans' _ _ _ hbalance
        (Q'.ge_of_eqv (Q'.eqv_trans _ _ _ hrightRing hrightSub)))
  exact Q'.le_of_mul_le_mul_left hscaled (by decide)

theorem fineSevenReserveAtomsCertifiedDebt :
    Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenT1ExactAtom) +
        fineSevenDebt * (fineSevenD1ExactAtom * fineSevenD4ExactAtom) <=
      fineSevenD1ExactAtom * fineSevenT4ExactAtom :=
  reserve_of_doubled_path
    fineSevenD1ExactAtom fineSevenD4ExactAtom
    fineSevenT1ExactAtom fineSevenT4ExactAtom
    fineSevenP1ExactAtom fineSevenP4ExactAtom fineSevenDebt
    fineSevenTwiceT1_eqv_P1 fineSevenTwiceT4_eqv_P4
    fineSevenDoubledReserveAtoms

theorem fineSevenReserveAtomsPhysicalDebt :
    Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenT1ExactAtom) +
        blockParityDebt 7 *
          (fineSevenD1ExactAtom * fineSevenD4ExactAtom) <=
      fineSevenD1ExactAtom * fineSevenT4ExactAtom := by
  have hleft :
      Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenT1ExactAtom) +
          blockParityDebt 7 *
            (fineSevenD1ExactAtom * fineSevenD4ExactAtom) ≈
        Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenT1ExactAtom) +
          fineSevenDebt *
            (fineSevenD1ExactAtom * fineSevenD4ExactAtom) := by
    exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ _
        (Q'.eqv_symm fineSevenDebt_eqv_physical))
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft)
    fineSevenReserveAtomsCertifiedDebt

/-- Honest carrier for downstream variable-index transport.  The structural
equalities identify every sealed atom with the repository's physical
definition; `reserve` is the exact `k=7` fine-reserve inequality. -/
structure FineSevenPhysicalReserveCertificate : Type where
  D1 : Q'
  D4 : Q'
  T1 : Q'
  T4 : Q'
  D1_eq : D1 = coordNormSq (blockWeight 8) 1279
  D4_eq : D4 = coordNormSq (qpow (blockWeight 8) 4) 639
  T1_eq : T1 = coefficientDeficit (blockWeight 8) 1279
  T4_eq : T4 = coefficientDeficit (qpow (blockWeight 8) 4) 639
  reserve : Q'.ofNat 2 * (D4 * T1) +
      blockParityDebt 7 * (D1 * D4) <= D1 * T4

def fineSevenPhysicalReserveCertificate : FineSevenPhysicalReserveCertificate where
  D1 := fineSevenD1ExactAtom
  D4 := fineSevenD4ExactAtom
  T1 := fineSevenT1ExactAtom
  T4 := fineSevenT4ExactAtom
  D1_eq := fineSevenD1ExactAtom_eq
  D4_eq := fineSevenD4ExactAtom_eq
  T1_eq := fineSevenT1ExactAtom_eq
  T4_eq := fineSevenT4ExactAtom_eq
  reserve := fineSevenReserveAtomsPhysicalDebt

#print axioms fineSevenTwiceT1_eqv_P1
#print axioms fineSevenTwiceT4_eqv_P4
#print axioms fineSevenReserveAtomsPhysicalDebt
#print axioms fineSevenPhysicalReserveCertificate

end YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenPhysical
