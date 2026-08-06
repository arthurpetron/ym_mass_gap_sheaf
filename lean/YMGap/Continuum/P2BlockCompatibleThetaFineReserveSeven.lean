/-
Track 11.7-fusion / R3y -- opaque instantiation of the `k=7` fine reserve.

The compiler and its generated tables live in the imported module.  This
module deliberately instantiates the generic soundness theorems only across
that object-code boundary, preventing the elaborator from re-expanding a
1,280-step certificate.
-/

import YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint

namespace YMGap.Continuum.P2BlockCompatibleThetaFineReserveSeven

set_option maxHeartbeats 12000000
set_option maxRecDepth 30000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
open YMGap.Continuum.RGTransport

/-- Sealed compiler and physical values.  Since `Q'.le` is an inline
cross-product predicate, these atoms prevent order elaboration from evaluating
the full closed sums.  The immediately following structural equalities retain
their exact meanings. -/
def fineSevenD1MassAtom : Q' := fineSevenMass 1 1280
def fineSevenD4MassAtom : Q' := fineSevenMass 4 640
def fineSevenP1PathAtom : Q' := fineSevenPath 1 1279
def fineSevenP4PathAtom : Q' := fineSevenPath 4 639

def fineSevenD1ExactAtom : Q' := coordNormSq (blockWeight 8) 1279
def fineSevenD4ExactAtom : Q' := coordNormSq (qpow (blockWeight 8) 4) 639
def fineSevenP1ExactAtom : Q' :=
  coeffW (blockWeight 8) 0 * coeffW (blockWeight 8) 0 +
    coeffW (blockWeight 8) 1279 * coeffW (blockWeight 8) 1279 +
      dirichletEnergy (blockWeight 8) 1279
def fineSevenP4ExactAtom : Q' :=
  coeffW (qpow (blockWeight 8) 4) 0 * coeffW (qpow (blockWeight 8) 4) 0 +
    coeffW (qpow (blockWeight 8) 4) 639 *
      coeffW (qpow (blockWeight 8) 4) 639 +
        dirichletEnergy (qpow (blockWeight 8) 4) 639

theorem fineSevenD1MassAtom_eq : fineSevenD1MassAtom = fineSevenMass 1 1280 := rfl
theorem fineSevenD4MassAtom_eq : fineSevenD4MassAtom = fineSevenMass 4 640 := rfl
theorem fineSevenP1PathAtom_eq : fineSevenP1PathAtom = fineSevenPath 1 1279 := rfl
theorem fineSevenP4PathAtom_eq : fineSevenP4PathAtom = fineSevenPath 4 639 := rfl
theorem fineSevenD1ExactAtom_eq :
    fineSevenD1ExactAtom = coordNormSq (blockWeight 8) 1279 := rfl
theorem fineSevenD4ExactAtom_eq :
    fineSevenD4ExactAtom = coordNormSq (qpow (blockWeight 8) 4) 639 := rfl
theorem fineSevenP1ExactAtom_eq : fineSevenP1ExactAtom =
    coeffW (blockWeight 8) 0 * coeffW (blockWeight 8) 0 +
      coeffW (blockWeight 8) 1279 * coeffW (blockWeight 8) 1279 +
        dirichletEnergy (blockWeight 8) 1279 := rfl
theorem fineSevenP4ExactAtom_eq : fineSevenP4ExactAtom =
    coeffW (qpow (blockWeight 8) 4) 0 * coeffW (qpow (blockWeight 8) 4) 0 +
      coeffW (qpow (blockWeight 8) 4) 639 *
        coeffW (qpow (blockWeight 8) 4) 639 +
          dirichletEnergy (qpow (blockWeight 8) 4) 639 := rfl

attribute [irreducible] fineSevenD1MassAtom fineSevenD4MassAtom
  fineSevenP1PathAtom fineSevenP4PathAtom fineSevenD1ExactAtom
  fineSevenD4ExactAtom fineSevenP1ExactAtom fineSevenP4ExactAtom

private theorem coordValue_nonneg {w : Q'} (hw : (0 : Q') <= w)
    (N : Nat) (value : Q') (hvalue : value = coordNormSq w N) :
    (0 : Q') <= value := by
  subst value
  exact coordNormSq_nonneg hw N

private theorem boundaryDirichlet_nonneg {w : Q'} (hw : (0 : Q') <= w)
    (N : Nat) :
    (0 : Q') <= coeffW w 0 * coeffW w 0 +
      coeffW w N * coeffW w N + dirichletEnergy w N := by
  exact Q'.zero_le_add _ _
    (Q'.zero_le_add _ _
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw 0) (coeffW_nonneg hw 0))
      (Q'.mul_nonneg _ _ (coeffW_nonneg hw N) (coeffW_nonneg hw N)))
    (dirichletEnergy_nonneg w N)

private theorem pathValue_nonneg {w : Q'} (hw : (0 : Q') <= w)
    (N : Nat) (value : Q')
    (hvalue : value = coeffW w 0 * coeffW w 0 +
      coeffW w N * coeffW w N + dirichletEnergy w N) :
    (0 : Q') <= value := by
  subst value
  exact boundaryDirichlet_nonneg hw N

theorem fineSevenD1ExactAtom_nonneg : (0 : Q') <= fineSevenD1ExactAtom :=
  coordValue_nonneg (blockWeight_nonneg 8) 1279 _ fineSevenD1ExactAtom_eq

theorem fineSevenD4ExactAtom_nonneg : (0 : Q') <= fineSevenD4ExactAtom :=
  coordValue_nonneg
    (qpow_nonneg (blockWeight 8) (blockWeight_nonneg 8) 4) 639 _
    fineSevenD4ExactAtom_eq

theorem fineSevenP1ExactAtom_nonneg : (0 : Q') <= fineSevenP1ExactAtom :=
  pathValue_nonneg (blockWeight_nonneg 8) 1279 _ fineSevenP1ExactAtom_eq

theorem fineSevenP4ExactAtom_nonneg : (0 : Q') <= fineSevenP4ExactAtom :=
  pathValue_nonneg
    (qpow_nonneg (blockWeight 8) (blockWeight_nonneg 8) 4) 639 _
    fineSevenP4ExactAtom_eq

theorem fineSevenD1LowerTable_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassLowerBlockedNum 1 40 0) <=
      fineSevenD1ExactAtom := by
  have htable := fineSevenMassLowerBlocked_le_value_at 1 40 0 1280
    fineSevenD1MassAtom (by decide) fineSevenD1MassAtom_eq
  have hbridge := fineSevenMassValues_eqv_at 1 (blockWeight 8)
    fineSevenCoeff_one_eqv 1279 1280 fineSevenD1MassAtom
    fineSevenD1ExactAtom (by decide) fineSevenD1MassAtom_eq
    fineSevenD1ExactAtom_eq
  exact Q'.le_trans'
    (fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenMassLowerBlockedNum 1 40 0))
    fineSevenD1MassAtom fineSevenD1ExactAtom
    htable (Q'.le_of_eqv hbridge)

theorem fineSevenD1_le_upperTable :
    fineSevenD1ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperBlockedNum 1 40 0) := by
  have htable := fineSevenMass_value_le_upperBlocked_at 1 40 0 1280
    fineSevenD1MassAtom (by decide) fineSevenD1MassAtom_eq
  have hbridge := fineSevenMassValues_eqv_at 1 (blockWeight 8)
    fineSevenCoeff_one_eqv 1279 1280 fineSevenD1MassAtom
    fineSevenD1ExactAtom (by decide) fineSevenD1MassAtom_eq
    fineSevenD1ExactAtom_eq
  exact Q'.le_trans' fineSevenD1ExactAtom fineSevenD1MassAtom
    (fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenMassUpperBlockedNum 1 40 0))
    (Q'.ge_of_eqv hbridge) htable

theorem fineSevenD4_le_upperTable :
    fineSevenD4ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenMassUpperBlockedNum 4 20 0) := by
  have htable := fineSevenMass_value_le_upperBlocked_at 4 20 0 640
    fineSevenD4MassAtom (by decide) fineSevenD4MassAtom_eq
  have hbridge := fineSevenMassValues_eqv_at 4 (qpow (blockWeight 8) 4)
    fineSevenCoeff_four_eqv 639 640 fineSevenD4MassAtom
    fineSevenD4ExactAtom (by decide) fineSevenD4MassAtom_eq
    fineSevenD4ExactAtom_eq
  exact Q'.le_trans' fineSevenD4ExactAtom fineSevenD4MassAtom
    (fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenMassUpperBlockedNum 4 20 0))
    (Q'.ge_of_eqv hbridge) htable

theorem fineSevenP1_le_upperTable :
    fineSevenP1ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathUpperBlockedNum 1 39 31) := by
  have htable := fineSevenPath_value_le_upperBlocked_at 1 39 31 1279
    fineSevenP1PathAtom (by decide) fineSevenP1PathAtom_eq
  have hbridge := fineSevenPathValues_eqv 1 (blockWeight 8)
    fineSevenCoeff_one_eqv 1279 fineSevenP1PathAtom fineSevenP1ExactAtom
    fineSevenP1PathAtom_eq fineSevenP1ExactAtom_eq
  exact Q'.le_trans'
    fineSevenP1ExactAtom fineSevenP1PathAtom
    (fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenPathUpperBlockedNum 1 39 31))
    (Q'.ge_of_eqv hbridge) htable

theorem fineSevenP4LowerTable_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        (fineSevenPathLowerBlockedNum 4 19 31) <=
      fineSevenP4ExactAtom := by
  have htable := fineSevenPathLowerBlocked_le_value_at 4 19 31 639
    fineSevenP4PathAtom (by decide) fineSevenP4PathAtom_eq
  have hbridge := fineSevenPathValues_eqv 4 (qpow (blockWeight 8) 4)
    fineSevenCoeff_four_eqv 639 fineSevenP4PathAtom fineSevenP4ExactAtom
    fineSevenP4PathAtom_eq fineSevenP4ExactAtom_eq
  exact Q'.le_trans'
    (fixedPointVal fineSevenScale fineSevenScale_pos
      (fineSevenPathLowerBlockedNum 4 19 31))
    fineSevenP4PathAtom fineSevenP4ExactAtom htable
    (Q'.le_of_eqv hbridge)

end YMGap.Continuum.P2BlockCompatibleThetaFineReserveSeven
