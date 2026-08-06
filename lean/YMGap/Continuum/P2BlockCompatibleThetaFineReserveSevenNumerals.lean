/-
Track 11.7-fusion / R3z -- numeral repoint for the `k=7` reserve tables.

All semantic work is opaque in the imported module.  The only task here is
to replace each generated table expression by its independently checked
natural-number witness.
-/

import YMGap.Continuum.P2BlockCompatibleThetaFineReserveSeven

namespace YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenNumerals

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AllWindowCorrDirichlet
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.FixedPointPowerInterval
open YMGap.Continuum.P2BlockCompatibleSchedule
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveFixedPoint
open YMGap.Continuum.P2BlockCompatibleThetaFineReserveSeven
open YMGap.Continuum.P2BlockCompatibleThetaParityTransport
open YMGap.Continuum.RGTransport

local infix:50 " ≈ " => Q'.eqv

private theorem fixedPointLower_repoint
    (table witness : Nat) (right : Q')
    (htable : table = witness)
    (h : fixedPointVal fineSevenScale fineSevenScale_pos table <= right) :
    fixedPointVal fineSevenScale fineSevenScale_pos witness <= right := by
  subst witness
  exact h

private theorem fixedPointUpper_repoint
    (table witness : Nat) (left : Q')
    (htable : table = witness)
    (h : left <= fixedPointVal fineSevenScale fineSevenScale_pos table) :
    left <= fixedPointVal fineSevenScale fineSevenScale_pos witness := by
  subst witness
  exact h

theorem fineSevenD1Lower_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        fineSevenD1LowerWitness <= fineSevenD1ExactAtom := by
  exact fixedPointLower_repoint _ _ fineSevenD1ExactAtom
    fineSevenD1LowerBlockedGenerated fineSevenD1LowerTable_le

theorem fineSevenD1_le_upper :
    fineSevenD1ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        fineSevenD1UpperWitness := by
  exact fixedPointUpper_repoint _ _ fineSevenD1ExactAtom
    fineSevenD1UpperBlockedGenerated fineSevenD1_le_upperTable

theorem fineSevenD4_le_upper :
    fineSevenD4ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        fineSevenD4UpperWitness := by
  exact fixedPointUpper_repoint _ _ fineSevenD4ExactAtom
    fineSevenD4UpperBlockedGenerated fineSevenD4_le_upperTable

theorem fineSevenP1_le_upper :
    fineSevenP1ExactAtom <=
      fixedPointVal fineSevenScale fineSevenScale_pos
        fineSevenP1UpperWitness := by
  exact fixedPointUpper_repoint _ _ fineSevenP1ExactAtom
    fineSevenP1UpperBlockedGenerated fineSevenP1_le_upperTable

theorem fineSevenP4Lower_le :
    fixedPointVal fineSevenScale fineSevenScale_pos
        fineSevenP4LowerWitness <=
      fineSevenP4ExactAtom := by
  exact fixedPointLower_repoint _ _ fineSevenP4ExactAtom
    fineSevenP4LowerBlockedGenerated fineSevenP4LowerTable_le

def fineSevenD1Lower : Q' :=
  fixedPointVal fineSevenScale fineSevenScale_pos fineSevenD1LowerWitness
def fineSevenD1Upper : Q' :=
  fixedPointVal fineSevenScale fineSevenScale_pos fineSevenD1UpperWitness
def fineSevenD4Upper : Q' :=
  fixedPointVal fineSevenScale fineSevenScale_pos fineSevenD4UpperWitness
def fineSevenP1Upper : Q' :=
  fixedPointVal fineSevenScale fineSevenScale_pos fineSevenP1UpperWitness
def fineSevenP4Lower : Q' :=
  fixedPointVal fineSevenScale fineSevenScale_pos fineSevenP4LowerWitness

/-- Exact rational form of the physical `k=7` parity debt. -/
def fineSevenDebt : Q' := Q'.mkPos 1 754974720 (by decide)

theorem fineSevenDebt_eqv_physical :
    fineSevenDebt ≈ blockParityDebt 7 := by
  unfold fineSevenDebt blockParityDebt blockMargin
    YMGap.Constructive.HalfPow.half
    SpectralLocalizationCrux.q112 blockQuarter qpow
  decide

/-- The sole closed arithmetic comparison after all interval soundness has
been factored out. -/
theorem fineSevenNumeralBalance :
    Q'.ofNat 2 * (fineSevenD4Upper * fineSevenP1Upper) +
        Q'.ofNat 2 *
          (fineSevenDebt * (fineSevenD1Upper * fineSevenD4Upper)) <=
      fineSevenD1Lower * fineSevenP4Lower := by
  unfold fineSevenD4Upper fineSevenP1Upper fineSevenDebt
    fineSevenD1Upper fineSevenD1Lower fineSevenP4Lower
    fineSevenD4UpperWitness fineSevenP1UpperWitness
    fineSevenD1UpperWitness fineSevenD1LowerWitness
    fineSevenP4LowerWitness fineSevenScale
    FixedPointPowerInterval.fixedPointVal
  decide

/-- Certified doubled fine-reserve inequality for the four sealed physical
atoms.  Combined with `2*T = P`, this is exactly the `k=7` reserve shape. -/
theorem fineSevenDoubledReserveAtoms :
    Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenP1ExactAtom) +
        Q'.ofNat 2 *
          (fineSevenDebt *
            (fineSevenD1ExactAtom * fineSevenD4ExactAtom)) <=
      fineSevenD1ExactAtom * fineSevenP4ExactAtom := by
  have hD1nonneg : (0 : Q') <= fineSevenD1ExactAtom :=
    Q'.le_trans' _ _ _
      (fixedPointVal_nonneg fineSevenScale fineSevenScale_pos
        fineSevenD1LowerWitness) fineSevenD1Lower_le
  have hD4UpperNonneg : (0 : Q') <= fineSevenD4Upper := by
    unfold fineSevenD4Upper
    exact fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _
  have hD1UpperNonneg : (0 : Q') <= fineSevenD1Upper := by
    unfold fineSevenD1Upper
    exact fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _
  have hP4LowerNonneg : (0 : Q') <= fineSevenP4Lower := by
    unfold fineSevenP4Lower
    exact fixedPointVal_nonneg fineSevenScale fineSevenScale_pos _
  have hD4P1 : fineSevenD4ExactAtom * fineSevenP1ExactAtom <=
      fineSevenD4Upper * fineSevenP1Upper := by
    exact Q'.mul_le_mul_of_nonneg fineSevenD4_le_upper fineSevenP1_le_upper
      hD4UpperNonneg fineSevenP1ExactAtom_nonneg
  have hD1D4 : fineSevenD1ExactAtom * fineSevenD4ExactAtom <=
      fineSevenD1Upper * fineSevenD4Upper := by
    exact Q'.mul_le_mul_of_nonneg fineSevenD1_le_upper fineSevenD4_le_upper
      hD1UpperNonneg fineSevenD4ExactAtom_nonneg
  have hdebt : fineSevenDebt *
        (fineSevenD1ExactAtom * fineSevenD4ExactAtom) <=
      fineSevenDebt * (fineSevenD1Upper * fineSevenD4Upper) :=
    Q'.mul_le_mul_of_nonneg_left _ _ fineSevenDebt hD1D4 (by decide)
  have hleft :
      Q'.ofNat 2 * (fineSevenD4ExactAtom * fineSevenP1ExactAtom) +
          Q'.ofNat 2 *
            (fineSevenDebt *
              (fineSevenD1ExactAtom * fineSevenD4ExactAtom)) <=
        Q'.ofNat 2 * (fineSevenD4Upper * fineSevenP1Upper) +
          Q'.ofNat 2 *
            (fineSevenDebt * (fineSevenD1Upper * fineSevenD4Upper)) :=
    Q'.add_le_add
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hD4P1 (by decide))
      (Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hdebt (by decide))
  have hright : fineSevenD1Lower * fineSevenP4Lower <=
      fineSevenD1ExactAtom * fineSevenP4ExactAtom := by
    exact Q'.mul_le_mul_of_nonneg fineSevenD1Lower_le fineSevenP4Lower_le
      hD1nonneg hP4LowerNonneg
  exact Q'.le_trans' _ _ _ hleft
    (Q'.le_trans' _ _ _ fineSevenNumeralBalance hright)

end YMGap.Continuum.P2BlockCompatibleThetaFineReserveSevenNumerals
