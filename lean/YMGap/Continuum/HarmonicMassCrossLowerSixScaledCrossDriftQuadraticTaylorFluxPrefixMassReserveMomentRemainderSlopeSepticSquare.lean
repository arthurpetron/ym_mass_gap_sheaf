/-
Order-safe square perturbation for the seventh-order slope enclosure.

These lemmas convert `T <= S <= T+E`, with `E <= 1`, into one-sided square
bounds without assuming a fixed sign for the root slope.  This is the local
inequality mechanism needed by the old/next finite-Hermite carrier.
-/

import YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticCarrier

namespace YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquare

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum

local infix:50 " ≈ " => Q'.eqv

private abbrev PE := RingNormaliser.PolyExpr

private def pSubReassembleL : PE :=
  .add (.var 0) (.add (.var 1) (.neg (.var 0)))

private def pSubReassembleR : PE := .var 1

private theorem pSubReassemble_normal :
    RingNormaliser.normalize pSubReassembleL =
      RingNormaliser.normalize pSubReassembleR := by decide

private theorem sub_reassemble (T S : Q') :
    T + (S + -T) ≈ S := by
  simpa [pSubReassembleL, pSubReassembleR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSubReassembleL pSubReassembleR pSubReassemble_normal
      (fun | 0 => T | _ => S))

private def pCancelRightL : PE :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 0))

private def pCancelRightR : PE := .var 1

private theorem pCancelRight_normal :
    RingNormaliser.normalize pCancelRightL =
      RingNormaliser.normalize pCancelRightR := by decide

private theorem cancel_right (T E : Q') :
    (T + E) + -T ≈ E := by
  simpa [pCancelRightL, pCancelRightR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pCancelRightL pCancelRightR pCancelRight_normal
      (fun | 0 => T | _ => E))

private def pCancelErrorL : PE :=
  .add (.add (.var 0) (.var 1)) (.neg (.var 1))

private def pCancelErrorR : PE := .var 0

private theorem pCancelError_normal :
    RingNormaliser.normalize pCancelErrorL =
      RingNormaliser.normalize pCancelErrorR := by decide

private theorem cancel_error (T E : Q') :
    (T + E) + -E ≈ T := by
  simpa [pCancelErrorL, pCancelErrorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pCancelErrorL pCancelErrorR pCancelError_normal
      (fun | 0 => T | _ => E))

private def pSquareExpandL : PE :=
  .mul (.add (.var 0) (.var 1)) (.add (.var 0) (.var 1))

private def pSquareExpandR : PE :=
  .add (.mul (.var 0) (.var 0))
    (.add (.mul (.const 2) (.mul (.var 0) (.var 1)))
      (.mul (.var 1) (.var 1)))

private theorem pSquareExpand_normal :
    RingNormaliser.normalize pSquareExpandL =
      RingNormaliser.normalize pSquareExpandR := by decide

private theorem square_expand (T e : Q') :
    (T + e) * (T + e) ≈
      T * T + (Q'.ofNat 2 * (T * e) + e * e) := by
  simpa [pSquareExpandL, pSquareExpandR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pSquareExpandL pSquareExpandR pSquareExpand_normal
      (fun | 0 => T | _ => e))

private def pThreeErrorL : PE :=
  .add (.mul (.const 2) (.var 0)) (.var 0)

private def pThreeErrorR : PE := .mul (.const 3) (.var 0)

private theorem pThreeError_normal :
    RingNormaliser.normalize pThreeErrorL =
      RingNormaliser.normalize pThreeErrorR := by decide

private theorem two_add_one_error (E : Q') :
    Q'.ofNat 2 * E + E ≈ Q'.ofNat 3 * E := by
  simpa [pThreeErrorL, pThreeErrorR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pThreeErrorL pThreeErrorR pThreeError_normal (fun _ => E))

private def pFourNegativeL : PE :=
  .mul (.const 2) (.mul (.neg (.const 2)) (.var 0))

private def pFourNegativeR : PE :=
  .neg (.mul (.const 4) (.var 0))

private theorem pFourNegative_normal :
    RingNormaliser.normalize pFourNegativeL =
      RingNormaliser.normalize pFourNegativeR := by decide

private theorem twice_negTwo_mul (e : Q') :
    Q'.ofNat 2 * (-(Q'.ofNat 2) * e) ≈
      -(Q'.ofNat 4 * e) := by
  simpa [pFourNegativeL, pFourNegativeR,
    RingNormaliser.eval] using
    (RingNormaliser.poly_identity_of_normal_eq
      pFourNegativeL pFourNegativeR pFourNegative_normal (fun _ => e))

private theorem error_difference_le
    {T S E : Q'} (hupper : S ≤ T + E) :
    S + -T ≤ E := by
  have hadd := Q'.add_le_add_right S (T + E) (-T) hupper
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (cancel_right T E))

private theorem subtract_error_le_model
    {T S E : Q'} (hupper : S ≤ T + E) :
    S + -E ≤ T := by
  have hadd := Q'.add_le_add_right S (T + E) (-E) hupper
  exact Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv (cancel_error T E))

/-- Upper square perturbation, valid across the sign change of the root
slope. -/
theorem square_le_model_square_add_three_error
    {T S E : Q'}
    (hmodel : T ≤ S) (hupper : S ≤ T + E)
    (hsone : S ≤ (1 : Q'))
    (hE1 : E ≤ (1 : Q')) :
    S * S ≤ T * T + Q'.ofNat 3 * E := by
  let e := S + -T
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact Q'.sub_nonneg_of_le hmodel
  have heE : e ≤ E := by
    dsimp only [e]
    exact error_difference_le hupper
  have he1 : e ≤ (1 : Q') := Q'.le_trans' _ _ _ heE hE1
  have hT1 : T ≤ (1 : Q') := Q'.le_trans' _ _ _ hmodel hsone
  have hTe : T * e ≤ E := by
    have hmul := Q'.mul_le_mul_of_nonneg_right T (1 : Q') e hT1 he0
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv e)) heE)
  have htwo : Q'.ofNat 2 * (T * e) ≤ Q'.ofNat 2 * E :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hTe (by decide)
  have hee : e * e ≤ E := by
    have hmul := Q'.mul_le_mul_of_nonneg_right e (1 : Q') e he1 he0
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv e)) heE)
  have hinner : Q'.ofNat 2 * (T * e) + e * e ≤
      Q'.ofNat 2 * E + E := Q'.add_le_add htwo hee
  have hadd := Q'.add_le_add_left (T * T) _ _ hinner
  have hreassemble : T + e ≈ S := by
    dsimp only [e]
    exact sub_reassemble T S
  have hreassembleSq : (T + e) * (T + e) ≈ S * S :=
    Q'.eqv_trans _ (S * (T + e)) _
      (Q'.mul_eqv_congr_right _ _ _ hreassemble)
      (Q'.mul_eqv_congr_left _ _ _ hreassemble)
  have hsquare : S * S ≈
      T * T + (Q'.ofNat 2 * (T * e) + e * e) :=
    Q'.eqv_trans _ ((T + e) * (T + e)) _
      (Q'.eqv_symm hreassembleSq)
      (square_expand T e)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hsquare)
    (Q'.le_trans' _ _ _ hadd
      (Q'.add_le_add_left (T * T) _ _
        (Q'.le_of_eqv (two_add_one_error E))))

/-- Lower square perturbation, valid across the sign change of the root
slope. -/
theorem model_square_sub_four_error_le_square
    {T S E : Q'}
    (hminus : -(1 : Q') ≤ S)
    (hmodel : T ≤ S) (hupper : S ≤ T + E)
    (hE1 : E ≤ (1 : Q')) :
    T * T + -(Q'.ofNat 4 * E) ≤ S * S := by
  let e := S + -T
  have he0 : (0 : Q') ≤ e := by
    dsimp only [e]
    exact Q'.sub_nonneg_of_le hmodel
  have heE : e ≤ E := by
    dsimp only [e]
    exact error_difference_le hupper
  have hnegE : -(1 : Q') ≤ -E := Q'.neg_le_neg hE1
  have hminusTwoRaw : -(1 : Q') + -(1 : Q') ≤ S + -E :=
    Q'.add_le_add hminus hnegE
  have hsub : S + -E ≤ T := subtract_error_le_model hupper
  have hminusTwo : -(Q'.ofNat 2) ≤ T := by
    have hconst : -(Q'.ofNat 2) ≈ -(1 : Q') + -(1 : Q') := by decide
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hconst)
      (Q'.le_trans' _ _ _ hminusTwoRaw hsub)
  have hTe : -(Q'.ofNat 2) * e ≤ T * e :=
    Q'.mul_le_mul_of_nonneg_right _ _ e hminusTwo he0
  have htwoTe : Q'.ofNat 2 * (-(Q'.ofNat 2) * e) ≤
      Q'.ofNat 2 * (T * e) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hTe (by decide)
  have hfour : -(Q'.ofNat 4 * E) ≤ Q'.ofNat 2 * (T * e) := by
    have h4mul := Q'.mul_le_mul_of_nonneg_left e E (Q'.ofNat 4) heE (by decide)
    have hneg := Q'.neg_le_neg h4mul
    exact Q'.le_trans' _ _ _ hneg
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.eqv_symm (twice_negTwo_mul e))) htwoTe)
  have hee0 : (0 : Q') ≤ e * e := Q'.mul_nonneg _ _ he0 he0
  have hinner : -(Q'.ofNat 4 * E) + (0 : Q') ≤
      Q'.ofNat 2 * (T * e) + e * e := Q'.add_le_add hfour hee0
  have hzero : -(Q'.ofNat 4 * E) + (0 : Q') ≈
      -(Q'.ofNat 4 * E) := QPoly.q_add_zero_eqv _
  have hadd := Q'.add_le_add_left (T * T) _ _ hinner
  have hreassemble : T + e ≈ S := by
    dsimp only [e]
    exact sub_reassemble T S
  have hreassembleSq : (T + e) * (T + e) ≈ S * S :=
    Q'.eqv_trans _ (S * (T + e)) _
      (Q'.mul_eqv_congr_right _ _ _ hreassemble)
      (Q'.mul_eqv_congr_left _ _ _ hreassemble)
  have hsquare : T * T + (Q'.ofNat 2 * (T * e) + e * e) ≈
      S * S :=
    Q'.eqv_trans _ ((T + e) * (T + e)) _
      (Q'.eqv_symm (square_expand T e))
      hreassembleSq
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (T * T) _ _ (Q'.ge_of_eqv hzero))
    (Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hsquare))

#print axioms square_le_model_square_add_three_error
#print axioms model_square_sub_four_error_le_square

end YMGap.Continuum.HarmonicMassCrossLowerSixScaledCrossDriftQuadraticTaylorFluxPrefixMassReserveMomentRemainderSlopeSepticSquare
