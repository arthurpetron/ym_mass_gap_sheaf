/-
# Strictly positive ORIGINAL interacting plaquette minor at a certified nome

The four actual heat-dressed Haar moments are placed in explicit intervals
using the original shared-link remainder and kernel-certified constants.
Their determinant is <= -1/1024 at EVERY representation cutoff. Its square
has the cutoff-independent floor 1/1048576. For K>=1 the retained channel
weight is positive, so the concrete original minor and finite recentering
floor are positive, with no sign/nonvanishing premise left to supply.

The nome is fixed at 1/1024 and the slab has extent one. This is the finite
input for the subsequent SmallNomeUniformFloor and
SmallNomeCenteredNontriviality modules, not a physical transfer or any
volume/spacing-uniform mass-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

theorem error_from_norm (K : Nat) (p : RatPoly) (C : Q') (hC : polynomialCoefficientL1 p ≤ C) :
    Q'.abs (lowerMomentError nome K p) ≤ C * errorCeiling :=
  Q'.le_trans' _ _ _ (lowerMomentError_bound (Q'.le_of_lt nome_pos) (Q'.le_of_lt nome_lt_one) K p lower_guards)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ lowerBudget_small (polynomialCoefficientL1_nonnegative p))
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hC (by decide)))

theorem moment_interval (K : Nat) (p : RatPoly) (b delta : Q')
    (hbase : quaternionHaar 116 p ≈ b) (herr : Q'.abs (lowerMomentError nome K p) ≤ delta) :
    b + -delta ≤ heatMoment nome K p ∧ heatMoment nome K p ≤ b + delta := by
  have h := Q'.eqv_trans _ _ _ (lowerMoment_eq nome K p)
    (Q'.add_eqv_congr_right _ _ _ hbase)
  constructor
  · exact Q'.le_trans' _ _ _
      (Q'.add_le_add_left b _ _ (Q'.le_trans' _ _ _ (Q'.neg_le_neg herr) (ExpNeg.neg_abs_le _)))
      (Q'.ge_of_eqv h)
  · exact Q'.le_trans' _ _ _ (Q'.le_of_eqv h)
      (Q'.add_le_add_left b _ _ (Q'.le_trans' _ _ _ (Q'.le_abs_self _) herr))

theorem probe_abs (K : Nat) : Q'.abs (heatMoment nome K (lower probe)) ≤ Q'.invSucc 511 := by
  have he : Q'.abs (lowerMomentError nome K (lower probe)) ≤ Q'.invSucc 511 :=
    Q'.le_trans' _ _ _ (error_from_norm K _ 128 probe_coefficientL1) (by decide)
  have h := moment_interval K _ 0 _ probe_haar_zero he
  rw [Q'.zero_add', Q'.zero_add'] at h
  exact Q'.abs_le h.1 h.2

theorem scalar_abs (K : Nat) : Q'.abs (heatMoment nome K scalarPolynomial) ≤ HalfPow.half := by
  have he : Q'.abs (lowerMomentError nome K scalarPolynomial) ≤ HalfPow.half :=
    Q'.le_trans' _ _ _ (error_from_norm K _ 1 scalar_coefficientL1) (by decide)
  have h := moment_interval K _ 0 _ scalarChannel_haar_zero he
  rw [Q'.zero_add', Q'.zero_add'] at h
  exact Q'.abs_le h.1 h.2

theorem mixed_lower (K : Nat) : Q'.invSucc 255 ≤ heatMoment nome K (polyMul (lower probe) scalarPolynomial) := by
  have he : Q'.abs (lowerMomentError nome K (polyMul (lower probe) scalarPolynomial)) ≤ Q'.invSucc 511 :=
    Q'.le_trans' _ _ _ (error_from_norm K _ 128 mixed_coefficientL1) (by decide)
  have h := moment_interval K _ (Q'.invSucc 127) _ probe_scalarChannel_haar he
  exact Q'.le_trans' _ _ _ (by decide) h.1

theorem unit_bounds (K : Nat) : HalfPow.half ≤ heatMoment nome K polyOne ∧ heatMoment nome K polyOne ≤ (2 : Q') := by
  have he : Q'.abs (lowerMomentError nome K polyOne) ≤ errorCeiling :=
    Q'.le_trans' _ _ _ (error_from_norm K _ 1 unit_coefficientL1) (Q'.le_of_eqv (Q'.one_mul_eqv _))
  have h := moment_interval K _ 1 _ unit_haar_one he
  exact ⟨Q'.le_trans' _ _ _ (by decide) h.1, Q'.le_trans' _ _ _ h.2 (by decide)⟩

theorem product_upper_of_abs {a b A B : Q'} (ha : Q'.abs a ≤ A) (hb : Q'.abs b ≤ B) : a * b ≤ A * B :=
  Q'.le_trans' _ _ _ (Q'.le_abs_self _) (Q'.le_trans' _ _ _ (ExpNeg.abs_mul_le a b)
    (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_right _ _ _ ha (Q'.abs_nonneg b))
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hb (Q'.le_trans' _ _ _ (Q'.abs_nonneg a) ha))))

/-- Same ORIGINAL four-moment determinant, at every finite representation cutoff. -/
theorem determinant_negative (K : Nat) : heatDeterminant nome K ≤ -Q'.invSucc 1023 := by
  have hav := product_upper_of_abs (probe_abs K) (scalar_abs K)
  have hbu : Q'.invSucc 255 * HalfPow.half ≤
      heatMoment nome K (polyMul (lower probe) scalarPolynomial) * heatMoment nome K polyOne :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (mixed_lower K) HalfPow.half_nonneg)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (unit_bounds K).1
        (Q'.le_trans' _ _ _ (Q'.le_of_lt (Q'.invSucc_pos 255)) (mixed_lower K)))
  exact Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hav (Q'.neg_le_neg hbu)) (by decide)

private theorem neg_square (a : Q') : (-a) * (-a) ≈ a * a :=
  Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv a (-a))
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ (Q'.mul_neg_eqv a a)) (Q'.neg_neg_eqv _))

theorem determinant_square_floor (K : Nat) : Q'.invSucc 1048575 ≤ heatDeterminant nome K * heatDeterminant nome K := by
  have hd : Q'.invSucc 1023 ≤ -heatDeterminant nome K :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv (Q'.neg_neg_eqv _)) (Q'.neg_le_neg (determinant_negative K))
  have hn : (0 : Q') ≤ -heatDeterminant nome K :=
    Q'.le_trans' _ _ _ (Q'.le_of_lt (Q'.invSucc_pos 1023)) hd
  exact Q'.le_trans' _ _ _ (by decide : Q'.invSucc 1048575 ≤ Q'.invSucc 1023 * Q'.invSucc 1023)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ hd (Q'.le_of_lt (Q'.invSucc_pos 1023)))
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hd hn) (Q'.le_of_eqv (neg_square _))))

theorem minor_floor (K : Nat) (hK : 1 ≤ K) :
    channelWeightPower nome 4 * Q'.invSucc 1048575 ≤ scalarPlaquetteMinor nome (Q'.le_of_lt nome_pos) K hK :=
  Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (determinant_square_floor K) (Q'.le_of_lt (channelWeightPower_positive nome_pos 4)))
    (Q'.ge_of_eqv (scalarPlaquetteMinor_eq nome (Q'.le_of_lt nome_pos) K hK))

theorem minor_positive (K : Nat) (hK : 1 ≤ K) : (0 : Q') < scalarPlaquetteMinor nome (Q'.le_of_lt nome_pos) K hK :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (channelWeightPower_positive nome_pos 4) (Q'.invSucc_pos 1048575)) (minor_floor K hK)

theorem finite_floor_positive (K : Nat) (hK : 1 ≤ K) : (0 : Q') < scalarPlaquetteFloor nome (Q'.le_of_lt nome_pos) K hK :=
  scalarPlaquetteFloor_positive nome (Q'.le_of_lt nome_pos) K hK (minor_positive K hK)

end YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.error_from_norm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.moment_interval
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.probe_abs
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.scalar_abs
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.mixed_lower
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.unit_bounds
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.product_upper_of_abs
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.determinant_negative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.determinant_square_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.minor_floor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.minor_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor.finite_floor_positive
