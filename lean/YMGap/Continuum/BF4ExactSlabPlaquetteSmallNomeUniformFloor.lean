/-
# One positive ORIGINAL raw reflected-norm floor for every cutoff and center

At the certified nome w=1/1024 on the extent-one slab, the two retained
unit amplitudes have energy <=5. The original determinant square has floor
1/1048576 and the fixed channel weight is positive. Dividing their product
by 11 therefore gives a strictly positive rational lower bound for the
ORIGINAL raw reflected norm of probe-c*unit, for EVERY K>=1 and rational c.

The floor is explicit and independent of K and c, not of the physical
coupling or volume. It supplies the unnormalized input for the subsequent
SmallNomeCenteredNontriviality module, not a physical transfer or mass gap.
Constants were produced by computations/original_plaquette_small_nome_minor.py.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor

namespace YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeCertificate
open YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeMinor
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

def unitEnergy (K : Nat) (hK : 1 ≤ K) : Q' :=
  twoProbeEnergy nome (Q'.le_of_lt nome_pos) K 0
    (interfaceUnit (Q'.le_of_lt nome_pos) K 0).leaf (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).leaf .unit

theorem unitEnergy_eq (K : Nat) (hK : 1 ≤ K) :
    unitEnergy K hK ≈
      heatMoment nome K polyOne * heatMoment nome K polyOne +
      channelWeightPower nome 4 * (heatMoment nome K scalarPolynomial * heatMoment nome K scalarPolynomial) := by
  have hu := unit_amplitude nome (Q'.le_of_lt nome_pos) K .unit
  have hv := scalar_unit_amplitude nome (Q'.le_of_lt nome_pos) K hK
  exact Q'.add_eqv_congr'
    (Q'.eqv_trans _ _ _ (mul_congr (interfaceUnit (Q'.le_of_lt nome_pos) K 0).weight_one (mul_congr hu hu))
      (Q'.one_mul_eqv _))
    (mul_congr (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).weight_pin (mul_congr hv hv))

theorem unitEnergy_le_five (K : Nat) (hK : 1 ≤ K) : unitEnergy K hK ≤ (5 : Q') := by
  have hu : Q'.abs (heatMoment nome K polyOne) ≤ (2 : Q') := by
    rw [ExpNeg.abs_of_nonneg (Q'.le_trans' _ _ _ HalfPow.half_nonneg (unit_bounds K).1)]
    exact (unit_bounds K).2
  have hu2 : heatMoment nome K polyOne * heatMoment nome K polyOne ≤ (4 : Q') :=
    Q'.le_trans' _ _ _ (product_upper_of_abs hu hu) (by decide)
  have hv2 : heatMoment nome K scalarPolynomial * heatMoment nome K scalarPolynomial ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ (product_upper_of_abs (scalar_abs K) (scalar_abs K)) (by decide)
  have hwv : channelWeightPower nome 4 * (heatMoment nome K scalarPolynomial * heatMoment nome K scalarPolynomial) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hv2 (Q'.le_of_lt (channelWeightPower_positive nome_pos 4)))
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_one_eqv _)) channelWeight_le_one)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (unitEnergy_eq K hK))
    (Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 hu2 hwv) (by decide))

theorem referenceBudget_le_ten (K : Nat) (hK : 1 ≤ K) :
    referenceBudget nome (Q'.le_of_lt nome_pos) K 0
      (interfaceUnit (Q'.le_of_lt nome_pos) K 0).leaf (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).leaf ≤ (10 : Q') :=
  Q'.le_trans' _ _ _ (ExpNeg.add_le_add2 (unitEnergy_le_five K hK) (unitEnergy_le_five K hK)) (by decide)

/-- One rational witness, with neither representation cutoff nor center as an argument. -/
def rawFloor : Q' := Q'.divPos (channelWeightPower nome 4 * Q'.invSucc 1048575) 11 (by decide)

theorem rawFloor_pos : (0 : Q') < rawFloor :=
  Q'.divPos_pos _ _ _ (Q'.mul_pos (channelWeightPower_positive nome_pos 4) (Q'.invSucc_pos 1048575))

theorem rawFloor_value : rawFloor ≈ Q'.invSucc 958235145249362713112862894527859283460095 := by decide

/-- Actual original reflected numerator, every cutoff K>=1 and rational recentering. -/
theorem rawFloor_bound (K : Nat) (hK : 1 ≤ K) (c : Q') :
    rawFloor ≤ rawForm nome K (recentered 0 probe c) (recentered 0 probe c) := by
  have hm : scalarPlaquetteMinor nome (Q'.le_of_lt nome_pos) K hK ≤
      rawForm nome K (recentered 0 probe c) (recentered 0 probe c) *
      referenceBudget nome (Q'.le_of_lt nome_pos) K 0
        (interfaceUnit (Q'.le_of_lt nome_pos) K 0).leaf (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).leaf :=
    Q'.le_trans' _ _ _
      (Q'.ge_of_eqv (twoProbeMinor_recentered nome (Q'.le_of_lt nome_pos) K 0
        (interfaceUnit (Q'.le_of_lt nome_pos) K 0).leaf (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).leaf probe c))
      (twoProbeMinor_bound nome (Q'.le_of_lt nome_pos) K 0
        (interfaceUnit (Q'.le_of_lt nome_pos) K 0).leaf (scalarLoopChannel (Q'.le_of_lt nome_pos) K hK).leaf (recentered 0 probe c))
  exact Q'.divPos_le_of_le_mul _ _ _ (Q'.le_trans' _ _ _ (minor_floor K hK)
    (Q'.le_trans' _ _ _ hm
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (Q'.le_trans' _ _ _ (referenceBudget_le_ten K hK) (by decide : (10 : Q') ≤ 11))
        (rawForm_nonnegative nome (Q'.le_of_lt nome_pos) K _))))

theorem every_recentered_positive (K : Nat) (hK : 1 ≤ K) (c : Q') :
    (0 : Q') < rawForm nome K (recentered 0 probe c) (recentered 0 probe c) :=
  Q'.pos_of_lt_of_le rawFloor_pos (rawFloor_bound K hK c)

end YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.unitEnergy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.unitEnergy_eq
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.unitEnergy_le_five
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.referenceBudget_le_ten
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.rawFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.rawFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.rawFloor_value
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.rawFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteSmallNomeUniformFloor.every_recentered_positive
