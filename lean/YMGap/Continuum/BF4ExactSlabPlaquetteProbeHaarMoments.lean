/-
# Exact reference Haar moments of the concrete plaquette/channel pair

These are bare product-Haar integrals of the SAME original polynomials on
the SAME 116-link carrier. The plaquette and scalar-loop means vanish, and
their mixed moment is 1/128. Thus the unweighted reference amplitude
determinant is nonzero. No interacting heat product is inserted here.

This does not prove the interacting minor positive: its amplitudes include
the lower heat product, and its channel weight (2*w^3)^4 vanishes at w=0.
Controlling that insertion at positive w and retaining a cutoff-limit floor
are separate open steps.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor

namespace YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

theorem carrier_count : (boundaryCompleteSlabLinks (centralExtent 0)).length = 116 :=
  correctedSlabLinks_extent_one_length

theorem probe_haar_zero : (quaternionHaar 116 (lower probe)).eqv 0 := by decide +kernel

theorem scalarChannel_haar_zero :
    (quaternionHaar 116 (loopPolynomial (fun _ => (false, false)))).eqv 0 := by decide +kernel

theorem probe_scalarChannel_haar :
    (quaternionHaar 116 (polyMul (lower probe) (loopPolynomial (fun _ => (false, false))))).eqv
      (Q'.invSucc 127) := by decide +kernel

theorem unit_haar_one : (quaternionHaar 116 polyOne).eqv 1 := by decide +kernel

def referenceDeterminant : Q' := determinant
  (quaternionHaar 116 (lower probe))
  (quaternionHaar 116 (polyMul (lower probe) (loopPolynomial (fun _ => (false, false)))))
  (quaternionHaar 116 polyOne)
  (quaternionHaar 116 (loopPolynomial (fun _ => (false, false))))

theorem referenceDeterminant_value : referenceDeterminant.eqv (-Q'.invSucc 127) := by
  have ha : ((quaternionHaar 116 (lower probe)) *
      quaternionHaar 116 (loopPolynomial (fun _ => (false, false)))).eqv 0 :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ probe_haar_zero) (RingNormaliser.q_zero_mul _)
  have hb : ((quaternionHaar 116 (polyMul (lower probe) (loopPolynomial (fun _ => (false, false))))) *
      quaternionHaar 116 polyOne).eqv (Q'.invSucc 127) :=
    Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ probe_scalarChannel_haar)
      (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ unit_haar_one) (Q'.mul_one_eqv _))
  exact Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)) (QPoly.q_zero_add_eqv _)

theorem referenceDeterminant_square : (referenceDeterminant * referenceDeterminant).eqv (Q'.invSucc 16383) :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ referenceDeterminant_value)
    (Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_left _ _ _ referenceDeterminant_value) (by decide))

theorem referenceDeterminant_square_positive : (0 : Q') < referenceDeterminant * referenceDeterminant :=
  Q'.pos_of_lt_of_le (Q'.invSucc_pos 16383) (Q'.ge_of_eqv referenceDeterminant_square)

end YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.carrier_count
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.probe_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.scalarChannel_haar_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.probe_scalarChannel_haar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.unit_haar_one
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.referenceDeterminant
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.referenceDeterminant_value
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.referenceDeterminant_square
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments.referenceDeterminant_square_positive
