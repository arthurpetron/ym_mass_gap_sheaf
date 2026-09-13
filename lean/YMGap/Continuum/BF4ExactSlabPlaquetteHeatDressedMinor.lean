/-
# The concrete original minor as four heat-dressed polynomial moments

The actual unit and scalar-loop leaf amplitudes are identified with Haar
integrals retaining the original lower heat product. Their weighted minor
is exactly (2*w^3)^4 times the square of the four-moment determinant.
Thus the open coefficient estimate no longer involves tree-path recodings.

No nonvanishing of the heat-dressed determinant is assumed or proved here.
The positive-square consumer is conditional on its displayed finite test;
it is not a completed nontriviality or spectral-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments

namespace YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteConcreteMinor
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteProbeHaarMoments
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabAllExtentRetainedVacuumChannel
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.ReflectedSquareTreeRealizedLeaf
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

theorem determinant_congr {a a' b b' u u' v v' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') (hu : u ≈ u') (hv : v ≈ v') :
    determinant a b u v ≈ determinant a' b' u' v' :=
  Q'.add_eqv_congr' (mul_congr ha hv) (Q'.neg_eqv_congr _ _ (mul_congr hb hu))

def scalarPolynomial : RatPoly := loopPolynomial (fun _ => (false, false))

/-- Only the original lower interaction is inserted; no replacement law. -/
def heatMoment (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  quaternionHaar 116 (polyMul p (lowerHeatProduct w K 0))

theorem heatMoment_congr (w : Q') (K : Nat) {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    heatMoment w K p ≈ heatMoment w K q := haar_of_coeff_eqv 116 (h.mul_right _)

private theorem reorder (p L r : RatPoly) : RatPolyCoeffEqv (polyMul (polyMul p L) r) (polyMul (polyMul p r) L) :=
  (RatPolyCoeffEqv.mul_assoc p L r).trans
    (((RatPolyCoeffEqv.mul_comm L r).mul_left p).trans (RatPolyCoeffEqv.mul_assoc p r L).symm)

theorem realized_amplitude (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) {p : RatPoly} {v : Q'}
    (l : RealizedLeaf (interfaceExpansion hw K 0).tree p v) (e : PlaquetteExpression 0) :
    channelAmplitude w hw K 0 l.leaf e ≈ heatMoment w K (polyMul (lower e) p) := by
  unfold channelAmplitude Pair.amplitude
  rw [carrier_count]
  exact haar_of_coeff_eqv 116 ((l.channel_pin.mul_left (dressedLower w K e)).trans
    ((reorder (lower e) _ p).trans ((lowerObservable_one w K 0).mul_left _)))

theorem unit_amplitude (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (e : PlaquetteExpression 0) :
    channelAmplitude w hw K 0 (interfaceUnit hw K 0).leaf e ≈ heatMoment w K (lower e) :=
  Q'.eqv_trans _ _ _ (realized_amplitude w hw K (.ofUnit (interfaceUnit hw K 0)) e)
    (heatMoment_congr w K (RatPolyCoeffEqv.mul_one _))

theorem scalar_amplitude (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) (e : PlaquetteExpression 0) :
    channelAmplitude w hw K 0 (scalarLoopChannel hw K hK).leaf e ≈ heatMoment w K (polyMul (lower e) scalarPolynomial) :=
  realized_amplitude w hw K (scalarLoopChannel hw K hK) e

theorem scalar_unit_amplitude (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) :
    channelAmplitude w hw K 0 (scalarLoopChannel hw K hK).leaf .unit ≈ heatMoment w K scalarPolynomial :=
  Q'.eqv_trans _ _ _ (scalar_amplitude w hw K hK .unit)
    (heatMoment_congr w K (RatPolyCoeffEqv.one_mul _))

def heatDeterminant (w : Q') (K : Nat) : Q' := determinant
  (heatMoment w K (lower probe)) (heatMoment w K (polyMul (lower probe) scalarPolynomial))
  (heatMoment w K polyOne) (heatMoment w K scalarPolynomial)

/-- Complete same-object identity with all four original interacting moments. -/
theorem scalarPlaquetteMinor_eq (w : Q') (hw : (0 : Q') ≤ w) (K : Nat) (hK : 1 ≤ K) :
    scalarPlaquetteMinor w hw K hK ≈ channelWeightPower w 4 * (heatDeterminant w K * heatDeterminant w K) := by
  have hD := determinant_congr (unit_amplitude w hw K probe) (scalar_amplitude w hw K hK probe)
    (unit_amplitude w hw K .unit) (scalar_unit_amplitude w hw K hK)
  have hW := Q'.eqv_trans _ _ _
    (mul_congr (interfaceUnit hw K 0).weight_one (scalarLoopChannel hw K hK).weight_pin) (Q'.one_mul_eqv _)
  exact mul_congr hW (mul_congr hD hD)

theorem channelWeightPower_positive {w : Q'} (hw : (0 : Q') < w) :
    (n : Nat) → (0 : Q') < channelWeightPower w n
  | 0 => show (0 : Q') < 1 by decide
  | n + 1 => Q'.mul_pos (fundamentalWeight_positive hw) (channelWeightPower_positive hw n)

theorem scalarPlaquetteMinor_positive_of_square (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (hD : (0 : Q') < heatDeterminant w K * heatDeterminant w K) :
    (0 : Q') < scalarPlaquetteMinor w (Q'.le_of_lt hw) K hK :=
  Q'.pos_of_lt_of_le (Q'.mul_pos (channelWeightPower_positive hw 4) hD)
    (Q'.ge_of_eqv (scalarPlaquetteMinor_eq w (Q'.le_of_lt hw) K hK))

theorem scalarPlaquetteFloor_positive_of_square (w : Q') (hw : (0 : Q') < w) (K : Nat) (hK : 1 ≤ K)
    (hD : (0 : Q') < heatDeterminant w K * heatDeterminant w K) :
    (0 : Q') < scalarPlaquetteFloor w (Q'.le_of_lt hw) K hK :=
  scalarPlaquetteFloor_positive w (Q'.le_of_lt hw) K hK (scalarPlaquetteMinor_positive_of_square w hw K hK hD)

end YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.determinant_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalarPolynomial
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.heatMoment
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.heatMoment_congr
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.realized_amplitude
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.unit_amplitude
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalar_amplitude
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalar_unit_amplitude
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.heatDeterminant
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalarPlaquetteMinor_eq
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.channelWeightPower_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalarPlaquetteMinor_positive_of_square
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor.scalarPlaquetteFloor_positive_of_square
