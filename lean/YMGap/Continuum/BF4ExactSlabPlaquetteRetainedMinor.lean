/-
# A centering-independent floor from ORIGINAL interface coefficients

Two distinct paths in the actual all-extent interface expansion determine
four exact rational Haar amplitudes: observable/reference in each channel.
Their weighted squared determinant gives a computable floor for the ORIGINAL
reflected numerator of e-c*unit, for EVERY rational c. The denominator is the
retained unit energy plus one, so division never needs an unproved nonzero
amplitude. The lower heat product and all its shared variables remain intact.

Strict positivity is reduced to the decidable positivity of that computed
minor, not assumed for any particular channel pair. No pair with a proved
positive minor, cutoff-uniform floor, completed excitation, or gap is asserted.
-/

import YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
import YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS

namespace YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllCutoffReflectionPositivity
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPlaquetteFiniteGNS
open YMGap.Continuum.ReflectedSquareTreeRetainedChannel
open YMGap.Continuum.ReflectedSquareTreeTwoChannelBound
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

private theorem mul_congr {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha) (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem minor_congr_left {a0 a1 a0' a1' : Q'} (w0 w1 b0 b1 : Q')
    (h0 : a0 ≈ a0') (h1 : a1 ≈ a1') : minor w0 w1 a0 a1 b0 b1 ≈ minor w0 w1 a0' a1' b0 b1 := by
  have h : determinant a0 a1 b0 b1 ≈ determinant a0' a1' b0 b1 :=
    Q'.add_eqv_congr' (Q'.mul_eqv_congr_right _ _ _ h0)
      (Q'.neg_eqv_congr _ _ (Q'.mul_eqv_congr_right _ _ _ h1))
  exact Q'.mul_eqv_congr_left _ _ _ (mul_congr h h)

variable (w : Q') (hw : (0 : Q') ≤ w) (K half : Nat)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "tree" => LocalSquareExpansion.tree (interfaceExpansion hw K half)

/-- The full original action dresses the observable BEFORE channel integration. -/
def channelAmplitude (l : Leaf tree) (e : PlaquetteExpression half) : Q' :=
  Pair.amplitude blocks l (dressedLower w K e)

theorem channelAmplitude_add (l : Leaf tree) (e f : PlaquetteExpression half) :
    channelAmplitude w hw K half l (.add e f) ≈
      channelAmplitude w hw K half l e + channelAmplitude w hw K half l f := by
  change quaternionHaar blocks (polyMul (polyMul (polyAdd (lower e) (lower f)) _) _) ≈ _
  rw [polyMul_add_left_exact, polyMul_add_left_exact]
  exact quaternionHaar_append blocks _ _

theorem channelAmplitude_smul (l : Leaf tree) (c : Q') (e : PlaquetteExpression half) :
    channelAmplitude w hw K half l (.smul c e) ≈ c * channelAmplitude w hw K half l e :=
  Q'.eqv_trans _ _ _ (haar_of_coeff_eqv blocks
    (((RatPolyCoeffEqv.polyMul_smul_left c (lower e) (lowerObservable w K half (fun _ => 1))).mul_right l.channel).trans
      (RatPolyCoeffEqv.polyMul_smul_left _ _ _))) (quaternionHaar_polySmul blocks _ _)

def recentered (e : PlaquetteExpression half) (c : Q') : PlaquetteExpression half := .add e (.smul (-c) .unit)

theorem channelAmplitude_recentered (l : Leaf tree) (e : PlaquetteExpression half) (c : Q') :
    channelAmplitude w hw K half l (recentered half e c) ≈
      channelAmplitude w hw K half l e + (-c) * channelAmplitude w hw K half l .unit :=
  Q'.eqv_trans _ _ _ (channelAmplitude_add w hw K half l e _)
    (Q'.add_eqv_congr_left _ _ _ (channelAmplitude_smul w hw K half l (-c) .unit))

def retainedMinor (p : Pair tree) (e : PlaquetteExpression half) : Q' :=
  minor p.first.weight p.second.weight
    (channelAmplitude w hw K half p.first e) (channelAmplitude w hw K half p.second e)
    (channelAmplitude w hw K half p.first .unit) (channelAmplitude w hw K half p.second .unit)

def referenceEnergy (p : Pair tree) : Q' := energy p.first.weight p.second.weight
  (channelAmplitude w hw K half p.first .unit) (channelAmplitude w hw K half p.second .unit)

theorem referenceEnergy_nonnegative (p : Pair tree) : (0 : Q') ≤ referenceEnergy w hw K half p :=
  energy_nonnegative (Pair.weight_nonnegative p.first (interfaceExpansion hw K half).weightsNonnegative)
    (Pair.weight_nonnegative p.second (interfaceExpansion hw K half).weightsNonnegative) _ _

theorem retainedMinor_nonnegative (p : Pair tree) (e : PlaquetteExpression half) :
    (0 : Q') ≤ retainedMinor w hw K half p e :=
  minor_nonnegative (Pair.weight_nonnegative p.first (interfaceExpansion hw K half).weightsNonnegative)
    (Pair.weight_nonnegative p.second (interfaceExpansion hw K half).weightsNonnegative) _ _ _ _

theorem retainedMinor_recentered (p : Pair tree) (e : PlaquetteExpression half) (c : Q') :
    retainedMinor w hw K half p (recentered half e c) ≈ retainedMinor w hw K half p e :=
  Q'.eqv_trans _ _ _ (minor_congr_left _ _ _ _ (channelAmplitude_recentered w hw K half p.first e c)
    (channelAmplitude_recentered w hw K half p.second e c)) (minor_shift _ _ _ _ _ _ c)

/-- Literal numerator-to-tree pin. No alternative conditional law occurs. -/
theorem rawForm_eq_dressedSquareSum (e : PlaquetteExpression half) :
    rawForm w K e e ≈ haarSquareSum blocks ((tree).multiplyTerm 1 (dressedLower w K e)) :=
  upper_numerator_eq_squareValue w K e hw

theorem retainedMinor_le_rawForm (p : Pair tree) (e : PlaquetteExpression half) :
    retainedMinor w hw K half p e ≤ rawForm w K e e * referenceEnergy w hw K half p :=
  Q'.le_trans' _ _ _
    (p.minor_le_full_energy blocks (interfaceExpansion hw K half).weightsNonnegative
      (dressedLower w K e) (dressedLower w K (.unit : PlaquetteExpression half)))
    (Q'.ge_of_eqv (Q'.mul_eqv_congr_right _ _ _ (rawForm_eq_dressedSquareSum w hw K half e)))

/-- A single computed minor controls EVERY rational centering coefficient. -/
theorem retainedMinor_le_every_recentered (p : Pair tree) (e : PlaquetteExpression half) (c : Q') :
    retainedMinor w hw K half p e ≤
      rawForm w K (recentered half e c) (recentered half e c) * referenceEnergy w hw K half p :=
  Q'.le_trans' _ _ _ (Q'.ge_of_eqv (retainedMinor_recentered w hw K half p e c))
    (retainedMinor_le_rawForm w hw K half p (recentered half e c))

theorem floorDenominator_pos (p : Pair tree) : (0 : Q') < referenceEnergy w hw K half p + 1 :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (referenceEnergy_nonnegative w hw K half p))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

/-- Defined without any strict-amplitude premise; it may be zero. -/
def retainedFloor (p : Pair tree) (e : PlaquetteExpression half) : Q' :=
  Q'.divPos (retainedMinor w hw K half p e) (referenceEnergy w hw K half p + 1)
    (floorDenominator_pos w hw K half p)

theorem retainedFloor_bound (p : Pair tree) (e : PlaquetteExpression half) (c : Q') :
    retainedFloor w hw K half p e ≤ rawForm w K (recentered half e c) (recentered half e c) :=
  Q'.divPos_le_of_le_mul _ _ _ (Q'.le_trans' _ _ _
    (retainedMinor_le_every_recentered w hw K half p e c)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (rawForm_nonnegative w hw K _)))

/-- The only strict test is an exact finite rational coefficient inequality. -/
theorem retainedFloor_positive (p : Pair tree) (e : PlaquetteExpression half)
    (h : (0 : Q') < retainedMinor w hw K half p e) : (0 : Q') < retainedFloor w hw K half p e :=
  Q'.divPos_pos _ _ _ h

theorem every_recentered_positive (p : Pair tree) (e : PlaquetteExpression half)
    (h : (0 : Q') < retainedMinor w hw K half p e) (c : Q') :
    (0 : Q') < rawForm w K (recentered half e c) (recentered half e c) :=
  Q'.pos_of_lt_of_le (retainedFloor_positive w hw K half p e h) (retainedFloor_bound w hw K half p e c)

end YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.channelAmplitude
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.channelAmplitude_add
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.channelAmplitude_smul
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.recentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.channelAmplitude_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedMinor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.referenceEnergy
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.referenceEnergy_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedMinor_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedMinor_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.rawForm_eq_dressedSquareSum
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedMinor_le_rawForm
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedMinor_le_every_recentered
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.floorDenominator_pos
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedFloor
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedFloor_bound
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.retainedFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteRetainedMinor.every_recentered_positive
