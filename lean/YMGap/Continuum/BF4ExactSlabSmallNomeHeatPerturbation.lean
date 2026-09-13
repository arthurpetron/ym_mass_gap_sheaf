/-
# Cutoff-independent perturbation of the ORIGINAL shared-link heat product

Every factor is the original finite heat prefix on its original variables.
Its positive-label remainder has the computed first-character bound delta_i.
The list recursions compute B = product_i (1+delta_i) and E = B-1 without
subtraction. They bound the product and its explicit telescoping remainder
at every representation cutoff, under the finite list of small-nome guards.

Inserting any actual polynomial gives an exact bare-Haar-plus-error identity
with error at most L1(p)*E. The final declarations apply this to the SAME
lower action in the four-moment plaquette determinant. No independent-face
Haar factorization, numerical smallness certificate, determinant sign,
completed nontriviality or volume/spacing-uniform claim is supplied.
-/

import YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
import YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
import YMGap.Continuum.PolynomialProductRemainder

namespace YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabSmallNomeFaceRemainder
open YMGap.Continuum.BF4ExactSlabPlaquetteHeatDressedMinor
open YMGap.Continuum.PolynomialProductRemainder
open YMGap.Continuum.SU2HeatCharacterPolynomialMajorant
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

def faceDelta (w : Q') (extent id : Nat) : Q' := firstTailBound w (faceScalar extent id)

def productBudget (w : Q') (extent : Nat) (ids : List Nat) : Q' :=
  productBound (fun id => 1 + faceDelta w extent id) ids

/-- E(empty)=0; E(i::ids)=E(ids)+delta_i*B(ids). -/
def remainderBudget (w : Q') (extent : Nat) : List Nat → Q'
  | [] => 0
  | id :: ids => remainderBudget w extent ids + faceDelta w extent id * productBudget w extent ids

theorem productBudget_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (extent : Nat) (ids : List Nat) :
    (0 : Q') ≤ productBudget w extent ids :=
  productBound_nonnegative _ (fun id => Q'.zero_le_add _ _ Q'.zero_le_one
    (firstTailBound_nonnegative hw (faceScalar extent id))) ids

theorem remainderBudget_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (extent : Nat) :
    ∀ ids : List Nat, (0 : Q') ≤ remainderBudget w extent ids
  | [] => Q'.le_refl' 0
  | _ :: ids => Q'.zero_le_add _ _ (remainderBudget_nonnegative hw extent ids)
    (Q'.mul_nonneg _ _ (firstTailBound_nonnegative hw _) (productBudget_nonnegative hw extent ids))

theorem one_add_remainderBudget (w : Q') (extent : Nat) :
    ∀ ids : List Nat, 1 + remainderBudget w extent ids ≈ productBudget w extent ids
  | [] => by change (1 + (0 : Q')) ≈ 1; decide
  | _ :: ids =>
    Q'.eqv_trans _ _ _ (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _))
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (one_add_remainderBudget w extent ids))
        (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr_right _ _ _ (Q'.eqv_symm (Q'.one_mul_eqv _)))
          (Q'.eqv_symm (ExpNeg.add_mul_eqv _ _ _))))

def productPerturbation (w : Q') (extent K : Nat) (ids : List Nat) : RatPoly :=
  productRemainder (fun _ => polyOne) (faceHeatPolynomial w K extent)
    (fun id => faceHeatTail w extent id 1 K) ids

private theorem unitProduct : ∀ ids : List Nat,
    RatPolyCoeffEqv (polynomialProduct (fun _ => polyOne) ids) polyOne
  | [] => RatPolyCoeffEqv.refl _
  | _ :: ids => ((unitProduct ids).mul_left polyOne).trans (RatPolyCoeffEqv.one_mul _)

theorem product_eq_one_add (w : Q') (extent K : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyAdd polyOne (productPerturbation w extent K ids)) :=
  (polynomialProduct_remainder _ _ _ (fun id => faceHeat_eq_one_add w extent id K) ids).trans
    ((unitProduct ids).add (RatPolyCoeffEqv.refl _))

theorem product_coefficientL1_small {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (extent K : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → firstRatio w (faceScalar extent id) ≤ HalfPow.half) →
    polynomialCoefficientL1 (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤ productBudget w extent ids
  | [], _ => by change polynomialCoefficientL1 polyOne ≤ (1 : Q'); decide
  | id :: ids, hsmall => Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
    (Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _ _ (faceHeat_coefficientL1_small hw0 hw1 extent id K (hsmall id List.mem_cons_self))
        (polynomialCoefficientL1_nonnegative _))
      (Q'.mul_le_mul_of_nonneg_left _ _ _
        (product_coefficientL1_small hw0 hw1 extent K ids (fun j hj => hsmall j (List.mem_cons_of_mem id hj)))
        (Q'.zero_le_add _ _ Q'.zero_le_one (firstTailBound_nonnegative hw0 _))))

theorem productPerturbation_coefficientL1 {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (extent K : Nat) : ∀ ids : List Nat,
    (∀ id, id ∈ ids → firstRatio w (faceScalar extent id) ≤ HalfPow.half) →
    polynomialCoefficientL1 (productPerturbation w extent K ids) ≤ remainderBudget w extent ids
  | [], _ => Q'.le_refl' 0
  | id :: ids, hsmall => by
    have htail := fun j hj => hsmall j (List.mem_cons_of_mem id hj)
    have hfirst := Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le polyOne _)
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.one_mul_eqv _))
        (productPerturbation_coefficientL1 hw0 hw1 extent K ids htail))
    have hlast := Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_right _ _ _ (faceTail_coefficientL1 hw0 hw1 extent id K (hsmall id List.mem_cons_self))
          (polynomialCoefficientL1_nonnegative _))
        (Q'.mul_le_mul_of_nonneg_left _ _ _ (product_coefficientL1_small hw0 hw1 extent K ids htail)
          (firstTailBound_nonnegative hw0 _)))
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (coefficientL1_add _ _)) (ExpNeg.add_le_add2 hfirst hlast)

/-- Computed error on the same shared-variable Haar carrier. -/
def momentError (w : Q') (extent K : Nat) (ids : List Nat) (blocks : Nat) (p : RatPoly) : Q' :=
  quaternionHaar blocks (polyMul p (productPerturbation w extent K ids))

theorem moment_eq_reference_add_error (w : Q') (extent K : Nat) (ids : List Nat) (blocks : Nat) (p : RatPoly) :
    quaternionHaar blocks (polyMul p (polynomialProduct (faceHeatPolynomial w K extent) ids)) ≈
      quaternionHaar blocks p + momentError w extent K ids blocks p :=
  Q'.eqv_trans _ _ _
    (haar_of_coeff_eqv blocks (((product_eq_one_add w extent K ids).mul_left p).trans (RatPolyCoeffEqv.mul_add_right _ _ _)))
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _)
      (Q'.add_eqv_congr' (haar_of_coeff_eqv blocks (RatPolyCoeffEqv.mul_one p)) (Q'.eqv_refl _)))

theorem momentError_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (extent K : Nat) (ids : List Nat) (blocks : Nat) (p : RatPoly)
    (hsmall : ∀ id, id ∈ ids → firstRatio w (faceScalar extent id) ≤ HalfPow.half) :
    Q'.abs (momentError w extent K ids blocks p) ≤ polynomialCoefficientL1 p * remainderBudget w extent ids :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 blocks _)
    (Q'.le_trans' _ _ _ (polynomialCoefficientL1_mul_le _ _)
      (Q'.mul_le_mul_of_nonneg_left _ _ _ (productPerturbation_coefficientL1 hw0 hw1 extent K ids hsmall)
        (polynomialCoefficientL1_nonnegative p)))

def lowerBudget (w : Q') : Q' := remainderBudget w 1 (centralLowerFaceIds 0)

def lowerMomentError (w : Q') (K : Nat) (p : RatPoly) : Q' :=
  momentError w 1 K (centralLowerFaceIds 0) 116 p

theorem lowerMoment_eq (w : Q') (K : Nat) (p : RatPoly) :
    heatMoment w K p ≈ quaternionHaar 116 p + lowerMomentError w K p :=
  moment_eq_reference_add_error w 1 K (centralLowerFaceIds 0) 116 p

theorem lowerMomentError_bound {w : Q'} (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (K : Nat) (p : RatPoly)
    (hsmall : ∀ id, id ∈ centralLowerFaceIds 0 → firstRatio w (faceScalar 1 id) ≤ HalfPow.half) :
    Q'.abs (lowerMomentError w K p) ≤ polynomialCoefficientL1 p * lowerBudget w :=
  momentError_bound hw0 hw1 1 K (centralLowerFaceIds 0) 116 p hsmall

end YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation

#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.faceDelta
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.productBudget
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.remainderBudget
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.productBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.remainderBudget_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.one_add_remainderBudget
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.productPerturbation
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.product_eq_one_add
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.product_coefficientL1_small
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.productPerturbation_coefficientL1
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.momentError
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.moment_eq_reference_add_error
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.momentError_bound
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.lowerBudget
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.lowerMomentError
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.lowerMoment_eq
#print axioms YMGap.Continuum.BF4ExactSlabSmallNomeHeatPerturbation.lowerMomentError_bound
