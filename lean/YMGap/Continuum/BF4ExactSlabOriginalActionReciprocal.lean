/-
# The reciprocal of the ORIGINAL interacting slab action limit

The proved finite-action certificate supplies a computed positive tail of
the existing CReal representative. Its shifted samples have explicit
regularity; their reciprocal limit multiplies the ORIGINAL action to one.
Both positive lower and upper reciprocal bounds are computed from the nome
and finite slab. No auxiliary positive law or uniform spectral estimate.
-/

import YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor
import YMGap.Continuum.PositiveRationalCauchyReciprocal

namespace YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentActionFloorCertificate
open YMGap.Continuum.BF4ExactSlabOriginalActionStrictFloor
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half : Nat)

/-- Explicit regularity of the existing original CReal, before any reciprocal. -/
theorem action_approx_close (epsilon : Q') (he : (0 : Q') < epsilon) (p q : Nat)
    (hp : epsilon.den ≤ p) (hq : epsilon.den ≤ q) :
    (fullActionLimit w hw0 hw1 half).approx p ≤ (fullActionLimit w hw0 hw1 half).approx q + epsilon ∧
    (fullActionLimit w hw0 hw1 half).approx q ≤ (fullActionLimit w hw0 hw1 half).approx p + epsilon := by
  let c := heatProductHaarCauchy w hw0 hw1
    (boundaryCompleteSlabLinks (centralExtent half)).length
    (centralExtent half) (slabPhysicalFaceEdges (centralExtent half))
  rcases Nat.le_total p q with hpq | hqp
  · exact CReal.QMhat_directed _ c epsilon he p q hpq hp
  · exact (CReal.QMhat_directed _ c epsilon he q p hqp hq).symm

def positiveSample (n : Nat) : Q' :=
  (fullActionLimit w hw0 hw1 half).approx
    ((fullActionFloorCertificate w hw0 hw1 half).index + n)

theorem positiveSample_floor (n : Nat) :
    (fullActionFloorCertificate w hw0 hw1 half).floor ≤ positiveSample w hw0 hw1 half n :=
  (fullActionFloorCertificate w hw0 hw1 half).approx_ge hw0 hw1 _ (Nat.le_add_right _ _)

def positiveSampleCauchy : CReal.QCauchy (positiveSample w hw0 hw1 half) where
  M epsilon := epsilon.den
  bound := fun epsilon he p q hp hq => action_approx_close w hw0 hw1 half epsilon he
    ((fullActionFloorCertificate w hw0 hw1 half).index + p)
    ((fullActionFloorCertificate w hw0 hw1 half).index + q)
    (Nat.le_trans hp (Nat.le_add_left _ _)) (Nat.le_trans hq (Nat.le_add_left _ _))

theorem positiveSample_converges :
    CReal.ConvergesTo (fun n => CReal.ofQ' (positiveSample w hw0 hw1 half n))
      (fullActionLimit w hw0 hw1 half) := by
  intro epsilon he
  refine ⟨epsilon.den, fun n hn => ⟨epsilon.den, fun m hm => ?_⟩⟩
  exact action_approx_close w hw0 hw1 half epsilon he _ m
    (Nat.le_trans hn (Nat.le_add_left _ _)) hm

theorem sampleLimit_eq_action : CReal.Equiv
    (CReal.ofQ'CauchySeq _ (positiveSampleCauchy w hw0 hw1 half)) (fullActionLimit w hw0 hw1 half) :=
  CReal.Equiv_of_ofQ'_limit_close (CReal.convergesTo_ofQ'CauchySeq _ _)
    (positiveSample_converges w hw0 hw1 half)
    (fun _ he => ⟨0, fun _ _ =>
      ⟨Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he), Q'.add_le_self_of_nonneg _ _ (Q'.le_of_lt he)⟩⟩)

def actionReciprocal : CReal :=
  PositiveRationalCauchyReciprocal.value (positiveSampleCauchy w hw0 hw1 half)
    (fullActionFloorCertificate w hw0 hw1 half).floor
    (fullActionFloorCertificate w hw0 hw1 half).floor_pos
    (positiveSample_floor w hw0 hw1 half)

/-- Reciprocal-stream modulus, exposed as data rather than a Prop witness. -/
def reciprocalModulus (epsilon : Q') : Nat :=
  (PositiveRationalCauchyReciprocal.reciprocalCauchy (positiveSampleCauchy w hw0 hw1 half)
    (fullActionFloorCertificate w hw0 hw1 half).floor
    (fullActionFloorCertificate w hw0 hw1 half).floor_pos
    (positiveSample_floor w hw0 hw1 half)).M epsilon

def reciprocalCeiling : Q' := Q'.recipPos
  (fullActionFloorCertificate w hw0 hw1 half).floor
  (fullActionFloorCertificate w hw0 hw1 half).floor_pos

theorem reciprocalCeiling_pos : (0 : Q') < reciprocalCeiling w hw0 hw1 half := Q'.recipPos_pos _ _

theorem actionReciprocal_approx_pos (n : Nat) : (0 : Q') < (actionReciprocal w hw0 hw1 half).approx n :=
  PositiveRationalCauchyReciprocal.value_approx_pos _ _ _ _ n

theorem actionReciprocal_approx_le (n : Nat) :
    (actionReciprocal w hw0 hw1 half).approx n ≤ reciprocalCeiling w hw0 hw1 half :=
  PositiveRationalCauchyReciprocal.value_approx_le _ _ _ _ n

def actionCeiling : Q' :=
  heatProductBound w (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) + 1

theorem actionCeiling_pos (w : Q') (hw0 : (0 : Q') < w) (half : Nat) :
    (0 : Q') < actionCeiling w half :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1)
    (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ (heatProductBound_nonnegative (Q'.le_of_lt hw0) _ _))
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))

theorem action_approx_le (n : Nat) : (fullActionLimit w hw0 hw1 half).approx n ≤ actionCeiling w half := by
  unfold fullActionLimit
  rw [heatProductHaarLimit_approx]
  exact Q'.le_trans' _ _ _ (Q'.le_abs_self _)
    (Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
      (Q'.le_trans' _ _ _ (heatProduct_coefficientL1_bound hw0 hw1 _ _ _)
        (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)))

def reciprocalFloor : Q' := Q'.recipPos (actionCeiling w half) (actionCeiling_pos w hw0 half)

theorem reciprocalFloor_pos : (0 : Q') < reciprocalFloor w hw0 half := Q'.recipPos_pos _ _

theorem actionReciprocal_approx_ge (n : Nat) :
    reciprocalFloor w hw0 half ≤ (actionReciprocal w hw0 hw1 half).approx n :=
  PositiveRationalCauchyReciprocal.value_approx_ge _ _ _ _ _ (actionCeiling_pos w hw0 half)
    (fun _ => action_approx_le w hw0 hw1 half _) n

/-- Exact cancellation against the ORIGINAL action, not just a new limit. -/
theorem action_mul_reciprocal : CReal.Equiv
    (CReal.mul (fullActionLimit w hw0 hw1 half) (actionReciprocal w hw0 hw1 half)) CReal.cone :=
  (Pivot2.mul_congr_left (sampleLimit_eq_action w hw0 hw1 half).symm).trans
    (PositiveRationalCauchyReciprocal.mul_value _ _ _ _)

end YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal

#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.action_approx_close
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.positiveSample
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.positiveSample_floor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.positiveSampleCauchy
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.positiveSample_converges
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.sampleLimit_eq_action
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionReciprocal
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.reciprocalModulus
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.reciprocalCeiling
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.reciprocalCeiling_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionReciprocal_approx_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionReciprocal_approx_le
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionCeiling
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionCeiling_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.action_approx_le
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.reciprocalFloor
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.reciprocalFloor_pos
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.actionReciprocal_approx_ge
#print axioms YMGap.Continuum.BF4ExactSlabOriginalActionReciprocal.action_mul_reciprocal
