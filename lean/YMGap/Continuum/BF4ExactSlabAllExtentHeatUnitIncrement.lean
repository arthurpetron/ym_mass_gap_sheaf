/-
# Same-object GNS increments of the full original heat-unit sequence

The difference of two actual boundary codes is mapped to the explicit lower
and upper product remainders. Its ORIGINAL finite and cutoff-limit squared
norm is their joint Haar integral with the original interface heat product.
The interface stage is computed independently of the two boundary anchors.
This is a norm identity, not a gap or physical-vacuum stationarity theorem.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentBoundaryCutoffRecoding
open YMGap.Continuum.BF4ExactSlabAllExtentFiniteBoundaryObservable
open YMGap.Continuum.BF4ExactSlabAllExtentCutoffLimitForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem sum_linear {A : Type} (P : A → RatPoly) (c d : A → Q') (s : Q') : ∀ xs : List A,
    RatPolyCoeffEqv (finitePolySum (fun i => polySmul (c i + s * d i) (P i)) xs)
      (polyAdd (finitePolySum (fun i => polySmul (c i) (P i)) xs)
        (polySmul s (finitePolySum (fun i => polySmul (d i) (P i)) xs)))
  | [] => RatPolyCoeffEqv.refl _
  | i :: xs => by
    have hhead := (RatPolyCoeffEqv.add_smul_same (c i) (s * d i) (P i)).symm.trans
      ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_assoc s (d i) (P i)).symm)
    exact (hhead.add (sum_linear P c d s xs)).trans
      ((RatPolyCoeffEqv.four_add_swap _ _ _ _).trans
        ((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.smul_add _ _ _).symm))

private theorem difference_of_remainder (p q r : RatPoly) (h : RatPolyCoeffEqv q (polyAdd p r)) :
    RatPolyCoeffEqv (polyAdd q (polySmul (-1) p)) r :=
  (h.add (RatPolyCoeffEqv.refl _)).trans
    (((RatPolyCoeffEqv.add_comm p r).add (RatPolyCoeffEqv.refl _)).trans
      ((RatPolyCoeffEqv.add_assoc _ _ _).trans
        (((RatPolyCoeffEqv.refl _).add (RatPolyCoeffEqv.add_neg_smul p)).trans (RatPolyCoeffEqv.add_zero r))))

/-- The actual finite-boundary difference, with its cutoff witness retained. -/
def heatUnitIncrement (K L half : Nat) : BoundaryObservable half :=
  (heatUnitCode (K + L) half).add ((heatUnitCode K half).smul (-1))

def lowerHeatRemainder (w : Q') (K L half : Nat) : RatPoly :=
  heatProductRemainder w (centralExtent half) K L (centralLowerFaceIds half)

def upperHeatRemainder (w : Q') (K L half : Nat) : RatPoly :=
  heatProductRemainder w (centralExtent half) K L (centralUpperFaceIds half)

theorem lowerHeatUnitIncrement (w : Q') (S K L half : Nat) (hS : K + L ≤ S) :
    RatPolyCoeffEqv (lowerObservable w S half (heatUnitIncrement K L half).coefficient)
      (lowerHeatRemainder w K L half) := by
  have h := sum_linear (lowerPolynomial w S half) (heatUnitCode (K + L) half).coefficient
    (heatUnitCode K half).coefficient (-1) (centralHalfStates S half)
  have ha := (lowerObservable_extension w hS half (fun _ => 1)).trans (lowerObservable_one w (K + L) half)
  have hb := (lowerObservable_extension w (by omega : K ≤ S) half (fun _ => 1)).trans (lowerObservable_one w K half)
  exact h.trans ((ha.add (hb.smul (-1))).trans
    (difference_of_remainder _ _ _ (heatProduct_cutoff_append w (centralExtent half) K L (centralLowerFaceIds half))))

theorem upperHeatUnitIncrement (w : Q') (S K L half : Nat) (hS : K + L ≤ S) :
    RatPolyCoeffEqv (upperObservable w S half (heatUnitIncrement K L half).coefficient)
      (upperHeatRemainder w K L half) := by
  have h := sum_linear (upperPolynomial w S half) (heatUnitCode (K + L) half).coefficient
    (heatUnitCode K half).coefficient (-1) (centralHalfStates S half)
  have ha := (upperObservable_extension w hS half (fun _ => 1)).trans (upperObservable_one w (K + L) half)
  have hb := (upperObservable_extension w (by omega : K ≤ S) half (fun _ => 1)).trans (upperObservable_one w K half)
  exact h.trans ((ha.add (hb.smul (-1))).trans
    (difference_of_remainder _ _ _ (heatProduct_cutoff_append w (centralExtent half) K L (centralUpperFaceIds half))))

def heatUnitIncrementIntegrand (w : Q') (S K L half : Nat) : RatPoly :=
  polyMul (lowerHeatRemainder w K L half) (polyMul (interfaceHeatProduct w S half) (upperHeatRemainder w K L half))

theorem heatUnitIncrement_finite_norm (w : Q') (S K L half : Nat) (hS : K + L ≤ S) :
    finiteForm w S (heatUnitIncrement K L half) (heatUnitIncrement K L half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length (heatUnitIncrementIntegrand w S K L half) :=
  Q'.eqv_trans _ _ _ (exact_bilinear_eq_haar w S half _ _)
    (haar_of_coeff_eqv _ ((lowerHeatUnitIncrement w S K L half hS).mul
      ((interfaceHeatInsertion_eq_product w S half).mul (upperHeatUnitIncrement w S K L half hS))))

def heatUnitIncrementStage (w : Q') (K L half : Nat) : Nat :=
  max (K + L) (formModulus w (heatUnitIncrement K L half) (heatUnitIncrement K L half))

theorem heatUnitIncrement_limit_norm (w : Q') (K L half : Nat) :
    limitForm w (heatUnitIncrement K L half) (heatUnitIncrement K L half) ≈
      quaternionHaar (boundaryCompleteSlabLinks (centralExtent half)).length
        (heatUnitIncrementIntegrand w (heatUnitIncrementStage w K L half) K L half) :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (finiteForm_stable w _ _ _ (Nat.le_max_right _ _)))
    (heatUnitIncrement_finite_norm w _ K L half (Nat.le_max_left _ _))

end YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.heatUnitIncrement
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.lowerHeatRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.upperHeatRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.lowerHeatUnitIncrement
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.upperHeatUnitIncrement
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.heatUnitIncrementIntegrand
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.heatUnitIncrement_finite_norm
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.heatUnitIncrementStage
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatUnitIncrement.heatUnitIncrement_limit_norm
