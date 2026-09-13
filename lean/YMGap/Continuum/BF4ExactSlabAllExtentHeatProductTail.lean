/-
# Computed remainders for full ORIGINAL heat products

Every finite list of original plaquette factors has a cutoff-independent
coefficient bound at fixed w, extent and face list. A common per-face
tolerance is rescaled by the computed product sensitivity; a finite maximum
of the original face cutoffs then bounds the explicit product remainder.

All shared quaternion variables and original heat coefficients remain.
The same theorem applies to the actual lower, interface, upper and complete
slab products. No Haar independence, volume/spacing uniformity, physical
stationary vacuum or spectral gap is inferred.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound
import YMGap.Continuum.PolynomialProductRemainder

namespace YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatTail
open YMGap.Continuum.BF4ExactSlabAllExtentFaceHeatBound
open YMGap.Continuum.PolynomialProductRemainder
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

def heatProductBound (w : Q') (extent : Nat) (ids : List Nat) : Q' :=
  productBound (faceHeatBound w extent) ids

def heatProductSensitivity (w : Q') (extent : Nat) (ids : List Nat) : Q' :=
  productSensitivity (faceHeatBound w extent) ids

theorem heatProductBound_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (extent : Nat) (ids : List Nat) :
    (0 : Q') ≤ heatProductBound w extent ids :=
  productBound_nonnegative _ (faceHeatBound_nonnegative hw extent) ids

theorem heatProductSensitivity_nonnegative {w : Q'} (hw : (0 : Q') ≤ w) (extent : Nat) (ids : List Nat) :
    (0 : Q') ≤ heatProductSensitivity w extent ids :=
  productSensitivity_nonnegative _ (faceHeatBound_nonnegative hw extent) ids

theorem heatProduct_coefficientL1_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) :
    polynomialCoefficientL1 (polynomialProduct (faceHeatPolynomial w K extent) ids) ≤ heatProductBound w extent ids :=
  polynomialProduct_coefficientL1 _ _ (faceHeatBound_nonnegative (Q'.le_of_lt hw0) extent)
    (fun id => faceHeat_coefficientL1_bound hw0 hw1 extent id K) ids

/-- Tolerance is divided by the computed full-list sensitivity plus one. -/
def heatProductTolerance (w : Q') (extent : Nat) (ids : List Nat) (ε : Q') : Q' :=
  HKConv.divPos ε (heatProductSensitivity w extent ids + 1)

theorem heatProductTolerance_pos (w : Q') (extent : Nat) (ids : List Nat) {ε : Q'} (hε : (0 : Q') < ε) :
    (0 : Q') < heatProductTolerance w extent ids ε := HKConv.divPos_pos (CReal.num_pos_of_pos hε)

theorem heatProductTolerance_budget {w : Q'} (hw : (0 : Q') ≤ w) (extent : Nat) (ids : List Nat)
    {ε : Q'} (hε : (0 : Q') < ε) :
    heatProductTolerance w extent ids ε * heatProductSensitivity w extent ids ≤ ε := by
  have hD := heatProductSensitivity_nonnegative hw extent ids
  have hp : (0 : Q') < heatProductSensitivity w extent ids + 1 :=
    lt_of_lt_of_le (by decide : (0 : Q') < 1)
      (Q'.le_trans' _ _ _ (Q'.add_le_self_of_nonneg 1 _ hD) (Q'.le_of_eqv (Q'.add_comm_eqv _ _)))
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_left _ _ _ (Q'.add_le_self_of_nonneg _ 1 Q'.zero_le_one)
      (Q'.le_of_lt (heatProductTolerance_pos w extent ids hε)))
    (Q'.le_of_eqv (HKConv.divPos_mul_eqv (CReal.num_pos_of_pos hp)))

private def faceCutoffMax (w : Q') (extent : Nat) (δ : Q') : List Nat → Nat
  | [] => 0
  | id :: ids => max (faceHeatCutoff w extent id δ) (faceCutoffMax w extent δ ids)

private theorem faceCutoffMax_covers (w : Q') (extent : Nat) (δ : Q') :
    ∀ ids : List Nat, ∀ id, id ∈ ids → faceHeatCutoff w extent id δ ≤ faceCutoffMax w extent δ ids
  | [], _, h => False.elim (List.not_mem_nil h)
  | j :: ids, id, h => by
    rcases List.mem_cons.mp h with he | ht
    · subst id; exact Nat.le_max_left _ _
    · exact Nat.le_trans (faceCutoffMax_covers w extent δ ids id ht) (Nat.le_max_right _ _)

/-- All later product prefixes are controlled beyond this Type-level cutoff. -/
def heatProductCutoff (w : Q') (extent : Nat) (ids : List Nat) (ε : Q') : Nat :=
  faceCutoffMax w extent (heatProductTolerance w extent ids ε) ids

/-- Actual telescoping polynomial on the original shared link carrier. -/
def heatProductRemainder (w : Q') (extent K L : Nat) (ids : List Nat) : RatPoly :=
  productRemainder (faceHeatPolynomial w K extent) (faceHeatPolynomial w (K + L) extent)
    (fun id => faceHeatTail w extent id (K + 1) L) ids

theorem heatProduct_cutoff_append (w : Q') (extent K L : Nat) (ids : List Nat) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w (K + L) extent) ids)
      (polyAdd (polynomialProduct (faceHeatPolynomial w K extent) ids) (heatProductRemainder w extent K L ids)) :=
  polynomialProduct_remainder _ _ _ (fun id => by
    rw [faceHeatPolynomial_cutoff_append]; exact RatPolyCoeffEqv.refl _) ids

theorem heatProductRemainder_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat)
    (hK : heatProductCutoff w extent ids ε ≤ K) :
    polynomialCoefficientL1 (heatProductRemainder w extent K L ids) ≤ ε := by
  have hδ := heatProductTolerance_pos w extent ids hε
  have h := productRemainder_coefficientL1
    (faceHeatPolynomial w K extent) (faceHeatPolynomial w (K + L) extent)
    (fun id => faceHeatTail w extent id (K + 1) L) (faceHeatBound w extent)
    (faceHeatBound_nonnegative (Q'.le_of_lt hw0) extent)
    (fun id => faceHeat_coefficientL1_bound hw0 hw1 extent id K)
    (fun id => faceHeat_coefficientL1_bound hw0 hw1 extent id (K + L))
    (heatProductTolerance w extent ids ε) (Q'.le_of_lt hδ) ids
    (fun id hi => faceHeatTail_small hw0 hw1 extent id _ hδ K L
      (Nat.le_trans (faceCutoffMax_covers w extent _ ids id hi) hK))
  exact Q'.le_trans' _ _ _ h (heatProductTolerance_budget (Q'.le_of_lt hw0) extent ids hε)

theorem heatProductRemainder_haar_small {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (blocks extent : Nat) (ids : List Nat) (ε : Q') (hε : (0 : Q') < ε) (K L : Nat)
    (hK : heatProductCutoff w extent ids ε ≤ K) :
    Q'.abs (quaternionHaar blocks (heatProductRemainder w extent K L ids)) ≤ ε :=
  Q'.le_trans' _ _ _ (quaternionHaar_abs_le_coefficientL1 _ _)
    (heatProductRemainder_small hw0 hw1 extent ids ε hε K L hK)

theorem lowerHeatProduct_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K half : Nat) :
    polynomialCoefficientL1 (lowerHeatProduct w K half) ≤
      heatProductBound w (centralExtent half) (centralLowerFaceIds half) :=
  heatProduct_coefficientL1_bound hw0 hw1 K _ _

theorem interfaceHeatProduct_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K half : Nat) :
    polynomialCoefficientL1 (interfaceHeatProduct w K half) ≤
      heatProductBound w (centralExtent half) (centralFixedFaceIds half) :=
  heatProduct_coefficientL1_bound hw0 hw1 K _ _

theorem upperHeatProduct_bound {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (K half : Nat) :
    polynomialCoefficientL1 (upperHeatProduct w K half) ≤
      heatProductBound w (centralExtent half) (centralUpperFaceIds half) :=
  heatProduct_coefficientL1_bound hw0 hw1 K _ _

end YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductBound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductSensitivity
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductBound_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductSensitivity_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProduct_coefficientL1_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductTolerance
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductTolerance_pos
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductTolerance_budget
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductCutoff
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductRemainder
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProduct_cutoff_append
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductRemainder_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.heatProductRemainder_haar_small
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.lowerHeatProduct_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.interfaceHeatProduct_bound
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentHeatProductTail.upperHeatProduct_bound
