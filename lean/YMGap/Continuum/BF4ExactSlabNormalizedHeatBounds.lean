/-
# Identity-normalized ORIGINAL finite heat-product bounds

The literal SU(2) character prefix has its maximum at the identity: each
nonnegative heat coefficient multiplies a character bounded above by its
dimension. Its identity value is at least the vacuum term 1. Here the
original cutoff K always means the prefix of length K+1.

At the already computed finiteCutoff, every original face factor is positive.
The entire shared-link action polynomial can therefore be multiplied by the
explicit reciprocal of H_K(1)^ids.length. Its pointwise values and its SAME
finite Haar integral lie between the positive rational
finiteFloor(w)^ids.length / H_K(1)^ids.length and 1. No factor is discarded or
independently integrated; repeated and overlapping face labels are allowed.

This is identity normalization, not normalization by the partition function.
The lower bound depends on the number of factors. No algebraic Certificate,
entropy estimate, uniform-volume bound, H1, OS gap or continuum claim follows
here. Pointwise arguments use actual unit assignments, never Haar-only
equivalence.
-/

import YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder
import YMGap.Continuum.HeatKernelNodeQuad

namespace YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.RepTheory.RationalQuaternion (UnitNorm)
open YMGap.Continuum.BondMovingStep (coeffW coeffW_nonneg coeffW_zero)
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity (SupportedQuaternionBlocks)
open YMGap.Continuum.SU2QuaternionWilsonWeightSOS (evalRatPoly_one evalRatPoly_smul)
open YMGap.Continuum.SU2AllLabelPointwiseHeatCorridor
open YMGap.Continuum.SU2PointwiseHeatStrictFloor (finiteCutoff finiteFloor finiteFloor_pos)
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm (faceHeatPolynomial)
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization (polynomialProduct)
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit (heatProductHaar)
open YMGap.Continuum.BF4ExactSlabHeatPointwiseFloor
open YMGap.Continuum.BF4ExactSlabOriginalHeatHaarOrder (faceScalar_box)
open YMGap.Continuum.QuaternionHaarFiniteProductOrder (environment)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry (boundaryCompleteSlabLinks)

local infix:50 " ≈ " => Q'.eqv

private theorem term_le_at_one {w x : Q'} (hw0 : (0 : Q') ≤ w)
    (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) (label : Nat) :
    pointwiseHeatTerm w x label ≤ pointwiseHeatTerm w 1 label := by
  have hu : Cheb.U label x ≤ Cheb.U label 1 :=
    Q'.le_trans' _ _ _ (ChebU.absU_le label x hxhi hxlo).1
      (Q'.ge_of_eqv (HeatKernelNodeQuad.U_at_one label))
  exact Q'.mul_le_mul_of_nonneg_left _ _ _ hu (coeffW_nonneg hw0 label)

/-- All finite original prefixes, including the empty one, are maximized
at the identity class coordinate. No upper-nome or late-cutoff guard is needed. -/
theorem standardPointwiseHeatPartial_le_at_one {w x : Q'}
    (hw0 : (0 : Q') ≤ w) (hxlo : (-1 : Q') ≤ x) (hxhi : x ≤ (1 : Q')) (N : Nat) :
    standardPointwiseHeatPartial w x N ≤ standardPointwiseHeatPartial w 1 N :=
  CharacterTail.finSum_le_termwise _ _ (term_le_at_one hw0 hxlo hxhi) N

/-- Identity value for the literal inclusive cutoff K. -/
def identityHeat (w : Q') (K : Nat) : Q' := standardPointwiseHeatPartial w 1 (K+1)

/-- The vacuum term contributes exactly 1 and all other identity terms are nonnegative. -/
theorem one_le_identityHeat {w : Q'} (hw0 : (0 : Q') ≤ w) (K : Nat) :
    (1 : Q') ≤ identityHeat w K := by
  have hz : standardPointwiseHeatPartial w 1 1 ≈ (1 : Q') := by
    change (0 : Q') + coeffW w 0 * Cheb.U 0 1 ≈ 1
    rw [coeffW_zero]
    decide
  have hn (label : Nat) : (0 : Q') ≤ pointwiseHeatTerm w 1 label :=
    Q'.mul_nonneg _ _ (coeffW_nonneg hw0 label) (HeatKernelNodeQuad.U_at_one_nonneg label)
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hz)
    (finSum_monotone_of_nonneg _ hn 1 (K+1) (Nat.succ_le_succ (Nat.zero_le K)))

theorem identityHeat_positive {w : Q'} (hw0 : (0 : Q') ≤ w) (K : Nat) :
    (0 : Q') < identityHeat w K :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < 1) (one_le_identityHeat hw0 K)

/-- The actual face polynomial, evaluated on the SAME shared unit-link assignment. -/
theorem faceHeatPolynomial_le_identityHeat {w : Q'} (hw0 : (0 : Q') ≤ w)
    (K extent id : Nat) (qs : Nat → UnitNorm) :
    evalRatPoly (environment qs) (faceHeatPolynomial w K extent id) ≤ identityHeat w K :=
  Q'.le_trans' _ _ _ (Q'.le_of_eqv (eval_faceHeatPolynomial_eqv w K extent id (environment qs)))
    (standardPointwiseHeatPartial_le_at_one hw0
      (faceScalar_box extent id qs).1 (faceScalar_box extent id qs).2 (K+1))

/-- The product of the identity values, with the ORIGINAL factor count. -/
def productCeiling (w : Q') (K : Nat) (ids : List Nat) : Q' :=
  identityHeat w K ^ ids.length

theorem productCeiling_positive {w : Q'} (hw0 : (0 : Q') ≤ w) (K : Nat) (ids : List Nat) :
    (0 : Q') < productCeiling w K ids :=
  HKPos.pow_pos (identityHeat_positive hw0 K) ids.length

/-- Multiplying positive ORIGINAL factors preserves the identity ceiling;
the late-cutoff floor supplies positivity before multiplication. -/
theorem heatProduct_le_productCeiling {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (qs : Nat → UnitNorm) (hK : finiteCutoff w ≤ K+1) : ∀ ids : List Nat,
    evalRatPoly (environment qs) (polynomialProduct (faceHeatPolynomial w K extent) ids)
      ≤ productCeiling w K ids
  | [] => Q'.le_of_eqv (evalRatPoly_one (environment qs))
  | id::ids => by
      have hf := finiteFloor_le_eval_faceHeatPolynomial hw0 hw1 K extent id (environment qs) hK
        (faceScalar_box extent id qs).1 (faceScalar_box extent id qs).2
      have hf0 := Q'.le_trans' _ _ _ (Q'.le_of_lt (finiteFloor_pos hw0 hw1)) hf
      have ht := heatProduct_le_productCeiling hw0 hw1 K extent qs hK ids
      exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (evalRatPoly_mul (environment qs) _ _))
        (HKConv.mul_le_mul' hf0 (Q'.le_of_lt (productCeiling_positive (Q'.le_of_lt hw0) K ids))
          (faceHeatPolynomial_le_identityHeat (Q'.le_of_lt hw0) K extent id qs) ht)

/-- The same ceiling holds under the original finite shared-link Haar functional. -/
theorem heatProductHaar_le_productCeiling {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) :
    heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K ≤ productCeiling w K ids :=
  QuaternionHaarFiniteProductOrder.haar_upper_bound _ _
    (BF4ExactSlabFaceLinkLocality.heatProduct_supported w K extent ids) _
    (fun qs => heatProduct_le_productCeiling hw0 hw1 K extent qs hK ids)

/-- Computable positive reciprocal of the ORIGINAL identity ceiling. -/
def normalizingFactor (w : Q') (hw0 : (0 : Q') < w) (K : Nat) (ids : List Nat) : Q' :=
  Q'.recipPos (productCeiling w K ids) (productCeiling_positive (Q'.le_of_lt hw0) K ids)

theorem normalizingFactor_positive {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) (ids : List Nat) :
    (0 : Q') < normalizingFactor w hw0 K ids := Q'.recipPos_pos _ _

private theorem normalization_cancel {w : Q'} (hw0 : (0 : Q') < w) (K : Nat) (ids : List Nat) :
    normalizingFactor w hw0 K ids * productCeiling w K ids ≈ (1 : Q') :=
  Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
    (Q'.mul_recipPos_eqv _ (productCeiling_positive (Q'.le_of_lt hw0) K ids))

/-- The original action polynomial divided by H_K(1)^number_of_factors.
This is not division by its Haar partition. -/
def normalizedHeatProduct (w : Q') (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) : RatPoly :=
  polySmul (normalizingFactor w hw0 K ids) (polynomialProduct (faceHeatPolynomial w K extent) ids)

/-- The explicit ratio finiteFloor(w)^number_of_factors / H_K(1)^number_of_factors. -/
def normalizedFloor (w : Q') (hw0 : (0 : Q') < w) (K : Nat) (ids : List Nat) : Q' :=
  normalizingFactor w hw0 K ids * productFloor w ids

theorem normalizedFloor_positive {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K : Nat) (ids : List Nat) : (0 : Q') < normalizedFloor w hw0 K ids :=
  Q'.mul_pos (normalizingFactor_positive hw0 K ids) (productFloor_pos hw0 hw1 ids)

theorem normalizedHeatProduct_supported (w : Q') (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length
      (normalizedHeatProduct w hw0 K extent ids) := by
  intro t ht
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
  exact BF4ExactSlabFaceLinkLocality.heatProduct_supported w K extent ids s hs

/-- Strictly positive lower data and unit ceiling for the literal normalized
polynomial on every explicit assignment; all original action factors remain. -/
theorem normalizedHeatProduct_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) (qs : Nat → UnitNorm) :
    normalizedFloor w hw0 K ids ≤ evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) ∧
      evalRatPoly (environment qs) (normalizedHeatProduct w hw0 K extent ids) ≤ (1 : Q') := by
  have he := evalRatPoly_smul (environment qs) (normalizingFactor w hw0 K ids)
    (polynomialProduct (faceHeatPolynomial w K extent) ids)
  have hr := Q'.le_of_lt (normalizingFactor_positive hw0 K ids)
  have hl := productFloor_le_eval_heatProduct hw0 hw1 K extent (environment qs) hK ids
    (fun id _ => faceScalar_box extent id qs)
  have hu := heatProduct_le_productCeiling hw0 hw1 K extent qs hK ids
  exact ⟨Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hl hr) (Q'.ge_of_eqv he),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv he)
      (Q'.le_trans' _ _ _ (Q'.mul_le_mul_of_nonneg_left _ _ _ hu hr)
        (Q'.le_of_eqv (normalization_cancel hw0 K ids)))⟩

/-- Normalization is literal scalar multiplication of the original partition. -/
theorem normalizedHeatProductHaar_pin (w : Q') (hw0 : (0 : Q') < w)
    (K extent : Nat) (ids : List Nat) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids) ≈
      normalizingFactor w hw0 K ids *
        heatProductHaar w (boundaryCompleteSlabLinks extent).length extent ids K :=
  BF4CompactActionCPOrder.quaternionHaar_polySmul _ _ _

/-- The same original finite Haar integral obeys the same explicit normalized window. -/
theorem normalizedHeatProductHaar_bounds {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (ids : List Nat) (hK : finiteCutoff w ≤ K+1) :
    normalizedFloor w hw0 K ids ≤
        quaternionHaar (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids) ∧
      quaternionHaar (boundaryCompleteSlabLinks extent).length (normalizedHeatProduct w hw0 K extent ids)
        ≤ (1 : Q') :=
  ⟨QuaternionHaarFiniteProductOrder.haar_lower_bound _ _
      (normalizedHeatProduct_supported w hw0 K extent ids) _
      (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).1),
    QuaternionHaarFiniteProductOrder.haar_upper_bound _ _
      (normalizedHeatProduct_supported w hw0 K extent ids) _
      (fun qs => (normalizedHeatProduct_bounds hw0 hw1 K extent ids hK qs).2)⟩

end YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds

#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.standardPointwiseHeatPartial_le_at_one
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.identityHeat
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.one_le_identityHeat
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.identityHeat_positive
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.faceHeatPolynomial_le_identityHeat
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.productCeiling
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.productCeiling_positive
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.heatProduct_le_productCeiling
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.heatProductHaar_le_productCeiling
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizingFactor
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizingFactor_positive
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedHeatProduct
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedFloor
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedHeatProduct_supported
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedHeatProduct_bounds
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedHeatProductHaar_pin
#print axioms YMGap.Continuum.BF4ExactSlabNormalizedHeatBounds.normalizedHeatProductHaar_bounds
