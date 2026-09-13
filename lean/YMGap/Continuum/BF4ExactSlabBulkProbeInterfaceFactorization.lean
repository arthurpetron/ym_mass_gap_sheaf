/-
# Four selected ORIGINAL faces times the full spectator interface

The physical central face list is partitioned into the four translated
probe faces and all remaining faces. Products are reordered only through
coefficient identities. The retained unit interface is the full spectator
Gram heat product. The retained scalar interface is exactly

  (2*w^3)^4 * theta(scalarLoop) * scalarLoop * spectatorInterface.

The cutoff and volume remain explicit. No spectator channel is frozen to
its unit leaf, and no positivity of an interacting determinant is assumed.
-/

import YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm
import YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests

namespace YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CayleyParentInj
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.BF4ExactSlabBulkProbeInterface
open YMGap.Continuum.BF4ExactSlabBulkProbeHaarReference
open YMGap.Continuum.BF4ExactSlabBulkProbeSpectatorTests
open YMGap.Continuum.BF4ExactSlabPartialInterfaceHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentSpatialGramPositivity
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabFundamentalRetainedChannels
open YMGap.Continuum.BF4ExactSlabPlaquetteCoordinateChannels
open YMGap.Continuum.BF4ExactSlabLocalSquareExpansion
open YMGap.Continuum.BF4ExactSlabReflectedSquareAlgebra
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry

local notation "blocks" half => List.length (boundaryCompleteSlabLinks (centralExtent half))

def selectedIds (half : Nat) : List Nat := (centralFixedFaceIds half).filter (fun id => decide (id ∈ crossingIds half))
def spectatorIds (half : Nat) : List Nat := (centralFixedFaceIds half).filter (fun id => !(decide (id ∈ crossingIds half)))

theorem fixedIds_nodup (half : Nat) : (centralFixedFaceIds half).Nodup := by
  have hfull : (slabPhysicalFaceEdges (centralExtent half)).Nodup := range_nodup _
  have hparts := (centralSlabFaceIdParts_perm half).symm.nodup hfull
  exact (List.nodup_append.mp (List.nodup_append.mp hparts).1).2.1

theorem selectedIds_perm (half : Nat) : (selectedIds half).Perm (crossingIds half) := by
  apply perm_of_nodup_mem_iff _ _ (List.filter_sublist.nodup (fixedIds_nodup half)) (crossingIds_nodup half)
  intro id
  constructor
  · intro hi
    exact of_decide_eq_true (List.mem_filter.mp hi).2
  · intro hi
    exact List.mem_filter.mpr ⟨crossingIds_fixed hi, decide_eq_true hi⟩

theorem crossing_spectator_partition (half : Nat) :
    (crossingIds half ++ spectatorIds half).Perm (centralFixedFaceIds half) :=
  ((selectedIds_perm half).symm.append (List.Perm.refl _)).trans
    (List.filter_append_perm (fun id => decide (id ∈ crossingIds half)) _)

theorem spectatorIds_fixed {half id : Nat} (hi : id ∈ spectatorIds half) : id ∈ centralFixedFaceIds half :=
  (List.mem_filter.mp hi).1

theorem spectatorIds_unselected {half id : Nat} (hi : id ∈ spectatorIds half) : id ∉ crossingIds half := by
  intro hs
  have h := (List.mem_filter.mp hi).2
  simp only [decide_eq_true hs, Bool.not_true] at h
  cases h

def spectatorInterface (w : Q') (K half : Nat) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K half) (spectatorIds half)

def spectatorExpansion {w : Q'} (hw : (0 : Q') ≤ w) (K half : Nat) :
    LocalSquareExpansion half (spectatorInterface w K half) :=
  LocalSquareExpansion.finiteProduct _ _ (fun _ hi => faceExpansion hw K (spectatorIds_fixed hi))

def selectedProduct (w : Q') (half : Nat) (c : CoordinateChoice) : RatPoly :=
  polynomialProduct (fun id => squareFactor half (choiceWeight w c) (choicePolynomial half id c)) (crossingIds half)

/-- This separates actual factors, not independent replacement variables. -/
theorem retained_factorization (w : Q') (K half : Nat) (c : CoordinateChoice) :
    RatPolyCoeffEqv (retainedPolynomial (w := w) K half (localChoice half c))
      (polyMul (selectedProduct w half c) (spectatorInterface w K half)) := by
  let f := fun id => faceFactor w K half id (localChoice half c id)
  have hs : polynomialProduct f (crossingIds half) = selectedProduct w half c :=
    polynomialProduct_congr _ _ _ (fun id hi => by
      simp only [f, localChoice_selected half c hi, faceFactor])
  have hr : polynomialProduct f (spectatorIds half) = spectatorInterface w K half :=
    polynomialProduct_congr _ _ _ (fun id hi => by
      simp only [f, localChoice_spectator half c (spectatorIds_unselected hi), faceFactor])
  have h := (polynomialProduct_perm f (crossing_spectator_partition half).symm).trans
    (polynomialProduct_append f _ _)
  rw [hs, hr] at h
  exact h

theorem squareFactor_product (half : Nat) (a b : Q') (p q : RatPoly) :
    PaddedPolynomialCoeffEqv (blocks half) (polyMul (squareFactor half a p) (squareFactor half b q))
      (squareFactor half (a*b) (polyMul p q)) :=
  SquareTree.eval_product (centralExtent half) (.term a p) (.term b q)

theorem unit_product (half : Nat) : ∀ ids : List Nat,
    PaddedPolynomialCoeffEqv (blocks half)
      (polynomialProduct (fun _ => squareFactor half 1 polyOne) ids) polyOne
  | [] => .refl _ _
  | _ :: ids => (((LocalSquareExpansion.one half).image.symm).mul (unit_product half ids)).trans
      (.of_coeff (RatPolyCoeffEqv.one_mul _))

theorem scalar_product (w : Q') (half : Nat) (f : Nat → RatPoly) : ∀ ids : List Nat,
    PaddedPolynomialCoeffEqv (blocks half)
      (polynomialProduct (fun id => squareFactor half (BondMovingStep.coeffW w 1) (f id)) ids)
      (squareFactor half (channelWeightPower w ids.length) (polynomialProduct f ids))
  | [] => (LocalSquareExpansion.one half).image
  | _ :: ids => ((PaddedPolynomialCoeffEqv.refl _ _).mul (scalar_product w half f ids)).trans
      (squareFactor_product half _ _ _ _)

theorem selected_unit (w : Q') (half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (selectedProduct w half none) polyOne := unit_product half _

theorem selected_scalar (w : Q') (half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (selectedProduct w half (some (false,false)))
      (squareFactor half (channelWeightPower w 4) (bulkScalar half)) := by
  have h := scalar_product w half (fun id => faceCoordinatePolynomial half id false false) (crossingIds half)
  rw [crossingIds_length, ← bulkScalar_coordinate_pin] at h
  exact h

theorem retained_unit_pin (w : Q') (K half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (retainedPolynomial (w := w) K half (localChoice half none))
      (spectatorInterface w K half) :=
  (PaddedPolynomialCoeffEqv.of_coeff (retained_factorization w K half none)).trans
    (((selected_unit w half).mul (.refl _ _)).trans (.of_coeff (RatPolyCoeffEqv.one_mul _)))

/-- The SAME original fundamental heat weight appears exactly four times. -/
theorem retained_scalar_pin (w : Q') (K half : Nat) :
    PaddedPolynomialCoeffEqv (blocks half) (retainedPolynomial (w := w) K half (localChoice half (some (false,false))))
      (polyMul (squareFactor half (channelWeightPower w 4) (bulkScalar half)) (spectatorInterface w K half)) :=
  (PaddedPolynomialCoeffEqv.of_coeff (retained_factorization w K half (some (false,false)))).trans
    ((selected_scalar w half).mul (.refl _ _))

end YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization

#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.fixedIds_nodup
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.selectedIds_perm
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.crossing_spectator_partition
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.spectatorIds_fixed
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.spectatorIds_unselected
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.spectatorExpansion
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.retained_factorization
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.squareFactor_product
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.unit_product
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.scalar_product
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.selected_unit
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.selected_scalar
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.retained_unit_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkProbeInterfaceFactorization.retained_scalar_pin
