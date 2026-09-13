/-
# ORIGINAL embedded-interior integral equals the smaller-slab integral

The actual bulk link map transports every original heat factor and arbitrary
supported polynomial insertion together. Finite Haar preservation removes
only unused target variables. Thus the interior-weighted target integral is
exactly the original smaller-slab numerator at every common cutoff, and the
identity survives cutoff removal. The interior partition is the original
smaller-slab partition, not a new or assumed normalization.

This is NOT equality with the full enlarged action: its exterior factors
remain in the boundary-response numerator. No decay or padding limit.
-/

import YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding

namespace YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabAllExtentActionLimit
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabBulkHaarEmbedding
open YMGap.Continuum.BF4ExactSlabBulkActionDressing
open YMGap.Continuum.BF4ExactSlabBulkBoundaryResponse
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionArbitraryHaarBlockReflection
open YMGap.Continuum.SU2QuaternionHaarBlockEmbedding
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem imageSum {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (finitePolySum f xs)) (finitePolySum g xs)
  | [], _ => .nil
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyAdd (f a) (finitePolySum f xs))) _
      rw [E.polynomial_add]
      exact (h a List.mem_cons_self).append (imageSum E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem imageProduct {A : Type} {source target : Nat} (E : BlockEmbedding source target)
    (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → QuaternionPrefixPolynomialEqv target (E.polynomial (f a)) (g a)) →
    QuaternionPrefixPolynomialEqv target (E.polynomial (polynomialProduct f xs)) (polynomialProduct g xs)
  | [], _ => E.polynomial_one_prefix
  | a :: xs, h => by
      change QuaternionPrefixPolynomialEqv target (E.polynomial (polyMul (f a) (polynomialProduct f xs))) _
      rw [E.polynomial_mul]
      exact (h a List.mem_cons_self).mul (imageProduct E f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem sum_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (finitePolySum f xs)
  | [] => fun _ ht => False.elim (List.not_mem_nil ht)
  | a :: xs => supported_add (h a) (sum_support f h xs)

private theorem product_support {A : Type} {blocks : Nat} (f : A → RatPoly)
    (h : ∀ a, SupportedQuaternionBlocks blocks (f a)) :
    ∀ xs : List A, SupportedQuaternionBlocks blocks (polynomialProduct f xs)
  | [] => supported_one blocks
  | a :: xs => supported_polyMul (h a) (product_support f h xs)

theorem heatFactor_pin (w : Q') (K : Nat) {half padding id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges (centralExtent half)) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      ((slabEmbedding half padding).polynomial (faceHeatPolynomial w K (centralExtent half) id))
      (geometricHeat w K (centralExtent (half+padding)) (shiftFace padding padding (slabPlaquetteAt (centralExtent half) id))) := by
  apply imageSum
  intro spin _
  unfold localFaceTerm
  rw [BlockEmbedding.polynomial_smul]
  exact (character_pin (half := half) (padding := padding) (slabPlaquetteAt_mem hi) spin).smul _

theorem fullHeatProduct_pin (w : Q') (K half padding : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      ((slabEmbedding half padding).polynomial (fullHeatProduct w K half)) (embeddedHeat w K half padding) := by
  rw [embeddedHeat_geometric]
  exact imageProduct (slabEmbedding half padding) _ _ _ (fun _ hi => heatFactor_pin w K hi)

theorem embeddedHeat_supported (w : Q') (K half padding : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length (embeddedHeat w K half padding) := by
  rw [embeddedHeat_geometric]
  exact product_support _ (fun _ => sum_support _ (fun _ => supported_smul (original_character_support _ _ _) _) _) _

theorem interiorMoment_prefix {w : Q'} {K half padding : Nat} {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent (half+padding))).length q) :
    interiorMoment w K half padding p ≈ interiorMoment w K half padding q :=
  quaternionHaar_prefixPolynomialEqv _ (h.mul (.refl _ _))
    (supported_polyMul hp (embeddedHeat_supported w K half padding))
    (supported_polyMul hq (embeddedHeat_supported w K half padding))

/-- The SAME supported insertion and ORIGINAL heat action move together. -/
theorem interiorMoment_small (w : Q') (K half padding : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) :
    interiorMoment w K half padding ((slabEmbedding half padding).polynomial p) ≈
      numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) p K := by
  have himage : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks (centralExtent (half+padding))).length
      ((slabEmbedding half padding).polynomial (polyMul p (fullHeatProduct w K half)))
      (polyMul ((slabEmbedding half padding).polynomial p) (embeddedHeat w K half padding)) := by
    rw [BlockEmbedding.polynomial_mul]
    exact (QuaternionPrefixPolynomialEqv.refl _ _).mul (fullHeatProduct_pin w K half padding)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ himage
      ((slabEmbedding half padding).polynomial_supported _)
      (supported_polyMul ((slabEmbedding half padding).polynomial_supported p) (embeddedHeat_supported w K half padding))))
    (haar_embedding half padding _ (supported_polyMul hp (fullHeatProduct_supported w K half)))

theorem interiorSequence_small (w : Q') (K half padding : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) :
    interiorSequence w half padding ((slabEmbedding half padding).polynomial p) K ≈
      numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) p K :=
  Q'.eqv_trans _ _ _ (interiorMoment_numerator w K half padding _) (interiorMoment_small w K half padding p hp)

theorem interiorSequence_one (w : Q') (K half padding : Nat) :
    interiorSequence w half padding polyOne K ≈
      numerator w (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) polyOne K :=
  Q'.eqv_trans _ _ _ (interiorMoment_numerator w K half padding polyOne)
    (Q'.eqv_trans _ _ _
      (Q'.eqv_symm (interiorMoment_prefix (w := w) (K := K) (half := half) (padding := padding)
        (slabEmbedding half padding).polynomial_one_prefix ((slabEmbedding half padding).polynomial_supported polyOne) (supported_one _)))
      (interiorMoment_small w K half padding polyOne (supported_one _)))

variable (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (half padding : Nat)

theorem interiorLimit_small (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks (centralExtent half)).length p) :
    CReal.Equiv (interiorMomentLimit w hw0 hw1 half padding ((slabEmbedding half padding).polynomial p))
      (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks (centralExtent half)).length (centralExtent half)
        (slabPhysicalFaceEdges (centralExtent half)) p) :=
  CReal.Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ _) (numerator_converges w hw0 hw1 _ _ _ p)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (interiorSequence_small w K half padding p hp) epsilon he⟩)

/-- The interior partition is exactly the ORIGINAL smaller-slab partition. -/
theorem interiorPartition_small :
    CReal.Equiv (interiorMomentLimit w hw0 hw1 half padding polyOne) (fullActionLimit w hw0 hw1 half) :=
  (CReal.Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ polyOne)
    (numerator_converges w hw0 hw1 _ _ _ polyOne)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (interiorSequence_one w K half padding) epsilon he⟩)).trans
      (numeratorLimit_one w hw0 hw1 _ _ _)

end YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin

#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.heatFactor_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.fullHeatProduct_pin
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.embeddedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorMoment_prefix
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorMoment_small
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorSequence_small
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorSequence_one
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorLimit_small
#print axioms YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin.interiorPartition_small
