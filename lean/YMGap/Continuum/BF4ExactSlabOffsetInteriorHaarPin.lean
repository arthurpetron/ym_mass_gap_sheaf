/-
# The off-center ORIGINAL interior action has the original source integral

All source heat factors and the observable insertion move through the SAME
injective link map. Exact product-Haar preservation gives the smaller-slab
numerator at every representation cutoff. The identity passes to the
existing explicit-modulus cutoff limits, including the source partition.
No equality with the fully interacting larger slab is asserted: the actual
exterior factors remain in OffsetAction.boundaryNumerator.
-/

import YMGap.Continuum.BF4ExactSlabOffsetAction
import YMGap.Continuum.BF4ExactSlabBulkInteriorHaarPin

namespace YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
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
open YMGap.Continuum.BF4ExactSlabOffsetHaarEmbedding
open YMGap.Continuum.BF4ExactSlabOffsetAction
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

theorem heatFactor_pin (P : Placement) (w : Q') (K : Nat) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges P.source) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial (faceHeatPolynomial w K P.source id)) (faceHeatPolynomial w K P.target (P.faceId id)) := by
  apply imageSum
  intro spin _
  unfold localFaceTerm
  rw [BlockEmbedding.polynomial_smul]
  have h := P.character_pin (slabPlaquetteAt_mem hi) spin
  rw [← P.faceId_pin hi] at h
  exact h.smul _

theorem fullHeatProduct_pin (P : Placement) (w : Q') (K : Nat) :
    QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial (fullHeatProduct w K P.half)) (embeddedHeat P w K) :=
  imageProduct P.embedding _ _ _ (fun _ hi => heatFactor_pin P w K hi)

theorem embeddedHeat_supported (P : Placement) (w : Q') (K : Nat) :
    SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length (embeddedHeat P w K) :=
  product_support _ (fun _ => sum_support _ (fun _ => supported_smul (original_character_support _ _ _) _) _) _

theorem interiorMoment_prefix (P : Placement) (w : Q') (K : Nat) {p q : RatPoly}
    (h : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.target).length q) :
    interiorMoment P w K p ≈ interiorMoment P w K q :=
  Q'.eqv_trans _ _ _ (interiorMoment_pin P w K p)
    (Q'.eqv_trans _ _ _ (quaternionHaar_prefixPolynomialEqv _ (h.mul (.refl _ _))
      (supported_polyMul hp (embeddedHeat_supported P w K))
      (supported_polyMul hq (embeddedHeat_supported P w K)))
      (Q'.eqv_symm (interiorMoment_pin P w K q)))

/-- Off-center placement moves the SAME insertion and heat action together. -/
theorem interiorMoment_small (P : Placement) (w : Q') (K : Nat) (p : RatPoly)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) :
    interiorMoment P w K (P.embedding.polynomial p) ≈
      numerator w (boundaryCompleteSlabLinks P.source).length P.source (slabPhysicalFaceEdges P.source) p K := by
  have himage : QuaternionPrefixPolynomialEqv (boundaryCompleteSlabLinks P.target).length
      (P.embedding.polynomial (polyMul p (fullHeatProduct w K P.half)))
      (polyMul (P.embedding.polynomial p) (embeddedHeat P w K)) := by
    rw [BlockEmbedding.polynomial_mul]
    exact (QuaternionPrefixPolynomialEqv.refl _ _).mul (fullHeatProduct_pin P w K)
  exact Q'.eqv_trans _ _ _ (interiorMoment_pin P w K _)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_prefixPolynomialEqv _ himage
      (P.embedding.polynomial_supported _)
      (supported_polyMul (P.embedding.polynomial_supported p) (embeddedHeat_supported P w K))))
      (P.haar _ (supported_polyMul hp (fullHeatProduct_supported w K P.half))))

theorem interiorMoment_one (P : Placement) (w : Q') (K : Nat) :
    interiorMoment P w K polyOne ≈
      numerator w (boundaryCompleteSlabLinks P.source).length P.source (slabPhysicalFaceEdges P.source) polyOne K :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (interiorMoment_prefix P w K P.embedding.polynomial_one_prefix
    (P.embedding.polynomial_supported polyOne) (supported_one _)))
    (interiorMoment_small P w K polyOne (supported_one _))

def interiorLimit (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) (p : RatPoly) : CReal :=
  numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks P.target).length P.target (interiorIds P) p

theorem interiorLimit_small (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : RatPoly) (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks P.source).length p) :
    Equiv (interiorLimit P w hw0 hw1 (P.embedding.polynomial p))
      (numeratorLimit w hw0 hw1 (boundaryCompleteSlabLinks P.source).length P.source (slabPhysicalFaceEdges P.source) p) :=
  Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ _) (numerator_converges w hw0 hw1 _ _ _ p)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (interiorMoment_small P w K p hp) epsilon he⟩)

theorem interiorPartition_small (P : Placement) (w : Q') (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    Equiv (interiorLimit P w hw0 hw1 polyOne) (fullActionLimit w hw0 hw1 P.half) :=
  (Equiv_of_ofQ'_limit_close (numerator_converges w hw0 hw1 _ _ _ polyOne)
    (numerator_converges w hw0 hw1 _ _ _ polyOne)
    (fun epsilon he => ⟨0, fun K _ => eqv_close (interiorMoment_one P w K) epsilon he⟩)).trans
      (numeratorLimit_one w hw0 hw1 _ _ _)

end YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin

#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.heatFactor_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.fullHeatProduct_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.embeddedHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorMoment_prefix
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorMoment_small
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorMoment_one
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorLimit
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorLimit_small
#print axioms YMGap.Continuum.BF4ExactSlabOffsetInteriorHaarPin.interiorPartition_small
