/-
# Reflection invariance of the ORIGINAL interacting polynomial functional

The actual oriented plaquette reflection permutes the complete physical face
list, with every original heat coefficient retained. Its full product is
therefore reflection invariant on the supported quaternion carrier. Product
Haar invariance gives the same identity with any supported insertion; the
original numerator limit and SAME Z preserve it.

This is invariance of the concrete finite-slab functional, not a transfer
operator or inter-slab stationarity theorem.
-/

import YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity

namespace YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabAllExtentHeatUnit
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity
open YMGap.Continuum.BF4ExactSlabPolynomialInsertionLimit
open YMGap.Continuum.BF4ExactSlabPolynomialExpectation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

theorem character_reflection_id {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) (spin : Nat) :
    ReflectionImage extent (characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent id)).scalar spin)
      (characterPolynomial (correctedSlabPlaquettePolynomial extent (slabPlaquetteAt extent (slabFaceReflectId extent id))).scalar spin) := by
  rw [slabPlaquetteAt_slabFaceReflectId hi]
  exact plaquette_character_reflection (slabPlaquetteAt_mem hi) spin

private theorem reflected_sum {A : Type} (extent : Nat) (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → ReflectionImage extent (f a) (g a)) →
      ReflectionImage extent (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => ReflectionImage.zero extent
  | a :: xs, h => (h a List.mem_cons_self).add
      (reflected_sum extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

private theorem reflected_product {A : Type} (extent : Nat) (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → ReflectionImage extent (f a) (g a)) →
      ReflectionImage extent (polynomialProduct f xs) (polynomialProduct g xs)
  | [], _ => ReflectionImage.one extent
  | a :: xs, h => (h a List.mem_cons_self).mul
      (reflected_product extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

theorem faceHeat_reflection (w : Q') (K : Nat) {extent id : Nat} (hi : id ∈ slabPhysicalFaceEdges extent) :
    ReflectionImage extent (faceHeatPolynomial w K extent id) (faceHeatPolynomial w K extent (slabFaceReflectId extent id)) :=
  reflected_sum extent _ _ _ (fun spin _ => (character_reflection_id hi spin).smul _)

theorem fullHeatProduct_reflection (w : Q') (K half : Nat) :
    ReflectionImage (centralExtent half) (fullHeatProduct w K half) (fullHeatProduct w K half) := by
  let f := faceHeatPolynomial w K (centralExtent half)
  have h := reflected_product (centralExtent half) f (fun id => f (slabFaceReflectId (centralExtent half) id))
    (slabPhysicalFaceEdges (centralExtent half)) (fun _ hi => faceHeat_reflection w K hi)
  have hp := polynomialProduct_perm f (slabFaceReflectId_range_perm (centralExtent half))
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans (PaddedPolynomialCoeffEqv.of_coeff hp)

theorem upper_reflection {half : Nat} : ∀ e : PlaquetteExpression half,
    ReflectionImage (centralExtent half) (upper e) (lower e)
  | .unit => ReflectionImage.one _
  | .character _ hi spin => by
      have h := character_reflection_id (slabFaceReflectId_physical (mem_centralLowerFaceIds.mp hi).1) spin
      rw [slabFaceReflectId_involutive (mem_centralLowerFaceIds.mp hi).1] at h
      exact h
  | .add p q => (upper_reflection p).add (upper_reflection q)
  | .mul p q => (upper_reflection p).mul (upper_reflection q)
  | .smul c p => (upper_reflection p).smul c

private theorem haar_reflection_image {extent : Nat} {p q : RatPoly} (h : ReflectionImage extent p q)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q) :
    quaternionHaar (boundaryCompleteSlabLinks extent).length p ≈ quaternionHaar (boundaryCompleteSlabLinks extent).length q :=
  Q'.eqv_trans _ _ _ (Q'.eqv_symm (quaternionHaar_reflectCorrectedSlabPolynomial extent p hp))
    (PaddedPolynomialCoeffEqv.haar h (reflectCorrectedSlabPolynomial_support extent p) hq)

variable (w : Q') (K half : Nat)

local notation "blocks" => List.length (boundaryCompleteSlabLinks (centralExtent half))
local notation "faces" => slabPhysicalFaceEdges (centralExtent half)

theorem numerator_reflection_image {p q : RatPoly} (h : ReflectionImage (centralExtent half) p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    numerator w blocks (centralExtent half) faces p K ≈ numerator w blocks (centralExtent half) faces q K :=
  haar_reflection_image (h.mul (fullHeatProduct_reflection w K half))
    (supported_polyMul hp (fullHeatProduct_supported w K half))
    (supported_polyMul hq (fullHeatProduct_supported w K half))

theorem numerator_padded_congr {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    numerator w blocks (centralExtent half) faces p K ≈ numerator w blocks (centralExtent half) faces q K :=
  (h.mul (PaddedPolynomialCoeffEqv.refl blocks (fullHeatProduct w K half))).haar
    (supported_polyMul hp (fullHeatProduct_supported w K half))
    (supported_polyMul hq (fullHeatProduct_supported w K half))

theorem expectation_reflection_image (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {p q : RatPoly} (h : ReflectionImage (centralExtent half) p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    CReal.Equiv (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q) :=
  Pivot2.mul_congr_left (CReal.Equiv_of_ofQ'_limit_close
    (numerator_converges w hw0 hw1 blocks (centralExtent half) faces p)
    (numerator_converges w hw0 hw1 blocks (centralExtent half) faces q)
    (fun epsilon he => ⟨0, fun k _ => eqv_close (numerator_reflection_image w k half h hp hq) epsilon he⟩))

theorem expectation_padded_congr (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {p q : RatPoly} (h : PaddedPolynomialCoeffEqv blocks p q)
    (hp : SupportedQuaternionBlocks blocks p) (hq : SupportedQuaternionBlocks blocks q) :
    CReal.Equiv (expectation w hw0 hw1 half p) (expectation w hw0 hw1 half q) :=
  Pivot2.mul_congr_left (CReal.Equiv_of_ofQ'_limit_close
    (numerator_converges w hw0 hw1 blocks (centralExtent half) faces p)
    (numerator_converges w hw0 hw1 blocks (centralExtent half) faces q)
    (fun epsilon he => ⟨0, fun k _ => eqv_close (numerator_padded_congr w k half h hp hq) epsilon he⟩))

/-- The literal full action is invariant with EVERY supported polynomial observable. -/
theorem expectation_reflection_invariant (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (p : RatPoly) (hp : SupportedQuaternionBlocks blocks p) :
    CReal.Equiv (expectation w hw0 hw1 half (reflectCorrectedSlabPolynomial (centralExtent half) p))
      (expectation w hw0 hw1 half p) :=
  (expectation_reflection_image w half hw0 hw1 (PaddedPolynomialCoeffEqv.refl _ _) hp
    (reflectCorrectedSlabPolynomial_support _ _)).symm

end YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance

#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.character_reflection_id
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.faceHeat_reflection
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.fullHeatProduct_reflection
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.upper_reflection
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.numerator_reflection_image
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.numerator_padded_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.expectation_reflection_image
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.expectation_padded_congr
#print axioms YMGap.Continuum.BF4ExactSlabPolynomialReflectionInvariance.expectation_reflection_invariant
