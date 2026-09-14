/-
# Original minimal moments reduce to the literal fundamental tube integral

The full original spin-network integrand loses only its spin-zero factors.
For accepted minimal mixed moments the occupied list is the proved literal
tube; for accepted partition moments it is empty. These are exact signed
Haar identities, not a change of measure or an evaluation by cardinality.
-/

import YMGap.Continuum.BF4ExactSlabMinimalMixedTube
import YMGap.Continuum.QPolyHaarPositiveSubstitution

namespace YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabPositiveFaceCutMinimum
open YMGap.Continuum.BF4ExactSlabShiftedProbeTubeGeometry
open YMGap.Continuum.BF4ExactSlabShiftedProbeCenterCharge
open YMGap.Continuum.BF4ExactSlabMinimalMomentContinuation
open YMGap.Continuum.BF4ExactSlabMinimalMixedTube
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ThreeCutSaturation

local infix:50 " ≈ " => Q'.eqv
local notation "N" margin => List.length (boundaryCompleteSlabLinks (responseExtent margin))

def fundamentalCharacter (extent : Nat) (face : Z4Plaq) : RatPoly :=
  characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 1

theorem binary_character_product {A : Type} (characters : A → Nat → RatPoly)
    (labels : A → Nat) (hzero : ∀ a, characters a 0 = polyOne) :
    ∀ faces : List A, (∀ f, f ∈ faces → labels f ≤ 1) →
    RatPolyCoeffEqv (polynomialProduct (fun f => characters f (labels f)) faces)
      (polynomialProduct (fun f => characters f 1) (faces.filter (fun f => decide (0 < labels f))))
  | [], _ => RatPolyCoeffEqv.refl polyOne
  | f::fs, h => by
    have hb := h f List.mem_cons_self
    have ht := binary_character_product characters labels hzero fs
      (fun g hg => h g (List.mem_cons_of_mem f hg))
    by_cases hz : labels f = 0
    · simp only [List.filter_cons, hz, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ↓reduceIte]
      change RatPolyCoeffEqv (polyMul (characters f (labels f)) _) _
      rw [hz,hzero]
      exact ((RatPolyCoeffEqv.refl polyOne).mul ht).trans (RatPolyCoeffEqv.one_mul _)
    · have ho : labels f = 1 := by omega
      simp only [List.filter_cons, ho, Nat.zero_lt_succ, decide_true, ↓reduceIte]
      change RatPolyCoeffEqv (polyMul (characters f (labels f)) _) _
      rw [ho]
      exact ht.mul_left (characters f 1)

theorem fundamental_integrand (extent : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges extent → state id ≤ 1) :
    RatPolyCoeffEqv (exactCorrectedSlabSpinNetworkIntegrand extent state)
      (polynomialProduct (fundamentalCharacter extent) (positiveFaces extent state)) :=
  binary_character_product
    (fun f spin => characterPolynomial (correctedSlabPlaquettePolynomial extent f).scalar spin)
    (fun f => state ((boundaryCompleteSlabPlaquettes extent).idxOf f)) (fun _ => rfl) _
    (fun _ hf => hs _ (List.mem_range.mpr (List.idxOf_lt_length_of_mem hf)))

def tubeFaceList (margin : Nat) : List Z4Plaq :=
  sliceFace margin 0 :: (tubeSides margin ++ [sliceFace margin 3])

theorem tubeFaceList_physical (margin : Nat) :
    ∀ f, f ∈ tubeFaceList margin → f ∈ boundaryCompleteSlabPlaquettes (responseExtent margin) := by
  intro f hf
  rcases List.mem_cons.mp hf with he | hf
  · exact he ▸ slice_physical margin ⟨0,by decide⟩
  · rcases List.mem_append.mp hf with hf | hf
    · exact tubeSides_physical margin f hf
    · have he := List.mem_singleton.mp hf
      exact he ▸ slice_physical margin ⟨3,by decide⟩

def bareTubePolynomial (margin : Nat) : RatPoly :=
  polynomialProduct (fundamentalCharacter (responseExtent margin)) (tubeFaceList margin)

def bareTubeMoment (margin : Nat) : Q' := quaternionHaar (N margin) (bareTubePolynomial margin)

theorem endpoints_product {A : Type} (f : A → RatPoly) (left right : A) (faces : List A) :
    RatPolyCoeffEqv (polyMul (polyMul (f left) (f right)) (polynomialProduct f faces))
      (polynomialProduct f (left :: (faces ++ [right]))) := by
  have ht := (polynomialProduct_append f faces [right]).trans
    ((RatPolyCoeffEqv.refl _).mul (RatPolyCoeffEqv.mul_one (f right)))
  exact (RatPolyCoeffEqv.mul_assoc _ _ _).trans
    ((RatPolyCoeffEqv.refl _).mul ((RatPolyCoeffEqv.mul_comm _ _).trans ht.symm))

theorem accepted_mixed_moment_pin (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin true true state = true) :
    moment margin true true state ≈ bareTubeMoment margin := by
  have hp := (fundamental_integrand _ state hs).trans
    (polynomialProduct_perm _ (accepted_mixed_support_perm margin state hs hw hc))
  apply haar_of_coeff
  change RatPolyCoeffEqv (polyMul (insertion margin true true) _) _
  unfold insertion
  rw [lower_shifted_probe_pin,upper_shifted_probe_pin]
  exact ((RatPolyCoeffEqv.refl _).mul hp).trans
    (endpoints_product (fundamentalCharacter (responseExtent margin)) _ _ _)

theorem accepted_partition_one (margin : Nat) (state : EdgeLabelling)
    (hs : ∀ id, id ∈ slabPhysicalFaceEdges (responseExtent margin) → state id ≤ 1)
    (hw : ∀ f, f ∈ positiveFaces (responseExtent margin) state → window margin f = true)
    (hc : momentCheck margin false false state = true) : moment margin false false state ≈ 1 := by
  have hp := fundamental_integrand _ state hs
  rw [accepted_partition_empty margin state hs hw hc] at hp
  have h : RatPolyCoeffEqv (polyMul (insertion margin false false)
      (exactCorrectedSlabSpinNetworkIntegrand (responseExtent margin) state)) polyOne :=
    ((RatPolyCoeffEqv.one_mul polyOne).mul hp).trans (RatPolyCoeffEqv.one_mul polyOne)
  exact Q'.eqv_trans _ _ _ (haar_of_coeff h) (QPolyHaarPositiveSubstitution.haar_one _)

end YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin

#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.binary_character_product
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.fundamental_integrand
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.tubeFaceList_physical
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.bareTubeMoment
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.endpoints_product
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.accepted_mixed_moment_pin
#print axioms YMGap.Continuum.BF4ExactSlabMinimalTubeMomentPin.accepted_partition_one
