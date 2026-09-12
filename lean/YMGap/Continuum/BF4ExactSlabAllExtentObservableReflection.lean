/-
# Literal reflection of the complete original observable at every odd extent

The same face weights, signed coefficients and bounded labelling carrier are
retained. Physical face reflection is an involution and exchanges the lower
and upper enumerations. The all-spin plaquette pin therefore lifts through
their products and sums to a coefficient-sensitive reflection identity.

This is stronger than equality of isolated Haar values: every supported
spectator can be retained when the identity is integrated. Positivity and
the physical transfer are separate consequences, not hypotheses here.
-/

import YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection

namespace YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentPlaquetteReflection
open YMGap.Continuum.BF4ExactSlabSpatialChannelReflection
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionTranslationPolynomialImages
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneReflectedFactor
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

theorem reflected_lower_ids (half : Nat) :
    ((centralLowerFaceIds half).map (slabFaceReflectId (centralExtent half))).Perm (centralUpperFaceIds half) := by
  have h := (centralUpperFaceIds_reflection_perm half).map (slabFaceReflectId (centralExtent half))
  have hi : ((centralUpperFaceIds half).map (slabFaceReflectId (centralExtent half))).map
      (slabFaceReflectId (centralExtent half)) = centralUpperFaceIds half := by
    rw [List.map_map]
    have hm : (centralUpperFaceIds half).map
        (fun id => slabFaceReflectId (centralExtent half) (slabFaceReflectId (centralExtent half) id)) =
        (centralUpperFaceIds half).map (fun id => id) := by
      apply List.map_congr_left
      intro id hid
      exact slabFaceReflectId_involutive (mem_centralUpperFaceIds.mp hid).1
    exact hm.trans (List.map_id _)
  change (((centralUpperFaceIds half).map (slabFaceReflectId (centralExtent half))).map
    (slabFaceReflectId (centralExtent half))).Perm _ at h
  rw [hi] at h
  exact h.symm

theorem weightedFace_reflection (w : Q') (K extent : Nat) (state : EdgeLabelling) {id : Nat}
    (hi : id ∈ slabPhysicalFaceEdges extent) :
    ReflectionImage extent (weightedFacePolynomial w K extent state id)
      (weightedFacePolynomial w K extent (fun j => state (slabFaceReflectId extent j)) (slabFaceReflectId extent id)) := by
  unfold weightedFacePolynomial
  dsimp only
  rw [slabFaceReflectId_involutive hi, slabPlaquetteAt_slabFaceReflectId hi]
  exact (plaquette_character_reflection (slabPlaquetteAt_mem hi) (state id)).smul _

private theorem reflected_fold {A : Type} (extent : Nat) (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → ReflectionImage extent (f a) (g a)) →
      ReflectionImage extent (polynomialProduct f xs) (polynomialProduct g xs)
  | [], _ => ReflectionImage.one extent
  | a :: xs, h => (h a List.mem_cons_self).mul
      (reflected_fold extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- The original upper product is the reflected original lower product,
with all heat weights and labels unchanged. -/
theorem lowerPolynomial_reflection (w : Q') (K half : Nat) (state : EdgeLabelling) :
    ReflectionImage (centralExtent half) (lowerPolynomial w K half state) (upperPolynomial w K half state) := by
  let upper := weightedFacePolynomial w K (centralExtent half)
    (fun j => state (slabFaceReflectId (centralExtent half) j))
  have h := reflected_fold (centralExtent half) (weightedFacePolynomial w K (centralExtent half) state)
    (fun id => upper (slabFaceReflectId (centralExtent half) id)) (centralLowerFaceIds half)
    (fun _ hi => weightedFace_reflection w K (centralExtent half) state (mem_centralLowerFaceIds.mp hi).1)
  have hp := polynomialProduct_perm upper (reflected_lower_ids half)
  simp only [polynomialProduct, List.foldr_map] at hp
  exact h.trans (.of_coeff hp)

private theorem reflected_sum {A : Type} (extent : Nat) (f g : A → RatPoly) : ∀ xs : List A,
    (∀ a, a ∈ xs → ReflectionImage extent (f a) (g a)) →
      ReflectionImage extent (finitePolySum f xs) (finitePolySum g xs)
  | [], _ => ReflectionImage.zero extent
  | a :: xs, h => (h a List.mem_cons_self).add
      (reflected_sum extent f g xs (fun b hb => h b (List.mem_cons_of_mem a hb)))

/-- Coefficient-sensitive literal reflection of the SAME complete signed
boundary observable, every odd extent and every finite cutoff. -/
theorem lowerObservable_reflection (w : Q') (K half : Nat) (c : EdgeLabelling → Q') :
    ReflectionImage (centralExtent half) (lowerObservable w K half c) (upperObservable w K half c) :=
  reflected_sum (centralExtent half) _ _ _
    (fun state _ => (lowerPolynomial_reflection w K half state).smul (c state))

end YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection

#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection.reflected_lower_ids
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection.weightedFace_reflection
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection.lowerPolynomial_reflection
#print axioms YMGap.Continuum.BF4ExactSlabAllExtentObservableReflection.lowerObservable_reflection
