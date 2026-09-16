/-
# Original spatial factors on the two endpoint slices

A temporal sweep leaves every spatial face factor literally unchanged.
Arbitrary signed character sums and repeated faces are permitted. If the
face bases lie on the two endpoint slices, every remaining polynomial
variable is a spatial link on those slices. Off-carrier links retain the
existing identity fallback, so locality needs no physical-face premise.

The heat-factor utility pins any selected face list to its ORIGINAL
polynomial product at sweep zero. These are exact algebra and support
facts for two-layer Haar gluing, not an independence or contraction claim.
-/

import YMGap.Continuum.BF4ExactSlabTemporalSweep
import YMGap.Continuum.BF4ExactSlabFaceLinkLocality

namespace YMGap.Continuum.BF4ExactSlabSpatialSliceFactors

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactSlabTemporalSweep
open YMGap.Continuum.BF4ExactSlabTemporalSweepCharacters
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactPhysicalCenteredVacuumHaarResummation
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local notation "blocks" extent => List.length (boundaryCompleteSlabLinks extent)

/-- Spatial links on exactly the two endpoint time slices. -/
def EndpointLink (start : Nat) (link : Z4Link) : Prop :=
  link.2 ≠ .x3 ∧ (link.1.2.2.2 = start ∨ link.1.2.2.2 = start+2)

private theorem finiteSum_congr {A : Type} (f g : A → RatPoly)
    (h : ∀ a, f a = g a) : ∀ xs : List A, finitePolySum f xs = finitePolySum g xs
  | [] => rfl
  | a::xs => by simp only [finitePolySum, h a, finiteSum_congr f g h xs]

/-- A spatial factor is never selected by any temporal sweep. -/
theorem spatialFactors_swept_eq_zero (extent cut : Nat) : ∀ fs : List FaceFactor,
    (∀ f, f ∈ fs → (dirsOf f.1.2).2 ≠ .x3) →
    sweptProduct extent cut fs = sweptProduct extent 0 fs
  | [], _ => rfl
  | f::fs, hsp => by
      have hn : ¬ Swept cut f.1 := fun h => hsp f List.mem_cons_self h.1
      have hf : factor (sweptCharacter extent cut) f = factor (sweptCharacter extent 0) f := by
        apply finiteSum_congr
        intro term
        simp only [sweptCharacter, if_neg hn, if_neg (not_swept_zero f.1)]
      change polyMul (factor (sweptCharacter extent cut) f) (sweptProduct extent cut fs) =
        polyMul (factor (sweptCharacter extent 0) f) (sweptProduct extent 0 fs)
      rw [hf, spatialFactors_swept_eq_zero extent cut fs (fun g hg => hsp g (List.mem_cons_of_mem f hg))]

/-- Each literal edge of a spatial face has the face's base time. -/
theorem spatial_face_edge (face : Z4Plaq) (hsp : (dirsOf face.2).2 ≠ .x3)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    link.2 ≠ .x3 ∧ link.1.2.2.2 = face.1.2.2.2 := by
  rcases face with ⟨⟨x,y,z,t⟩,plane⟩
  cases plane <;> simp only [dirsOf] at hsp <;> try exact False.elim (hsp rfl)
  all_goals simp only [edgesOf, dirsOf, addE, List.mem_cons, List.not_mem_nil, or_false] at hl
  all_goals rcases hl with rfl | rfl | rfl | rfl
  all_goals exact ⟨(by intro h; cases h), rfl⟩

/-- Actual original endpoint factors have no middle-slice variables. -/
theorem endpointFactors_local (extent start : Nat) (fs : List FaceFactor)
    (hsp : ∀ f, f ∈ fs → (dirsOf f.1.2).2 ≠ .x3)
    (ht : ∀ f, f ∈ fs → f.1.1.2.2.2 = start ∨ f.1.1.2.2.2 = start+2) :
    BlockLocal (blocks extent) (fun b => EndpointLink start (correctedSlabLinkAt extent b))
      (sweptProduct extent 0 fs) := by
  rw [swept_zero]
  apply BlockLocal.fold
  intro f hf
  apply BlockLocal.finiteSum
  intro term _
  apply BlockLocal.smul
  apply BlockLocal.character
  intro monomial hm block hb hn
  apply face_scalar_local extent f.1 monomial hm block hb
  intro he
  have hg := spatial_face_edge f.1 (hsp f hf) (correctedSlabLinkAt extent block) he
  apply hn
  refine ⟨hg.1, ?_⟩
  rw [hg.2]
  exact ht f hf

theorem endpointFactors_swept_local (extent start cut : Nat) (fs : List FaceFactor)
    (hsp : ∀ f, f ∈ fs → (dirsOf f.1.2).2 ≠ .x3)
    (ht : ∀ f, f ∈ fs → f.1.1.2.2.2 = start ∨ f.1.1.2.2.2 = start+2) :
    BlockLocal (blocks extent) (fun b => EndpointLink start (correctedSlabLinkAt extent b))
      (sweptProduct extent cut fs) := by
  rw [spatialFactors_swept_eq_zero extent cut fs hsp]
  exact endpointFactors_local extent start fs hsp ht

/-- Selected ORIGINAL heat factors, retaining list order and multiplicity. -/
def heatFactors (w : Q') (K extent : Nat) (ids : List Nat) : List FaceFactor :=
  ids.map (fun id => (slabPlaquetteAt extent id, heatWeights w K))

private theorem finiteSum_map {A B : Type} (f : B → RatPoly) (g : A → B) : ∀ xs : List A,
    finitePolySum f (xs.map g) = finitePolySum (fun a => f (g a)) xs
  | [] => rfl
  | a::xs => by simp only [List.map_cons, finitePolySum, finiteSum_map f g xs]

/-- No new heat action: this is literal equality with the existing product. -/
theorem heatFactors_zero (w : Q') (K extent : Nat) : ∀ ids : List Nat,
    sweptProduct extent 0 (heatFactors w K extent ids) =
      polynomialProduct (faceHeatPolynomial w K extent) ids
  | [] => rfl
  | id::ids => by
      change polyMul _ (sweptProduct extent 0 (heatFactors w K extent ids)) =
        polyMul _ (polynomialProduct _ ids)
      rw [heatFactors_zero w K extent ids]
      congr 1
      simp only [factor, heatWeights, finiteSum_map, sweptCharacter, if_neg (not_swept_zero _)]
      rfl

end YMGap.Continuum.BF4ExactSlabSpatialSliceFactors

#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.EndpointLink
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.spatialFactors_swept_eq_zero
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.spatial_face_edge
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.endpointFactors_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.endpointFactors_swept_local
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.heatFactors
#print axioms YMGap.Continuum.BF4ExactSlabSpatialSliceFactors.heatFactors_zero
