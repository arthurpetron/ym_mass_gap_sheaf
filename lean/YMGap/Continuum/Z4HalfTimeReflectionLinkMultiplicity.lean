/-
# Reflection invariance of corrected-slab SU(2) link multiplicities

The corrected slab incidence reindex supplies a permutation of the external
spin list at every reflected link.  The fusion-complete permutation theorem
turns that geometric permutation into exact equality of the production
`6*K` local multiplicity.  Multiplying over the reflection-permuted link list
then gives invariance of the complete link factor and, together with the
already proved face factor theorem, of one corrected-slab spin-foam term.
-/

import YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
import YMGap.Continuum.Z4FusionMultiplicityPermutationLift

namespace YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FusionMultiplicityPermutationLift
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4UnitCubeEnumerationParity

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Corrected-slab degree and boundedness -/

theorem slabIncidentPlaqIds_length_eq_incidentFaces
    (extent : Nat) (link : Z4Link) :
    (slabIncidentPlaqIds extent link).length =
      ((boundaryCompleteSlabPlaquettes extent).filter fun plaquette =>
        decide (link ∈ edgesOf plaquette)).length := by
  unfold slabIncidentPlaqIds
  rw [List.length_map]
  let entries := enumerate (boundaryCompleteSlabPlaquettes extent)
  let predicate : Z4Plaq → Bool := fun plaquette =>
    decide (link ∈ edgesOf plaquette)
  have hmapped :
      (entries.filter (predicate ∘ Prod.snd)).map Prod.snd =
        (boundaryCompleteSlabPlaquettes extent).filter predicate := by
    rw [← List.filter_map, enumerate_map_snd]
  change (entries.filter (predicate ∘ Prod.snd)).length = _
  rw [← List.length_map Prod.snd, hmapped]

theorem slabIncidentPlaqIds_length_le_six
    (extent : Nat) (link : Z4Link) :
    (slabIncidentPlaqIds extent link).length ≤ 6 := by
  obtain ⟨vertex, direction⟩ := link
  rw [slabIncidentPlaqIds_length_eq_incidentFaces]
  have hnodup :
      ((boundaryCompleteSlabPlaquettes extent).filter fun plaquette =>
        decide ((vertex, direction) ∈ edgesOf plaquette)).Nodup :=
    List.filter_sublist.nodup
      (boundaryCompleteSlabPlaquettes_nodup extent)
  have hsubset : ∀ plaquette,
      plaquette ∈
          ((boundaryCompleteSlabPlaquettes extent).filter fun face =>
            decide ((vertex, direction) ∈ edgesOf face)) →
        plaquette ∈ edgePlaqs vertex direction := by
    intro plaquette hplaquette
    have hincidence : (vertex, direction) ∈ edgesOf plaquette := by
      simpa only [decide_eq_true_eq] using
        (List.mem_filter.mp hplaquette).2
    exact edge_complete plaquette vertex direction hincidence
  have hlength := nodup_subset_length_le _ _ hnodup hsubset
  rw [edgePlaqs_length] at hlength
  exact hlength

theorem slabIncidentSpins_bounded
    {K extent : Nat} {physical : Nat → Nat}
    (hbounded : SlabFaceLabellingBounded K extent physical)
    (link : Z4Link) :
    SpinsBounded K
      ((slabIncidentPlaqIds extent link).map physical) := by
  intro spin hspin
  obtain ⟨id, hid, hidSpin⟩ := List.mem_map.mp hspin
  rw [← hidSpin]
  exact hbounded id (slabIncidentPlaqId_physical hid)

/-! ## 2. One link and the full link product -/

def slabExplicitLinkMultiplicity
    (K extent : Nat) (physical : Nat → Nat)
    (link : Z4Link) : Nat :=
  let spins := (slabIncidentPlaqIds extent link).map physical
  explicitValenceMultiplicity (linkAuxiliaryCutoff K) spins.length
    (externalSpinsOfList spins)

/-- The exact local production multiplicity is preserved when both the link
and the bounded face-spin labelling are reflected. -/
theorem slabExplicitLinkMultiplicity_reflection
    {K extent : Nat} {physical : Nat → Nat}
    {link : Z4Link}
    (hlink : link ∈ boundaryCompleteSlabLinks extent)
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    slabExplicitLinkMultiplicity K extent physical link =
      slabExplicitLinkMultiplicity K extent
        (reflectSlabFaceLabelling extent physical)
        (timeReflectLink extent link) := by
  unfold slabExplicitLinkMultiplicity
  exact explicitValenceMultiplicity_physical_perm
    (slabIncidentSpinList_reflection_perm extent physical hlink)
    (by simpa only [List.length_map] using
      slabIncidentPlaqIds_length_le_six extent link)
    (slabIncidentSpins_bounded hbounded link)

def natListProduct {A : Type} (value : A → Nat) : List A → Nat
  | [] => 1
  | head :: tail => value head * natListProduct value tail

theorem natListProduct_perm {A : Type} (value : A → Nat)
    {left right : List A} (hperm : left.Perm right) :
    natListProduct value left = natListProduct value right := by
  induction hperm with
  | nil => rfl
  | cons head hperm ih =>
      simp only [natListProduct]
      rw [ih]
  | swap first second rest =>
      simp only [natListProduct]
      calc
        value second * (value first * natListProduct value rest) =
            (value second * value first) *
              natListProduct value rest :=
          (Nat.mul_assoc _ _ _).symm
        _ = (value first * value second) *
              natListProduct value rest := by
          rw [Nat.mul_comm (value second) (value first)]
        _ = value first *
              (value second * natListProduct value rest) :=
          Nat.mul_assoc _ _ _
  | trans hleft hright ihleft ihrigh =>
      exact ihleft.trans ihrigh

theorem natListProduct_map {A B : Type}
    (value : B → Nat) (reindex : A → B) : ∀ xs : List A,
    natListProduct value (xs.map reindex) =
      natListProduct (fun x => value (reindex x)) xs
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, natListProduct]
      rw [natListProduct_map value reindex tail]

theorem natListProduct_congr {A : Type}
    (left right : A → Nat) : ∀ xs : List A,
    (∀ x, x ∈ xs → left x = right x) →
    natListProduct left xs = natListProduct right xs
  | [], _ => rfl
  | head :: tail, hagree => by
      simp only [natListProduct]
      rw [hagree head List.mem_cons_self,
        natListProduct_congr left right tail
          (fun x hx => hagree x (List.mem_cons_of_mem head hx))]

def slabExplicitLinkMultiplicityProduct
    (K extent : Nat) (physical : Nat → Nat) : Nat :=
  natListProduct
    (slabExplicitLinkMultiplicity K extent physical)
    (boundaryCompleteSlabLinks extent)

/-- The product of all corrected-slab link multiplicities is exactly
reflection-invariant. -/
theorem slabExplicitLinkMultiplicityProduct_reflection
    {K extent : Nat} {physical : Nat → Nat}
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    slabExplicitLinkMultiplicityProduct K extent
        (reflectSlabFaceLabelling extent physical) =
      slabExplicitLinkMultiplicityProduct K extent physical := by
  unfold slabExplicitLinkMultiplicityProduct
  let links := boundaryCompleteSlabLinks extent
  let reflectedValue := slabExplicitLinkMultiplicity K extent
    (reflectSlabFaceLabelling extent physical)
  let sourceValue := slabExplicitLinkMultiplicity K extent physical
  calc
    natListProduct reflectedValue links =
        natListProduct reflectedValue
          (links.map (timeReflectLink extent)) :=
      natListProduct_perm reflectedValue
        (timeReflect_boundaryCompleteSlabLinks_perm extent).symm
    _ = natListProduct
        (fun link => reflectedValue (timeReflectLink extent link))
        links := natListProduct_map reflectedValue
          (timeReflectLink extent) links
    _ = natListProduct sourceValue links := by
      apply natListProduct_congr
      intro link hlink
      exact (slabExplicitLinkMultiplicity_reflection hlink hbounded).symm

/-! ## 3. The complete corrected-slab term -/

def slabParametricKPhysicalTerm
    (w : Q') (K extent : Nat) (physical : Nat → Nat) : Q' :=
  slabParametricKPhysicalFaceFactor w K extent physical *
    Q'.ofNat (slabExplicitLinkMultiplicityProduct K extent physical)

/-- Face coefficients and every SU(2) invariant multiplicity are preserved
together: one full corrected-slab spin-foam summand is reflection-invariant. -/
theorem slabParametricKPhysicalTerm_reflection
    (w : Q') {K extent : Nat} {physical : Nat → Nat}
    (hbounded : SlabFaceLabellingBounded K extent physical) :
    slabParametricKPhysicalTerm w K extent
        (reflectSlabFaceLabelling extent physical) ≈
      slabParametricKPhysicalTerm w K extent physical := by
  unfold slabParametricKPhysicalTerm
  rw [slabExplicitLinkMultiplicityProduct_reflection hbounded]
  exact Q'.mul_eqv_congr_right _ _ _
    (slabParametricKPhysicalFaceFactor_reflection
      w K extent physical)

end YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.slabIncidentPlaqIds_length_le_six
#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.slabIncidentSpins_bounded
#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.slabExplicitLinkMultiplicity_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.natListProduct_perm
#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.slabExplicitLinkMultiplicityProduct_reflection
#print axioms YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity.slabParametricKPhysicalTerm_reflection
