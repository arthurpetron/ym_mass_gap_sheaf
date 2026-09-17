/-
# Erase exactly the original action factors touching a plaquette boundary

The selected star touches ANY of the chosen face's four literal links. Its
complement is independent of EVERY such link. There are at most twenty-four
star factors for a physical selected list without repetitions; all other
factors remain in the same original Haar integral.

Two distinct plaquettes need not have a common private link relative to a
larger family. Instead, a computed missing link is chosen separately for
each pair. This proves exact retained-background character orthogonality,
including closed surfaces, and the chosen character's unit second moment.
No full-action orthogonality, summed frame bound or spectral gap is asserted.
-/

import YMGap.Continuum.BF4ExactSlabSelectedStarPredictionError
import YMGap.Continuum.Z4PlaquetteBoundaryRigidity

set_option autoImplicit false

namespace YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4ExactCorrectedSlabHaarNetwork
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentTemporalHaarForm (original_character_support)
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSingleLinkCharacterSelection
open YMGap.Continuum.BF4ExactSlabLinkStarGeometry (incidentIds mem_incidentIds_iff incidentIds_length_le_six)
open YMGap.Continuum.BF4ExactSlabSelectedStarVariance (faceCharacter faceCharacter_supported)
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionSolidZonalCharacter (HasQuaternionBlockDegree)
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionBlockLocality
open YMGap.Continuum.QuaternionHaarSquareCertificate (haar_of_coeff)
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap_mul_left)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4PlaquetteBoundaryRigidity (two_boundary_links_determine_face)
open YMGap.Continuum.CayleyPruferInjection (nodup_subset_length_le)

local infix:50 " ≈ " => Q'.eqv
local notation:max "B" extent:arg => List.length (boundaryCompleteSlabLinks extent)

attribute [local irreducible] correctedSlabPlaquettePolynomial

def touches (face other : Z4Plaq) : Bool :=
  (edgesOf face).any (fun link => decide (link ∈ edgesOf other))

theorem touches_iff (face other : Z4Plaq) :
    touches face other = true ↔ ∃ link, link ∈ edgesOf face ∧ link ∈ edgesOf other := by
  simp only [touches, List.any_eq_true, decide_eq_true_eq]

def boundaryStar (extent : Nat) (ids : List Nat) (face : Z4Plaq) : List Nat :=
  ids.filter (fun id => touches face (slabPlaquetteAt extent id))

def boundaryRest (extent : Nat) (ids : List Nat) (face : Z4Plaq) : List Nat :=
  ids.filter (fun id => !(touches face (slabPlaquetteAt extent id)))

theorem boundaryStar_mem {extent : Nat} {ids : List Nat} {face : Z4Plaq} {id : Nat}
    (hi : id ∈ boundaryStar extent ids face) :
    id ∈ ids ∧ ∃ link, link ∈ edgesOf face ∧ link ∈ edgesOf (slabPlaquetteAt extent id) :=
  ⟨(List.mem_filter.mp hi).1, (touches_iff _ _).mp (List.mem_filter.mp hi).2⟩

theorem boundaryRest_mem {extent : Nat} {ids : List Nat} {face : Z4Plaq} {id : Nat}
    (hi : id ∈ boundaryRest extent ids face) :
    id ∈ ids ∧ touches face (slabPlaquetteAt extent id) = false := by
  simpa only [boundaryRest, List.mem_filter, Bool.not_eq_true'] using hi

theorem selected_partition (extent : Nat) (ids : List Nat) (face : Z4Plaq) :
    (boundaryStar extent ids face ++ boundaryRest extent ids face).Perm ids :=
  List.filter_append_perm _ _

private theorem incident_flatMap_length (extent : Nat) : ∀ links : List Z4Link,
    (links.flatMap (incidentIds extent)).length ≤ 6*links.length
  | [] => Nat.le_refl _
  | link :: links => by
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      have hh := incidentIds_length_le_six extent link
      have ht := incident_flatMap_length extent links
      omega

/-- The bound counts original occurrences only once; overlapping link stars
do not produce repeated factors in boundaryStar. -/
theorem boundaryStar_length_le_twentyFour (extent : Nat) (ids : List Nat)
    (hids : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hnodup : ids.Nodup) (face : Z4Plaq) :
    (boundaryStar extent ids face).length ≤ 24 := by
  have hn : (boundaryStar extent ids face).Nodup := List.filter_sublist.nodup hnodup
  have hsub : ∀ id, id ∈ boundaryStar extent ids face →
      id ∈ (edgesOf face).flatMap (incidentIds extent) := by
    intro id hi
    have hm := boundaryStar_mem hi
    obtain ⟨link, hl, he⟩ := hm.2
    exact List.mem_flatMap.mpr ⟨link, hl, (mem_incidentIds_iff extent link id).mpr ⟨hids id hm.1, he⟩⟩
  have h := Nat.le_trans (nodup_subset_length_le _ _ hn hsub)
    (incident_flatMap_length extent (edgesOf face))
  simpa only [edgesOf, List.length_cons, List.length_nil] using h

def starHeat (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (boundaryStar extent ids face)

def restHeat (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) : RatPoly :=
  polynomialProduct (faceHeatPolynomial w K extent) (boundaryRest extent ids face)

/-- A factorization of the SAME selected action, not of its Haar integral. -/
theorem selected_heat_partition (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) :
    RatPolyCoeffEqv (polynomialProduct (faceHeatPolynomial w K extent) ids)
      (polyMul (starHeat w K extent ids face) (restHeat w K extent ids face)) :=
  (polynomialProduct_perm _ (selected_partition extent ids face).symm).trans
    (polynomialProduct_append _ _ _)

theorem starHeat_supported (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (starHeat w K extent ids face) :=
  heatProduct_supported w K extent _

theorem restHeat_supported (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) :
    SupportedQuaternionBlocks (B extent) (restHeat w K extent ids face) :=
  heatProduct_supported w K extent _

/-- Every boundary link of the chosen face is absent from the retained factors. -/
theorem rest_misses (extent : Nat) (ids : List Nat) (face : Z4Plaq)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    link ∉ faceLinks extent (boundaryRest extent ids face) := by
  intro hm
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hm
  have hfalse := (boundaryRest_mem hi).2
  have htrue := (touches_iff face (slabPlaquetteAt extent id)).mpr ⟨link, hl, he⟩
  rw [htrue] at hfalse
  cases hfalse

theorem restHeat_local (w : Q') (K extent : Nat) (ids : List Nat) (face : Z4Plaq) :
    LinkLocal extent (faceLinks extent (boundaryRest extent ids face)) (restHeat w K extent ids face) :=
  heatProduct_local w K extent _

/-- The exact degree-zero statement uses each selected physical link's
original quaternion index. -/
theorem restHeat_degree_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) :
    HasQuaternionBlockDegree ((boundaryCompleteSlabLinks extent).idxOf link) 0
      (restHeat w K extent ids face) :=
  linkLocal_degree_zero (restHeat_local w K extent ids face) link
    ((mem_boundaryCompleteSlabLinks_iff extent link).mpr ⟨face, hf, hl⟩)
    (rest_misses extent ids face link hl)

/-- Only two explicit finite membership tests are needed: two distinct
origin links cannot both belong to the boundary of another plaquette. -/
def missingLink (face other : Z4Plaq) (hne : face ≠ other) :
    {link : Z4Link // link ∈ edgesOf face ∧ link ∉ edgesOf other} := by
  let a : Z4Link := (face.1, (dirsOf face.2).1)
  let b : Z4Link := (face.1, (dirsOf face.2).2)
  have ha : a ∈ edgesOf face := List.mem_cons_self
  have hb : b ∈ edgesOf face := List.mem_cons_of_mem _ List.mem_cons_self
  have hab : a ≠ b := fun he => dirsOf_ne face.2 (congrArg Prod.snd he)
  if har : a ∈ edgesOf other then
    if hbr : b ∈ edgesOf other then
      exact False.elim (hne (two_boundary_links_determine_face face other a b ha hb hab har hbr))
    else exact ⟨b, hb, hbr⟩
  else exact ⟨a, ha, har⟩

/-- An exterior or upper-time predictor need only miss ONE selected boundary
link; all other coordinates and all retained action factors remain. -/
theorem rest_character_spectator_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (link : Z4Link) (hl : link ∈ edgesOf face) (spin : Nat) (hs : 0 < spin)
    (q : RatPoly) (hq : SupportedQuaternionBlocks (B extent) q) (links : List Z4Link)
    (hlocal : LinkLocal extent links q) (hfree : link ∉ links) :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin) q)) ≈ 0 := by
  let R := restHeat w K extent ids face
  let allowed := faceLinks extent (boundaryRest extent ids face) ++ links
  have hr : LinkLocal extent allowed R := (restHeat_local w K extent ids face).mono
    (fun _ hi => List.mem_append.mpr (Or.inl hi))
  have hq' : LinkLocal extent allowed q := hlocal.mono
    (fun _ hi => List.mem_append.mpr (Or.inr hi))
  have hnone : link ∉ allowed := fun hi =>
    (List.mem_append.mp hi).elim (rest_misses extent ids face link hl) hfree
  have hz := original_character_local_zero hf link hl spin hs (polyMul R q) allowed
    (supported_polyMul (restHeat_supported w K extent ids face) hq) (BlockLocal.mul hr hq') hnone
  exact Q'.eqv_trans _ _ _ (haar_of_coeff
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.mul (.var 1) (.var 2)))
      (.mul (.var 1) (.mul (.var 0) (.var 2))) (by decide)
      (fun | 0 => R | 1 => characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar spin | _ => q))) hz

/-- A different missing link is computed for each distinct face. Shared-link
and closed-surface configurations require no common private-edge hypothesis. -/
theorem rest_distinct_character_zero (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent)
    (other : Z4Plaq) (hne : face ≠ other) :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face) (faceCharacter extent other))) ≈ 0 :=
  rest_character_spectator_zero w K extent ids hf (missingLink face other hne).val
    (missingLink face other hne).property.1 1 (by decide)
    (faceCharacter extent other) (faceCharacter_supported extent other) (edgesOf other)
    ((face_scalar_local extent other).character 1) (missingLink face other hne).property.2

private theorem first_character_square (p : RatPoly) :
    RatPolyCoeffEqv (polyMul (characterPolynomial p 1) (characterPolynomial p 1))
      (polyAdd (characterPolynomial p 2) polyOne) := by
  let a := polyMul (characterPolynomial p 1) (characterPolynomial p 1)
  let b := characterPolynomial p 0
  exact (coeffEvalExpr_eqv_of_normalize_eq (.var 0)
    (.add (.add (.var 0) (.mul (.const (-1)) (.var 1))) (.var 1)) (by decide)
    (fun i => if i = 0 then a else b)).trans
    (((RatPolyCoeffEqv.refl a).add (cap_mul_left (-1) b)).add (RatPolyCoeffEqv.refl b))

/-- Exact unit second moment against the complete four-link-independent rest. -/
theorem rest_square_moment (w : Q') (K extent : Nat) (ids : List Nat)
    {face : Z4Plaq} (hf : face ∈ boundaryCompleteSlabPlaquettes extent) :
    quaternionHaar (B extent)
      (polyMul (restHeat w K extent ids face)
        (polyMul (faceCharacter extent face) (faceCharacter extent face))) ≈
      quaternionHaar (B extent) (restHeat w K extent ids face) := by
  let R := restHeat w K extent ids face
  let chi2 := characterPolynomial (correctedSlabPlaquettePolynomial extent face).scalar 2
  let link : Z4Link := (face.1, (dirsOf face.2).1)
  have hl : link ∈ edgesOf face := List.mem_cons_self
  have hz := original_character_local_zero hf link hl 2 (by decide) R
    (faceLinks extent (boundaryRest extent ids face)) (restHeat_supported w K extent ids face)
    (restHeat_local w K extent ids face) (rest_misses extent ids face link hl)
  have he : RatPolyCoeffEqv
      (polyMul R (polyMul (faceCharacter extent face) (faceCharacter extent face)))
      (polyAdd (polyMul chi2 R) (polyMul polyOne R)) :=
    ((first_character_square (correctedSlabPlaquettePolynomial extent face).scalar).mul_left R).trans
      (coeffEvalExpr_eqv_of_normalize_eq
        (.mul (.var 2) (.add (.var 0) (.var 1)))
        (.add (.mul (.var 0) (.var 2)) (.mul (.var 1) (.var 2)))
        (by decide) (fun | 0 => chi2 | 1 => polyOne | _ => R))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff he)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append _ _ _)
      (Q'.eqv_trans _ _ _ (Q'.add_eqv_congr' hz (haar_of_coeff (RatPolyCoeffEqv.one_mul R)))
        (Q'.eqv_of_eq (Q'.zero_add' _))))

end YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure

#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.touches
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.touches_iff
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.boundaryStar
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.boundaryRest
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.boundaryStar_mem
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.boundaryRest_mem
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.selected_partition
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.boundaryStar_length_le_twentyFour
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.starHeat
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.restHeat
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.selected_heat_partition
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.starHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.restHeat_supported
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.rest_misses
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.restHeat_local
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.restHeat_degree_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.missingLink
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.rest_character_spectator_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.rest_distinct_character_zero
#print axioms YMGap.Continuum.BF4ExactSlabPlaquetteBoundaryErasure.rest_square_moment
