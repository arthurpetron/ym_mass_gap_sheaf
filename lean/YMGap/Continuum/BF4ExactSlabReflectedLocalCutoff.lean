/-
# Local cutoff selection WITH computed reflection compatibility

For a selected crossing face, every other face touching its lower exposed
link is lower. Fix only that lower collar at B and reflect the lower cutoff
profile to the upper half. Other lower and crossing cutoffs remain arbitrary.
The previous full-action selection theorem now applies to this positive
reflected family on the original carrier, not to unrelated mixed profiles.

Exact saturation then removes the SELECTED crossing cutoff from the finite
comparison floor. The computed degree has no distant-cutoff argument. It
still depends on B, the insertion, nome profiles and extent. No normalized
thermodynamic OS-norm estimate, original transfer preimage, continuum or Clay
closure is asserted.
-/

import YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles
import YMGap.Continuum.BF4ExactSlabLocalBulkCutoff

namespace YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4GeometricSpinNetworkMehler
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactSlabAllExtentObservableHaarForm
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.BF4ExactSlabAllExtentExposedLinkDegree
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabLocalBulkSelection
open YMGap.Continuum.BF4ExactSlabLocalBulkCutoff
open YMGap.Continuum.BF4ExactSlabReflectedHeatProfiles
open YMGap.Continuum.BF4ExactSlabLocalInterfaceCoercivity
open YMGap.Continuum.BF4ExactSlabPlaquettePathGram
open YMGap.Continuum.BF4ExactSlabPlaquetteObservableAlgebra
open YMGap.Continuum.BF4ExactSlabPlaquetteReflectionPositivity (reflectedInsertion)
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization

local infix:50 " ≈ " => Q'.eqv

private theorem fixed_exposed_not_edge {half : Nat} {selected other : Z4Plaq}
    (hs : plaquetteHalfSide half selected = .fixed)
    (ho : plaquetteHalfSide half other = .fixed) (hne : other ≠ selected) :
    faceLinkA selected ∉ edgesOf other := by
  intro h
  have hm : faceLinkA selected ∈ (orientedPlaquetteBoundary other).map OrientedBF4Link.link := by
    simpa [orientedPlaquetteBoundary,edgesOf,or_comm,or_left_comm,or_assoc] using h
  obtain ⟨entry, he, hl⟩ := List.mem_map.mp hm
  exact exposed_link_not_in_other hs ho hne he hl.symm

/-- The other touching faces are in the lower half, not additional crossings. -/
theorem touching_other_lower {half id j : Nat} (hi : id ∈ centralFixedFaceIds half)
    (hj : j ∈ slabPhysicalFaceEdges (centralExtent half)) (hne : j ≠ id)
    (ht : detachedTest (centralExtent half) [faceLinkA (slabPlaquetteAt (centralExtent half) id)] [] j = false) :
    j ∈ centralLowerFaceIds half := by
  have he : faceLinkA (slabPlaquetteAt (centralExtent half) id) ∈
      edgesOf (slabPlaquetteAt (centralExtent half) j) := by
    simpa [detachedTest,disjointTest,faceLinks] using ht
  apply mem_centralLowerFaceIds.mpr
  refine ⟨hj,?_⟩
  cases hs : plaquetteHalfSide half (slabPlaquetteAt (centralExtent half) j) with
  | lower => rfl
  | upper => exact False.elim ((lower_link_incident_face_ne_upper
      (crossing_face_path_sides (mem_centralFixedFaceIds.mp hi).2).1 he) hs)
  | fixed => exact False.elim (fixed_exposed_not_edge (mem_centralFixedFaceIds.mp hi).2 hs
      (fun h => hne (slabPlaquetteAt_injective_on_physical hj (mem_centralFixedFaceIds.mp hi).1 h)) he)

def crossingCutoff (id : Nat) (rest : Nat → Nat) (K j : Nat) : Nat :=
  if j=id then K else rest j

/-- Only touching LOWER faces are capped; their upper partners are computed. -/
def bulkCutoff (half id B : Nat) (rest : Nat → Nat) : Nat → Nat :=
  localCutoff (centralExtent half) (slabPlaquetteAt (centralExtent half) id) B rest

/-- The reflected profile is literally the old local full-cutoff profile
on every physical face. Its detached profile does not depend on K. -/
theorem cutoff_pin {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (B : Nat) (bulkRest crossRest : Nat → Nat) (K : Nat)
    {j : Nat} (hj : j ∈ slabPhysicalFaceEdges (centralExtent half)) :
    reflectedProfile (bulkCutoff half id B bulkRest) (crossingCutoff id crossRest K) half j =
      fullCutoff (centralExtent half) id B
        (reflectedProfile (bulkCutoff half id B bulkRest) crossRest half) K j := by
  by_cases hji : j=id
  · subst j
    rw [reflectedProfile_fixed _ _ hi]
    simp only [crossingCutoff,fullCutoff,ite_true]
  · have he : reflectedProfile (bulkCutoff half id B bulkRest) (crossingCutoff id crossRest K) half j =
        reflectedProfile (bulkCutoff half id B bulkRest) crossRest half j := by
      unfold reflectedProfile
      split <;> simp only [crossingCutoff,if_neg hji]
    rw [he]
    unfold fullCutoff
    rw [if_neg hji]
    cases ht : detachedTest (centralExtent half) [faceLinkA (slabPlaquetteAt (centralExtent half) id)] [] j
    · rw [reflectedProfile_lower _ _ (touching_other_lower hi hj hji ht)]
      simp only [bulkCutoff,localCutoff,ht,Bool.false_eq_true,if_false]
    · simp only [localCutoff,ht,if_true]

def quadratic (bulk crossing : Nat → Q') (B : Nat) (bulkRest crossRest : Nat → Nat)
    {half : Nat} (id : Nat) (e : PlaquetteExpression half) (K : Nat) : Q' :=
  fullQuadratic bulk (bulkCutoff half id B bulkRest) crossing (crossingCutoff id crossRest K) e

theorem quadratic_pin {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk crossing : Nat → Q') (B : Nat) (bulkRest crossRest : Nat → Nat)
    (e : PlaquetteExpression half) (K : Nat) :
    quadratic bulk crossing B bulkRest crossRest id e K =
      fullPairing (reflectedProfile bulk crossing half) B
        (reflectedProfile (bulkCutoff half id B bulkRest) crossRest half)
        (centralExtent half) id (reflectedInsertion e) K := by
  have h : fullHeat bulk (bulkCutoff half id B bulkRest) crossing (crossingCutoff id crossRest K) half =
      profileHeat (reflectedProfile bulk crossing half)
        (fullCutoff (centralExtent half) id B (reflectedProfile (bulkCutoff half id B bulkRest) crossRest half) K)
        (centralExtent half) (slabPhysicalFaceEdges (centralExtent half)) := by
    apply polynomialProduct_congr
    intro j hj
    rw [cutoff_pin hi B bulkRest crossRest K hj]
  unfold quadratic fullQuadratic fullPairing
  rw [h]

/-- No bulkRest, crossRest or selected cutoff occurs in this computed threshold. -/
def degree {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk crossing : Nat → Q') (B : Nat) (e : PlaquetteExpression half) : Nat :=
  fullDegree (mem_centralFixedFaceIds.mp hi).1 (reflectedProfile bulk crossing half) B (reflectedInsertion e)

theorem quadratic_stable {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk crossing : Nat → Q') (B : Nat) (bulkRest crossRest : Nat → Nat)
    (e : PlaquetteExpression half) (N K : Nat) (hN : degree hi bulk crossing B e ≤ N) (hK : N ≤ K) :
    quadratic bulk crossing B bulkRest crossRest id e K ≈ quadratic bulk crossing B bulkRest crossRest id e N := by
  rw [quadratic_pin hi,quadratic_pin hi]
  have hp := supported_polyMul (reflectCorrectedSlabPolynomial_support (centralExtent half) (lower e)) (lower_supported e)
  exact Q'.eqv_trans _ _ _ (fullPairing_stable (mem_centralFixedFaceIds.mp hi).1 _ B _ _ hp K (Nat.le_trans hN hK))
    (Q'.eqv_symm (fullPairing_stable (mem_centralFixedFaceIds.mp hi).1 _ B _ _ hp N hN))

theorem quadratic_nonnegative (bulk crossing : Nat → Q') (hc : ∀ id,(0 : Q') ≤ crossing id)
    (B : Nat) (bulkRest crossRest : Nat → Nat) {half : Nat} (id : Nat) (e : PlaquetteExpression half) (K : Nat) :
    (0 : Q') ≤ quadratic bulk crossing B bulkRest crossRest id e K :=
  fullQuadratic_nonnegative bulk _ crossing hc _ e

def singleMask (id j : Nat) : Bool := decide (j=id)

theorem singleMask_count {half id : Nat} (hi : id ∈ centralFixedFaceIds half) :
    changedFaceCount (singleMask id) half = 1 := by
  have hp : ((centralFixedFaceIds half).filter (singleMask id)).Perm [id] := by
    apply YMGap.Continuum.Z4CanonicalPolymerUniverse.perm_of_nodup_mem_iff
    · exact List.filter_sublist.nodup (YMGap.Continuum.BF4ExactSlabAnchoredCutoffLimit.fixedFaceIds_nodup half)
    · simp
    · intro j
      simp only [List.mem_filter,singleMask,decide_eq_true_eq,List.mem_singleton]
      exact ⟨fun h => h.2,fun h => ⟨h.symm ▸ hi,h⟩⟩
  exact hp.length_eq

/-- Simultaneous threshold for the target and the one-face nome-one reference.
Only the fixed touching cutoff B occurs; there are no distant cutoff inputs. -/
def comparisonDegree {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk : Nat → Q') (w : Q') (B : Nat) (e : PlaquetteExpression half) : Nat :=
  max (degree hi bulk (fun _ => w) B e) (degree hi bulk (referenceNome w (singleMask id)) B e)

def comparisonFloor {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk : Nat → Q') (w : Q') (B : Nat) (e : PlaquetteExpression half) : Q' :=
  YMGap.Continuum.RGTransport.qpow w (comparisonDegree hi bulk w B e * (comparisonDegree hi bulk w B e+2))

theorem comparisonFloor_positive {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk : Nat → Q') (w : Q') (hw : (0 : Q') < w) (B : Nat) (e : PlaquetteExpression half) :
    (0 : Q') < comparisonFloor hi bulk w B e := by
  have h := localFloor_positive w hw (singleMask id) (fun _ => comparisonDegree hi bulk w B e) half
  rw [localFloor_constant,singleMask_count hi,Nat.mul_one] at h
  exact h

/-- The same explicit positive factor works for EVERY distant cutoff profile
and EVERY selected cutoff above the local degree. The touching B remains fixed. -/
theorem quadratic_local_lower {half id : Nat} (hi : id ∈ centralFixedFaceIds half)
    (bulk : Nat → Q') (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q')) (B : Nat)
    (bulkRest crossRest : Nat → Nat) (e : PlaquetteExpression half) (K : Nat)
    (hK : comparisonDegree hi bulk w B e ≤ K) :
    comparisonFloor hi bulk w B e * quadratic bulk (referenceNome w (singleMask id)) B bulkRest crossRest id e K ≤
      quadratic bulk (fun _ => w) B bulkRest crossRest id e K := by
  let D := comparisonDegree hi bulk w B e
  have htarget := quadratic_stable hi bulk (fun _ => w) B bulkRest crossRest e D K (Nat.le_max_left _ _) hK
  have href := quadratic_stable hi bulk (referenceNome w (singleMask id)) B bulkRest crossRest e D K (Nat.le_max_right _ _) hK
  have hsmall := fullQuadratic_local_lower bulk (bulkCutoff half id B bulkRest) w hw0 hw1 (singleMask id) D
    (crossingCutoff id crossRest D) e (by
      intro j _ hs
      have he : j=id := of_decide_eq_true hs
      subst j
      simp only [crossingCutoff,ite_true,Nat.le_refl])
  rw [singleMask_count hi,Nat.mul_one] at hsmall
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv (Q'.mul_eqv_congr_left _ _ _ href))
    (Q'.le_trans' _ _ _ hsmall (Q'.ge_of_eqv htarget))

theorem quadratic_local_upper (bulk : Nat → Q') (w : Q') (hw0 : (0 : Q') ≤ w) (hw1 : w ≤ (1 : Q'))
    (B : Nat) (bulkRest crossRest : Nat → Nat) {half : Nat} (id : Nat) (e : PlaquetteExpression half) (K : Nat) :
    quadratic bulk (fun _ => w) B bulkRest crossRest id e K ≤
      quadratic bulk (referenceNome w (singleMask id)) B bulkRest crossRest id e K :=
  fullQuadratic_local_upper bulk _ w hw0 hw1 (singleMask id) _ e

end YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff

#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.touching_other_lower
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.crossingCutoff
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.bulkCutoff
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.cutoff_pin
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic_pin
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.degree
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic_stable
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic_nonnegative
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.singleMask
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.singleMask_count
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.comparisonDegree
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.comparisonFloor
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.comparisonFloor_positive
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic_local_lower
#print axioms YMGap.Continuum.BF4ExactSlabReflectedLocalCutoff.quadratic_local_upper
