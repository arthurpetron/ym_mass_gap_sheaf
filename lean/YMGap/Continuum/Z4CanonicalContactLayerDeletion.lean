/-
# Finite contact-layer deletion around a canonical Z4 polymer

An atom incompatible with a fixed canonical root contains either a root face
or a face sharing one of the root's physical links.  We enumerate those
possible numerical face identifiers directly from the four boundary links of
each root plaquette and the at-most-six incident plaquettes per link.

Combining this finite contact cover with the uniform pinned-layer half bound
gives a volume-independent partition comparison.  For the 24-face dyadic cube
the (deliberately non-deduplicated) contact list has length at most 600, so the
complete deletion cost is at most `2^600` in every containing box.
-/

import YMGap.Continuum.FiniteCompatibilityLayerDeletion
import YMGap.Continuum.Z4CanonicalIncompatibilityWalk
import YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
import YMGap.Continuum.Z4DyadicUnitCubeActivity
import YMGap.Continuum.Z4SpinDependentIncidenceProductBound

namespace YMGap.Continuum.Z4CanonicalContactLayerDeletion

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteCompatibilityGas
open YMGap.Continuum.FiniteCompatibilityLayerDeletion
open YMGap.Continuum.FiniteCompatibilityMarkedBound
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalFiniteCompatibilityGas
open YMGap.Continuum.Z4CanonicalIncompatibilityWalk
open YMGap.Continuum.Z4CanonicalPinnedLayerDeletion
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicUnitCubeActivity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4FiniteBoxIncidentDegreeBound
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4PhysicalSurfaceComponents
open YMGap.Continuum.Z4SpinDependentIncidenceProductBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. A concrete contact cover -/

/-- The root face itself, followed by every numerical plaquette incident on
one of its four geometric boundary links.  Duplicates are intentionally kept:
they simplify the exact cover proof and only enlarge the final fixed exponent. -/
def canonicalFaceContactCandidates (n rootFace : Nat) : List Nat :=
  rootFace :: (edgesOf (boxPlaquetteAt n rootFace)).flatMap
    (incidentPlaqIds n)

def canonicalContactFaceCandidates (n : Nat) (root : List Nat) : List Nat :=
  root.flatMap (canonicalFaceContactCandidates n)

theorem rootFace_mem_canonicalFaceContactCandidates (n rootFace : Nat) :
    rootFace ∈ canonicalFaceContactCandidates n rootFace :=
  List.mem_cons_self

theorem adjacentFace_mem_canonicalFaceContactCandidates
    {n rootFace otherFace : Nat}
    (hadj : faceLinkAdjacentB n rootFace otherFace = true) :
    otherFace ∈ canonicalFaceContactCandidates n rootFace := by
  unfold faceLinkAdjacentB at hadj
  obtain ⟨link, _, hrootIncident, hotherIncident⟩ :=
    shareListedPhysicalLinkWitness n rootFace otherFace
      (distinctBoxLinks n) hadj
  obtain ⟨rootPlaq, hrootEnum, hrootEdge⟩ :=
    decodeIncidentPlaqId hrootIncident
  have hrootEq : boxPlaquetteAt n rootFace = rootPlaq :=
    boxPlaquetteAt_eq_of_enumerate hrootEnum
  have hlink : link ∈ edgesOf (boxPlaquetteAt n rootFace) := by
    rw [hrootEq]
    exact hrootEdge
  unfold canonicalFaceContactCandidates
  apply List.mem_cons_of_mem
  exact List.mem_flatMap.mpr
    ⟨link, hlink, hotherIncident⟩

/-- Every false root/polymer compatibility test exposes a face of the polymer
in the explicit finite contact list. -/
theorem canonicalIncompatible_has_contactCandidate
    {n : Nat} {root polymer : List Nat}
    (hincompatible : canonicalPolymerCompatibleB n root polymer = false) :
    ∃ face, face ∈ canonicalContactFaceCandidates n root ∧
      face ∈ polymer := by
  obtain ⟨rootFace, hrootFace, polymerFace, hpolymerFace, hcontact⟩ :=
    canonicalPolymer_incompatible_contact hincompatible
  refine ⟨polymerFace, ?_, hpolymerFace⟩
  unfold canonicalContactFaceCandidates
  apply List.mem_flatMap.mpr
  refine ⟨rootFace, hrootFace, ?_⟩
  rcases hcontact with heq | hadj
  · subst polymerFace
    exact rootFace_mem_canonicalFaceContactCandidates n rootFace
  · exact adjacentFace_mem_canonicalFaceContactCandidates hadj

/-! ## 2. Uniform cardinality of the cover -/

private theorem length_flatMap_le {A B : Type}
    (f : A → List B) (bound : Nat) :
    ∀ xs : List A,
      (∀ item, item ∈ xs → (f item).length ≤ bound) →
      (xs.flatMap f).length ≤ xs.length * bound
  | [], _ => by simp
  | head :: tail, hbound => by
      have hhead := hbound head List.mem_cons_self
      have htail := length_flatMap_le f bound tail
        (fun item hitem =>
          hbound item (List.mem_cons_of_mem head hitem))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [Nat.succ_mul]
      omega

theorem canonicalFaceContactCandidates_length_le_twentyfive
    (n rootFace : Nat) :
    (canonicalFaceContactCandidates n rootFace).length ≤ 25 := by
  have hlinks := length_flatMap_le (incidentPlaqIds n) 6
    (edgesOf (boxPlaquetteAt n rootFace))
    (fun link _ => incidentPlaqIds_length_le_six n link)
  rw [edgesOf_length] at hlinks
  unfold canonicalFaceContactCandidates
  simp only [List.length_cons]
  omega

theorem canonicalContactFaceCandidates_length_le
    (n : Nat) (root : List Nat) :
    (canonicalContactFaceCandidates n root).length ≤ root.length * 25 := by
  unfold canonicalContactFaceCandidates
  exact length_flatMap_le (canonicalFaceContactCandidates n) 25 root
    (fun rootFace _ =>
      canonicalFaceContactCandidates_length_le_twentyfive n rootFace)

/-! ## 3. Iterated deletion and compatibility of every survivor -/

def canonicalContactDeletedAmbient
    (n : Nat) (root : List Nat) : List (List Nat) :=
  deleteMarkedLayers
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers n)

theorem canonicalContactDeletedAmbient_survivor_compatible
    {n : Nat} {root polymer : List Nat}
    (hpolymer : polymer ∈ canonicalContactDeletedAmbient n root) :
    canonicalPolymerCompatibleB n root polymer = true := by
  cases hcompat : canonicalPolymerCompatibleB n root polymer with
  | true => rfl
  | false =>
      obtain ⟨face, hfaceContact, hfacePolymer⟩ :=
        canonicalIncompatible_has_contactCandidate hcompat
      have hmarkFalse := mem_deleteMarkedLayers_mark_false
        (fun contact atom => canonicalContainsFaceB contact atom)
        (canonicalContactFaceCandidates n root)
        (canonicalSurfacePolymers n) polymer hpolymer face hfaceContact
      have hmarkTrue : canonicalContainsFaceB face polymer = true := by
        unfold canonicalContainsFaceB
        exact decide_eq_true hfacePolymer
      change canonicalContainsFaceB face polymer = false at hmarkFalse
      rw [hmarkTrue] at hmarkFalse
      cases hmarkFalse

/-- The full exact anchor partition is controlled by the contact-deleted
partition with a factor depending only on the explicit finite contact list. -/
theorem canonicalPolymerPartition_le_contactDeleted
    (n : Nat) (root : List Nat) :
    canonicalPolymerPartition anchorCoupling n (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^ (canonicalContactFaceCandidates n root).length *
        canonicalPolymerPartition anchorCoupling n
          (canonicalContactDeletedAmbient n root) := by
  unfold canonicalPolymerPartition canonicalContactDeletedAmbient
  apply partition_le_two_pow_mul_deleteMarkedLayers
    (canonicalPolymerCompatibleB n)
    (canonicalSurfaceActivity anchorCoupling n)
    (canonicalSurfacePolymer_activity_nonnegative n)
    (fun face polymer => canonicalContainsFaceB face polymer)
    (canonicalContactFaceCandidates n root)
    (canonicalSurfacePolymers n)
  intro face _
  change canonicalPinnedLayerActivity n face ≤
    Q'.mkPos 1 2 (by decide)
  exact canonicalPinnedLayerActivity_le_half n face

/-! ## 4. The fixed `2^600` dyadic-cube bound -/

def dyadicUnitCubeContactFaceCandidates (n : Nat) : List Nat :=
  canonicalContactFaceCandidates n (dyadicUnitCubeSupportIdsAt n)

def dyadicUnitCubeContactDeletedAmbient (n : Nat) : List (List Nat) :=
  canonicalContactDeletedAmbient n (dyadicUnitCubeSupportIdsAt n)

theorem dyadicUnitCubeContactFaceCandidates_length_le_six_hundred
    {n : Nat} (hn : 4 ≤ n) :
    (dyadicUnitCubeContactFaceCandidates n).length ≤ 600 := by
  have hlength := canonicalContactFaceCandidates_length_le n
    (dyadicUnitCubeSupportIdsAt n)
  have htransport := transportPolymer_length_eq hn
    dyadicUnitCubeSupportIds_mem_cutoffOneFaceSupports
  unfold dyadicUnitCubeContactFaceCandidates dyadicUnitCubeSupportIdsAt at hlength ⊢
  rw [htransport, dyadicUnitCubeSupportIds_length] at hlength
  simpa using hlength

private theorem qpow_le_succ_of_one_le {base : Q'}
    (hbase : (1 : Q') ≤ base) (exponent : Nat) :
    base ^ exponent ≤ base ^ (exponent + 1) := by
  rw [Q'.pow_succ]
  have hpow0 : (0 : Q') ≤ base ^ exponent :=
    Q'.pow_nonneg base
      (Q'.le_trans' _ _ _ Q'.zero_le_one hbase) exponent
  have hscaled : (1 : Q') * base ^ exponent ≤
      base * base ^ exponent :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hbase hpow0
  exact Q'.le_trans' _ _ _
    (Q'.ge_of_eqv (Q'.one_mul_eqv (base ^ exponent))) hscaled

private theorem qpow_add_mono_of_one_le {base : Q'}
    (hbase : (1 : Q') ≤ base) (first : Nat) :
    ∀ offset : Nat, base ^ first ≤ base ^ (first + offset)
  | 0 => Q'.le_refl' _
  | offset + 1 => by
      have hindex : first + (offset + 1) =
          (first + offset) + 1 := by omega
      rw [hindex]
      exact Q'.le_trans' _ _ _
        (qpow_add_mono_of_one_le hbase first offset)
        (qpow_le_succ_of_one_le hbase (first + offset))

private theorem qpow_mono_exponent_of_one_le {base : Q'}
    (hbase : (1 : Q') ≤ base) {first second : Nat}
    (hle : first ≤ second) : base ^ first ≤ base ^ second := by
  obtain ⟨offset, rfl⟩ := Nat.exists_eq_add_of_le hle
  exact qpow_add_mono_of_one_le hbase first offset

/-- A single fixed, volume-independent contact-deletion cost for the
transported 24-face cube in every containing box. -/
theorem dyadicUnitCubePartition_le_two_pow_six_hundred_mul_deleted
    {n : Nat} (hn : 4 ≤ n) :
    canonicalPolymerPartition anchorCoupling n (canonicalSurfacePolymers n) ≤
      (Q'.ofNat 2) ^ 600 *
        canonicalPolymerPartition anchorCoupling n
          (dyadicUnitCubeContactDeletedAmbient n) := by
  have hraw := canonicalPolymerPartition_le_contactDeleted n
    (dyadicUnitCubeSupportIdsAt n)
  have hlength :=
    dyadicUnitCubeContactFaceCandidates_length_le_six_hundred hn
  have hpow :
      (Q'.ofNat 2) ^ (dyadicUnitCubeContactFaceCandidates n).length ≤
        (Q'.ofNat 2) ^ 600 :=
    qpow_mono_exponent_of_one_le (by decide) hlength
  have hpartition0 : (0 : Q') ≤
      canonicalPolymerPartition anchorCoupling n
        (dyadicUnitCubeContactDeletedAmbient n) :=
    anchorCanonicalPolymerPartition_nonnegative n _
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ _ hpow hpartition0
  unfold dyadicUnitCubeContactFaceCandidates at hscaled
  unfold dyadicUnitCubeContactDeletedAmbient
  exact Q'.le_trans' _ _ _ hraw hscaled

end YMGap.Continuum.Z4CanonicalContactLayerDeletion

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.adjacentFace_mem_canonicalFaceContactCandidates
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.canonicalIncompatible_has_contactCandidate
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.canonicalContactFaceCandidates_length_le
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.canonicalContactDeletedAmbient_survivor_compatible
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.canonicalPolymerPartition_le_contactDeleted
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.dyadicUnitCubeContactFaceCandidates_length_le_six_hundred
#print axioms YMGap.Continuum.Z4CanonicalContactLayerDeletion.dyadicUnitCubePartition_le_two_pow_six_hundred_mul_deleted
