/-
# Exact shared-face and retained-face partition for two link families

The finite ambient physical face list is split into faces touching both
literal link lists and its complement. This is set geometry only; no
polynomial weights or conditional dynamics are changed here.
-/

import YMGap.Continuum.BF4ExactSlabLocalSupportComparison
import YMGap.Continuum.BF4ExactSlabSharedFaceUniqueness

namespace YMGap.Continuum.BF4ExactSlabSharedFaceRegion

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabLocalSupportComparison
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.CayleyParentInj

/-- A face belongs to the shared collar exactly when it touches both lists. -/
def sharedTest (extent : Nat) (A B : List Z4Link) (id : Nat) : Bool :=
  !(detachedTest extent A [] id) && !(detachedTest extent B [] id)

/-- Ambient physical faces touching both selected link families. -/
def sharedIds (extent : Nat) (A B : List Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (sharedTest extent A B)

/-- All remaining ambient physical faces, including A-only, B-only, and
fully exterior faces. -/
def retainedIds (extent : Nat) (A B : List Z4Link) : List Nat :=
  (slabPhysicalFaceEdges extent).filter (fun id => !(sharedTest extent A B id))

def sharedCount (extent : Nat) (A B : List Z4Link) : Nat :=
  (sharedIds extent A B).length

/-- Shared faces followed by all retained faces partition the original
ambient list by permutation; no face factor is dropped. -/
theorem shared_partition (extent : Nat) (A B : List Z4Link) :
    (sharedIds extent A B ++ retainedIds extent A B).Perm
      (slabPhysicalFaceEdges extent) := by
  unfold sharedIds retainedIds
  exact List.filter_append_perm (sharedTest extent A B) (slabPhysicalFaceEdges extent)

theorem shared_physical {extent : Nat} {A B : List Z4Link} {id : Nat}
    (h : id ∈ sharedIds extent A B) : id ∈ slabPhysicalFaceEdges extent :=
  (List.mem_filter.mp h).1

theorem retained_physical {extent : Nat} {A B : List Z4Link} {id : Nat}
    (h : id ∈ retainedIds extent A B) : id ∈ slabPhysicalFaceEdges extent :=
  (List.mem_filter.mp h).1

/-- A retained face fails to touch at least one of the two link families. -/
theorem retained_not_touches_both {extent : Nat} {A B : List Z4Link} {id : Nat}
    (h : id ∈ retainedIds extent A B) :
    detachedTest extent A [] id = true ∨ detachedTest extent B [] id = true := by
  have ht := (List.mem_filter.mp h).2
  unfold sharedTest at ht
  cases ha : detachedTest extent A [] id <;>
    cases hb : detachedTest extent B [] id <;>
    simp [ha, hb] at ht ⊢

private theorem shared_nodup (extent : Nat) (A B : List Z4Link) :
    (sharedIds extent A B).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup _)

theorem shared_mem_left_collar (extent : Nat) (A B : List Z4Link) :
    ∀ id, id ∈ sharedIds extent A B → id ∈ collar extent A := by
  intro id h
  have ht := (List.mem_filter.mp h).2
  unfold sharedTest at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
  exact List.mem_filter.mpr ⟨(List.mem_filter.mp h).1,
    by simpa only [Bool.not_eq_true'] using ht.1⟩

theorem shared_mem_right_collar (extent : Nat) (A B : List Z4Link) :
    ∀ id, id ∈ sharedIds extent A B → id ∈ collar extent B := by
  intro id h
  have ht := (List.mem_filter.mp h).2
  unfold sharedTest at ht
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at ht
  exact List.mem_filter.mpr ⟨(List.mem_filter.mp h).1,
    by simpa only [Bool.not_eq_true'] using ht.2⟩

theorem sharedCount_le_left (extent : Nat) (A B : List Z4Link) :
    sharedCount extent A B ≤ 6 * A.length := by
  have hs := CayleyPruferInjection.nodup_subset_length_le
    (sharedIds extent A B) (collar extent A)
    (shared_nodup extent A B) (shared_mem_left_collar extent A B)
  exact Nat.le_trans hs (collarCount_le extent A)

theorem sharedCount_le_right (extent : Nat) (A B : List Z4Link) :
    sharedCount extent A B ≤ 6 * B.length := by
  have hs := CayleyPruferInjection.nodup_subset_length_le
    (sharedIds extent A B) (collar extent B)
    (shared_nodup extent A B) (shared_mem_right_collar extent A B)
  exact Nat.le_trans hs (collarCount_le extent B)

/-- This block-list construction agrees with the existing two-link geometry;
it does not replace or weaken the sharper distinct-link uniqueness result. -/
theorem sharedIds_singleton (extent : Nat) (left right : Z4Link) :
    sharedIds extent [left] [right] =
      BF4ExactSlabSharedFaceGeometry.sharedIds extent left right := by
  unfold sharedIds BF4ExactSlabSharedFaceGeometry.sharedIds
  apply congrArg (fun f => (slabPhysicalFaceEdges extent).filter f)
  funext id
  by_cases hl : left ∈ edgesOf (slabPlaquetteAt extent id) <;>
    by_cases hr : right ∈ edgesOf (slabPlaquetteAt extent id) <;>
    simp [sharedTest, detachedTest, BF4ExactSlabSelectionSeparation.disjointTest,
      faceLinks, hl, hr]

theorem sharedCount_singleton_le_one (extent : Nat) (left right : Z4Link)
    (hne : left ≠ right) : sharedCount extent [left] [right] ≤ 1 := by
  unfold sharedCount
  rw [sharedIds_singleton]
  exact BF4ExactSlabSharedFaceUniqueness.sharedIds_length_le_one extent left right hne

#print axioms sharedTest
#print axioms sharedIds
#print axioms retainedIds
#print axioms sharedCount
#print axioms shared_partition
#print axioms shared_physical
#print axioms retained_physical
#print axioms retained_not_touches_both
#print axioms shared_mem_left_collar
#print axioms shared_mem_right_collar
#print axioms sharedCount_le_left
#print axioms sharedCount_le_right
#print axioms sharedIds_singleton
#print axioms sharedCount_singleton_le_one

end YMGap.Continuum.BF4ExactSlabSharedFaceRegion
