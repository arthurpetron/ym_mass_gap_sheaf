/-
# Computed detached spectator faces and their removed collar

From an actual ambient face list, keep precisely the faces whose literal
links avoid the probe-plus-anchor links. Their complement is the removed
collar. The split and its disjointness are proved, not input certificates.
No bound on collar size or global anchored-family decomposition is claimed.
-/

import YMGap.Continuum.BF4ExactSlabSelectionSeparation

namespace YMGap.Continuum.BF4ExactSlabDetachedFaceRegion

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation

def detachedTest (extent : Nat) (links : List Z4Link) (core : List Nat) (id : Nat) : Bool :=
  disjointTest (links++faceLinks extent core) (faceLinks extent [id])

def detachedIds (extent : Nat) (links : List Z4Link) (core ambient : List Nat) : List Nat :=
  ambient.filter (detachedTest extent links core)

def collarIds (extent : Nat) (links : List Z4Link) (core ambient : List Nat) : List Nat :=
  ambient.filter (fun id => !(detachedTest extent links core id))

theorem region_partition (extent : Nat) (links : List Z4Link) (core ambient : List Nat) :
    (collarIds extent links core ambient ++ detachedIds extent links core ambient).Perm ambient := by
  have h := List.filter_append_perm (fun id => !(detachedTest extent links core id)) ambient
  simpa only [Bool.not_not] using h

theorem detached_mem {extent : Nat} {links : List Z4Link} {core ambient : List Nat} {id : Nat}
    (hi : id ∈ detachedIds extent links core ambient) : id ∈ ambient := (List.mem_filter.mp hi).1

theorem collar_mem {extent : Nat} {links : List Z4Link} {core ambient : List Nat} {id : Nat}
    (hi : id ∈ collarIds extent links core ambient) : id ∈ ambient := (List.mem_filter.mp hi).1

theorem detached_disjoint (extent : Nat) (links : List Z4Link) (core ambient : List Nat) :
    LinksDisjoint (links++faceLinks extent core) (faceLinks extent (detachedIds extent links core ambient)) := by
  intro link hl hr
  obtain ⟨id, hi, he⟩ := List.mem_flatMap.mp hr
  have hd := (disjointTest_iff _ _).mp (List.mem_filter.mp hi).2
  exact hd link hl (List.mem_flatMap.mpr ⟨id, List.mem_cons_self, he⟩)

end YMGap.Continuum.BF4ExactSlabDetachedFaceRegion

#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.detachedTest
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.detachedIds
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.collarIds
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.region_partition
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.detached_mem
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.collar_mem
#print axioms YMGap.Continuum.BF4ExactSlabDetachedFaceRegion.detached_disjoint
