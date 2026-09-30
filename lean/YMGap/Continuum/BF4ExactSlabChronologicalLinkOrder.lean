/-
# Chronological enumeration of the original physical slab links

Every original quaternion block is listed exactly once, grouped by its
actual link time.  A prefix may stop within a time layer; even then it
contains all earlier-time links and no later-time links.  This finite
ordering is distinct from the eight-color conditional-sweep schedule.
-/

import YMGap.Continuum.BF4ExactSlabReplicaCutComparison
import YMGap.Continuum.BF4ExactSlabVacuumReflection
import YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
import YMGap.Continuum.Z4CanonicalPolymerUniverse
import YMGap.Continuum.CayleyParentInj

namespace YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabVacuumReflection
open YMGap.Continuum.BF4ExactSlabSpatialLinkReflection
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.BF4ExactSlabReplicaCutComparison

private abbrev blocks (extent : Nat) := (boundaryCompleteSlabLinks extent).length

def linkTime (extent j : Nat) : Nat :=
  (correctedSlabLinkAt extent j).1.2.2.2

/-- The original block indices whose actual physical links start at `time`. -/
def timeLayerBlocks (extent time : Nat) : List Nat :=
  (List.range (blocks extent)).filter (fun j => decide (linkTime extent j = time))

theorem mem_timeLayerBlocks (extent time j : Nat) :
    j ∈ timeLayerBlocks extent time ↔
      j < blocks extent ∧ linkTime extent j = time := by
  simp [timeLayerBlocks]

theorem timeLayerBlocks_nodup (extent time : Nat) :
    (timeLayerBlocks extent time).Nodup :=
  List.filter_sublist.nodup (CayleyParentInj.range_nodup _)

/-- A computable permutation of the original link-block list, grouped by
physical time and retaining original block order inside each layer. -/
def chronologicalBlocks (extent : Nat) : List Nat :=
  (List.range (extent+1)).flatMap (timeLayerBlocks extent)

private theorem time_mem_range {extent j : Nat} (hj : j < blocks extent) :
    linkTime extent j < extent+1 := by
  have hl := correctedSlabLinkAt_mem (List.mem_range.mpr hj)
  have ht := linkTimeAdmissible_of_mem_boundaryCompleteSlabLinks hl
  unfold linkTime
  cases hdir : (correctedSlabLinkAt extent j).2 <;>
    simp [linkTimeAdmissible, hdir] at ht <;> omega

theorem chronologicalBlocks_covers (extent j : Nat) (hj : j < blocks extent) :
    j ∈ chronologicalBlocks extent := by
  apply List.mem_flatMap.mpr
  refine ⟨linkTime extent j, List.mem_range.mpr (time_mem_range hj), ?_⟩
  exact (mem_timeLayerBlocks extent (linkTime extent j) j).mpr ⟨hj, rfl⟩

private theorem layers_nodup (extent : Nat) :
    ∀ ts : List Nat, ts.Pairwise (· < ·) →
      (ts.flatMap (timeLayerBlocks extent)).Nodup
  | [], _ => List.nodup_nil
  | time :: rest, ht => by
      have hparts := List.pairwise_cons.mp ht
      rw [List.flatMap_cons]
      apply List.nodup_append.mpr
      refine ⟨timeLayerBlocks_nodup extent time,
        layers_nodup extent rest hparts.2, ?_⟩
      intro i hi j hj he
      obtain ⟨later, hlater, hjlayer⟩ := List.mem_flatMap.mp hj
      have hitime := (mem_timeLayerBlocks extent time i).mp hi |>.2
      have hjtime := (mem_timeLayerBlocks extent later j).mp hjlayer |>.2
      have hlt := hparts.1 later hlater
      subst j
      omega

theorem chronologicalBlocks_nodup (extent : Nat) :
    (chronologicalBlocks extent).Nodup := by
  unfold chronologicalBlocks
  exact layers_nodup extent _ (CayleyParentInj.range_pairwise _)

/-- No boundary block is omitted or duplicated. -/
theorem chronologicalBlocks_perm (extent : Nat) :
    (chronologicalBlocks extent).Perm (List.range (blocks extent)) := by
  apply perm_of_nodup_mem_iff _ _
    (chronologicalBlocks_nodup extent)
    (CayleyParentInj.range_nodup _)
  intro j
  constructor
  · intro hj
    obtain ⟨time, _, htime⟩ := List.mem_flatMap.mp hj
    exact List.mem_range.mpr ((mem_timeLayerBlocks extent time j).mp htime).1
  · intro hj
    exact chronologicalBlocks_covers extent j (List.mem_range.mp hj)

theorem chronologicalBlocks_length (extent : Nat) :
    (chronologicalBlocks extent).length = blocks extent := by
  simpa only [List.length_range] using (chronologicalBlocks_perm extent).length_eq

private theorem pairwise_constant (extent time : Nat) :
    ∀ xs : List Nat,
      (∀ j, j ∈ xs → linkTime extent j = time) →
      xs.Pairwise (fun i j => linkTime extent i ≤ linkTime extent j)
  | [], _ => List.Pairwise.nil
  | i :: xs, h => by
      apply List.pairwise_cons.mpr
      constructor
      · intro j hj
        rw [h i List.mem_cons_self, h j (List.mem_cons_of_mem i hj)]
        exact Nat.le_refl _
      · exact pairwise_constant extent time xs
          (fun j hj => h j (List.mem_cons_of_mem i hj))

private theorem layers_pairwise (extent : Nat) :
    ∀ ts : List Nat, ts.Pairwise (· < ·) →
      (ts.flatMap (timeLayerBlocks extent)).Pairwise
        (fun i j => linkTime extent i ≤ linkTime extent j)
  | [], _ => List.Pairwise.nil
  | time :: rest, ht => by
      have hparts := List.pairwise_cons.mp ht
      rw [List.flatMap_cons, List.pairwise_append]
      refine ⟨pairwise_constant extent time _
        (fun j hj => ((mem_timeLayerBlocks extent time j).mp hj).2),
        layers_pairwise extent rest hparts.2, ?_⟩
      intro i hi j hj
      obtain ⟨later, hlater, hjlayer⟩ := List.mem_flatMap.mp hj
      have hitime := (mem_timeLayerBlocks extent time i).mp hi |>.2
      have hjtime := (mem_timeLayerBlocks extent later j).mp hjlayer |>.2
      have hlt := hparts.1 later hlater
      omega

theorem chronologicalBlocks_pairwise (extent : Nat) :
    (chronologicalBlocks extent).Pairwise
      (fun i j => linkTime extent i ≤ linkTime extent j) := by
  unfold chronologicalBlocks
  exact layers_pairwise extent _ (CayleyParentInj.range_pairwise _)

private theorem split_next : ∀ (xs : List Nat) (k : Nat), k < xs.length →
    xs = xs.take k ++ xs.getD k 0 :: xs.drop (k+1)
  | [], _, h => by simp at h
  | i :: xs, 0, _ => rfl
  | i :: xs, k+1, h => by
      have hk : k < xs.length := by simp at h; omega
      have ih := split_next xs k hk
      change i :: xs = (i :: xs.take k) ++ xs.getD k 0 :: xs.drop (k+1)
      simpa only [List.cons_append] using congrArg (List.cons i) ih

def nextBlock (extent k : Nat) : Nat :=
  (chronologicalBlocks extent).getD k 0

def nextTime (extent k : Nat) : Nat := linkTime extent (nextBlock extent k)

def prefixCut (extent k : Nat) : List Z4Link :=
  ((chronologicalBlocks extent).take k).map (correctedSlabLinkAt extent)

/-- At the next link's time, a chronological prefix contains all earlier
physical links and excludes all later ones. Same-time links are unrestricted. -/
theorem prefixCut_time_bounds (extent k : Nat)
    (hk : k < (chronologicalBlocks extent).length) :
    (∀ link, link ∈ boundaryCompleteSlabLinks extent →
      link.1.2.2.2 < nextTime extent k → link ∈ prefixCut extent k) ∧
    (∀ link, link ∈ boundaryCompleteSlabLinks extent →
      nextTime extent k < link.1.2.2.2 → link ∉ prefixCut extent k) := by
  let xs := chronologicalBlocks extent
  let pre := xs.take k
  let i := xs.getD k 0
  let post := xs.drop (k+1)
  have hsplit : xs = pre ++ i :: post := split_next xs k hk
  have hpw := chronologicalBlocks_pairwise extent
  change xs.Pairwise (fun a b => linkTime extent a ≤ linkTime extent b) at hpw
  rw [hsplit, List.pairwise_append] at hpw
  have htail := List.pairwise_cons.mp hpw.2.1
  constructor
  · intro link hlink htime
    let j := (boundaryCompleteSlabLinks extent).idxOf link
    have hj : j < blocks extent := List.idxOf_lt_length_of_mem hlink
    have hmem : j ∈ xs := chronologicalBlocks_covers extent j hj
    rw [hsplit] at hmem
    have hpre : j ∈ pre := by
      rcases List.mem_append.mp hmem with hpre | hrest
      · exact hpre
      · rcases List.mem_cons.mp hrest with heq | hpost
        · have hp : correctedSlabLinkAt extent j = link := correctedSlabLinkAt_idxOf hlink
          have ht : linkTime extent j = nextTime extent k := by
            rw [heq]
            rfl
          simp only [linkTime, hp] at ht
          omega
        · have horder := htail.1 j hpost
          have hp : correctedSlabLinkAt extent j = link := correctedSlabLinkAt_idxOf hlink
          change nextTime extent k ≤ linkTime extent j at horder
          simp only [linkTime, hp] at horder
          omega
    apply List.mem_map.mpr
    exact ⟨j, hpre, correctedSlabLinkAt_idxOf hlink⟩
  · intro link _ htime hselected
    obtain ⟨j, hj, heq⟩ := List.mem_map.mp hselected
    have horder := hpw.2.2 j hj i List.mem_cons_self
    change linkTime extent j ≤ nextTime extent k at horder
    rw [← heq] at htime
    change nextTime extent k < linkTime extent j at htime
    omega

/-- The existing two-layer area count applies to EVERY nonterminal
chronological prefix, including one stopped partway through a time layer. -/
theorem prefix_crossingCount_le_area (extent k : Nat)
    (hk : k < (chronologicalBlocks extent).length) :
    crossingCount extent (prefixCut extent k) ≤ 12 * (extent+1)^3 := by
  have h := prefixCut_time_bounds extent k hk
  exact crossingCount_le_area extent (nextTime extent k)
    (prefixCut extent k) h.1 h.2

#print axioms timeLayerBlocks
#print axioms chronologicalBlocks
#print axioms chronologicalBlocks_nodup
#print axioms chronologicalBlocks_covers
#print axioms chronologicalBlocks_perm
#print axioms chronologicalBlocks_length
#print axioms chronologicalBlocks_pairwise
#print axioms prefixCut_time_bounds
#print axioms prefix_crossingCount_le_area

end YMGap.Continuum.BF4ExactSlabChronologicalLinkOrder
