/-
# Volume-independent size counts for the ACTUAL boundary cores

The faithful tour-plus-mask code is applied to the existing `activeAnchors`
list, not to a replacement graph or a supplied counting hypothesis. At core
size n the bound is C(probe)*625^n, where C=2^M*625^M and M is the size of an
explicit connected carrier of the probe links. The singleton plaquette
instance has C=1250. Slab extent, ambient face count, the interior test,
representation cutoff and coupling do not enter the counting constant.

A distance-to-size bound and summing the weighted size strata remain separate
obligations. In particular this count is not a decay or physical-gap theorem.
-/

import YMGap.Continuum.BF4ExactSlabProbeCoreCode
import YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion

namespace YMGap.Continuum.BF4ExactSlabActiveCoreCount

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabProbeRootedBoundaryExpansion
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabProbeCoreCode
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder

local instance : DecidableEq CoreCode := fun left right =>
  if hm : left.1 = right.1 then
    if ht : left.2 = right.2 then isTrue (Prod.ext hm ht)
    else isFalse (fun he => ht (congrArg Prod.snd he))
  else isFalse (fun he => hm (congrArg Prod.fst he))

/-- A total finite encoder; the unused branch is never consumed by the count. -/
def rootedCode {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) (ids : List Nat) : CoreCode :=
  if ha : ids ∈ rootedAnchors extent links ambient then
    encodeCore probe extent n ids ((selected_sublist (List.mem_filter.mp ha).1).nodup hn)
      (fun id hi => hphys id (selected_mem (List.mem_filter.mp ha).1 id hi))
      (of_decide_eq_true (List.mem_filter.mp ha).2)
  else ([], [])

theorem rootedCode_injective {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (left right : List Nat) (hl : left ∈ rootedAnchors extent links ambient)
    (hr : right ∈ rootedAnchors extent links ambient)
    (he : rootedCode probe extent n ambient hn hphys left = rootedCode probe extent n ambient hn hphys right) :
    left = right := by
  apply encodeCore_injective probe extent n ambient left right hn hphys (List.mem_filter.mp hl).1
    (List.mem_filter.mp hr).1 (of_decide_eq_true (List.mem_filter.mp hl).2)
    (of_decide_eq_true (List.mem_filter.mp hr).2)
  simpa only [rootedCode, dif_pos hl, dif_pos hr] using he

theorem rootedCode_mem {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (ids : List Nat) (ha : ids ∈ rootedAnchors extent links ambient) (hs : ids.length ≤ n) :
    rootedCode probe extent n ambient hn hphys ids ∈ codeCarrier probe n := by
  rw [rootedCode, dif_pos ha]
  exact encodeCore_mem_carrier probe extent n ids _ _ _ hs

theorem rootedFamily_length_le {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (family : List (List Nat)) (hfamily : family.Nodup)
    (hroot : ∀ ids, ids ∈ family → ids ∈ rootedAnchors extent links ambient)
    (hsize : ∀ ids, ids ∈ family → ids.length ≤ n) :
    family.length ≤ 2^probe.animal.support.length * 625^(probe.animal.support.length+n) := by
  let f := rootedCode probe extent n ambient hn hphys
  have hm := CayleyPruferInjection.nodup_map_of_injOn f family hfamily
    (fun a ha b hb he => rootedCode_injective probe extent n ambient hn hphys a b
      (hroot a ha) (hroot b hb) he)
  have hcount := CayleyPruferInjection.nodup_subset_length_le (family.map f) (codeCarrier probe n) hm (by
    intro code hc
    obtain ⟨ids, hi, rfl⟩ := List.mem_map.mp hc
    exact rootedCode_mem probe extent n ambient hn hphys ids (hroot ids hi) (hsize ids hi))
  calc
    family.length = (family.map f).length := (List.length_map f).symm
    _ ≤ (codeCarrier probe n).length := hcount
    _ = _ := codeCarrier_length probe n

def activeAtSize (extent : Nat) (links : List Z4Link) (keep : Nat → Bool)
    (ambient : List Nat) (n : Nat) : List (List Nat) :=
  (activeAnchors extent links keep ambient).filter (fun ids => decide (ids.length = n))

theorem activeAtSize_nodup (extent : Nat) (links : List Z4Link) (keep : Nat → Bool)
    (ambient : List Nat) (n : Nat) (hn : ambient.Nodup) :
    (activeAtSize extent links keep ambient n).Nodup :=
  List.filter_sublist.nodup (List.filter_sublist.nodup (List.filter_sublist.nodup (selections_nodup ambient hn)))

def countPrefactor {links : List Z4Link} (probe : ProbeCarrier links) : Nat :=
  2^probe.animal.support.length * 625^probe.animal.support.length

/-- The original active-family size count with a probe-only prefactor and rate 625. -/
theorem activeAtSize_length_le {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat)
    (keep : Nat → Bool) (ambient : List Nat) (n : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    (activeAtSize extent links keep ambient n).length ≤ countPrefactor probe * 625^n := by
  have h := rootedFamily_length_le probe extent n ambient hn hphys
    (activeAtSize extent links keep ambient n) (activeAtSize_nodup extent links keep ambient n hn)
    (fun _ hi => (List.mem_filter.mp (List.mem_filter.mp hi).1).1)
    (fun _ hi => Nat.le_of_eq (of_decide_eq_true (List.mem_filter.mp hi).2))
  have he : 2^probe.animal.support.length * 625^(probe.animal.support.length+n) = countPrefactor probe * 625^n := by
    rw [Nat.pow_add, ← Nat.mul_assoc]
    rfl
  exact he ▸ h

theorem full_activeAtSize_length_le {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat)
    (keep : Nat → Bool) (n : Nat) :
    (activeAtSize extent links keep (slabPhysicalFaceEdges extent) n).length ≤ countPrefactor probe * 625^n :=
  activeAtSize_length_le probe extent keep _ n (CayleyParentInj.range_nodup _) (fun _ hi => hi)

/-- A concrete geometric carrier, with no supplied connectivity field. -/
theorem singleton_activeAtSize_length_le (p : Z4Plaq) (extent : Nat) (keep : Nat → Bool) (n : Nat) :
    (activeAtSize extent (edgesOf p) keep (slabPhysicalFaceEdges extent) n).length ≤ 1250 * 625^n := by
  have h := full_activeAtSize_length_le (singletonCarrier p) extent keep n
  have he : countPrefactor (singletonCarrier p) = 1250 := by
    change 2^1 * 625^1 = 1250
    decide
  exact (congrArg (fun m => m*625^n) he) ▸ h

end YMGap.Continuum.BF4ExactSlabActiveCoreCount

#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.rootedCode
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.rootedCode_injective
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.rootedCode_mem
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.rootedFamily_length_le
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.activeAtSize
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.activeAtSize_nodup
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.countPrefactor
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.activeAtSize_length_le
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.full_activeAtSize_length_le
#print axioms YMGap.Continuum.BF4ExactSlabActiveCoreCount.singleton_activeAtSize_length_le
