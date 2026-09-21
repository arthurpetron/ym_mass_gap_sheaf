/-
# The SAME connecting cores with descent-only entropy

The existing injective code and its exact decoder are unchanged. Its animal
tour lies in the image of a smaller carrier: binary shape plus one neighbor
choice per descent, padded to a common mass budget. Thus the actual original
connecting family has size-n count at most 2^M*96^M*96^n, instead of
2^M*625^M*625^n. No weight, measure, core selection or geometry is replaced.
-/
import YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode
import YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount

namespace YMGap.Continuum.BF4ExactSlabDescentCoreCount

set_option autoImplicit false
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier)
open YMGap.Continuum.BF4ExactSlabProbeCoreCode (CoreCode)
open YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
open YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount
open YMGap.Continuum.BF4ExactSlabRootedSelection (core)
open YMGap.Continuum.BF4ExactSlabSelectionSeparation (keep)
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteRootedAnimalDescentCode (inflate)
open YMGap.Continuum.FiniteRootedAnimalPaddedDescentCode
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteWeightedCartesianInjection (cartesian mem_cartesian_iff)
open YMGap.Continuum.BF4ExactSlabTwoCapLocalCode (cartesian_length)
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local instance : DecidableEq CoreCode := fun a b =>
  if hm : a.1 = b.1 then
    if ht : a.2 = b.2 then isTrue (Prod.ext hm ht)
    else isFalse (fun he => ht (congrArg Prod.snd he))
  else isFalse (fun he => hm (congrArg Prod.fst he))

/-- An enumerable image of the smaller codes in the OLD tour alphabet. -/
def tourCarrier (m : Nat) : List (List (Fin (z4Chain.D+1))) :=
  (carrier z4Chain.D m).map (fun c => inflate c.1 c.2)

theorem tourCarrier_length (m : Nat) : (tourCarrier m).length = 96^m := by
  rw [tourCarrier, List.length_map, carrier_length]
  rfl

theorem paddedTour_mem (animal : RootedConnectedAnimal z4Chain) (m : Nat)
    (hm : animal.support.length ≤ m) : rootedAnimalPaddedTourCode animal m ∈ tourCarrier m := by
  exact List.mem_map.mpr ⟨paddedCode animal ⟨0, by decide⟩ m,
    paddedCode_mem animal ⟨0, by decide⟩ m hm, inflate_paddedCode animal ⟨0, by decide⟩ m⟩

variable {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)

def codeCarrier (n : Nat) : List CoreCode :=
  cartesian (selections (P.animal.support++Q.animal.support))
    (tourCarrier (totalProbeSize P Q+n))

theorem encodeCore_mem (extent n : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hk : keep extent left right ids = true) (hf : core extent (left++right) ids = ids)
    (hs : ids.length ≤ n) : encodeCore P Q extent n ids hn hphys hk hf ∈ codeCarrier P Q n := by
  apply (mem_cartesian_iff _ _ _).mpr
  exact ⟨filter_selected _ _, paddedTour_mem (augmentedAnimal P Q extent ids hn hphys hk hf)
    (totalProbeSize P Q+n) (Nat.le_trans (augmented_size_le P Q extent ids) (Nat.add_le_add_left hs _))⟩

private theorem selections_length {A : Type} : ∀ xs : List A, (selections xs).length = 2^xs.length
  | [] => rfl
  | a::xs => by
      change (selections xs ++ (selections xs).map (fun ys => a::ys)).length = _
      rw [List.length_append, List.length_map, selections_length]
      simp only [List.length_cons, Nat.pow_succ]
      omega

theorem codeCarrier_length (n : Nat) :
    (codeCarrier P Q n).length = 2^(totalProbeSize P Q)*96^(totalProbeSize P Q+n) := by
  rw [codeCarrier, cartesian_length, tourCarrier_length]
  have hm := selections_length (P.animal.support++Q.animal.support : List Z4Plaq)
  rw [List.length_append] at hm
  exact congrArg (fun m => m*96^(totalProbeSize P Q+n)) hm

/-- The original decoder/injection now lands in the smaller counted image. -/
theorem connectingFamily_length_le (extent n : Nat) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (family : List (List Nat)) (hf : family.Nodup)
    (ha : ∀ ids, ids ∈ family → ids ∈ connectingAnchors extent left right ambient)
    (hs : ∀ ids, ids ∈ family → ids.length ≤ n) :
    family.length ≤ 2^(totalProbeSize P Q)*96^(totalProbeSize P Q+n) := by
  let f := connectingCode P Q extent n ambient hn hphys
  have hinj : ∀ a, a ∈ family → ∀ b, b ∈ family → f a = f b → a=b := by
    intro a hA b hB he
    have hh := congrArg (decodeCore P Q extent ambient) he
    rw [connectingCode_recovers P Q extent n ambient hn hphys a (ha a hA),
      connectingCode_recovers P Q extent n ambient hn hphys b (ha b hB)] at hh
    exact hh
  have hm := CayleyPruferInjection.nodup_map_of_injOn f family hf hinj
  have hb := CayleyPruferInjection.nodup_subset_length_le (family.map f) (codeCarrier P Q n) hm (by
    intro code hc
    obtain ⟨ids, hi, rfl⟩ := List.mem_map.mp hc
    change connectingCode P Q extent n ambient hn hphys ids ∈ _
    rw [connectingCode, dif_pos (ha ids hi)]
    exact encodeCore_mem P Q extent n ids _ _ _ _ (hs ids hi))
  rw [List.length_map, codeCarrier_length] at hb
  exact hb

def countPrefactor : Nat := 2^(totalProbeSize P Q)*96^(totalProbeSize P Q)

theorem connectingAtSize_length_le (extent : Nat) (ambient : List Nat) (n : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    ((connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length=n))).length ≤
      countPrefactor P Q*96^n := by
  have h := connectingFamily_length_le P Q extent n ambient hn hphys _
    (List.filter_sublist.nodup (connecting_nodup extent left right ambient hn))
    (fun _ hi => (List.mem_filter.mp hi).1)
    (fun _ hi => Nat.le_of_eq (of_decide_eq_true (List.mem_filter.mp hi).2))
  rw [Nat.pow_add, ← Nat.mul_assoc] at h
  exact h

end YMGap.Continuum.BF4ExactSlabDescentCoreCount

#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.tourCarrier
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.tourCarrier_length
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.paddedTour_mem
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.codeCarrier
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.encodeCore_mem
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.codeCarrier_length
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.connectingFamily_length_le
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.countPrefactor
#print axioms YMGap.Continuum.BF4ExactSlabDescentCoreCount.connectingAtSize_length_le
