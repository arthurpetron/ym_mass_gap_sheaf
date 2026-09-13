/-
# Separation-independent counting of ORIGINAL retained two-probe cores

The literal animal tour is paired with a mask recording which probe faces
belong to the original core. Decoding in ambient order recovers that core
exactly. For two carriers of total size M and n-face cores, the finite
code list has length 2^M * 625^(M+n). Neither separation, volume, cutoff
nor coupling enters this bound. No corridor between probes is included.

The counted list is exactly the common-root anchors passing the existing
separator test. The actual signed connected numerator expands over this
list after spectator resummation. Normalized weights, distance-to-size
control and thermodynamic time decay remain separate obligations.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
import YMGap.Continuum.BF4ExactSlabProbeCoreCode
import YMGap.Continuum.BF4ExactSlabRootedFamilyResummation

namespace YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier coreFaces)
open YMGap.Continuum.BF4ExactSlabProbeCoreCode (CoreCode coreFaces_mem_iff)
open YMGap.Continuum.BF4ExactSlabTwoProbeAnimal
open YMGap.Continuum.BF4ExactSlabRootedSelection (core)
open YMGap.Continuum.BF4ExactSlabRootedFamilyResummation
open YMGap.Continuum.BF4ExactSlabConnectedSelectionExpansion
open YMGap.Continuum.BF4ExactSlabDisconnectedHaarCancellation
open YMGap.Continuum.BF4ExactSlabSpectatorResummation
open YMGap.Continuum.BF4ExactSlabDetachedFaceRegion
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMerge
open YMGap.Continuum.FiniteSelectionMobius
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

local instance : DecidableEq CoreCode := fun a b =>
  if hm : a.1 = b.1 then
    if ht : a.2 = b.2 then isTrue (Prod.ext hm ht)
    else isFalse (fun he => ht (congrArg Prod.snd he))
  else isFalse (fun he => hm (congrArg Prod.fst he))

def connectingAnchors (extent : Nat) (left right : List Z4Link) (ambient : List Nat) : List (List Nat) :=
  (rootedAnchors extent (left++right) ambient).filter (keep extent left right)

theorem connecting_selected {extent : Nat} {left right : List Z4Link} {ambient ids : List Nat}
    (h : ids ∈ connectingAnchors extent left right ambient) : ids ∈ selections ambient :=
  (List.mem_filter.mp (List.mem_filter.mp h).1).1

theorem connecting_fixed {extent : Nat} {left right : List Z4Link} {ambient ids : List Nat}
    (h : ids ∈ connectingAnchors extent left right ambient) : core extent (left++right) ids = ids :=
  of_decide_eq_true (List.mem_filter.mp (List.mem_filter.mp h).1).2

theorem connecting_keep {extent : Nat} {left right : List Z4Link} {ambient ids : List Nat}
    (h : ids ∈ connectingAnchors extent left right ambient) : keep extent left right ids = true :=
  (List.mem_filter.mp h).2

theorem connecting_nodup (extent : Nat) (left right : List Z4Link) (ambient : List Nat) (hn : ambient.Nodup) :
    (connectingAnchors extent left right ambient).Nodup :=
  List.filter_sublist.nodup (List.filter_sublist.nodup (selections_nodup ambient hn))

section Probes

variable {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)

def totalProbeSize : Nat := P.animal.support.length+Q.animal.support.length

def mask (extent : Nat) (ids : List Nat) : List Z4Plaq :=
  (P.animal.support++Q.animal.support).filter (fun p => decide (p ∈ coreFaces extent ids))

def encodeCore (extent n : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hk : keep extent left right ids = true) (hf : core extent (left++right) ids = ids) : CoreCode :=
  (mask P Q extent ids, rootedAnimalPaddedTourCode (augmentedAnimal P Q extent ids hn hphys hk hf)
    (totalProbeSize P Q+n))

def codeFace (code : CoreCode) (p : Z4Plaq) : Bool :=
  if p ∈ P.animal.support++Q.animal.support then decide (p ∈ code.1)
  else decide (p ∈ decode z4Chain P.animal.root code.2)

def decodeCore (extent : Nat) (ambient : List Nat) (code : CoreCode) : List Nat :=
  ambient.filter (fun id => codeFace P Q code (slabPlaquetteAt extent id))

theorem codeFace_encode (extent n : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hk : keep extent left right ids = true) (hf : core extent (left++right) ids = ids) (p : Z4Plaq) :
    codeFace P Q (encodeCore P Q extent n ids hn hphys hk hf) p = true ↔ p ∈ coreFaces extent ids := by
  by_cases hp : p ∈ P.animal.support++Q.animal.support
  · change (if p ∈ P.animal.support++Q.animal.support then decide (p ∈ mask P Q extent ids) else _) = true ↔ _
    rw [if_pos hp, decide_eq_true_eq]
    exact ⟨fun h => of_decide_eq_true (List.mem_filter.mp h).2, fun h => List.mem_filter.mpr ⟨hp, decide_eq_true h⟩⟩
  · change (if p ∈ P.animal.support++Q.animal.support then _ else decide
        (p ∈ decode z4Chain P.animal.root
          (rootedAnimalPaddedTourCode (augmentedAnimal P Q extent ids hn hphys hk hf) (totalProbeSize P Q+n)))) = true ↔ _
    rw [if_neg hp, decide_eq_true_eq]
    have hnot : p ∉ probeSupport P Q := fun h => hp (List.mem_append.mpr ((probeSupport_mem P Q p).mp h))
    have hd := rootedAnimalPaddedTourCode_decode_sameSupport
      (augmentedAnimal P Q extent ids hn hphys hk hf) (totalProbeSize P Q+n)
    exact ⟨fun h => ((augmented_mem P Q extent ids p).mp (hd.2 p h)).resolve_left hnot,
      fun h => hd.1 p ((augmented_mem P Q extent ids p).mpr (Or.inr h))⟩

theorem decodeCore_encode (extent n : Nat) (ambient ids : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hs : ids ∈ selections ambient) (hk : keep extent left right ids = true)
    (hf : core extent (left++right) ids = ids) :
    decodeCore P Q extent ambient (encodeCore P Q extent n ids ((selected_sublist hs).nodup hn)
      (fun id hi => hphys id (selected_mem hs id hi)) hk hf) = ids := by
  apply selected_eq_of_mem_iff hn (filter_selected _ _) hs
  intro id
  constructor
  · intro h
    exact (coreFaces_mem_iff extent ids (fun j hj => hphys j (selected_mem hs j hj)) id
      (hphys id (List.mem_filter.mp h).1)).mp ((codeFace_encode P Q extent n ids _ _ hk hf _).mp (List.mem_filter.mp h).2)
  · intro hi
    exact List.mem_filter.mpr ⟨selected_mem hs id hi,
      (codeFace_encode P Q extent n ids _ _ hk hf _).mpr (List.mem_map.mpr ⟨id, hi, rfl⟩)⟩

def codeCarrier (n : Nat) : List CoreCode :=
  (selections (P.animal.support++Q.animal.support)).flatMap (fun mask =>
    (rootedAnimalPaddedTourCarrier z4Chain (totalProbeSize P Q+n)).map (fun tour => (mask, tour)))

theorem encodeCore_mem (extent n : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hk : keep extent left right ids = true) (hf : core extent (left++right) ids = ids) (hs : ids.length ≤ n) :
    encodeCore P Q extent n ids hn hphys hk hf ∈ codeCarrier P Q n := by
  apply List.mem_flatMap.mpr
  refine ⟨mask P Q extent ids, filter_selected _ _, List.mem_map.mpr ⟨_, ?_, rfl⟩⟩
  exact rootedAnimalPaddedTourCode_mem_carrier (augmentedAnimal P Q extent ids hn hphys hk hf)
    (totalProbeSize P Q+n) (Nat.le_trans (augmented_size_le P Q extent ids) (Nat.add_le_add_left hs _))

private theorem selections_length {A : Type} : ∀ xs : List A, (selections xs).length = 2^xs.length
  | [] => rfl
  | a :: xs => by
      change (selections xs ++ (selections xs).map (fun ys => a::ys)).length = _
      rw [List.length_append, List.length_map, selections_length]
      simp only [List.length_cons, Nat.pow_succ]
      omega

private theorem pairs_length {A B : Type} (ys : List B) : ∀ xs : List A,
    (xs.flatMap (fun x => ys.map (fun y => (x,y)))).length = xs.length*ys.length
  | [] => (Nat.zero_mul ys.length).symm
  | x :: xs => by
      rw [List.flatMap_cons, List.length_append, List.length_map, pairs_length, List.length_cons, Nat.add_mul]
      simp only [Nat.one_mul, Nat.add_comm]

theorem codeCarrier_length (n : Nat) : (codeCarrier P Q n).length = 2^(totalProbeSize P Q)*625^(totalProbeSize P Q+n) := by
  unfold codeCarrier
  rw [pairs_length]
  have hm := selections_length (P.animal.support++Q.animal.support : List Z4Plaq)
  rw [List.length_append] at hm
  exact (congrArg (fun m => m*(rootedAnimalPaddedTourCarrier z4Chain (totalProbeSize P Q+n)).length) hm).trans
    (congrArg (fun m => 2^(totalProbeSize P Q)*m) (z4RootedAnimalPaddedTourCarrier_length (totalProbeSize P Q+n)))

def connectingCode (extent n : Nat) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) (ids : List Nat) : CoreCode :=
  if ha : ids ∈ connectingAnchors extent left right ambient then
    encodeCore P Q extent n ids ((selected_sublist (connecting_selected ha)).nodup hn)
      (fun id hi => hphys id (selected_mem (connecting_selected ha) id hi)) (connecting_keep ha) (connecting_fixed ha)
  else ([], [])

theorem connectingCode_recovers (extent n : Nat) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) (ids : List Nat)
    (ha : ids ∈ connectingAnchors extent left right ambient) :
    decodeCore P Q extent ambient (connectingCode P Q extent n ambient hn hphys ids) = ids := by
  rw [connectingCode, dif_pos ha]
  exact decodeCore_encode P Q extent n ambient ids hn hphys (connecting_selected ha) (connecting_keep ha) (connecting_fixed ha)

theorem connectingFamily_length_le (extent n : Nat) (ambient : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (family : List (List Nat)) (hf : family.Nodup)
    (ha : ∀ ids, ids ∈ family → ids ∈ connectingAnchors extent left right ambient)
    (hs : ∀ ids, ids ∈ family → ids.length ≤ n) :
    family.length ≤ 2^(totalProbeSize P Q)*625^(totalProbeSize P Q+n) := by
  let f := connectingCode P Q extent n ambient hn hphys
  have hinj : ∀ a, a ∈ family → ∀ b, b ∈ family → f a = f b → a=b := by
    intro a hA b hB he
    have hd := congrArg (decodeCore P Q extent ambient) he
    rw [connectingCode_recovers P Q extent n ambient hn hphys a (ha a hA),
      connectingCode_recovers P Q extent n ambient hn hphys b (ha b hB)] at hd
    exact hd
  have hm := CayleyPruferInjection.nodup_map_of_injOn f family hf hinj
  have hb := CayleyPruferInjection.nodup_subset_length_le (family.map f) (codeCarrier P Q n) hm (by
    intro code hc
    obtain ⟨ids, hi, rfl⟩ := List.mem_map.mp hc
    change connectingCode P Q extent n ambient hn hphys ids ∈ _
    rw [connectingCode, dif_pos (ha ids hi)]
    exact encodeCore_mem P Q extent n ids _ _ _ _ (hs ids hi))
  rw [List.length_map, codeCarrier_length] at hb
  exact hb

def countPrefactor : Nat := 2^(totalProbeSize P Q)*625^(totalProbeSize P Q)

theorem connectingAtSize_length_le (extent : Nat) (ambient : List Nat) (n : Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent) :
    ((connectingAnchors extent left right ambient).filter (fun ids => decide (ids.length = n))).length ≤
      countPrefactor P Q*625^n := by
  have h := connectingFamily_length_le P Q extent n ambient hn hphys _
    (List.filter_sublist.nodup (connecting_nodup extent left right ambient hn))
    (fun _ hi => (List.mem_filter.mp hi).1)
    (fun _ hi => Nat.le_of_eq (of_decide_eq_true (List.mem_filter.mp hi).2))
  rw [Nat.pow_add, ← Nat.mul_assoc] at h
  exact h

end Probes

/-- Signed spectator resummation FIRST, then exact separator filtering. -/
theorem connectedNumerator_connecting_expansion (w : Q') (K extent : Nat) (p q : RatPoly)
    (left right : List Z4Link)
    (hp : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length p)
    (hq : SupportedQuaternionBlocks (boundaryCompleteSlabLinks extent).length q)
    (hl : LinkLocal extent left p) (hr : LinkLocal extent right q) (ambient : List Nat) (hn : ambient.Nodup) :
    connectedNumerator w K extent ambient p q ≈
      listQSum (fun ids => connectedCoefficient w K extent p q ids *
        partitionSquare w K extent (detachedIds extent (left++right) ids ambient))
        (connectingAnchors extent left right ambient) :=
  Q'.eqv_trans _ _ _ (connectedNumerator_resummed_expansion w K extent p q (left++right) hp hq
    (hl.mono (fun _ h => List.mem_append.mpr (Or.inl h)))
    (hr.mono (fun _ h => List.mem_append.mpr (Or.inr h))) ambient hn)
    (sum_filter_zero _ (keep extent left right) _ (fun ids _ hk =>
      Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _
        (coefficient_zero_of_discard w K extent p q left right hp hq hl hr ids hk)) (QPoly.q_zero_mul _)))

end YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectingAnchors
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connecting_selected
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connecting_fixed
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connecting_keep
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connecting_nodup
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.totalProbeSize
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.mask
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.encodeCore
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.codeFace
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.decodeCore
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.codeFace_encode
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.decodeCore_encode
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.codeCarrier
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.encodeCore_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.codeCarrier_length
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectingCode
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectingCode_recovers
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectingFamily_length_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.countPrefactor
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectingAtSize_length_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeCoreCount.connectedNumerator_connecting_expansion
