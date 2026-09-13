/-
# Faithful finite coding of the ORIGINAL probe-rooted core

The augmented animal's padded tour is paired with the subset of carrier
faces belonging to the original core. A finite decoder filters the original
ambient order and recovers that core literally. The mask is essential:
augmentation alone forgets which carrier faces were already present.

For a fixed M-face probe carrier and cores of size at most n, the code list
has length 2^M * 625^(M+n). Neither the list nor its length names slab extent,
representation cutoff or coupling. This module proves the code and inverse;
the actual active-family cardinality consumer is separate.
-/

import YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
import YMGap.Continuum.FiniteSelectionMerge

namespace YMGap.Continuum.BF4ExactSlabProbeCoreCode

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FinitePolynomialSubsetExpansion
open YMGap.Continuum.FiniteSelectionOrder
open YMGap.Continuum.FiniteSelectionMerge
open YMGap.Continuum.BddLatticeAnimal

abbrev CoreCode := List Z4Plaq × List (Fin (z4Chain.D+1))

def carrierMask {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat) (ids : List Nat) : List Z4Plaq :=
  probe.animal.support.filter (fun p => decide (p ∈ coreFaces extent ids))

def encodeCore {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hf : core extent links ids = ids) : CoreCode :=
  (carrierMask probe extent ids,
    rootedAnimalPaddedTourCode (augmentedAnimal probe extent ids hn hphys hf) (probe.animal.support.length+n))

def codeFace {links : List Z4Link} (probe : ProbeCarrier links) (code : CoreCode) (p : Z4Plaq) : Bool :=
  if p ∈ probe.animal.support then decide (p ∈ code.1)
  else decide (p ∈ decode z4Chain probe.animal.root code.2)

def decodeCore {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat)
    (ambient : List Nat) (code : CoreCode) : List Nat :=
  ambient.filter (fun id => codeFace probe code (slabPlaquetteAt extent id))

theorem codeFace_encode {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hf : core extent links ids = ids) (p : Z4Plaq) :
    codeFace probe (encodeCore probe extent n ids hn hphys hf) p = true ↔ p ∈ coreFaces extent ids := by
  by_cases hp : p ∈ probe.animal.support
  · change (if p ∈ probe.animal.support then decide (p ∈ carrierMask probe extent ids) else _) = true ↔ _
    rw [if_pos hp, decide_eq_true_eq]
    constructor
    · intro h; exact of_decide_eq_true (List.mem_filter.mp h).2
    · intro h; exact List.mem_filter.mpr ⟨hp, decide_eq_true h⟩
  · change (if p ∈ probe.animal.support then _ else decide
        (p ∈ decode z4Chain probe.animal.root
          (rootedAnimalPaddedTourCode (augmentedAnimal probe extent ids hn hphys hf)
            (probe.animal.support.length+n)))) = true ↔ _
    rw [if_neg hp, decide_eq_true_eq]
    have hd := rootedAnimalPaddedTourCode_decode_sameSupport
      (augmentedAnimal probe extent ids hn hphys hf) (probe.animal.support.length+n)
    constructor
    · intro h; exact ((augmented_mem_iff probe extent ids p).mp (hd.2 p h)).resolve_left hp
    · intro h; exact hd.1 p ((augmented_mem_iff probe extent ids p).mpr (Or.inr h))

theorem coreFaces_mem_iff (extent : Nat) (ids : List Nat)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) (id : Nat)
    (hi : id ∈ slabPhysicalFaceEdges extent) :
    slabPlaquetteAt extent id ∈ coreFaces extent ids ↔ id ∈ ids := by
  constructor
  · intro h
    obtain ⟨j, hj, he⟩ := List.mem_map.mp h
    exact (slabPlaquetteAt_injective_on_physical (hphys j hj) hi he) ▸ hj
  · intro h; exact List.mem_map.mpr ⟨id, h, rfl⟩

/-- The computed decoder restores literal identifiers in the original ambient order. -/
theorem decodeCore_encode {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient ids : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hs : ids ∈ selections ambient) (hf : core extent links ids = ids) :
    decodeCore probe extent ambient (encodeCore probe extent n ids ((selected_sublist hs).nodup hn)
      (fun id hi => hphys id (selected_mem hs id hi)) hf) = ids := by
  apply selected_eq_of_mem_iff hn (filter_selected _ _) hs
  intro id
  constructor
  · intro h
    have ha := (List.mem_filter.mp h).1
    exact (coreFaces_mem_iff extent ids (fun j hj => hphys j (selected_mem hs j hj)) id (hphys id ha)).mp
      ((codeFace_encode probe extent n ids _ _ hf _).mp (List.mem_filter.mp h).2)
  · intro hi
    exact List.mem_filter.mpr ⟨selected_mem hs id hi,
      (codeFace_encode probe extent n ids _ _ hf _).mpr (List.mem_map.mpr ⟨id, hi, rfl⟩)⟩

theorem encodeCore_injective {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ambient left right : List Nat) (hn : ambient.Nodup)
    (hphys : ∀ id, id ∈ ambient → id ∈ slabPhysicalFaceEdges extent)
    (hl : left ∈ selections ambient) (hr : right ∈ selections ambient)
    (hfl : core extent links left = left) (hfr : core extent links right = right)
    (he : encodeCore probe extent n left ((selected_sublist hl).nodup hn)
        (fun id hi => hphys id (selected_mem hl id hi)) hfl =
      encodeCore probe extent n right ((selected_sublist hr).nodup hn)
        (fun id hi => hphys id (selected_mem hr id hi)) hfr) : left = right := by
  have hd := congrArg (decodeCore probe extent ambient) he
  rw [decodeCore_encode probe extent n ambient left hn hphys hl hfl,
    decodeCore_encode probe extent n ambient right hn hphys hr hfr] at hd
  exact hd

def codeCarrier {links : List Z4Link} (probe : ProbeCarrier links) (n : Nat) : List CoreCode :=
  (selections probe.animal.support).flatMap (fun mask =>
    (rootedAnimalPaddedTourCarrier z4Chain (probe.animal.support.length+n)).map (fun tour => (mask, tour)))

theorem encodeCore_mem_carrier {links : List Z4Link} (probe : ProbeCarrier links) (extent n : Nat)
    (ids : List Nat) (hn : ids.Nodup) (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hf : core extent links ids = ids) (hsize : ids.length ≤ n) :
    encodeCore probe extent n ids hn hphys hf ∈ codeCarrier probe n := by
  apply List.mem_flatMap.mpr
  refine ⟨carrierMask probe extent ids, filter_selected _ _, ?_⟩
  apply List.mem_map.mpr
  refine ⟨_, rootedAnimalPaddedTourCode_mem_carrier (augmentedAnimal probe extent ids hn hphys hf)
    (probe.animal.support.length+n) ?_, rfl⟩
  exact Nat.le_trans (augmented_length_le probe extent ids) (Nat.add_le_add_left hsize _)

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

theorem codeCarrier_length {links : List Z4Link} (probe : ProbeCarrier links) (n : Nat) :
    (codeCarrier probe n).length = 2^probe.animal.support.length * 625^(probe.animal.support.length+n) := by
  unfold codeCarrier
  rw [pairs_length]
  exact (congrArg (fun m => m * (rootedAnimalPaddedTourCarrier z4Chain (probe.animal.support.length+n)).length)
    (selections_length (probe.animal.support : List Z4Plaq))).trans
    (congrArg (fun m => 2^probe.animal.support.length * m)
      (z4RootedAnimalPaddedTourCarrier_length (probe.animal.support.length+n)))

end YMGap.Continuum.BF4ExactSlabProbeCoreCode

#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.carrierMask
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.encodeCore
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.codeFace
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.decodeCore
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.codeFace_encode
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.coreFaces_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.decodeCore_encode
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.encodeCore_injective
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.codeCarrier
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.encodeCore_mem_carrier
#print axioms YMGap.Continuum.BF4ExactSlabProbeCoreCode.codeCarrier_length
