/-
# Independent spatial and temporal shifts of an actual connected probe

Translate the shared-link and path witnesses themselves. Coordinate
subtraction computes endpoint preimages; no path or endpoint data is
extracted from a propositional existence statement. The original box
support and link counts do not depend on either shift.
-/

import YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier

namespace YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal

def unshift (space time : Nat) (p : Z4Plaq) : Z4Plaq :=
  ((p.1.1-space, p.1.2.1-space, p.1.2.2.1-space, p.1.2.2.2-time), p.2)

theorem unshift_shift (space time : Nat) (p : Z4Plaq) :
    unshift space time (shiftFace space time p) = p := by
  obtain ⟨⟨a,b,c,d⟩, plane⟩ := p
  simp only [unshift, shiftFace, shiftVertex, Nat.add_sub_cancel]

theorem preimage_mem {space time : Nat} {support : List Z4Plaq} {p : Z4Plaq}
    (hp : p ∈ support.map (shiftFace space time)) : unshift space time p ∈ support := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [unshift_shift] using hq

theorem preimage_pin {space time : Nat} {support : List Z4Plaq} {p : Z4Plaq}
    (hp : p ∈ support.map (shiftFace space time)) : shiftFace space time (unshift space time p) = p := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  rw [unshift_shift]

def shiftAdjacent (space time : Nat) {p q : Z4Plaq} (h : z4Lattice.Adjacent p q) :
    z4Lattice.Adjacent (shiftFace space time p) (shiftFace space time q) := by
  refine ⟨shiftLink space time h.link, ?_, ?_⟩
  · apply decide_eq_true
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨h.link, of_decide_eq_true h.on_p, rfl⟩
  · apply decide_eq_true
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨h.link, of_decide_eq_true h.on_q, rfl⟩

def shiftPath (space time : Nat) {support : List Z4Plaq} : {p q : Z4Plaq} →
    ChainIn z4Lattice support p q →
    ChainIn z4Lattice (support.map (shiftFace space time)) (shiftFace space time p) (shiftFace space time q)
  | _, _, .refl _ => .refl _
  | _, _, .step adj hm rest => .step (shiftAdjacent space time adj)
      (List.mem_map.mpr ⟨_, hm, rfl⟩) (shiftPath space time rest)

def shiftAnimal (space time : Nat) (animal : RootedConnectedAnimal z4Chain) :
    RootedConnectedAnimal z4Chain where
  root := shiftFace space time animal.root
  support := animal.support.map (shiftFace space time)
  root_mem := List.mem_map.mpr ⟨_, animal.root_mem, rfl⟩
  support_nodup := CayleyPruferInjection.nodup_map_of_injOn _ _ animal.support_nodup
    (fun _ _ _ _ he => shiftFace_injective space time he)
  connected := fun p q hp hq => by
    have path := shiftPath space time (animal.connected (unshift space time p) (unshift space time q)
      (preimage_mem hp) (preimage_mem hq))
    rw [preimage_pin hp, preimage_pin hq] at path
    exact path

def shiftProbe (space time : Nat) {links : List Z4Link} (probe : ProbeCarrier links) :
    ProbeCarrier (links.map (shiftLink space time)) where
  animal := shiftAnimal space time probe.animal
  covers := by
    intro link hl
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
    obtain ⟨face, hf, he⟩ := List.mem_flatMap.mp (probe.covers source hs)
    apply List.mem_flatMap.mpr
    refine ⟨shiftFace space time face, List.mem_map.mpr ⟨face, hf, rfl⟩, ?_⟩
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨source, he, rfl⟩

theorem shiftAnimal_size (space time : Nat) (animal : RootedConnectedAnimal z4Chain) :
    (shiftAnimal space time animal).support.length = animal.support.length := List.length_map _

def shiftedBoxProbe (n space time : Nat) (hn : 0<n) :
    ProbeCarrier ((boxLinks n).map (shiftLink space time)) := shiftProbe space time (boxProbe n hn)

theorem shiftedBoxProbe_size (n space time : Nat) (hn : 0<n) :
    (shiftedBoxProbe n space time hn).animal.support.length = (n*n*n*n)*6 :=
  (shiftAnimal_size space time (boxAnimal n hn)).trans (boxAnimal_size n hn)

theorem shiftedBoxProbe_root (n space time : Nat) (hn : 0<n) :
    (shiftedBoxProbe n space time hn).animal.root = shiftFace space time originFace := rfl

theorem shiftedBoxLinks_length (n space time : Nat) :
    ((boxLinks n).map (shiftLink space time)).length = (n*n*n*n)*24 := by
  rw [List.length_map, boxLinks_length, Nat.mul_assoc]

end YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier

#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.unshift
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.unshift_shift
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.preimage_mem
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.preimage_pin
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftAdjacent
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftPath
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftAnimal
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftProbe
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftAnimal_size
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftedBoxProbe
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftedBoxProbe_size
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftedBoxProbe_root
#print axioms YMGap.Continuum.BF4ExactSlabOffsetProbeCarrier.shiftedBoxLinks_length
