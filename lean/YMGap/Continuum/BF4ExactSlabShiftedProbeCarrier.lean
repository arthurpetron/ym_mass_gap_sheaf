/-
# Translate a constructed probe carrier without changing its size

Paths and shared links are translated literally. Endpoints are recovered
by coordinate subtraction, so connectedness retains its Type-valued path
data without extracting a preimage from a propositional existential.
The finite-box probe therefore covers translated finite supports with a
size independent of the translation and of the ambient comparison slab.
-/

import YMGap.Continuum.Z4FiniteBoxConnectedAnimal
import YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation

namespace YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal
open YMGap.Continuum.BF4ExactSlabBulkEmbeddingGeometry
open YMGap.Continuum.BF4ExactSlabEmbeddedExteriorSeparation
open YMGap.Continuum.Z4FiniteBoxConnectedAnimal

theorem unshift_shift (shift : Nat) (p : Z4Plaq) :
    unshiftFace shift (shiftFace shift shift p) = p := by
  obtain ⟨⟨a,b,c,d⟩, P⟩ := p
  simp only [unshiftFace, shiftFace, shiftVertex, Nat.add_sub_cancel]

theorem preimage_mem {shift : Nat} {support : List Z4Plaq} {p : Z4Plaq}
    (hp : p ∈ support.map (shiftFace shift shift)) : unshiftFace shift p ∈ support := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [unshift_shift] using hq

theorem preimage_pin {shift : Nat} {support : List Z4Plaq} {p : Z4Plaq}
    (hp : p ∈ support.map (shiftFace shift shift)) :
    shiftFace shift shift (unshiftFace shift p) = p := by
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp
  rw [unshift_shift]

def shiftAdjacent (shift : Nat) {p q : Z4Plaq} (h : z4Lattice.Adjacent p q) :
    z4Lattice.Adjacent (shiftFace shift shift p) (shiftFace shift shift q) := by
  refine ⟨shiftLink shift shift h.link, ?_, ?_⟩
  · apply decide_eq_true
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨h.link, of_decide_eq_true h.on_p, rfl⟩
  · apply decide_eq_true
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨h.link, of_decide_eq_true h.on_q, rfl⟩

def shiftPath (shift : Nat) {support : List Z4Plaq} : {p q : Z4Plaq} →
    ChainIn z4Lattice support p q →
    ChainIn z4Lattice (support.map (shiftFace shift shift))
      (shiftFace shift shift p) (shiftFace shift shift q)
  | _, _, .refl _ => .refl _
  | _, _, .step adj hm rest => .step (shiftAdjacent shift adj)
      (List.mem_map.mpr ⟨_, hm, rfl⟩) (shiftPath shift rest)

def shiftAnimal (shift : Nat) (animal : RootedConnectedAnimal z4Chain) :
    RootedConnectedAnimal z4Chain where
  root := shiftFace shift shift animal.root
  support := animal.support.map (shiftFace shift shift)
  root_mem := List.mem_map.mpr ⟨_, animal.root_mem, rfl⟩
  support_nodup := CayleyPruferInjection.nodup_map_of_injOn _ _ animal.support_nodup
    (fun _ _ _ _ he => shiftFace_injective shift shift he)
  connected := fun p q hp hq => by
    have path := shiftPath shift
      (animal.connected (unshiftFace shift p) (unshiftFace shift q)
        (preimage_mem hp) (preimage_mem hq))
    rw [preimage_pin hp, preimage_pin hq] at path
    exact path

def shiftProbe (shift : Nat) {links : List Z4Link} (probe : ProbeCarrier links) :
    ProbeCarrier (links.map (shiftLink shift shift)) where
  animal := shiftAnimal shift probe.animal
  covers := by
    intro link hl
    obtain ⟨source, hs, rfl⟩ := List.mem_map.mp hl
    obtain ⟨face, hf, he⟩ := List.mem_flatMap.mp (probe.covers source hs)
    apply List.mem_flatMap.mpr
    refine ⟨shiftFace shift shift face, List.mem_map.mpr ⟨face, hf, rfl⟩, ?_⟩
    rw [edgesOf_shiftFace]
    exact List.mem_map.mpr ⟨source, he, rfl⟩

theorem shiftAnimal_size (shift : Nat) (animal : RootedConnectedAnimal z4Chain) :
    (shiftAnimal shift animal).support.length = animal.support.length := List.length_map _

def shiftedBoxProbe (n shift : Nat) (hn : 0<n) :
    ProbeCarrier ((boxLinks n).map (shiftLink shift shift)) := shiftProbe shift (boxProbe n hn)

theorem shiftedBoxProbe_size (n shift : Nat) (hn : 0<n) :
    (shiftedBoxProbe n shift hn).animal.support.length = (n*n*n*n)*6 :=
  (shiftAnimal_size shift (boxAnimal n hn)).trans (boxAnimal_size n hn)

theorem shiftedBoxProbe_root (n shift : Nat) (hn : 0<n) :
    (shiftedBoxProbe n shift hn).animal.root = shiftFace shift shift originFace := rfl

theorem shiftedBoxLinks_length (n shift : Nat) :
    ((boxLinks n).map (shiftLink shift shift)).length = (n*n*n*n)*24 := by
  rw [List.length_map, boxLinks_length, Nat.mul_assoc]

end YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier

#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.unshift_shift
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.preimage_mem
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.preimage_pin
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftAdjacent
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftPath
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftAnimal
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftProbe
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftAnimal_size
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftedBoxProbe
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftedBoxProbe_size
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftedBoxProbe_root
#print axioms YMGap.Continuum.BF4ExactSlabShiftedProbeCarrier.shiftedBoxLinks_length
