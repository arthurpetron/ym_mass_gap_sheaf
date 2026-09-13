/-
# Retained two-probe cores are literal connected plaquette animals

Each probe has its own connected carrier. They need not be adjacent and no
connecting corridor is added. The retained-coefficient test supplies an
actual path between them. Replacing its two virtual vertices by their
respective carriers gives a literal animal of at most M_left+M_right+n
faces for a fixed n-face common-root core. In particular its size allowance
contains the two support sizes, not the distance between the probes.

All paths are Type-valued and carry actual shared links. This is the
geometric producer for a two-probe count, not a normalized decay theorem.
-/

import YMGap.Continuum.BF4ExactSlabTwoProbeGraph
import YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal

namespace YMGap.Continuum.BF4ExactSlabTwoProbeAnimal

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabSelectionSeparation
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound (sharedLink)
open YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal (ProbeCarrier coreFaces faceAtLink idAtFace)
open YMGap.Continuum.BF4ExactSlabTwoProbeGraph
open YMGap.Continuum.FiniteRootedAnimalTourCode

private def union (a b : List Z4Plaq) : List Z4Plaq :=
  a ++ b.filter (fun p => !(decide (p ∈ a)))

private theorem union_mem (a b : List Z4Plaq) (p : Z4Plaq) :
    p ∈ union a b ↔ p ∈ a ∨ p ∈ b := by
  constructor
  · intro h
    exact (List.mem_append.mp h).elim Or.inl (fun h => Or.inr (List.mem_filter.mp h).1)
  · intro h
    by_cases hp : p ∈ a
    · exact List.mem_append.mpr (Or.inl hp)
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨h.resolve_left hp, by simp only [decide_eq_false hp, Bool.not_false]⟩))

private theorem union_nodup (a b : List Z4Plaq) (ha : a.Nodup) (hb : b.Nodup) : (union a b).Nodup := by
  refine List.nodup_append.mpr ⟨ha, List.filter_sublist.nodup hb, ?_⟩
  intro p hp q hq he
  have hn : q ∉ a := by simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using (List.mem_filter.mp hq).2
  exact hn (he ▸ hp)

private theorem union_length_le (a b : List Z4Plaq) : (union a b).length ≤ a.length+b.length := by
  change (a++_).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left (List.length_filter_le _ _) _

def probeSupport {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) : List Z4Plaq :=
  union P.animal.support Q.animal.support

theorem probeSupport_mem {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) (p : Z4Plaq) :
    p ∈ probeSupport P Q ↔ p ∈ P.animal.support ∨ p ∈ Q.animal.support := union_mem _ _ _

theorem probeSupport_nodup {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) :
    (probeSupport P Q).Nodup := union_nodup _ _ P.animal.support_nodup Q.animal.support_nodup

theorem probeSupport_length_le {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) :
    (probeSupport P Q).length ≤ P.animal.support.length+Q.animal.support.length := union_length_le _ _

def augmentedSupport {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ids : List Nat) : List Z4Plaq := union (probeSupport P Q) (coreFaces extent ids)

theorem augmented_mem {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ids : List Nat) (p : Z4Plaq) :
    p ∈ augmentedSupport P Q extent ids ↔ p ∈ probeSupport P Q ∨ p ∈ coreFaces extent ids := union_mem _ _ _

theorem augmented_length_le {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ids : List Nat) :
    (augmentedSupport P Q extent ids).length ≤ (probeSupport P Q).length+ids.length := by
  have h := union_length_le (probeSupport P Q) (coreFaces extent ids)
  simpa only [coreFaces, List.length_map] using h

theorem augmented_size_le {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ids : List Nat) :
    (augmentedSupport P Q extent ids).length ≤ P.animal.support.length+Q.animal.support.length+ids.length :=
  Nat.le_trans (augmented_length_le P Q extent ids) (Nat.add_le_add_right (probeSupport_length_le P Q) _)

theorem augmented_nodup {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right)
    (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    (augmentedSupport P Q extent ids).Nodup :=
  union_nodup _ _ (probeSupport_nodup P Q) (CayleyPruferInjection.nodup_map_of_injOn _ _ hn
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical (hphys a ha) (hphys b hb) he))

private def pathTrans {X : List Z4Plaq} : {a b c : Z4Plaq} →
    PolymerModel.ChainIn z4Lattice X a b → PolymerModel.ChainIn z4Lattice X b c →
      PolymerModel.ChainIn z4Lattice X a c
  | _, _, _, .refl _, right => right
  | _, _, _, .step adj hb rest, right => .step adj hb (pathTrans rest right)

private def pathMono {small large : List Z4Plaq} (hsub : ∀ p, p ∈ small → p ∈ large) :
    {a b : Z4Plaq} → PolymerModel.ChainIn z4Lattice small a b → PolymerModel.ChainIn z4Lattice large a b
  | _, _, .refl a => .refl a
  | _, _, .step adj hb rest => .step adj (hsub _ hb) (pathMono hsub rest)

private def pathReverse {X : List Z4Plaq} : {a b : Z4Plaq} →
    PolymerModel.ChainIn z4Lattice X a b → a ∈ X → PolymerModel.ChainIn z4Lattice X b a
  | _, _, .refl a, _ => .refl a
  | a, _, .step adj hb rest, ha =>
      pathTrans (pathReverse rest hb) (.step ⟨adj.link, adj.on_q, adj.on_p⟩ ha
        (PolymerModel.ChainIn.refl (L := z4Lattice) a))

section Probes

variable {left right : List Z4Link} (P : ProbeCarrier left) (Q : ProbeCarrier right) (extent : Nat) (ids : List Nat)

theorem left_support_mem (p : Z4Plaq) (hp : p ∈ P.animal.support) : p ∈ augmentedSupport P Q extent ids :=
  (augmented_mem _ _ _ _ _).mpr (Or.inl ((probeSupport_mem _ _ _).mpr (Or.inl hp)))

theorem right_support_mem (p : Z4Plaq) (hp : p ∈ Q.animal.support) : p ∈ augmentedSupport P Q extent ids :=
  (augmented_mem _ _ _ _ _).mpr (Or.inl ((probeSupport_mem _ _ _).mpr (Or.inr hp)))

def nodePoint : Node → Z4Plaq
  | .left => P.animal.root
  | .right => Q.animal.root
  | .face id => slabPlaquetteAt extent id

theorem nodePoint_mem (node : Node) (hn : node ∈ vertices ids) :
    nodePoint P Q extent node ∈ augmentedSupport P Q extent ids := by
  cases node with
  | left => exact left_support_mem P Q extent ids _ P.animal.root_mem
  | right => exact right_support_mem P Q extent ids _ Q.animal.root_mem
  | face id => exact (augmented_mem _ _ _ _ _).mpr (Or.inr
      (List.mem_map.mpr ⟨id, (face_mem_vertices ids id).mp hn, rfl⟩))

def nodeAccess (node : Node) (hn : node ∈ vertices ids) (link : Z4Link)
    (hl : link ∈ nodeLinks extent left right node) :
    Σ' p : Z4Plaq, (p ∈ augmentedSupport P Q extent ids) ×' (link ∈ edgesOf p) ×'
      PolymerModel.ChainIn z4Lattice (augmentedSupport P Q extent ids) (nodePoint P Q extent node) p := by
  cases node with
  | left =>
      obtain ⟨p, hp, he⟩ := faceAtLink link P.animal.support (P.covers link hl)
      exact ⟨p, left_support_mem P Q extent ids p hp, he,
        pathMono (left_support_mem P Q extent ids) (P.animal.connected _ _ P.animal.root_mem hp)⟩
  | right =>
      obtain ⟨p, hp, he⟩ := faceAtLink link Q.animal.support (Q.covers link hl)
      exact ⟨p, right_support_mem P Q extent ids p hp, he,
        pathMono (right_support_mem P Q extent ids) (Q.animal.connected _ _ Q.animal.root_mem hp)⟩
  | face id =>
      exact ⟨slabPlaquetteAt extent id, nodePoint_mem P Q extent ids (.face id) hn,
        by simpa only [nodeLinks, faceLinks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hl,
        .refl _⟩

def liftPath : {a b : Node} → FiniteBoolGraphComponents.ChainIn (adjacent extent left right) (vertices ids) a b →
    a ∈ vertices ids → PolymerModel.ChainIn z4Lattice (augmentedSupport P Q extent ids)
      (nodePoint P Q extent a) (nodePoint P Q extent b)
  | _, _, .refl _, _ => .refl _
  | a, _, @FiniteBoolGraphComponents.ChainIn.step _ _ _ _ b _ hab hb rest, ha => by
      have hd : disjointTest (nodeLinks extent left right a) (nodeLinks extent left right b) = false := by
        simpa only [adjacent, Bool.not_eq_true'] using hab
      obtain ⟨link, hl, hr⟩ := sharedLink _ _ hd
      obtain ⟨p, _, hp, pp⟩ := nodeAccess P Q extent ids a ha link hl
      obtain ⟨q, hq, he, pq⟩ := nodeAccess P Q extent ids b hb link hr
      let edge : z4Lattice.Adjacent p q := ⟨link, decide_eq_true hp, decide_eq_true he⟩
      exact pathTrans pp (pathTrans (.step edge hq (PolymerModel.ChainIn.refl (L := z4Lattice) q))
        (pathTrans (pathReverse pq (nodePoint_mem P Q extent ids b hb)) (liftPath rest hb)))

def probeBridge (hk : keep extent left right ids = true) :
    PolymerModel.ChainIn z4Lattice (augmentedSupport P Q extent ids) P.animal.root Q.animal.root :=
  liftPath P Q extent ids (probePath extent left right ids hk) List.mem_cons_self

def rootPath (hk : keep extent left right ids = true)
    (hf : BF4ExactSlabRootedSelection.core extent (left++right) ids = ids)
    (p : Z4Plaq) (hp : p ∈ augmentedSupport P Q extent ids) :
    PolymerModel.ChainIn z4Lattice (augmentedSupport P Q extent ids) P.animal.root p := by
  by_cases hl : p ∈ P.animal.support
  · exact pathMono (left_support_mem P Q extent ids) (P.animal.connected _ _ P.animal.root_mem hl)
  by_cases hr : p ∈ Q.animal.support
  · exact pathTrans (probeBridge P Q extent ids hk)
      (pathMono (right_support_mem P Q extent ids) (Q.animal.connected _ _ Q.animal.root_mem hr))
  have hc : p ∈ coreFaces extent ids := ((augmented_mem P Q extent ids p).mp hp).resolve_left
    (fun h => ((probeSupport_mem P Q p).mp h).elim hl hr)
  obtain ⟨id, hi, he⟩ := idAtFace extent p ids hc
  have path := coreFacePath extent left right ids hk id (hf.symm ▸ hi)
  have lifted := liftPath P Q extent ids path List.mem_cons_self
  change PolymerModel.ChainIn z4Lattice (augmentedSupport P Q extent ids) P.animal.root (slabPlaquetteAt extent id) at lifted
  exact he ▸ lifted

def augmentedAnimal (hn : ids.Nodup) (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hk : keep extent left right ids = true)
    (hf : BF4ExactSlabRootedSelection.core extent (left++right) ids = ids) : RootedConnectedAnimal z4Chain where
  root := P.animal.root
  support := augmentedSupport P Q extent ids
  root_mem := left_support_mem P Q extent ids _ P.animal.root_mem
  support_nodup := augmented_nodup P Q extent ids hn hphys
  connected := fun a b ha hb => pathTrans (pathReverse (rootPath P Q extent ids hk hf a ha)
    (left_support_mem P Q extent ids _ P.animal.root_mem)) (rootPath P Q extent ids hk hf b hb)

end Probes
end YMGap.Continuum.BF4ExactSlabTwoProbeAnimal

#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.probeSupport
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.probeSupport_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.probeSupport_nodup
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.probeSupport_length_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmentedSupport
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmented_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmented_length_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmented_size_le
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmented_nodup
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.left_support_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.right_support_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.nodePoint
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.nodePoint_mem
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.nodeAccess
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.liftPath
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.probeBridge
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.rootPath
#print axioms YMGap.Continuum.BF4ExactSlabTwoProbeAnimal.augmentedAnimal
