/-
# Replace the virtual probe root by a literal connected plaquette carrier

The actual rooted-selection graph joins all probe links at `none`. A fixed
connected geometric carrier covering those links converts each fixed core
into a genuine degree-24 plaquette animal, with at most M+n faces. Paths and
shared faces are computed from finite lists. The singleton plaquette carrier
is constructed here; a general carrier is explicit geometric data, not an
analytic summability premise. Augmentation alone is NOT an injective code:
the core's intersection with the carrier must also be retained.
-/

import YMGap.Continuum.BF4ExactSlabRootedSelection
import YMGap.Continuum.BF4ExactSlabCollarDegreeBound
import YMGap.Continuum.FiniteRootedAnimalTourCode

namespace YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.BF4ExactSlabFaceLinkLocality
open YMGap.Continuum.BF4ExactSlabRootedSelection
open YMGap.Continuum.BF4ExactSlabCollarDegreeBound
open YMGap.Continuum.FiniteRootedAnimalTourCode

structure ProbeCarrier (links : List Z4Link) : Type where
  animal : RootedConnectedAnimal z4Chain
  covers : ∀ link, link ∈ links → link ∈ animal.support.flatMap edgesOf

def singletonCarrier (p : Z4Plaq) : ProbeCarrier (edgesOf p) where
  animal := ⟨p, [p], List.mem_cons_self,
    List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
    PolymerModel.connectedIn_singleton (L := z4Chain.toLattice) p⟩
  covers := fun _ hl => List.mem_flatMap.mpr ⟨p, List.mem_cons_self, hl⟩

def coreFaces (extent : Nat) (ids : List Nat) : List Z4Plaq :=
  ids.map (slabPlaquetteAt extent)

def augmentedSupport {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (ids : List Nat) : List Z4Plaq :=
  probe.animal.support ++ (coreFaces extent ids).filter (fun p => !(decide (p ∈ probe.animal.support)))

theorem augmented_mem_iff {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (ids : List Nat) (p : Z4Plaq) :
    p ∈ augmentedSupport probe extent ids ↔ p ∈ probe.animal.support ∨ p ∈ coreFaces extent ids := by
  constructor
  · intro h
    exact (List.mem_append.mp h).elim Or.inl (fun h => Or.inr (List.mem_filter.mp h).1)
  · intro h
    by_cases hp : p ∈ probe.animal.support
    · exact List.mem_append.mpr (Or.inl hp)
    · exact List.mem_append.mpr (Or.inr (List.mem_filter.mpr
        ⟨h.resolve_left hp, by
          change Bool.not (decide (p ∈ probe.animal.support)) = true
          simp only [decide_eq_false hp, Bool.not_false]⟩))

theorem augmented_length_le {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (ids : List Nat) :
    (augmentedSupport probe extent ids).length ≤ probe.animal.support.length + ids.length := by
  change ((probe.animal.support : List Z4Plaq) ++ _).length ≤ _
  rw [List.length_append]
  exact Nat.add_le_add_left (Nat.le_trans (List.length_filter_le _ _)
    (Nat.le_of_eq (List.length_map (slabPlaquetteAt extent)))) probe.animal.support.length

theorem augmented_nodup {links : List Z4Link} (probe : ProbeCarrier links)
    (extent : Nat) (ids : List Nat) (hn : ids.Nodup)
    (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent) :
    (augmentedSupport probe extent ids).Nodup := by
  have hm : (coreFaces extent ids).Nodup := CayleyPruferInjection.nodup_map_of_injOn _ _ hn
    (fun a ha b hb he => slabPlaquetteAt_injective_on_physical (hphys a ha) (hphys b hb) he)
  refine List.nodup_append.mpr ⟨probe.animal.support_nodup, List.filter_sublist.nodup hm, ?_⟩
  intro a ha b hb he
  have hb' : b ∉ probe.animal.support := by
    simpa only [Bool.not_eq_true', decide_eq_false_iff_not] using (List.mem_filter.mp hb).2
  exact hb' (he ▸ ha)

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

/-- Finite search retains the incident carrier face as data. -/
def faceAtLink (link : Z4Link) : ∀ faces : List Z4Plaq,
    link ∈ faces.flatMap edgesOf → Σ' p : Z4Plaq, (p ∈ faces) ×' (link ∈ edgesOf p)
  | [], h => False.elim (List.not_mem_nil h)
  | p :: faces, h => by
      by_cases hp : link ∈ edgesOf p
      · exact ⟨p, List.mem_cons_self, hp⟩
      · have ht : link ∈ faces.flatMap edgesOf := (List.mem_append.mp h).resolve_left hp
        obtain ⟨q, hq, he⟩ := faceAtLink link faces ht
        exact ⟨q, List.mem_cons_of_mem p hq, he⟩

/-- Finite search retains a face identifier, without extracting a Prop existential. -/
def idAtFace (extent : Nat) (p : Z4Plaq) : ∀ ids : List Nat,
    p ∈ coreFaces extent ids → Σ' id : Nat, (id ∈ ids) ×' (slabPlaquetteAt extent id = p)
  | [], h => False.elim (List.not_mem_nil h)
  | id :: ids, h => by
      by_cases he : slabPlaquetteAt extent id = p
      · exact ⟨id, List.mem_cons_self, he⟩
      · have ht : p ∈ coreFaces extent ids := (List.mem_cons.mp h).resolve_left (Ne.symm he)
        obtain ⟨j, hj, he⟩ := idAtFace extent p ids ht
        exact ⟨j, List.mem_cons_of_mem id hj, he⟩

def nodePoint {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat) : Option Nat → Z4Plaq
  | none => probe.animal.root
  | some id => slabPlaquetteAt extent id

theorem nodePoint_mem {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat)
    (ids : List Nat) (node : Option Nat) (hn : node ∈ vertices ids) :
    nodePoint probe extent node ∈ augmentedSupport probe extent ids := by
  apply (augmented_mem_iff _ _ _ _).mpr
  cases node with
  | none => exact Or.inl probe.animal.root_mem
  | some id =>
      have hi : id ∈ ids := by
        simpa only [vertices, List.mem_cons, List.mem_map, Option.some.injEq,
          Option.some_ne_none, false_or, exists_eq_right] using hn
      exact Or.inr (List.mem_map.mpr ⟨id, hi, rfl⟩)

/-- Access to any link carried by a virtual node is realized inside the augmented support. -/
def nodeAccess {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat)
    (ids : List Nat) (node : Option Nat) (hn : node ∈ vertices ids) (link : Z4Link)
    (hl : link ∈ nodeLinks extent links node) :
    Σ' p : Z4Plaq, (p ∈ augmentedSupport probe extent ids) ×' (link ∈ edgesOf p) ×'
      PolymerModel.ChainIn z4Lattice (augmentedSupport probe extent ids) (nodePoint probe extent node) p := by
  cases node with
  | none =>
      obtain ⟨p, hp, he⟩ := faceAtLink link probe.animal.support (probe.covers link hl)
      exact ⟨p, (augmented_mem_iff _ _ _ _).mpr (Or.inl hp), he,
        pathMono (fun p hp => (augmented_mem_iff _ _ _ _).mpr (Or.inl hp))
          (probe.animal.connected _ _ probe.animal.root_mem hp)⟩
  | some id =>
      exact ⟨slabPlaquetteAt extent id, nodePoint_mem probe extent ids (some id) hn,
        by simpa only [nodeLinks, faceLinks, List.flatMap_cons, List.flatMap_nil, List.append_nil] using hl,
        .refl _⟩

/-- Every virtual-root path is translated to a path on literal shared plaquette links. -/
def liftPath {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat) (ids : List Nat) :
    {a b : Option Nat} → FiniteBoolGraphComponents.ChainIn (adjacent extent links) (vertices ids) a b →
    a ∈ vertices ids → PolymerModel.ChainIn z4Lattice (augmentedSupport probe extent ids)
      (nodePoint probe extent a) (nodePoint probe extent b)
  | _, _, .refl _, _ => .refl _
  | a, _, @FiniteBoolGraphComponents.ChainIn.step _ _ _ _ b _ hab hb rest, ha => by
      have hd : BF4ExactSlabSelectionSeparation.disjointTest
          (nodeLinks extent links a) (nodeLinks extent links b) = false := by
        simpa only [adjacent, Bool.not_eq_true'] using hab
      obtain ⟨link, hl, hr⟩ := sharedLink _ _ hd
      obtain ⟨p, _, hp, pp⟩ := nodeAccess probe extent ids a ha link hl
      obtain ⟨q, hq, he, pq⟩ := nodeAccess probe extent ids _ hb link hr
      let edge : z4Lattice.Adjacent p q := ⟨link, decide_eq_true hp, decide_eq_true he⟩
      exact pathTrans pp (pathTrans (.step edge hq (PolymerModel.ChainIn.refl (L := z4Lattice) q))
        (pathTrans (pathReverse pq (nodePoint_mem probe extent ids _ hb)) (liftPath probe extent ids rest hb)))

def rootPath {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat) (ids : List Nat)
    (hf : core extent links ids = ids) (p : Z4Plaq) (hp : p ∈ augmentedSupport probe extent ids) :
    PolymerModel.ChainIn z4Lattice (augmentedSupport probe extent ids) probe.animal.root p := by
  by_cases hc : p ∈ probe.animal.support
  · exact pathMono (fun p hp => (augmented_mem_iff _ _ _ _).mpr (Or.inl hp))
      (probe.animal.connected _ _ probe.animal.root_mem hc)
  · obtain ⟨id, hi, he⟩ := idAtFace extent p ids ((augmented_mem_iff _ _ _ _).mp hp |>.resolve_left hc)
    have path := core_path extent links ids id (hf.symm ▸ hi)
    rw [hf] at path
    have lifted := liftPath probe extent ids path List.mem_cons_self
    change PolymerModel.ChainIn z4Lattice (augmentedSupport probe extent ids)
      probe.animal.root (slabPlaquetteAt extent id) at lifted
    exact he ▸ lifted

def augmentedAnimal {links : List Z4Link} (probe : ProbeCarrier links) (extent : Nat) (ids : List Nat)
    (hn : ids.Nodup) (hphys : ∀ id, id ∈ ids → id ∈ slabPhysicalFaceEdges extent)
    (hf : core extent links ids = ids) : RootedConnectedAnimal z4Chain where
  root := probe.animal.root
  support := augmentedSupport probe extent ids
  root_mem := (augmented_mem_iff _ _ _ _).mpr (Or.inl probe.animal.root_mem)
  support_nodup := augmented_nodup probe extent ids hn hphys
  connected := fun a b ha hb => pathTrans
    (pathReverse (rootPath probe extent ids hf a ha)
      ((augmented_mem_iff _ _ _ _).mpr (Or.inl probe.animal.root_mem)))
    (rootPath probe extent ids hf b hb)

end YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal

#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.singletonCarrier
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.coreFaces
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.augmentedSupport
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.augmented_mem_iff
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.augmented_length_le
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.augmented_nodup
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.faceAtLink
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.idAtFace
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.nodePoint
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.nodePoint_mem
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.nodeAccess
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.liftPath
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.rootPath
#print axioms YMGap.Continuum.BF4ExactSlabProbeCarrierAnimal.augmentedAnimal
