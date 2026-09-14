/-
# Every actual spatial component is a genuine local rooted animal

The original Boolean paths are lifted, link witness by link witness, to the
local occurrence lattice. The component carrier is only proof-annotated:
forgetting annotations returns the EXACT original list. Its duplicate
freedom comes from the component permutation theorem, not from erasure.
The existing constructive BFS therefore supplies its faithful spanning tree.
-/

import YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice
import YMGap.Continuum.FiniteBoolGraphComponentPermutation

namespace YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal

set_option autoImplicit false

open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.BddLatticeAnimal
open YMGap.Continuum.PolymerModel
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents
open YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice
open YMGap.Continuum.BF4ExactSlabOriginalCoreTailWindow
open YMGap.Continuum.PairedPositiveFaceLabellings
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphComponentPermutation

local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

def Locality (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Prop :=
  ∀ x, x ∈ occurrences margin pair → x ∈ rootCarrier margin

theorem short_locality {K margin : Nat} {ids : List Nat} {pair : EdgeLabelling × EdgeLabelling}
    (hs : ids ∈ shortOtherCores 33 margin) (hp : pair ∈ labels K ids) : Locality margin pair :=
  original_occurrence_local hs hp

theorem component_subset {margin : Nat} {pair : EdgeLabelling × EdgeLabelling}
    {c : List Occurrence} (hc : c ∈ components margin pair)
    (x : Occurrence) (hx : x ∈ c) : x ∈ occurrences margin pair :=
  (graphComponents_covers adjacent (occurrences margin pair) x).mpr ⟨c,hc,hx⟩

def annotate {margin : Nat} {c : List Occurrence}
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) (x : Occurrence) (hx : x ∈ c) :
    LocalOccurrence margin := ⟨x,hl x hx⟩

def localSupport {margin : Nat} (c : List Occurrence)
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) : List (LocalOccurrence margin) :=
  c.attach.map (fun x => annotate hl x.val x.property)

theorem localSupport_mem {margin : Nat} {c : List Occurrence}
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) (x : Occurrence) (hx : x ∈ c) :
    annotate hl x hx ∈ localSupport c hl :=
  List.mem_map.mpr ⟨⟨x,hx⟩,List.mem_attach _ _,rfl⟩

theorem localSupport_original {margin : Nat} {c : List Occurrence}
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) (x : LocalOccurrence margin)
    (hx : x ∈ localSupport c hl) : x.val ∈ c := by
  obtain ⟨y,_,he⟩ := List.mem_map.mp hx
  have hy : y.val=x.val := congrArg Subtype.val he
  exact hy ▸ y.property

theorem localSupport_forget {margin : Nat} (c : List Occurrence)
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) : (localSupport c hl).map Subtype.val=c := by
  simp only [localSupport,List.map_map,annotate,Function.comp_def,List.attach_map_subtype_val]

theorem localSupport_length {margin : Nat} (c : List Occurrence)
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) : (localSupport c hl).length=c.length := by
  rw [localSupport,List.length_map,List.length_attach]

theorem localSupport_nodup {margin : Nat} (c : List Occurrence)
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) (hn : c.Nodup) : (localSupport c hl).Nodup := by
  apply nodup_map_of_injOn _ _ (attach_nodup_of_nodup c hn)
  intro x _ y _ he
  have hxy : x.val=y.val := congrArg (fun z : LocalOccurrence margin => z.val) he
  exact Subtype.ext hxy

def liftPath {margin : Nat} {c : List Occurrence}
    (hl : ∀ x, x ∈ c → x ∈ rootCarrier margin) :
    {x y : Occurrence} → (hx : x ∈ c) → (hy : y ∈ c) →
    FiniteBoolGraphComponents.ChainIn adjacent c x y →
    PolymerModel.ChainIn (occurrenceLattice margin) (localSupport c hl)
      (annotate hl x hx) (annotate hl y hy)
  | _, _, _, _, .refl _ => .refl _
  | x, _, hx, hy, @FiniteBoolGraphComponents.ChainIn.step _ _ _ _ y _ he hnext rest => by
    let link := adjacent_link x y he
    let edge : (occurrenceLattice margin).Adjacent (annotate hl x hx) (annotate hl y hnext) :=
      ⟨link.1,decide_eq_true link.2.1,decide_eq_true link.2.2⟩
    exact .step edge (localSupport_mem hl y hnext) (liftPath hl hnext hy rest)

def componentAnimal (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hl : Locality margin pair) (c : List Occurrence) (hc : c ∈ components margin pair) :
    RootedConnectedAnimal (boundedLattice margin) := by
  let root := graphComponents_allNonempty adjacent (occurrences margin pair) c hc
  have hlocal : ∀ x, x ∈ c → x ∈ rootCarrier margin := fun x hx => hl x (component_subset hc x hx)
  refine ⟨annotate hlocal root.1 root.2,localSupport c hlocal,
    localSupport_mem hlocal root.1 root.2,
    localSupport_nodup c hlocal (graph_component_nodup adjacent _ (occurrences_nodup margin pair) c hc),?_⟩
  intro x y hx hy
  have hxc := localSupport_original hlocal x hx
  have hyc := localSupport_original hlocal y hy
  exact liftPath hlocal hxc hyc (original_components_connected margin pair c hc x.val y.val hxc hyc)

theorem componentAnimal_support_length (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hl : Locality margin pair) (c : List Occurrence) (hc : c ∈ components margin pair) :
    (componentAnimal margin pair hl c hc).support.length=c.length := localSupport_length c _

theorem componentAnimal_support_forget (margin : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hl : Locality margin pair) (c : List Occurrence) (hc : c ∈ components margin pair) :
    (componentAnimal margin pair hl c hc).support.map Subtype.val=c := localSupport_forget c _

end YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal

#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.short_locality
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.component_subset
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.annotate
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport_original
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport_forget
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.localSupport_nodup
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.liftPath
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.componentAnimal
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.componentAnimal_support_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal.componentAnimal_support_forget
