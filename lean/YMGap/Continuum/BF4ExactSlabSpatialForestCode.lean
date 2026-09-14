/-
# The original spatial pair has a support-recovering whole-forest code

Every actual component is sent through its genuine BFS spanning tree. The
forest has exactly S vertices, at most S/2 roots for nonzero original pairs,
and code carrier size at most 7200000^S. Decoding recovers the original
replica-tagged occurrence support. Locality is proved for every original
short pair; the code is totalized by an explicit finite locality test.

This is a spatial code, not yet the full higher-label configuration count
or its weighted sum. No physical action, occurrence, or multiplicity changes.
-/

import YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal
import YMGap.Continuum.FiniteRootedAnimalForestCode

namespace YMGap.Continuum.BF4ExactSlabSpatialForestCode

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteRootedAnimalTourCode
open YMGap.Continuum.FiniteRootedAnimalForestCode
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.BF4ExactSlabShiftedProbeConnectedCut
open YMGap.Continuum.BF4ExactSlabPairChannelParity
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceNeighbors
open YMGap.Continuum.BF4ExactSlabSpatialOccurrenceComponents
open YMGap.Continuum.BF4ExactSlabSpatialComponentAnimal
open YMGap.Continuum.BF4ExactSlabLocalOccurrenceLattice
open YMGap.Continuum.FiniteBoolGraphComponentPermutation

local infix:50 " ≈ " => Q'.eqv
local instance : DecidableEq Z4Plaq := inferInstanceAs (DecidableEq (Z4Vertex × Z4Plane))

def animals (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    List (RootedConnectedAnimal (boundedLattice margin)) :=
  (components margin pair).attach.map (fun c => componentAnimal margin pair hl c.val c.property)

theorem animals_length (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    (animals margin pair hl).length=(components margin pair).length := by
  rw [animals,List.length_map,List.length_attach]

theorem component_mass_sum {A : Type} : ∀ cs : List (List A),
    FiniteBoolGraphComponentMass.mass cs=(cs.map List.length).sum
  | [] => rfl
  | c::cs => congrArg (Nat.add c.length) (component_mass_sum cs)

theorem original_forest_mass (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    FiniteRootedForestCode.mass (trees (animals margin pair hl))=pairSpatial margin pair := by
  rw [trees_mass]
  simp only [animals,List.map_map,Function.comp_def,componentAnimal_support_length,List.attach_map_val]
  rw [← component_mass_sum,original_component_mass]

theorem animals_forget (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    ((support (animals margin pair hl)).map Subtype.val).Perm (occurrences margin pair) := by
  have he : (support (animals margin pair hl)).map Subtype.val=(components margin pair).flatten := by
    simp only [support,animals,List.flatMap_map]
    change ((components margin pair).attach.flatMap (fun a =>
      (componentAnimal margin pair hl a.val a.property).support) : List (LocalOccurrence margin)).map
      (fun x : LocalOccurrence margin => x.val)=(components margin pair).flatten
    rw [List.map_flatMap]
    simp only [componentAnimal_support_forget]
    change (components margin pair).attach.flatMap (fun a => id a.val)=(components margin pair).flatten
    rw [← List.flatMap_map Subtype.val id,List.attach_map_subtype_val,← List.flatten_eq_flatMap]
  rw [he]
  exact graph_flatten_perm adjacent _

def localCode (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    FiniteRootedForestCode.Code (LocalOccurrence margin) 3216 := forestCode (animals margin pair hl)

def decodeOriginal (margin : Nat) (code : FiniteRootedForestCode.Code (LocalOccurrence margin) 3216) :
    List Occurrence := (decodedSupport (boundedLattice margin) code).map Subtype.val

theorem localCode_support (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair)
    (x : Occurrence) : x ∈ occurrences margin pair ↔ x ∈ decodeOriginal margin (localCode margin pair hl) := by
  have hp := animals_forget margin pair hl
  have hd := forestCode_support (animals margin pair hl)
  constructor
  · intro hx
    obtain ⟨y,hy,he⟩ := List.mem_map.mp (hp.mem_iff.mpr hx)
    exact List.mem_map.mpr ⟨y,hd.1 y hy,he⟩
  · intro hx
    obtain ⟨y,hy,he⟩ := List.mem_map.mp hx
    exact hp.mem_iff.mp (List.mem_map.mpr ⟨y,hd.2 y hy,he⟩)

def codeCarrier (margin S : Nat) : List (FiniteRootedForestCode.Code (LocalOccurrence margin) 3216) :=
  FiniteRootedForestCount.carrier (rootPool margin) 3216 S

theorem codeCarrier_length_le (margin S : Nat) : (codeCarrier margin S).length ≤ 7200000^S :=
  local_forest_carrier_bound margin S

theorem localCode_mem (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) : localCode margin pair hl ∈ codeCarrier margin (pairSpatial margin pair) := by
  rw [← original_forest_mass margin pair hl]
  apply FiniteRootedForestCount.encode_mem
  · exact fun r _ => rootPool_complete margin r
  · rw [trees_length,animals_length,original_forest_mass]
    exact original_component_count margin pair hne

def localityTest (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) : Bool :=
  (occurrences margin pair).all (localTest margin)

theorem localityTest_iff (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    localityTest margin pair=true ↔ Locality margin pair := by
  constructor
  · intro h x hx
    exact localTest_sound (List.all_eq_true.mp h x hx)
  · intro h
    exact List.all_eq_true.mpr (fun x hx => decide_eq_true (h x hx))

def code (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) :
    FiniteRootedForestCode.Code (LocalOccurrence margin) 3216 :=
  if hl : localityTest margin pair=true then localCode margin pair ((localityTest_iff margin pair).mp hl)
  else ([],[],[])

theorem code_pin (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair) :
    code margin pair=localCode margin pair hl := by
  rw [code,dif_pos ((localityTest_iff margin pair).mpr hl)]

theorem code_support (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair)
    (x : Occurrence) : x ∈ occurrences margin pair ↔ x ∈ decodeOriginal margin (code margin pair) := by
  rw [code_pin margin pair hl]
  exact localCode_support margin pair hl x

theorem code_mem (margin : Nat) (pair : EdgeLabelling × EdgeLabelling) (hl : Locality margin pair)
    (hne : ¬pairTerm margin pair.1 pair.2 ≈ 0) : code margin pair ∈ codeCarrier margin (pairSpatial margin pair) := by
  rw [code_pin margin pair hl]
  exact localCode_mem margin pair hl hne

theorem code_eq_occurrences {margin : Nat} {left right : EdgeLabelling × EdgeLabelling}
    (hl : Locality margin left) (hr : Locality margin right) (he : code margin left=code margin right)
    (x : Occurrence) : x ∈ occurrences margin left ↔ x ∈ occurrences margin right := by
  rw [code_support margin left hl,code_support margin right hr,he]

end YMGap.Continuum.BF4ExactSlabSpatialForestCode

#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.animals
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.animals_length
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.component_mass_sum
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.original_forest_mass
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.animals_forget
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.localCode
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.decodeOriginal
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.localCode_support
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.codeCarrier
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.codeCarrier_length_le
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.localCode_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.localityTest
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.localityTest_iff
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.code
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.code_pin
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.code_support
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.code_mem
#print axioms YMGap.Continuum.BF4ExactSlabSpatialForestCode.code_eq_occurrences
