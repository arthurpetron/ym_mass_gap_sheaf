/-
# Executable finite search for a BF4 binary multicover

The all-even strand-colouring input should not remain an opaque existential
over arbitrary functions.  At every fixed corrected slab it is a finite
problem:

* enumerate every subset of the physical plaquette list;
* check even incidence only on the finite union of its boundary links;
* turn every passing subset into a certified closed binary layer;
* enumerate layer words up to a chosen budget; and
* check pointwise reconstruction only on the finite physical face list.

This file proves both finite checks globally sound.  Consequently every
successful execution of `binaryMulticoverSearch` produces a literal
`BinaryEvenSlabMulticover`, hence can be fed to the existing joint-carrier
construction.

The search is intentionally budget-indexed.  No unproved assertion that a
particular budget suffices is hidden in the implementation.

## Axiom gate

Finite lists, decidable equality, and natural arithmetic only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
import YMGap.Continuum.CayleyPruferInjection
import YMGap.Continuum.Z4CanonicalPolymerRange

namespace YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicDeterministicSupportKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4UnitCubeIncidenceParity

/-! ## 1. A finite and globally sound closure check -/

/-- Every link that can have nonzero incidence on `support`. -/
def supportBoundaryLinks (support : List Z4Plaq) : List Z4Link :=
  (support.flatMap edgesOf).eraseDups

/-- Check even face incidence on the complete finite boundary-link list. -/
def evenFaceIncidenceCheck (support : List Z4Plaq) : Bool :=
  (supportBoundaryLinks support).all
    (fun link => decide (faceIncidenceCount link support % 2 = 0))

theorem evenFaceIncidenceCheck_sound
    (support : List Z4Plaq)
    (hcheck : evenFaceIncidenceCheck support = true) :
    EvenFaceIncidence support := by
  intro link
  by_cases hlink : link ∈ supportBoundaryLinks support
  · exact of_decide_eq_true
      (List.all_eq_true.mp hcheck link hlink)
  · have hflat : link ∉ support.flatMap edgesOf := by
      simpa only [supportBoundaryLinks, List.mem_eraseDups] using hlink
    rw [← occurrenceCount_flatMap_edgesOf]
    rw [occurrenceCount_eq_zero_of_not_mem
      link (support.flatMap edgesOf) hflat]

theorem evenFaceIncidenceCheck_complete
    (support : List Z4Plaq)
    (heven : EvenFaceIncidence support) :
    evenFaceIncidenceCheck support = true := by
  unfold evenFaceIncidenceCheck
  apply List.all_eq_true.mpr
  intro link _
  exact decide_eq_true (heven link)

/-! ## 2. Certified finite alphabet of all closed binary layers -/

/-- A support retained by the literal powerset-and-parity scan. -/
structure ClosedBinarySlabSupport (S : SlabScalePair) : Type where
  support : List Z4Plaq
  power_mem :
    support ∈ sublists
      (boundaryCompleteSlabPlaquettes S.fine.extent)
  even_check : evenFaceIncidenceCheck support = true

namespace ClosedBinarySlabSupport

variable {S : SlabScalePair}

theorem subset (code : ClosedBinarySlabSupport S) :
    ∀ plaquette, plaquette ∈ code.support →
      plaquette ∈
        boundaryCompleteSlabPlaquettes S.fine.extent := by
  intro plaquette hplaquette
  exact mem_of_mem_sublists
    (boundaryCompleteSlabPlaquettes S.fine.extent)
    code.support code.power_mem plaquette hplaquette

theorem nodup (code : ClosedBinarySlabSupport S) :
    code.support.Nodup :=
  nodup_of_mem_sublists
    (boundaryCompleteSlabPlaquettes S.fine.extent)
    code.support
    (boundaryCompleteSlabPlaquettes_nodup S.fine.extent)
    code.power_mem

theorem even (code : ClosedBinarySlabSupport S) :
    EvenFaceIncidence code.support :=
  evenFaceIncidenceCheck_sound code.support code.even_check

/-- Interpret a certified support as an actual cutoff-one even sheet. -/
def toLayer (code : ClosedBinarySlabSupport S) :
    BinaryEvenSlabLayer S :=
  binaryEvenSlabLayerOfSupport
    S code.support code.subset code.nodup code.even

end ClosedBinarySlabSupport

/-- Canonical closed-support code carried by an arbitrary binary even
layer. -/
def supportCodeOfLayer
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    ClosedBinarySlabSupport S where
  support :=
    fineOddSlabSupport (binaryScalePair S) layer.state
  power_mem := by
    unfold fineOddSlabSupport
    rw [binaryScalePair_fine_extent]
    exact filter_mem_sublists _ _
  even_check :=
    evenFaceIncidenceCheck_complete _
      layer.oddSupport_even

/-- Canonicalization through odd support preserves the cutoff-one layer
state exactly. -/
theorem supportCodeOfLayer_toLayer_state
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    (supportCodeOfLayer layer).toLayer.state =
      layer.state := by
  have hstate :=
    cutoffOneFineState_eq_oddSupportLabelling
      (S := binaryScalePair S) rfl layer.state_mem
  rw [binaryScalePair_fine_extent] at hstate
  exact hstate.symm

/-- Certify one attached powerset entry exactly when its finite parity check
passes. -/
def certifyClosedSupport?
    (S : SlabScalePair)
    (entry :
      { support : List Z4Plaq //
        support ∈ sublists
          (boundaryCompleteSlabPlaquettes S.fine.extent) }) :
    Option (ClosedBinarySlabSupport S) :=
  if hcheck : evenFaceIncidenceCheck entry.val = true then
    some {
      support := entry.val
      power_mem := entry.property
      even_check := hcheck
    }
  else
    none

/-- The executable finite alphabet of every closed binary support in the
corrected slab. -/
def closedBinarySlabSupports
    (S : SlabScalePair) : List (ClosedBinarySlabSupport S) :=
  (sublists
    (boundaryCompleteSlabPlaquettes S.fine.extent)).attach.filterMap
      (certifyClosedSupport? S)

/-- The corresponding finite alphabet of genuine binary even layers. -/
def closedBinarySlabLayers
    (S : SlabScalePair) : List (BinaryEvenSlabLayer S) :=
  (closedBinarySlabSupports S).map
    ClosedBinarySlabSupport.toLayer

theorem supportCodeOfLayer_mem
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    supportCodeOfLayer layer ∈ closedBinarySlabSupports S := by
  let code := supportCodeOfLayer layer
  let entry :
      { support : List Z4Plaq //
        support ∈ sublists
          (boundaryCompleteSlabPlaquettes S.fine.extent) } :=
    ⟨code.support, code.power_mem⟩
  unfold closedBinarySlabSupports
  apply List.mem_filterMap.mpr
  refine ⟨entry, List.mem_attach _ entry, ?_⟩
  unfold certifyClosedSupport?
  rw [dif_pos code.even_check]

theorem supportCodeOfLayer_toLayer_mem
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S) :
    (supportCodeOfLayer layer).toLayer ∈
      closedBinarySlabLayers S := by
  unfold closedBinarySlabLayers
  exact List.mem_map.mpr
    ⟨supportCodeOfLayer layer,
      supportCodeOfLayer_mem layer, rfl⟩

/-! ## 3. Finite words and reconstruction -/

/-- All words of one exact length over a finite alphabet. -/
def wordsOfLength {A : Type} (alphabet : List A) :
    Nat → List (List A)
  | 0 => [[]]
  | length + 1 =>
      alphabet.flatMap (fun head =>
        (wordsOfLength alphabet length).map
          (fun tail => head :: tail))

/-- All words of length at most the displayed budget. -/
def wordsUpTo {A : Type} (alphabet : List A) :
    Nat → List (List A)
  | 0 => [[]]
  | budget + 1 =>
      wordsUpTo alphabet budget ++
        wordsOfLength alphabet (budget + 1)

theorem mem_wordsOfLength_of_all_mem
    {A : Type} (alphabet : List A) :
    ∀ word : List A,
      (∀ entry, entry ∈ word → entry ∈ alphabet) →
        word ∈ wordsOfLength alphabet word.length
  | [], _ => by
      exact List.mem_singleton.mpr rfl
  | head :: tail, hall => by
      unfold wordsOfLength
      apply List.mem_flatMap.mpr
      refine ⟨head, hall head List.mem_cons_self, ?_⟩
      apply List.mem_map.mpr
      refine ⟨tail, mem_wordsOfLength_of_all_mem
        alphabet tail ?_, rfl⟩
      intro entry hentry
      exact hall entry (List.mem_cons_of_mem head hentry)

theorem mem_wordsUpTo_of_length_le
    {A : Type} (alphabet : List A) :
    ∀ budget word,
      word.length ≤ budget →
      (∀ entry, entry ∈ word → entry ∈ alphabet) →
        word ∈ wordsUpTo alphabet budget
  | 0, word, hlength, hall => by
      have hempty : word = [] := by
        apply List.eq_nil_of_length_eq_zero
        omega
      rw [hempty]
      exact List.mem_singleton.mpr rfl
  | budget + 1, word, hlength, hall => by
      unfold wordsUpTo
      by_cases hsmall : word.length ≤ budget
      · exact List.mem_append.mpr
          (Or.inl
            (mem_wordsUpTo_of_length_le
              alphabet budget word hsmall hall))
      · have hexact : word.length = budget + 1 := by
          omega
        exact List.mem_append.mpr
          (Or.inr
            (hexact ▸
              mem_wordsOfLength_of_all_mem
                alphabet word hall))

/-- Replace every abstract binary layer by the canonical layer generated
from its own odd support. -/
def canonicalizeLayers {S : SlabScalePair} :
    List (BinaryEvenSlabLayer S) →
      List (BinaryEvenSlabLayer S)
  | [] => []
  | head :: tail =>
      (supportCodeOfLayer head).toLayer ::
        canonicalizeLayers tail

theorem canonicalizeLayers_length
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      (canonicalizeLayers layers).length = layers.length
  | [] => rfl
  | _ :: tail => by
      simp only [canonicalizeLayers, List.length_cons]
      rw [canonicalizeLayers_length tail]

theorem canonicalizeLayers_all_mem
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      ∀ layer, layer ∈ canonicalizeLayers layers →
        layer ∈ closedBinarySlabLayers S
  | [], layer, hmem => absurd hmem List.not_mem_nil
  | head :: tail, layer, hmem => by
      rcases List.mem_cons.mp hmem with heq | htail
      · rw [heq]
        exact supportCodeOfLayer_toLayer_mem head
      · exact canonicalizeLayers_all_mem tail layer htail

theorem canonicalizeLayers_sum
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      sumLayerStates (canonicalizeLayers layers) =
        sumLayerStates layers
  | [] => rfl
  | head :: tail => by
      funext faceId
      unfold canonicalizeLayers sumLayerStates addEdgeLabelling
      rw [supportCodeOfLayer_toLayer_state head]
      rw [congrFun (canonicalizeLayers_sum tail) faceId]

/-- It is enough to compare two supported labellings on the finite physical
face-ID list. -/
def reconstructionCheck
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (layers : List (BinaryEvenSlabLayer S)) : Bool :=
  (slabPhysicalFaceEdges S.fine.extent).all
    (fun faceId =>
      decide (sumLayerStates layers faceId = fineState faceId))

private theorem layerState_zero_outside
    {S : SlabScalePair} (layer : BinaryEvenSlabLayer S)
    {faceId : Nat}
    (hface :
      faceId ∉ slabPhysicalFaceEdges S.fine.extent) :
    layer.state faceId = 0 := by
  have hmem := layer.state_mem
  change layer.state ∈
    boundedEdgeLabellings 1
      (slabPhysicalFaceEdges S.fine.extent) at hmem
  exact
    (boundedEdgeLabellings_sound 1
      (slabPhysicalFaceEdges S.fine.extent)
      layer.state hmem).2 faceId hface

theorem sumLayerStates_zero_outside
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      ∀ faceId,
        faceId ∉ slabPhysicalFaceEdges S.fine.extent →
          sumLayerStates layers faceId = 0
  | [], faceId, _ => by
      rfl
  | head :: tail, faceId, hface => by
      unfold sumLayerStates addEdgeLabelling
      rw [layerState_zero_outside head hface,
        sumLayerStates_zero_outside tail faceId hface]

theorem reconstructionCheck_sound
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    {layers : List (BinaryEvenSlabLayer S)}
    (hcheck : reconstructionCheck S fineState layers = true) :
    sumLayerStates layers = fineState := by
  funext faceId
  by_cases hface :
      faceId ∈ slabPhysicalFaceEdges S.fine.extent
  · exact of_decide_eq_true
      (List.all_eq_true.mp hcheck faceId hface)
  · rw [sumLayerStates_zero_outside layers faceId hface]
    have hmem := hfineMem
    change fineState ∈
      boundedEdgeLabellings S.fine.cutoff
        (slabPhysicalFaceEdges S.fine.extent) at hmem
    exact
      ((boundedEdgeLabellings_sound S.fine.cutoff
        (slabPhysicalFaceEdges S.fine.extent)
        fineState hmem).2 faceId hface).symm

theorem reconstructionCheck_complete
    {S : SlabScalePair} {fineState : EdgeLabelling}
    {layers : List (BinaryEvenSlabLayer S)}
    (hreconstruct : sumLayerStates layers = fineState) :
    reconstructionCheck S fineState layers = true := by
  unfold reconstructionCheck
  apply List.all_eq_true.mpr
  intro faceId _
  exact decide_eq_true (congrFun hreconstruct faceId)

/-! ## 4. Executable search and semantic extraction -/

/-- Search every closed-layer word up to `budget` for an exact
reconstruction of `fineState`. -/
def binaryMulticoverSearch
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (budget : Nat) :
    Option (List (BinaryEvenSlabLayer S)) :=
  (wordsUpTo (closedBinarySlabLayers S) budget).find?
    (reconstructionCheck S fineState)

/-- A successful finite search result is a genuine global multicover, not
merely a collection of pointwise test data. -/
def multicoverOfSearchSuccess
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    {budget : Nat} {layers : List (BinaryEvenSlabLayer S)}
    (hfound :
      binaryMulticoverSearch S fineState budget = some layers) :
    BinaryEvenSlabMulticover S fineState where
  layers := layers
  reconstruct :=
    reconstructionCheck_sound hfineMem
      (List.find?_some hfound)

/-! ## 5. Relative completeness of the finite search -/

/-- If a genuine multicover exists, the finite search succeeds at the
literal number of its layers.  Thus the search alphabet loses no abstract
binary layer: every layer is represented by its own odd-support code. -/
def searchSuccessOfMulticover
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState) :
    { layers : List (BinaryEvenSlabLayer S) //
      binaryMulticoverSearch
        S fineState multicover.layers.length = some layers } := by
  let canonical := canonicalizeLayers multicover.layers
  have hcanonicalLength :
      canonical.length = multicover.layers.length :=
    canonicalizeLayers_length multicover.layers
  have hcanonicalEntries :
      ∀ layer, layer ∈ canonical →
        layer ∈ closedBinarySlabLayers S :=
    canonicalizeLayers_all_mem multicover.layers
  have hword :
      canonical ∈
        wordsUpTo
          (closedBinarySlabLayers S)
          multicover.layers.length := by
    apply mem_wordsUpTo_of_length_le
    · omega
    · exact hcanonicalEntries
  have hreconstruct :
      sumLayerStates canonical = fineState :=
    (canonicalizeLayers_sum multicover.layers).trans
      multicover.reconstruct
  have hcheck :
      reconstructionCheck S fineState canonical = true :=
    reconstructionCheck_complete hreconstruct
  cases hsearch :
      binaryMulticoverSearch
        S fineState multicover.layers.length with
  | none =>
      have hfind :
          (wordsUpTo
            (closedBinarySlabLayers S)
            multicover.layers.length).find?
              (reconstructionCheck S fineState) = none := by
        simpa [binaryMulticoverSearch] using hsearch
      exact absurd hcheck
        ((List.find?_eq_none.mp hfind) canonical hword)
  | some layers =>
      exact ⟨layers, rfl⟩

/-- Extract the search-produced semantic multicover from any pre-existing
one.  The returned layers are the first passing finite word, not an opaque
choice. -/
def searchedMulticoverOfExisting
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (multicover : BinaryEvenSlabMulticover S fineState) :
    BinaryEvenSlabMulticover S fineState := by
  obtain ⟨layers, hfound⟩ :=
    searchSuccessOfMulticover multicover
  exact multicoverOfSearchSuccess hfineMem hfound

#print axioms evenFaceIncidenceCheck_sound
#print axioms evenFaceIncidenceCheck_complete
#print axioms ClosedBinarySlabSupport.subset
#print axioms ClosedBinarySlabSupport.nodup
#print axioms ClosedBinarySlabSupport.even
#print axioms ClosedBinarySlabSupport.toLayer
#print axioms supportCodeOfLayer_toLayer_state
#print axioms supportCodeOfLayer_mem
#print axioms mem_wordsUpTo_of_length_le
#print axioms canonicalizeLayers_sum
#print axioms sumLayerStates_zero_outside
#print axioms reconstructionCheck_sound
#print axioms reconstructionCheck_complete
#print axioms multicoverOfSearchSuccess
#print axioms searchSuccessOfMulticover
#print axioms searchedMulticoverOfExisting

end YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
