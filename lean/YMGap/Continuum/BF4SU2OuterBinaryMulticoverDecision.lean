/-
# A complete row-mass decision procedure for BF4 binary multicovers

The finite multicover search was initially indexed by an arbitrary layer
budget.  This file removes that unbounded existential parameter.

For a fine row `state`, let its physical face mass be the sum of its labels
over the corrected-slab face list.  Canonicalize every abstract binary layer
through its geometric support and delete the empty supports.  Every retained
sheet then consumes at least one unit of physical face mass, while deletion
and canonicalization preserve the reconstructed state.  Consequently every
multicover has an equivalent canonical representative containing at most
`slabFaceMass S state` layers.

Searching through that row-mass budget is therefore complete.  The resulting
decision object is constructive: it contains either a literal
`BinaryEvenSlabMulticover` or a function sending every alleged multicover to
`False`.

For a positive physical row, the same decision is applied to the exact
all-even residual after removal of the canonical odd sheet.  Success gives a
multicover of the original row; failure gives a constructive refutation of
the residual multicover input.  This does not assert residual normality.

## Axiom gate

Finite list recursion, decidable equality, and natural-number arithmetic
only.  No `Classical.*`, `sorry`, `native_decide`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
import YMGap.Continuum.BF4SU2OuterOddLayerResidual

namespace YMGap.Continuum.BF4SU2OuterBinaryMulticoverDecision

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverDecision
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverSearch
open YMGap.Continuum.BF4SU2OuterOddLayerResidual
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualCutoffOnePositivePhysicalClosure
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. Exact physical face mass -/

/-- Sum of a numerical face labelling over the literal corrected-slab face
identifier list. -/
def slabFaceMass (S : SlabScalePair) (state : EdgeLabelling) : Nat :=
  natListSum
    ((slabPhysicalFaceEdges S.fine.extent).map state)

private theorem natListSum_map_add
    (left right : Nat → Nat) :
    ∀ ids : List Nat,
      natListSum
          (ids.map (fun id => left id + right id)) =
        natListSum (ids.map left) +
          natListSum (ids.map right)
  | [] => rfl
  | head :: tail => by
      simp only [List.map_cons, natListSum]
      rw [natListSum_map_add left right tail]
      omega

private theorem natListSum_map_zero :
    ∀ ids : List Nat,
      natListSum (ids.map (fun _ => 0)) = 0
  | [] => rfl
  | _ :: tail => by
      simp only [List.map_cons, natListSum, Nat.zero_add]
      exact natListSum_map_zero tail

theorem slabFaceMass_zero (S : SlabScalePair) :
    slabFaceMass S zeroEdgeLabelling = 0 := by
  unfold slabFaceMass zeroEdgeLabelling
  exact natListSum_map_zero _

theorem slabFaceMass_add
    (S : SlabScalePair) (left right : EdgeLabelling) :
    slabFaceMass S (addEdgeLabelling left right) =
      slabFaceMass S left + slabFaceMass S right := by
  unfold slabFaceMass addEdgeLabelling
  exact natListSum_map_add left right _

theorem slabFaceMass_sumLayerStates
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      slabFaceMass S (sumLayerStates layers) =
        natListSum
          (layers.map
            (fun layer => slabFaceMass S layer.state))
  | [] => by
      simp only [sumLayerStates, List.map_nil, natListSum]
      exact slabFaceMass_zero S
  | head :: tail => by
      simp only [sumLayerStates, List.map_cons, natListSum]
      rw [slabFaceMass_add,
        slabFaceMass_sumLayerStates tail]

private theorem natListSum_pos_of_mem
    {value : Nat} :
    ∀ values : List Nat,
      value ∈ values → 0 < value →
        0 < natListSum values
  | [], hmem, _ => absurd hmem List.not_mem_nil
  | head :: tail, hmem, hpos => by
      rcases List.mem_cons.mp hmem with heq | htail
      · rw [← heq]
        simp only [natListSum]
        omega
      · have ih := natListSum_pos_of_mem tail htail hpos
        simp only [natListSum]
        omega

/-! ## 2. Empty-sheet pruning and its mass charge -/

/-- A nonempty certified support has strictly positive physical face mass
when interpreted as its canonical binary layer. -/
theorem closedBinarySlabSupport_faceMass_pos
    {S : SlabScalePair} (code : ClosedBinarySlabSupport S)
    (hnonempty : code.support ≠ []) :
    0 < slabFaceMass S code.toLayer.state := by
  cases hsupport : code.support with
  | nil =>
      exact absurd hsupport hnonempty
  | cons plaquette rest =>
      have hplaquetteSupport :
          plaquette ∈ code.support := by
        rw [hsupport]
        exact List.mem_cons_self
      have hplaquetteSlab :
          plaquette ∈
            boundaryCompleteSlabPlaquettes
              S.fine.extent :=
        code.subset plaquette hplaquetteSupport
      let faceId :=
        listIndexOf plaquette
          (boundaryCompleteSlabPlaquettes
            S.fine.extent)
      have hfaceId :
          faceId ∈
            slabPhysicalFaceEdges S.fine.extent := by
        unfold faceId slabPhysicalFaceEdges
        exact List.mem_range.mpr
          (listIndexOf_lt_of_mem
            plaquette
            (boundaryCompleteSlabPlaquettes
              S.fine.extent)
            hplaquetteSlab)
      have hlookup :
          slabPlaquetteAt S.fine.extent faceId =
            plaquette := by
        unfold faceId slabPlaquetteAt
        exact getD_listIndexOf_of_mem
          fallbackPlaquette plaquette
          (boundaryCompleteSlabPlaquettes
            S.fine.extent)
          hplaquetteSlab
      have hstate :
          code.toLayer.state faceId = 1 := by
        change
          slabBinarySupportLabelling
              S.fine.extent code.support faceId = 1
        rw [slabBinarySupportLabelling_eq_indicator
          hfaceId, hlookup]
        simp [hplaquetteSupport]
      unfold slabFaceMass
      apply natListSum_pos_of_mem
        ((slabPhysicalFaceEdges
          S.fine.extent).map code.toLayer.state)
      · exact List.mem_map.mpr
          ⟨faceId, hfaceId, rfl⟩
      · rw [hstate]
        exact Nat.zero_lt_succ 0

/-- The canonical layer of an empty support is the zero labelling. -/
theorem closedBinarySlabSupport_state_eq_zero
    {S : SlabScalePair} (code : ClosedBinarySlabSupport S)
    (hempty : code.support = []) :
    code.toLayer.state = zeroEdgeLabelling := by
  funext faceId
  change
    slabBinarySupportLabelling
        S.fine.extent code.support faceId =
      zeroEdgeLabelling faceId
  rw [hempty]
  unfold slabBinarySupportLabelling zeroEdgeLabelling
  split
  · simp
  · rfl

/-- Canonicalize arbitrary layers through their geometric support and remove
exactly the empty support codes. -/
def pruneCanonicalLayers {S : SlabScalePair} :
    List (BinaryEvenSlabLayer S) →
      List (BinaryEvenSlabLayer S)
  | [] => []
  | head :: tail =>
      if (supportCodeOfLayer head).support = [] then
        pruneCanonicalLayers tail
      else
        (supportCodeOfLayer head).toLayer ::
          pruneCanonicalLayers tail

theorem pruneCanonicalLayers_sum
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      sumLayerStates (pruneCanonicalLayers layers) =
        sumLayerStates layers
  | [] => rfl
  | head :: tail => by
      by_cases hempty :
          (supportCodeOfLayer head).support = []
      · simp only [pruneCanonicalLayers, if_pos hempty]
        funext faceId
        simp only [sumLayerStates, addEdgeLabelling]
        rw [← supportCodeOfLayer_toLayer_state head]
        rw [congrFun
          (closedBinarySlabSupport_state_eq_zero
            (supportCodeOfLayer head) hempty)
          faceId]
        unfold zeroEdgeLabelling
        rw [Nat.zero_add,
          congrFun (pruneCanonicalLayers_sum tail)
            faceId]
      · simp only [pruneCanonicalLayers, if_neg hempty,
          sumLayerStates]
        funext faceId
        rw [supportCodeOfLayer_toLayer_state head]
        change
          head.state faceId +
              sumLayerStates
                (pruneCanonicalLayers tail) faceId =
            head.state faceId +
              sumLayerStates tail faceId
        rw [congrFun
          (pruneCanonicalLayers_sum tail) faceId]

theorem pruneCanonicalLayers_all_mem
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      ∀ layer, layer ∈ pruneCanonicalLayers layers →
        layer ∈ closedBinarySlabLayers S
  | [], layer, hmem => absurd hmem List.not_mem_nil
  | head :: tail, layer, hmem => by
      by_cases hempty :
          (supportCodeOfLayer head).support = []
      · simp only [pruneCanonicalLayers, if_pos hempty] at hmem
        exact pruneCanonicalLayers_all_mem tail layer hmem
      · simp only [pruneCanonicalLayers, if_neg hempty] at hmem
        rcases List.mem_cons.mp hmem with heq | htail
        · rw [heq]
          exact supportCodeOfLayer_toLayer_mem head
        · exact pruneCanonicalLayers_all_mem
            tail layer htail

/-- Every retained canonical sheet is charged to at least one unit of the
state reconstructed by the original list. -/
theorem pruneCanonicalLayers_length_le_faceMass
    {S : SlabScalePair} :
    ∀ layers : List (BinaryEvenSlabLayer S),
      (pruneCanonicalLayers layers).length ≤
        slabFaceMass S (sumLayerStates layers)
  | [] => by
      simp only [pruneCanonicalLayers, List.length_nil,
        sumLayerStates, slabFaceMass_zero]
      exact Nat.zero_le _
  | head :: tail => by
      by_cases hempty :
          (supportCodeOfLayer head).support = []
      · simp only [pruneCanonicalLayers, if_pos hempty]
        have ih :=
          pruneCanonicalLayers_length_le_faceMass tail
        rw [sumLayerStates, slabFaceMass_add]
        omega
      · simp only [pruneCanonicalLayers, if_neg hempty,
          List.length_cons]
        have hhead :=
          closedBinarySlabSupport_faceMass_pos
            (supportCodeOfLayer head) hempty
        rw [supportCodeOfLayer_toLayer_state head] at hhead
        have ih :=
          pruneCanonicalLayers_length_le_faceMass tail
        rw [sumLayerStates, slabFaceMass_add]
        omega

/-! ## 3. Complete search at the row-mass cutoff -/

/-- Every genuine multicover has a canonical, empty-free representative
whose number of sheets is bounded by the exact physical row mass. -/
def massBoundedCanonicalMulticover
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState) :
    { layers : List (BinaryEvenSlabLayer S) //
      (∀ layer, layer ∈ layers →
        layer ∈ closedBinarySlabLayers S) ∧
      sumLayerStates layers = fineState ∧
      layers.length ≤ slabFaceMass S fineState } := by
  let layers := pruneCanonicalLayers multicover.layers
  refine ⟨layers, ?_, ?_, ?_⟩
  · exact pruneCanonicalLayers_all_mem
      multicover.layers
  · exact
      (pruneCanonicalLayers_sum
        multicover.layers).trans
          multicover.reconstruct
  · have hmass :=
      pruneCanonicalLayers_length_le_faceMass
        multicover.layers
    rw [multicover.reconstruct] at hmass
    exact hmass

/-- If any multicover exists, the literal finite search succeeds at the
row's physical face mass.  The bound is independent of the unknown cover. -/
def massBudgetSearchSuccessOfMulticover
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (multicover : BinaryEvenSlabMulticover S fineState) :
    { layers : List (BinaryEvenSlabLayer S) //
      binaryMulticoverSearch
        S fineState (slabFaceMass S fineState) =
          some layers } := by
  obtain ⟨canonical, hall, hreconstruct, hlength⟩ :=
    massBoundedCanonicalMulticover multicover
  have hword :
      canonical ∈
        wordsUpTo
          (closedBinarySlabLayers S)
          (slabFaceMass S fineState) :=
    mem_wordsUpTo_of_length_le
      (closedBinarySlabLayers S)
      (slabFaceMass S fineState)
      canonical hlength hall
  have hcheck :
      reconstructionCheck S fineState canonical = true :=
    reconstructionCheck_complete hreconstruct
  cases hsearch :
      binaryMulticoverSearch
        S fineState (slabFaceMass S fineState) with
  | none =>
      have hfind :
          (wordsUpTo
            (closedBinarySlabLayers S)
            (slabFaceMass S fineState)).find?
              (reconstructionCheck S fineState) = none := by
        simpa [binaryMulticoverSearch] using hsearch
      exact absurd hcheck
        ((List.find?_eq_none.mp hfind)
          canonical hword)
  | some layers =>
      exact ⟨layers, rfl⟩

/-- Constructive decision data for binary multicover existence. -/
inductive BinaryMulticoverDecision
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type
  | yes :
      BinaryEvenSlabMulticover S fineState →
        BinaryMulticoverDecision S fineState
  | no :
      (BinaryEvenSlabMulticover S fineState → False) →
        BinaryMulticoverDecision S fineState

/-- Complete finite decision at the row-mass cutoff.  In the negative branch,
any alleged multicover forces the same search to be both `none` and `some`. -/
def decideBinaryMulticover
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings) :
    BinaryMulticoverDecision S fineState := by
  cases hsearch :
      binaryMulticoverSearch
        S fineState (slabFaceMass S fineState) with
  | none =>
      apply BinaryMulticoverDecision.no
      intro multicover
      obtain ⟨layers, hfound⟩ :=
        massBudgetSearchSuccessOfMulticover multicover
      rw [hsearch] at hfound
      contradiction
  | some layers =>
      exact BinaryMulticoverDecision.yes
        (multicoverOfSearchSuccess hfineMem hsearch)

/-! ## 4. Positive rows reduce to a decided all-even residual -/

/-- Result type for the exact positive-row residual reduction.  The negative
branch refutes the residual input only; it does not claim that an unrelated
multicover of the original row would induce a residual cover. -/
inductive PositiveRowResidualDecision
    (S : SlabScalePair) (fineState residual : EdgeLabelling) : Type
  | cover :
      BinaryEvenSlabMulticover S fineState →
        PositiveRowResidualDecision S fineState residual
  | residualObstruction :
      (BinaryEvenSlabMulticover S residual → False) →
        PositiveRowResidualDecision S fineState residual

/-- For every positive physical row, finite computation produces either an
actual multicover of the original row or a constructive refutation of every
multicover of its canonical all-even residual. -/
def decidePositiveRowViaEvenResidual
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    PositiveRowResidualDecision
      S fineState
      (positiveOddResidual
        S fineState hfineMem hpositive) :=
  match decideBinaryMulticover
      S
      (positiveOddResidual
        S fineState hfineMem hpositive)
      (positiveOddResidual_mem
        S fineState hfineMem hpositive) with
  | BinaryMulticoverDecision.yes residualCover =>
      PositiveRowResidualDecision.cover
        (positivePhysicalTermMulticoverOfResidual
          S fineState hfineMem hpositive residualCover)
  | BinaryMulticoverDecision.no hrefute =>
      PositiveRowResidualDecision.residualObstruction
        hrefute

#print axioms slabFaceMass_zero
#print axioms slabFaceMass_add
#print axioms slabFaceMass_sumLayerStates
#print axioms closedBinarySlabSupport_faceMass_pos
#print axioms closedBinarySlabSupport_state_eq_zero
#print axioms pruneCanonicalLayers_sum
#print axioms pruneCanonicalLayers_all_mem
#print axioms pruneCanonicalLayers_length_le_faceMass
#print axioms massBoundedCanonicalMulticover
#print axioms massBudgetSearchSuccessOfMulticover
#print axioms BinaryMulticoverDecision
#print axioms decideBinaryMulticover
#print axioms PositiveRowResidualDecision
#print axioms decidePositiveRowViaEvenResidual

end YMGap.Continuum.BF4SU2OuterBinaryMulticoverDecision
