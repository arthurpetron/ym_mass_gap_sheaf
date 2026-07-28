/-
# Canonical odd sheet and exact residual for every positive SU(2) row

Every positive corrected-slab SU(2) summand has an even odd-spin support.
This file turns that support into the literal first member of the binary
multicover carrier and subtracts it pointwise from the original labelling.

The result is stronger than the parity statement alone:

* the sheet is an actual `BinaryEvenSlabLayer`;
* it is pointwise bounded by the original physical labelling;
* the residual is again a member of the same finite physical carrier;
* sheet plus residual reconstructs the original labelling exactly; and
* every physical residual label is even.

This is the constructive induction interface needed by a strand-colouring
argument.  It deliberately does not assert that the residual physical term
is positive: preservation of the local intertwiner cone under this
subtraction is the remaining normality step.

## Axiom gate

Finite list membership and natural-number arithmetic only.  No
`Classical.*`, `sorry`, `native_decide`, custom axiom, or noncomputable
declaration is used.
-/

import YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
import YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer

namespace YMGap.Continuum.BF4SU2OuterOddLayerResidual

set_option maxRecDepth 100000
set_option maxHeartbeats 12000000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2OuterBinaryLayerReduction
open YMGap.Continuum.BF4SU2OuterBinaryMulticoverReduction
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualAllCutoffOddParitySlabLayer
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2FusionSupportAddition

/-! ## 1. The canonical first closed sheet -/

/-- The odd-spin support of a positive row, realized as an actual closed
binary layer on the same corrected-slab geometry. -/
def positiveOddLayer
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    BinaryEvenSlabLayer S :=
  binaryEvenSlabLayerOfSupport
    S (fineOddSlabSupport S fineState)
    (fun _ hmem => fineOddSlabSupport_subset hmem)
    (fineOddSlabSupport_nodup S fineState)
    (positivePhysicalTerm_fineOddSupport_even hfineMem hpositive)

/-- On every physical face, the canonical layer is exactly the parity bit of
the original twice-spin label. -/
theorem positiveOddLayer_state_eq_mod_two
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (faceId : Nat) (hface : faceId ∈ S.fine.faceEdges) :
    (positiveOddLayer S fineState hfineMem hpositive).state faceId =
      fineState faceId % 2 := by
  exact slabBinaryFineOddSupport_eq_mod_two hface

/-- The canonical parity sheet never exceeds the original nonnegative
integer labelling, including off the physical face support. -/
theorem positiveOddLayer_state_le
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (faceId : Nat) :
    (positiveOddLayer S fineState hfineMem hpositive).state faceId ≤
      fineState faceId := by
  by_cases hface : faceId ∈ S.fine.faceEdges
  · rw [positiveOddLayer_state_eq_mod_two
      S fineState hfineMem hpositive faceId hface]
    exact Nat.mod_le _ _
  · have hzero :
        (positiveOddLayer S fineState hfineMem hpositive).state faceId = 0 := by
      unfold positiveOddLayer
      exact slabBinarySupportLabelling_eq_zero_of_not_physical hface
    rw [hzero]
    exact Nat.zero_le _

/-! ## 2. Pointwise subtraction and exact reconstruction -/

/-- Subtract the canonical parity sheet in `Nat`, pointwise. -/
def positiveOddResidual
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    EdgeLabelling :=
  fun faceId =>
    fineState faceId -
      (positiveOddLayer S fineState hfineMem hpositive).state faceId

/-- The canonical layer and its residual reconstruct the fine state
extensionally, without integer coercions or truncated-subtraction loss. -/
theorem positiveOddLayer_add_residual
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    addEdgeLabelling
        (positiveOddLayer S fineState hfineMem hpositive).state
        (positiveOddResidual S fineState hfineMem hpositive) =
      fineState := by
  funext faceId
  unfold addEdgeLabelling positiveOddResidual
  exact Nat.add_sub_of_le
    (positiveOddLayer_state_le
      S fineState hfineMem hpositive faceId)

/-- Subtraction preserves the physical finite carrier: it cannot increase a
label, and both the original labelling and the canonical sheet vanish off
the corrected-slab face list. -/
theorem positiveOddResidual_mem
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    positiveOddResidual S fineState hfineMem hpositive ∈
      S.fine.physicalLabellings := by
  have hsound :=
    boundedEdgeLabellings_sound
      S.fine.cutoff S.fine.faceEdges fineState hfineMem
  apply boundedEdgeLabellings_complete
  · intro faceId hface
    unfold positiveOddResidual
    exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (hsound.1 faceId hface)
  · intro faceId hface
    unfold positiveOddResidual
    rw [hsound.2 faceId hface]
    exact Nat.zero_sub _

/-- Every retained label after the canonical parity subtraction is even. -/
theorem positiveOddResidual_even_on_faces
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (faceId : Nat) (hface : faceId ∈ S.fine.faceEdges) :
    positiveOddResidual S fineState hfineMem hpositive faceId % 2 = 0 := by
  unfold positiveOddResidual
  rw [positiveOddLayer_state_eq_mod_two
    S fineState hfineMem hpositive faceId hface]
  omega

/-! ## 3. The exact induction package -/

/-- The canonical first-step data for an eventual integral strand-colouring
induction.  No positivity field for `residual` is smuggled into the package. -/
structure PositiveOddLayerResidual
    (S : SlabScalePair) (fineState : EdgeLabelling) : Type where
  layer : BinaryEvenSlabLayer S
  residual : EdgeLabelling
  layer_le : ∀ faceId, layer.state faceId ≤ fineState faceId
  reconstruct :
    addEdgeLabelling layer.state residual = fineState
  residual_mem : residual ∈ S.fine.physicalLabellings
  residual_even :
    ∀ faceId, faceId ∈ S.fine.faceEdges →
      residual faceId % 2 = 0

/-- Every positive physical row constructively supplies the exact first-step
strand-colouring package. -/
def positivePhysicalTermOddLayerResidual
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState) :
    PositiveOddLayerResidual S fineState where
  layer := positiveOddLayer S fineState hfineMem hpositive
  residual := positiveOddResidual S fineState hfineMem hpositive
  layer_le :=
    positiveOddLayer_state_le S fineState hfineMem hpositive
  reconstruct :=
    positiveOddLayer_add_residual S fineState hfineMem hpositive
  residual_mem :=
    positiveOddResidual_mem S fineState hfineMem hpositive
  residual_even :=
    positiveOddResidual_even_on_faces
      S fineState hfineMem hpositive

/-! ## 4. Exact reduction of the multicover obstruction -/

/-- If the even residual admits a binary multicover, prepending the
canonical odd sheet gives a multicover of the original positive row.

Thus the all-positive-row integral strand-colouring problem has been reduced
constructively to the same problem for an all-even residual; the parity
sheet itself is no longer part of the missing argument. -/
def PositiveOddLayerResidual.prependResidualMulticover
    {S : SlabScalePair} {fineState : EdgeLabelling}
    (firstStep : PositiveOddLayerResidual S fineState)
    (residualCover :
      BinaryEvenSlabMulticover S firstStep.residual) :
    BinaryEvenSlabMulticover S fineState where
  layers := firstStep.layer :: residualCover.layers
  reconstruct := by
    simp only [sumLayerStates]
    rw [residualCover.reconstruct]
    exact firstStep.reconstruct

/-- Positive-row specialization of
`PositiveOddLayerResidual.prependResidualMulticover`. -/
def positivePhysicalTermMulticoverOfResidual
    (S : SlabScalePair) (fineState : EdgeLabelling)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (hpositive : (0 : Q') < S.fine.physicalTerm fineState)
    (residualCover :
      BinaryEvenSlabMulticover S
        (positiveOddResidual S fineState hfineMem hpositive)) :
    BinaryEvenSlabMulticover S fineState :=
  (positivePhysicalTermOddLayerResidual
    S fineState hfineMem hpositive).prependResidualMulticover
      residualCover

#print axioms positiveOddLayer
#print axioms positiveOddLayer_state_eq_mod_two
#print axioms positiveOddLayer_state_le
#print axioms positiveOddLayer_add_residual
#print axioms positiveOddResidual_mem
#print axioms positiveOddResidual_even_on_faces
#print axioms PositiveOddLayerResidual
#print axioms positivePhysicalTermOddLayerResidual
#print axioms PositiveOddLayerResidual.prependResidualMulticover
#print axioms positivePhysicalTermMulticoverOfResidual

end YMGap.Continuum.BF4SU2OuterOddLayerResidual
