/-
# Base cases of the actual graph-to-sequential-kernel rewrite

The recursive graph-syntax proof has two exceptional base shapes.  The
zero-valent resolver is empty.  The one-valent resolver is not an ordinary
three-distinct-edge vertex: it is `(physical, vacuum, vacuum)`, so the same
vacuum terminator occurs in both remaining slots.

This module handles both shapes using the production `fuseLabels`, actual
bounded Cartesian enumeration, zero-padded physical packet, normalized
vacuum terminator, and vertex-only projector.  The one-leg calculation
proves pointwise that the repeated-vacuum graph term is exactly the first
step of `explicitSequentialKernel`, then lifts it through two finite sums.

Honest scope: these are the exact recursion bases.  The successor chain step
for lists of length at least two and actual identifier transport remain.
-/

import YMGap.Continuum.Z4SequentialLinkExplicitKernel

namespace YMGap.Continuum.Z4SequentialGraphKernelBaseCases

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalLinkFusionCompleteHaar
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4FiniteGraphVacuumCompletion
open YMGap.Continuum.Z4SequentialLinkExplicitKernel

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Empty resolver -/

def zeroValentVertexCartesianSum {K : Nat} (P : CharacterPacket K) : Q' :=
  listQSum
    (graphVertexProject (fuseLabels 0 1 [])
      (packetGraphBareAmplitude [] (fun _ => facePacketAtLinkCutoff P)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) [])

theorem zeroValentVertexSum_eq_explicitKernel
    {K : Nat} (P : CharacterPacket K) :
    zeroValentVertexCartesianSum P ≈
      explicitSequentialKernel P 0 0 := by
  unfold zeroValentVertexCartesianSum fuseLabels boundedEdgeLabellings
    graphVertexProject verticesAdmissibleB packetGraphBareAmplitude
    eliminateLinks explicitSequentialKernel
  change (1 : Q') + 0 ≈ 1
  exact q_add_zero_eqv 1

/-! ## 2. The repeated-vacuum one-leg resolver -/

def oneValentGraphEdges : List Nat := [0, 1]

def oneValentGraphVertices : List TrivalentVertex :=
  fuseLabels 1 2 [0]

theorem oneValentGraphVertices_exact :
    oneValentGraphVertices = [(0, 1, 1)] := by
  rfl

def oneValentGraphPackets {K : Nat} (P : CharacterPacket K) :
    Nat → CharacterPacket (linkAuxiliaryCutoff K) := fun edge =>
  if edge = 0 then facePacketAtLinkCutoff P
  else vacuumPacket (linkAuxiliaryCutoff K)

def oneValentVertexCartesianSum {K : Nat} (P : CharacterPacket K) : Q' :=
  listQSum
    (graphVertexProject oneValentGraphVertices
      (packetGraphBareAmplitude oneValentGraphEdges
        (oneValentGraphPackets P)))
    (boundedEdgeLabellings (linkAuxiliaryCutoff K) oneValentGraphEdges)

def oneValentGraphTerm {K : Nat} (P : CharacterPacket K)
    (external previous : Nat) : Q' :=
  if fusionOK external previous previous = true then
    coeffAt (facePacketAtLinkCutoff P) external *
      (coeffAt (vacuumPacket (linkAuxiliaryCutoff K)) previous * 1)
  else 0

def oneValentExplicitGraphSum {K : Nat} (P : CharacterPacket K) : Q' :=
  fsum (fun external => fsum (fun previous =>
    oneValentGraphTerm P external previous)
    (linkAuxiliaryCutoff K + 1))
    (linkAuxiliaryCutoff K + 1)

theorem oneValentVertexSum_eq_explicitGraph
    {K : Nat} (P : CharacterPacket K) :
    oneValentVertexCartesianSum P ≈
      oneValentExplicitGraphSum P := by
  unfold oneValentVertexCartesianSum oneValentGraphEdges
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 0 [1] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro external
  refine Q'.eqv_trans _ _ _
    (listQSum_bounded_cons (linkAuxiliaryCutoff K) 1 [] _) ?_
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro previous
  change listQSum _ [zeroEdgeLabelling] ≈
    oneValentGraphTerm P external previous
  change graphVertexProject oneValentGraphVertices
      (packetGraphBareAmplitude [0, 1] (oneValentGraphPackets P))
      (setEdgeLabel (setEdgeLabel zeroEdgeLabelling 1 previous) 0 external) +
      0 ≈ oneValentGraphTerm P external previous
  rw [oneValentGraphVertices_exact]
  unfold graphVertexProject verticesAdmissibleB packetGraphBareAmplitude
    eliminateLinks oneValentGraphPackets oneValentGraphTerm
  by_cases hfusion : fusionOK external previous previous = true
  · simp [setEdgeLabel, hfusion]
    exact q_add_zero_eqv _
  · simp [setEdgeLabel, hfusion]
    exact q_zero_add_eqv 0

private theorem oneValentGraphTerm_eq_kernelTerm
    {K external previous : Nat} (P : CharacterPacket K) :
    oneValentGraphTerm P external previous ≈
      fusionInd external previous 0 *
        (coeffAt (facePacketAtLinkCutoff P) external *
          (if previous = 0 then 1 else 0)) := by
  unfold oneValentGraphTerm
  rw [YMGap.Continuum.SU2FiniteTrivalentPacketGraphVacuumCylinder.coeffAt_vacuumPacket]
  by_cases hprevious : previous = 0
  · subst previous
    unfold fusionInd
    by_cases hfusion : fusionOK external 0 0 = true
    · rw [if_pos hfusion, if_pos hfusion, if_pos rfl]
      refine Q'.eqv_trans _
        (coeffAt (facePacketAtLinkCutoff P) external * 1) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.one_mul_eqv 1)) ?_
      refine Q'.eqv_trans _ (coeffAt (facePacketAtLinkCutoff P) external) _
        (Q'.mul_one_eqv _) ?_
      refine Q'.eqv_trans _
        (coeffAt (facePacketAtLinkCutoff P) external * 1) _
        (Q'.eqv_symm (Q'.mul_one_eqv _)) ?_
      exact Q'.eqv_symm (Q'.one_mul_eqv _)
    · rw [if_neg hfusion, if_neg hfusion, if_pos rfl]
      exact Q'.eqv_symm (Q'.zero_mul_eqv _)
  · unfold fusionInd
    rw [if_neg hprevious]
    have hright :
        (if fusionOK external previous 0 = true then (1 : Q') else 0) *
            (coeffAt (facePacketAtLinkCutoff P) external * 0) ≈ 0 :=
      Q'.eqv_trans _
        ((if fusionOK external previous 0 = true then (1 : Q') else 0) * 0) _
        (Q'.mul_eqv_congr_left _ _ _
          (Q'.mul_zero_eqv (coeffAt (facePacketAtLinkCutoff P) external)))
        (Q'.mul_zero_eqv _)
    by_cases hfusion : fusionOK external previous previous = true
    · rw [if_pos hfusion]
      refine Q'.eqv_trans _ 0 _ ?_ (Q'.eqv_symm hright)
      exact Q'.eqv_trans _
        (coeffAt (facePacketAtLinkCutoff P) external * 0) _
        (Q'.mul_eqv_congr_left _ _ _ (Q'.zero_mul_eqv 1))
        (Q'.mul_zero_eqv _)
    · rw [if_neg hfusion]
      exact Q'.eqv_symm hright

theorem oneValentExplicitGraphSum_eq_explicitKernel
    {K : Nat} (P : CharacterPacket K) :
    oneValentExplicitGraphSum P ≈
      explicitSequentialKernel P 1 0 := by
  unfold oneValentExplicitGraphSum explicitSequentialKernel
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro external
  apply YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
  intro previous
  exact oneValentGraphTerm_eq_kernelTerm P

theorem oneValentVertexSum_eq_explicitKernel
    {K : Nat} (P : CharacterPacket K) :
    oneValentVertexCartesianSum P ≈
      explicitSequentialKernel P 1 0 :=
  Q'.eqv_trans _ _ _ (oneValentVertexSum_eq_explicitGraph P)
    (oneValentExplicitGraphSum_eq_explicitKernel P)

end YMGap.Continuum.Z4SequentialGraphKernelBaseCases

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SequentialGraphKernelBaseCases.zeroValentVertexSum_eq_explicitKernel
#print axioms YMGap.Continuum.Z4SequentialGraphKernelBaseCases.oneValentGraphVertices_exact
#print axioms YMGap.Continuum.Z4SequentialGraphKernelBaseCases.oneValentVertexSum_eq_explicitGraph
#print axioms YMGap.Continuum.Z4SequentialGraphKernelBaseCases.oneValentExplicitGraphSum_eq_explicitKernel
#print axioms YMGap.Continuum.Z4SequentialGraphKernelBaseCases.oneValentVertexSum_eq_explicitKernel
