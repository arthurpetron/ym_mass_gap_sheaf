/-
# Exact enumeration of the cutoff-two cube-subset sector

The executable classifier language consists of one fundamental-spin cube and
the doubled images of the 64 binary labellings of its six faces.  This module
constructs that literal 65-state list and proves its cardinality and
duplicate-freeness.  It also characterizes membership in the doubled part by
the pointwise `0/2` cube-support condition used by the classifier semantics.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage
import YMGap.Continuum.Z4BoundedEdgeLabellingNodup

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration

set_option maxRecDepth 300000
set_option maxHeartbeats 4000000

open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup

/-! ## 1. Doubling the binary cube-face enumeration -/

/-- Pointwise doubling of an edge labelling. -/
def doubleEdgeLabelling (state : EdgeLabelling) : EdgeLabelling :=
  fun id => state id + state id

theorem doubleEdgeLabelling_injective :
    Function.Injective doubleEdgeLabelling := by
  intro left right heq
  funext id
  have hpoint := congrFun heq id
  unfold doubleEdgeLabelling at hpoint
  omega

/-- The 64 labellings carrying independently chosen labels zero or two on
the six faces of the distinguished cube and zero everywhere else. -/
def cutoffTwoDoubledCubeSubsetStates : List EdgeLabelling :=
  (boundedEdgeLabellings 1 centralLowerCubeFaceIds).map
    doubleEdgeLabelling

/-- The exact candidate sector: the fundamental cube followed by the 64
doubled-spin subsets.  The empty doubled subset is the vacuum. -/
def cutoffTwoCubeSectorStates : List EdgeLabelling :=
  centralLowerCubeState :: cutoffTwoDoubledCubeSubsetStates

theorem cutoffTwoDoubledCubeSubsetStates_length :
    cutoffTwoDoubledCubeSubsetStates.length = 64 := by
  decide

theorem cutoffTwoCubeSectorStates_length :
    cutoffTwoCubeSectorStates.length = 65 := by
  decide

theorem cutoffTwoDoubledCubeSubsetStates_nodup :
    cutoffTwoDoubledCubeSubsetStates.Nodup := by
  unfold cutoffTwoDoubledCubeSubsetStates
  apply nodup_map_of_injOn
  · apply boundedEdgeLabellings_nodup
    decide
  · intro left _ right _ heq
    exact doubleEdgeLabelling_injective heq

theorem centralLowerCubeState_not_mem_doubledCubeSubsetStates :
    centralLowerCubeState ∉ cutoffTwoDoubledCubeSubsetStates := by
  intro hmem
  unfold cutoffTwoDoubledCubeSubsetStates at hmem
  obtain ⟨binary, _, heq⟩ := List.mem_map.mp hmem
  have hpoint := congrFun heq 0
  change binary 0 + binary 0 = 1 at hpoint
  omega

theorem cutoffTwoCubeSectorStates_nodup :
    cutoffTwoCubeSectorStates.Nodup := by
  unfold cutoffTwoCubeSectorStates
  exact List.nodup_cons.mpr
    ⟨centralLowerCubeState_not_mem_doubledCubeSubsetStates,
      cutoffTwoDoubledCubeSubsetStates_nodup⟩

/-! ## 2. Pointwise membership semantics -/

theorem mem_cutoffTwoDoubledCubeSubsetStates_iff
    (state : EdgeLabelling) :
    state ∈ cutoffTwoDoubledCubeSubsetStates ↔
      (∀ id, id ∈ centralLowerCubeFaceIds →
        state id = 0 ∨ state id = 2) ∧
      (∀ id, id ∉ centralLowerCubeFaceIds → state id = 0) := by
  constructor
  · intro hmem
    unfold cutoffTwoDoubledCubeSubsetStates at hmem
    obtain ⟨binary, hbinary, heq⟩ := List.mem_map.mp hmem
    have hsound := boundedEdgeLabellings_sound
      1 centralLowerCubeFaceIds binary hbinary
    constructor
    · intro id hid
      have hbound := hsound.1 id hid
      have hpoint := congrFun heq id
      unfold doubleEdgeLabelling at hpoint
      omega
    · intro id hid
      have hzero := hsound.2 id hid
      have hpoint := congrFun heq id
      unfold doubleEdgeLabelling at hpoint
      omega
  · rintro ⟨hcube, hoff⟩
    let binary : EdgeLabelling := fun id => state id / 2
    have hbinary : binary ∈
        boundedEdgeLabellings 1 centralLowerCubeFaceIds := by
      apply boundedEdgeLabellings_complete
      · intro id hid
        rcases hcube id hid with hzero | htwo
        · simp [binary, hzero]
        · simp [binary, htwo]
      · intro id hid
        simp [binary, hoff id hid]
    apply List.mem_map.mpr
    refine ⟨binary, hbinary, ?_⟩
    funext id
    by_cases hid : id ∈ centralLowerCubeFaceIds
    · rcases hcube id hid with hzero | htwo
      · simp [doubleEdgeLabelling, binary, hzero]
      · simp [doubleEdgeLabelling, binary, htwo]
    · simp [doubleEdgeLabelling, binary, hoff id hid]

theorem mem_cutoffTwoCubeSectorStates_iff
    (state : EdgeLabelling) :
    state ∈ cutoffTwoCubeSectorStates ↔
      state = centralLowerCubeState ∨
        ((∀ id, id ∈ centralLowerCubeFaceIds →
          state id = 0 ∨ state id = 2) ∧
        (∀ id, id ∉ centralLowerCubeFaceIds → state id = 0)) := by
  rw [cutoffTwoCubeSectorStates, List.mem_cons,
    mem_cutoffTwoDoubledCubeSubsetStates_iff]

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration.cutoffTwoCubeSectorStates_length
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration.cutoffTwoCubeSectorStates_nodup
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration.mem_cutoffTwoCubeSectorStates_iff
