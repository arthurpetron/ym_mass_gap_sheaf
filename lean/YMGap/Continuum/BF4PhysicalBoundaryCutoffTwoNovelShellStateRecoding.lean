/-
# State-level recoding of the cutoff-two old image and novel shell

At a later representation cutoff, old/new block membership was originally
defined by membership in the image of the opaque cutoff-two component index
list.  This module removes that representation dependence.  A later index is
in the embedded old image exactly when its represented edge labelling lies in
the canonical cutoff-two vacuum-sector state list, hence exactly when it lies
in the certified 65-state cube sector.

An executable Boolean combines the direct cutoff-two label bound with the
existing cube-subset classifier.  On every later physical carrier state it is
equivalent to 65-sector membership.  The genuinely new block is therefore
the later vacuum component filtered by rejection of this state classifier.

This is a recoding theorem, not a bound on the size, mass, routes, or capacity
of the new shell.  It supplies no cofinal estimate, thermodynamic/continuum
construction, or Clay conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCarrierRecoding
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalVacuumSector
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubePositiveCarrier
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSectorRowClosure
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetClassifierLanguage
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCubeSubsetEnumeration
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLinearRealization
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphCutoffCoherence
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram

/-! ## 1. Embedded index images are exactly old state supports -/

theorem mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
    {w : Q'} {hw : (0 : Q') ≤ w}
    {base later half index : Nat}
    (hcutoff : base ≤ later)
    (hindexLt : index < centralPhysicalFiniteCarrierSize w hw later half) :
    index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
        w hw base later half ↔
      centralPhysicalFiniteStateAt w hw later half index ∈
        centralPhysicalFiniteVacuumSectorStates w hw base half := by
  constructor
  · intro himage
    rcases List.mem_map.mp himage with
      ⟨source, hsource, hsourceMap⟩
    unfold centralPhysicalFiniteVacuumSectorStates
    apply List.mem_map.mpr
    refine ⟨source, hsource, ?_⟩
    have hsourceLt := centralPhysicalFiniteVacuumSectorIndex_lt
      w hw base half hsource
    have hstate := centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      hcutoff hsourceLt
    rw [hsourceMap] at hstate
    exact hstate.symm
  · intro hstate
    rcases List.mem_map.mp hstate with
      ⟨source, hsource, hsourceState⟩
    apply List.mem_map.mpr
    refine ⟨source, hsource, ?_⟩
    have hsourceLt := centralPhysicalFiniteVacuumSectorIndex_lt
      w hw base half hsource
    have hmappedLt := centralPhysicalFiniteCutoffIndexMap_lt
      hcutoff hsourceLt
    have hmappedState := centralPhysicalFiniteStateAt_cutoffIndexMap_eq
      hcutoff hsourceLt
    exact centralPhysicalFiniteStateAt_injective_of_lt
      hmappedLt hindexLt (hmappedState.trans hsourceState)

theorem mem_cutoffTwoEdgeLoadOldStates_iff_state_mem_cubeSector
    {later index : Nat} (hcutoff : 2 ≤ later)
    (hindex : index ∈ cutoffTwoEdgeLoadFullStates later) :
    index ∈ cutoffTwoEdgeLoadOldStates later ↔
      centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 index ∈
        cutoffTwoCubeSectorStates := by
  unfold cutoffTwoEdgeLoadOldStates
  rw [mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff hcutoff]
  rw [mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
    hcutoff
    (centralPhysicalFiniteVacuumSectorIndex_lt
      cutoffTwoHalfCoupling (by decide) later 0 hindex)]
  exact centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _

theorem mem_cutoffTwoEdgeLoadNewStates_iff_state_not_mem_cubeSector
    {later index : Nat} (hcutoff : 2 ≤ later) :
    index ∈ cutoffTwoEdgeLoadNewStates later ↔
      index ∈ cutoffTwoEdgeLoadFullStates later ∧
        centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
            (by decide) later 0 index ∉
          cutoffTwoCubeSectorStates := by
  unfold cutoffTwoEdgeLoadNewStates cutoffTwoEdgeLoadFullStates
  rw [mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff]
  constructor
  · rintro ⟨hindex, hnotImage⟩
    refine ⟨hindex, ?_⟩
    intro hcube
    exact hnotImage
      ((mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
        hcutoff
        (centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) later 0 hindex)).mpr
        ((centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mpr
          hcube))
  · rintro ⟨hindex, hnotCube⟩
    refine ⟨hindex, ?_⟩
    intro himage
    have hstate :=
      (mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
        hcutoff
        (centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) later 0 hindex)).mp himage
    exact hnotCube
      ((centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff _).mp hstate)

/-! ## 2. A direct executable state classifier -/

def cutoffTwoCubeSectorStateB (state : EdgeLabelling) : Bool :=
  labelWithinB 2 (centralLowerFaceIds 0) state &&
    decide (cutoffTwoCubeSubsetClassifierTerminal state ≠ 2)

theorem mem_centralHalfStates_two_iff_labelWithin_of_mem_later
    {later : Nat} {state : EdgeLabelling}
    (hlater : state ∈ centralHalfStates later 0) :
    state ∈ centralHalfStates 2 0 ↔
      labelWithinB 2 (centralLowerFaceIds 0) state = true := by
  have hlaterSound := boundedEdgeLabellings_sound later
    (centralLowerFaceIds 0) state (by
      simpa only [centralHalfStates] using hlater)
  constructor
  · intro htwo
    have htwoSound := boundedEdgeLabellings_sound 2
      (centralLowerFaceIds 0) state (by
        simpa only [centralHalfStates] using htwo)
    exact (labelWithinB_true_iff
      2 (centralLowerFaceIds 0) state).mpr htwoSound.1
  · intro hwithin
    unfold centralHalfStates
    apply boundedEdgeLabellings_complete
    · exact (labelWithinB_true_iff
        2 (centralLowerFaceIds 0) state).mp hwithin
    · exact hlaterSound.2

theorem cutoffTwoCubeSectorStateB_true_iff_mem
    {later : Nat} {state : EdgeLabelling}
    (hlater : state ∈ centralHalfStates later 0) :
    cutoffTwoCubeSectorStateB state = true ↔
      state ∈ cutoffTwoCubeSectorStates := by
  unfold cutoffTwoCubeSectorStateB
  rw [Bool.and_eq_true]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨hwithin, hclassifier⟩
    have htwo :=
      (mem_centralHalfStates_two_iff_labelWithin_of_mem_later hlater).mpr
        hwithin
    exact (cutoffTwoCubeSubsetState_iff_mem_sector htwo).mp hclassifier
  · intro hsector
    have htwo := cutoffTwoCubeSectorState_mem_halfStates hsector
    refine ⟨
      (mem_centralHalfStates_two_iff_labelWithin_of_mem_later hlater).mp
        htwo,
      cutoffTwoCubeSubsetState_of_mem_sector hsector⟩

/-! ## 3. The new block is the classifier-reject filter -/

private theorem filter_eq_filter_of_eq_on_local
    {A : Type} (first second : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → first item = second item) →
      items.filter first = items.filter second
  | [], _ => rfl
  | head :: tail, heq => by
      have hhead := heq head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → first item = second item :=
        fun item hitem =>
          heq item (List.mem_cons_of_mem head hitem)
      simp only [List.filter_cons, hhead]
      exact congrArg
        (fun filteredTail =>
          if second head = true then head :: filteredTail else filteredTail)
        (filter_eq_filter_of_eq_on_local first second tail htail)

private theorem embeddedB_eq_cubeSectorStateB_of_mem_full
    {later index : Nat} (hcutoff : 2 ≤ later)
    (hindex : index ∈ cutoffTwoEdgeLoadFullStates later) :
    centralPhysicalFiniteEmbeddedVacuumSectorB
        cutoffTwoHalfCoupling (by decide) 2 later 0 index =
      cutoffTwoCubeSectorStateB
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 index) := by
  let state := centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
    (by decide) later 0 index
  have hstateHalf : state ∈ centralHalfStates later 0 :=
    (mem_centralPositiveHalfStates_iff.mp
      (centralPhysicalFiniteStateAt_mem_positive
        cutoffTwoHalfCoupling (by decide) later 0
        (centralPhysicalFiniteVacuumSectorIndex_lt
          cutoffTwoHalfCoupling (by decide) later 0 hindex))).1
  have himageIff :
      index ∈ centralPhysicalFiniteEmbeddedVacuumSectorIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0 ↔
        state ∈ cutoffTwoCubeSectorStates := by
    rw [mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
      hcutoff
      (centralPhysicalFiniteVacuumSectorIndex_lt
        cutoffTwoHalfCoupling (by decide) later 0 hindex)]
    exact centralPhysicalFiniteVacuumSectorStates_cutoffTwo_iff state
  have hclassifierIff :=
    cutoffTwoCubeSectorStateB_true_iff_mem hstateHalf
  cases himageDecision :
      centralPhysicalFiniteEmbeddedVacuumSectorB
        cutoffTwoHalfCoupling (by decide) 2 later 0 index with
  | false =>
      cases hclassifier : cutoffTwoCubeSectorStateB state with
      | false => rfl
      | true =>
          have hcube := hclassifierIff.mp hclassifier
          have himage := himageIff.mpr hcube
          unfold centralPhysicalFiniteEmbeddedVacuumSectorB at himageDecision
          rw [decide_eq_true himage] at himageDecision
          cases himageDecision
  | true =>
      cases hclassifier : cutoffTwoCubeSectorStateB state with
      | true => rfl
      | false =>
          have himage : index ∈
              centralPhysicalFiniteEmbeddedVacuumSectorIndices
                cutoffTwoHalfCoupling (by decide) 2 later 0 := by
            unfold centralPhysicalFiniteEmbeddedVacuumSectorB at himageDecision
            exact of_decide_eq_true himageDecision
          have hcube := himageIff.mp himage
          have htrue := hclassifierIff.mpr hcube
          rw [hclassifier] at htrue
          cases htrue

theorem cutoffTwoEdgeLoadNewStates_eq_classifierRejectFilter
    {later : Nat} (hcutoff : 2 ≤ later) :
    cutoffTwoEdgeLoadNewStates later =
      (cutoffTwoEdgeLoadFullStates later).filter
        (fun index =>
          !(cutoffTwoCubeSectorStateB
            (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
              (by decide) later 0 index))) := by
  unfold cutoffTwoEdgeLoadNewStates
    centralPhysicalFiniteVacuumSectorNewBlockIndices
    cutoffTwoEdgeLoadFullStates
  apply filter_eq_filter_of_eq_on_local
  intro index hindex
  exact congrArg Bool.not
    (embeddedB_eq_cubeSectorStateB_of_mem_full hcutoff hindex)

theorem mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject
    {later index : Nat} (hcutoff : 2 ≤ later) :
    index ∈ cutoffTwoEdgeLoadNewStates later ↔
      index ∈ cutoffTwoEdgeLoadFullStates later ∧
        cutoffTwoCubeSectorStateB
          (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
            (by decide) later 0 index) = false := by
  rw [cutoffTwoEdgeLoadNewStates_eq_classifierRejectFilter hcutoff,
    List.mem_filter]
  cases hclassifier :
      cutoffTwoCubeSectorStateB
        (centralPhysicalFiniteStateAt cutoffTwoHalfCoupling
          (by decide) later 0 index) <;>
    simp

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.mem_centralPhysicalFiniteEmbeddedVacuumSectorIndices_iff_state_mem
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.mem_cutoffTwoEdgeLoadOldStates_iff_state_mem_cubeSector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.mem_cutoffTwoEdgeLoadNewStates_iff_state_not_mem_cubeSector
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.cutoffTwoCubeSectorStateB_true_iff_mem
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.cutoffTwoEdgeLoadNewStates_eq_classifierRejectFilter
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelShellStateRecoding.mem_cutoffTwoEdgeLoadNewStates_iff_classifier_reject
