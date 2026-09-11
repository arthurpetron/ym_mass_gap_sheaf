/-
# Global fixed target/root/size residual-code injection

After the all-physical target Fubini, distinct realized targets are partitioned
by lowered physical field, cube root, and peel size.  Inside one such block,
the common order word and the auxiliary words reconstruct the entire exact
target key.  Distinct global representatives therefore have distinct residual
codes even when their original source physical fields differ.

Every residual code belongs to the established finite SU(2) target carrier.
Thus each global target/root/size block has cardinality at most the genuine
physical production multiplicity.  Summation over blocks and sizes remains
downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFubini
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Literal global target/root/size blocks -/

/-- Select exactly the global representatives with the displayed root, peel
size, and finite physical target word. -/
def globalCubeInwardMateFullPeelTargetBlockRepresentatives
    (K : Nat) (hK : 1 ≤ K)
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  (globalCubeInwardMateFullPeelTargetRepresentatives K hK).filter
    fun representative =>
      decide
        (representative.adaptiveInverseData.rootFaceId = rootFaceId ∧
         representative.adaptiveInverseData.peelSize = peelSize ∧
         finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
            representative.adaptiveInverseData.lowerPhysical =
          finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target)

/-- Membership exposes the three literal global block coordinates. -/
theorem globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hrepresentative : representative ∈
      globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize) :
    representative.adaptiveInverseData.rootFaceId = rootFaceId ∧
      representative.adaptiveInverseData.peelSize = peelSize ∧
      finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          representative.adaptiveInverseData.lowerPhysical =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target := by
  exact of_decide_eq_true (List.mem_filter.mp hrepresentative).2

/-- A global representative in the block has literally the selected bounded
physical target. -/
theorem globalCubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hrepresentative : representative ∈
      globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize) :
    representative.adaptiveInverseData.lowerPhysical = target := by
  apply edgeLabelling_eq_of_word_eq_of_supported
    (slabPhysicalFaceEdges 1)
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      representative.adaptiveInverseData.lowerPhysical
      representative.lowerPhysical_mem).2
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      target htarget).2
  · exact
      (globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec
        representative hrepresentative).2.2

/-! ## 2. Global residual-code injectivity -/

/-- The established order/auxiliary residual code of the underlying dependent
fixed-physical entry. -/
def globalCubeInwardMateFullPeelRepresentativeResidualCode
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    List (List Nat) × List (List Nat) :=
  cubeInwardMateFullPeelRepresentativeResidualCode representative.entry

private theorem map_injective_on_of_map_nodup
    {A B : Type} (map : A → B) : ∀ items : List A,
    (items.map map).Nodup →
      ∀ left, left ∈ items → ∀ right, right ∈ items →
        map left = map right → left = right
  | [], _, left, hleft, _, _, _ => absurd hleft List.not_mem_nil
  | head :: tail, hnodup, left, hleft, right, hright, heq => by
      have hparts := List.nodup_cons.mp hnodup
      rcases List.mem_cons.mp hleft with hleftHead | hleftTail
      · subst left
        rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · exact hrightHead.symm
        · exact absurd
            (heq ▸ List.mem_map.mpr ⟨right, hrightTail, rfl⟩)
            hparts.1
      · rcases List.mem_cons.mp hright with hrightHead | hrightTail
        · subst right
          exact absurd
            (heq.symm ▸ List.mem_map.mpr ⟨left, hleftTail, rfl⟩)
            hparts.1
        · exact map_injective_on_of_map_nodup map tail hparts.2
            left hleftTail right hrightTail heq

/-- Inside a fixed global target/root/size block, residual-code equality
recovers the exact global target key and hence the selected representative. -/
theorem globalCubeInwardMateFullPeelTargetBlock_residualCode_injective
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (left : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hleft : left ∈ globalCubeInwardMateFullPeelTargetBlockRepresentatives
      K hK target rootFaceId peelSize)
    (right : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hright : right ∈ globalCubeInwardMateFullPeelTargetBlockRepresentatives
      K hK target rootFaceId peelSize)
    (hcode : globalCubeInwardMateFullPeelRepresentativeResidualCode left =
      globalCubeInwardMateFullPeelRepresentativeResidualCode right) :
    left = right := by
  have hleftSpec :=
    globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec left hleft
  have hrightSpec :=
    globalCubeInwardMateFullPeelTargetBlockRepresentatives_spec right hright
  have horderCode :
      presentedSlabFusionWitnessAssignmentOrderWords
          (boundaryCompleteSlabLinks 1)
          left.adaptiveInverseData.lowerAssignment =
        presentedSlabFusionWitnessAssignmentOrderWords
          (boundaryCompleteSlabLinks 1)
          right.adaptiveInverseData.lowerAssignment := by
    exact
      (enumeratedCubeInwardMateFullSource_lowerOrderWords_eq left.entry).trans
        (cubeInwardMateFixedOrderTargetOrderWords_eq_enumerated right.entry)
  have hauxiliaryCode :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          left.adaptiveInverseData.lowerAssignment =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          right.adaptiveInverseData.lowerAssignment := by
    have hprojection := congrArg
      (fun code : List (List Nat) × List (List Nat) => code.2) hcode
    simpa only [globalCubeInwardMateFullPeelRepresentativeResidualCode,
      cubeInwardMateFullPeelRepresentativeResidualCode,
      GlobalEnumeratedCubeInwardMateFullSource.adaptiveInverseData] using
        hprojection
  have hkey : left.targetKey = right.targetKey := by
    exact PresentedAdaptiveInverseData.targetKey_eq_of_serialized_fields_eq
      left.adaptiveInverseData right.adaptiveInverseData
      (hleftSpec.1.trans hrightSpec.1.symm)
      (hleftSpec.2.1.trans hrightSpec.2.1.symm)
      (hleftSpec.2.2.trans hrightSpec.2.2.symm)
      horderCode hauxiliaryCode
  apply map_injective_on_of_map_nodup
    GlobalEnumeratedCubeInwardMateFullSource.targetKey
    (globalCubeInwardMateFullPeelTargetRepresentatives K hK)
    (keyRepresentatives_keys_nodup
      GlobalEnumeratedCubeInwardMateFullSource.targetKey
      (globalEnumeratedCubeInwardMateFullSources K hK))
  · exact (List.mem_filter.mp hleft).1
  · exact (List.mem_filter.mp hright).1
  · exact hkey

private theorem nodup_of_map_nodup
    {A B : Type} (map : A → B) : ∀ {items : List A},
    (items.map map).Nodup → items.Nodup
  | [], _ => List.nodup_nil
  | head :: tail, hnodup => by
      have hparts := List.nodup_cons.mp hnodup
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_of_map_nodup map hparts.2⟩
      intro hmem
      exact hparts.1 (List.mem_map.mpr ⟨head, hmem, rfl⟩)

/-- The global fixed block's residual codes are duplicate-free. -/
theorem globalCubeInwardMateFullPeelTargetBlock_residualCodes_nodup
    (K : Nat) (hK : 1 ≤ K)
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    ((globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize).map
      globalCubeInwardMateFullPeelRepresentativeResidualCode).Nodup := by
  apply nodup_map_of_injOn
  · unfold globalCubeInwardMateFullPeelTargetBlockRepresentatives
    apply List.filter_sublist.nodup
    apply nodup_of_map_nodup
      GlobalEnumeratedCubeInwardMateFullSource.targetKey
    exact keyRepresentatives_keys_nodup
      GlobalEnumeratedCubeInwardMateFullSource.targetKey
      (globalEnumeratedCubeInwardMateFullSources K hK)
  · intro left hleft right hright hcode
    exact globalCubeInwardMateFullPeelTargetBlock_residualCode_injective
      left hleft right hright hcode

/-! ## 3. Membership in the genuine finite SU(2) target carrier -/

private theorem presentedAuxiliary_mem_fixed_target
    {K : Nat} {leftPhysical target : EdgeLabelling}
    {link : SlabLink}
    (presented : PresentedSlabLinkFusionWitness K 1 leftPhysical link)
    (hphysical : leftPhysical = target)
    (order : SlabLinkFaceOrder 1 link)
    (horder : presented.order = order) :
    presented.auxiliary ∈ orderedSlabLinkFusionWitnesses K target order := by
  cases hphysical
  rw [← horder]
  exact presented.auxiliary_mem

/-- Every representative code in a fixed global block occurs in the same
flat Cartesian residual-code carrier as a genuine SU(2) target tuple. -/
theorem globalCubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hrepresentative : representative ∈
      globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize) :
    globalCubeInwardMateFullPeelRepresentativeResidualCode representative ∈
      cubeInwardMateFixedOrderTargetResidualCodes K target := by
  let auxiliaryChoice := fun
      linked : {link // link ∈ boundaryCompleteSlabLinks 1} =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1).length)
      (representative.adaptiveInverseData.lowerAssignment linked).auxiliary
  have hphysicalTarget :=
    globalCubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
      htarget representative hrepresentative
  have hchoice : ∀ linked,
      auxiliaryChoice linked ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target linked := by
    intro linked
    have hauxiliary := presentedAuxiliary_mem_fixed_target
      (representative.adaptiveInverseData.lowerAssignment linked)
      hphysicalTarget (cubeInwardMateCompleteSourceFaceOrder linked)
      (EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
        representative.entry linked)
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
    apply List.mem_map.mpr
    let witness : CubeInwardMateFixedOrderTargetWitness K target linked :=
      ⟨(representative.adaptiveInverseData.lowerAssignment linked).auxiliary,
        hauxiliary⟩
    exact ⟨witness,
      List.mem_attach
        (orderedSlabLinkFusionWitnesses K target
          (cubeInwardMateCompleteSourceFaceOrder linked)) witness,
      rfl⟩
  have hauxiliaryWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          representative.adaptiveInverseData.lowerAssignment ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments K target := by
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
    exact finiteRowAssignments_choice_mem
      (cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target)
      (boundaryCompleteSlabLinks 1).attach auxiliaryChoice hchoice
  unfold cubeInwardMateFixedOrderTargetResidualCodes
  apply List.mem_map.mpr
  refine ⟨presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      representative.adaptiveInverseData.lowerAssignment,
    hauxiliaryWords, ?_⟩
  rfl

/-! ## 4. Exact global finite SU(2) capacity -/

/-- The number of global realized representatives in one fixed
target/root/size block is bounded by the exact heterogeneous target-tuple
cardinality. -/
theorem globalCubeInwardMateFullPeelTargetBlock_length_le_targetTuples
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    (globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize).length ≤
      (cubeInwardMateFixedOrderTargetTuples K target).length := by
  let representatives := globalCubeInwardMateFullPeelTargetBlockRepresentatives
    K hK target rootFaceId peelSize
  let sourceCodes := representatives.map
    globalCubeInwardMateFullPeelRepresentativeResidualCode
  let targetCodes := cubeInwardMateFixedOrderTargetResidualCodes K target
  have hsourceNodup : sourceCodes.Nodup :=
    globalCubeInwardMateFullPeelTargetBlock_residualCodes_nodup
      K hK target rootFaceId peelSize
  have hsubset : ∀ code, code ∈ sourceCodes → code ∈ targetCodes := by
    intro code hcode
    obtain ⟨representative, hrepresentative, rfl⟩ :=
      List.mem_map.mp hcode
    exact
      globalCubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
        htarget representative hrepresentative
  have hlength := nodup_subset_length_le
    sourceCodes targetCodes hsourceNodup hsubset
  calc
    (globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize).length =
        sourceCodes.length := (List.length_map _).symm
    _ ≤ targetCodes.length := hlength
    _ = (cubeInwardMateFixedOrderTargetTuples K target).length :=
      cubeInwardMateFixedOrderTargetResidualCodes_length K target

/-- **Genuine global SU(2) fixed-block capacity.**  Each fixed lowered
physical-target/root/size block contains at most the production multiplicity
appearing in the BF4 target term. -/
theorem globalCubeInwardMateFullPeelTargetBlock_length_le_physicalMultiplicity
    {K : Nat} {hK : 1 ≤ K}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    (globalCubeInwardMateFullPeelTargetBlockRepresentatives
        K hK target rootFaceId peelSize).length ≤
      slabExplicitLinkMultiplicityProduct K 1 target := by
  refine Nat.le_trans
    (globalCubeInwardMateFullPeelTargetBlock_length_le_targetTuples
      htarget) ?_
  apply Nat.le_of_eq
  apply cubeInwardMateFixedOrderTargetTuples_length
  intro faceId hface
  exact Nat.lt_succ_iff.mp ((boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges 1) target htarget).1 faceId hface)

#print axioms globalCubeInwardMateFullPeelTargetBlockRepresentatives
#print axioms globalCubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
#print axioms globalCubeInwardMateFullPeelRepresentativeResidualCode
#print axioms globalCubeInwardMateFullPeelTargetBlock_residualCode_injective
#print axioms globalCubeInwardMateFullPeelTargetBlock_residualCodes_nodup
#print axioms globalCubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
#print axioms globalCubeInwardMateFullPeelTargetBlock_length_le_targetTuples
#print axioms globalCubeInwardMateFullPeelTargetBlock_length_le_physicalMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetBlockInjection
