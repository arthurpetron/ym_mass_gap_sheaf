/-
# Genuine SU(2) carrier for distinct global all-target atoms

Every successful all-target presentation uses the same complete-slab face
order: root-first on the twelve cube links and production order elsewhere.
For a fixed physical target, its auxiliary words therefore lie in the exact
flat code carrier whose cardinality equals the genuine heterogeneous SU(2)
target-tuple multiplicity.

The exact-key representatives have distinct target atoms.  Within one fixed
physical target block, equality of auxiliary codes would make their raw
targets, hence their exact keys, equal.  Thus the block injects into the
genuine target carrier.

This closes target-side finite cardinality, but does not yet perform the
weighted block sum or the physical-target Fubini normalization.  No posterior,
OS form, spectral-gap, or continuum claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeIncidence
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceWitnessPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFiberCapacity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPreimageInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.CompactDualSlabOrderedLinkPhysicalStrandPairing
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4LinkAuxiliaryCoordinatePartition

/-! ## 1. Every all-target presentation has the fixed order -/

/-- The global all-target construction uses exactly the common order profile
required by the genuine target-tuple carrier. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_order
    {K : Nat} {hK : 1 ≤ K}
    (source : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        source linked).order =
      cubeInwardMateCompleteSourceFaceOrder linked := by
  cases hfind : cubeProductionIncidenceForLink? linked.1 with
  | none =>
      have hnot :=
        (cubeProductionIncidenceForLink?_eq_none_iff linked.1).mp hfind
      have htargetOrder :
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
              source linked).order =
            productionSlabLinkFaceOrder 1 linked.1 := by
        unfold GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        split
        · rename_i incidence hsome
          rw [hfind] at hsome
          contradiction
        · rfl
      exact htargetOrder.trans
        (cubeInwardMateCompleteSourceFaceOrder_at_not_cube linked hnot).symm
  | some incidence =>
      have hfindDirect : cubeProductionIncidences.find?
          (cubeProductionIncidenceHasLink linked.1) = some incidence := by
        simpa [cubeProductionIncidenceForLink?] using hfind
      let cubeLinked : CubeProductionIncidenceMember :=
        ⟨incidence, List.mem_of_find?_eq_some hfindDirect⟩
      have htest := List.find?_some hfindDirect
      have hlink : incidence.link = linked.1 :=
        of_decide_eq_true (by
          simpa [cubeProductionIncidenceHasLink] using htest)
      have hlinked : cubeProductionIncidenceSlabLink cubeLinked = linked :=
        Subtype.ext hlink
      rw [← hlinked]
      rw [cubeInwardMateCompleteSourceFaceOrder_at_cube]
      calc
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            source (cubeProductionIncidenceSlabLink cubeLinked)).order =
            (presentedMatedLinkWitnessOfCubeInwardMateTarget
              K source.physical cubeLinked (source.entry.1 cubeLinked)).order :=
          congrArg (fun item => item.order)
            (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_at_cube
              source cubeLinked)
        _ = cubeInwardMateSourceFaceOrder cubeLinked := rfl

/-! ## 2. Partition representatives by their physical target -/

/-- Distinct exact target representatives with one displayed finite physical
target word. -/
def globalInwardMateTargetPhysicalBlockRepresentatives
    (K : Nat) (hK : 1 ≤ K) (target : EdgeLabelling) :
    List (GlobalCubeInwardMateCertifiedTargetFullSource K hK) :=
  (globalInwardMateTargetRepresentatives K hK).filter fun representative =>
    decide
      (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
            representative) =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target)

theorem globalInwardMateTargetPhysicalBlockRepresentatives_spec
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hrepresentative : representative ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target) :
    finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
          representative) =
      finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target := by
  exact of_decide_eq_true (List.mem_filter.mp hrepresentative).2

/-- A representative in a bounded physical block has literally the selected
target field, not merely the same serialized word. -/
theorem globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hrepresentative : representative ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
        representative = target := by
  apply edgeLabelling_eq_of_word_eq_of_supported
    (slabPhysicalFaceEdges 1)
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
        representative)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
        representative)).2
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      target htarget).2
  · exact globalInwardMateTargetPhysicalBlockRepresentatives_spec
      representative hrepresentative

/-! ## 3. Inject each physical block into the genuine target carrier -/

/-- The common order word paired with the complete all-target auxiliary
word. -/
def globalInwardMateTargetRepresentativeResidualCode
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List (List Nat) × List (List Nat) :=
  (cubeInwardMateFixedOrderTargetOrderWords,
    presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        representative))

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

private theorem prod_eq_of_fields_eq
    {A B : Type} {leftA rightA : A} {leftB rightB : B}
    (hleft : leftA = rightA) (hright : leftB = rightB) :
    (leftA, leftB) = (rightA, rightB) := by
  cases hleft
  cases hright
  rfl

/-- Within one physical target block, the auxiliary residual code recovers
the exact target key and hence its selected representative. -/
theorem globalInwardMateTargetPhysicalBlock_residualCode_injective
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (left : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hleft : left ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target)
    (right : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hright : right ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target)
    (hcode : globalInwardMateTargetRepresentativeResidualCode left =
      globalInwardMateTargetRepresentativeResidualCode right) :
    left = right := by
  have hphysicalLeft :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget left hleft
  have hphysicalRight :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget right hright
  have hphysical :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right :=
    hphysicalLeft.trans hphysicalRight.symm
  have hauxiliaryWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented left) =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented right) := by
    have hprojection := congrArg
      (fun code : List (List Nat) × List (List Nat) => code.2) hcode
    simpa only [globalInwardMateTargetRepresentativeResidualCode] using
      hprojection
  have hraw := globalTargetRaw_eq_of_auxiliaryWords_eq
    left right hauxiliaryWords
  have hatom :
      GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom left =
        GlobalCubeInwardMateCertifiedTargetFullSource.targetAtom right := by
    calc
      _ = (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical left,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw left) :=
        globalTargetAtom_eq left
      _ = (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical right,
          GlobalCubeInwardMateCertifiedTargetFullSource.targetRaw right) :=
        prod_eq_of_fields_eq hphysical hraw
      _ = _ := (globalTargetAtom_eq right).symm
  have hkey := globalTargetKey_eq_of_targetAtom_eq left right hatom
  apply map_injective_on_of_map_nodup
    globalInwardMateTargetKey
    (globalInwardMateTargetRepresentatives K hK)
    (keyRepresentatives_keys_nodup globalInwardMateTargetKey
      (globalCubeInwardMateCertifiedTargetFullSources K hK))
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

theorem globalInwardMateTargetPhysicalBlock_residualCodes_nodup
    (K : Nat) (hK : 1 ≤ K) (target : EdgeLabelling)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    ((globalInwardMateTargetPhysicalBlockRepresentatives K hK target).map
      globalInwardMateTargetRepresentativeResidualCode).Nodup := by
  apply nodup_map_of_injOn
  · unfold globalInwardMateTargetPhysicalBlockRepresentatives
    apply List.filter_sublist.nodup
    apply nodup_of_map_nodup globalInwardMateTargetKey
    exact keyRepresentatives_keys_nodup globalInwardMateTargetKey
      (globalCubeInwardMateCertifiedTargetFullSources K hK)
  · intro left hleft right hright hcode
    exact globalInwardMateTargetPhysicalBlock_residualCode_injective
      htarget left hleft right hright hcode

private theorem presentedAuxiliary_mem_fixed_target
    {K : Nat} {leftPhysical target : EdgeLabelling} {link : SlabLink}
    (presented : PresentedSlabLinkFusionWitness K 1 leftPhysical link)
    (hphysical : leftPhysical = target)
    (order : SlabLinkFaceOrder 1 link)
    (horder : presented.order = order) :
    presented.auxiliary ∈ orderedSlabLinkFusionWitnesses K target order := by
  cases hphysical
  rw [← horder]
  exact presented.auxiliary_mem

/-- Every all-target representative code in a fixed physical block occurs in
the flat code carrier equinumerous with the genuine SU(2) target tuples. -/
theorem globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hrepresentative : representative ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target) :
    globalInwardMateTargetRepresentativeResidualCode representative ∈
      cubeInwardMateFixedOrderTargetResidualCodes K target := by
  let auxiliaryChoice := fun
      linked : {link // link ∈ boundaryCompleteSlabLinks 1} =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1).length)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        representative linked).auxiliary
  have hphysicalTarget :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget representative hrepresentative
  have hchoice : ∀ linked,
      auxiliaryChoice linked ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target linked := by
    intro linked
    have hauxiliary := presentedAuxiliary_mem_fixed_target
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        representative linked)
      hphysicalTarget (cubeInwardMateCompleteSourceFaceOrder linked)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_order
        representative linked)
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
    apply List.mem_map.mpr
    let witness : CubeInwardMateFixedOrderTargetWitness K target linked :=
      ⟨(GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
          representative linked).auxiliary, hauxiliary⟩
    exact ⟨witness,
      List.mem_attach
        (orderedSlabLinkFusionWitnesses K target
          (cubeInwardMateCompleteSourceFaceOrder linked)) witness,
      rfl⟩
  have hauxiliaryWords :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
            representative) ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments K target := by
    unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
    exact finiteRowAssignments_choice_mem
      (cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target)
      (boundaryCompleteSlabLinks 1).attach auxiliaryChoice hchoice
  unfold globalInwardMateTargetRepresentativeResidualCode
    cubeInwardMateFixedOrderTargetResidualCodes
  apply List.mem_map.mpr
  exact ⟨presentedSlabFusionWitnessAssignmentAuxiliaryWords
      (boundaryCompleteSlabLinks 1)
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented
        representative), hauxiliaryWords, rfl⟩

/-- **Genuine SU(2) physical-target capacity.**  The distinct realized
all-target atoms over one physical target fit injectively into the exact
heterogeneous target-tuple fiber. -/
theorem globalInwardMateTargetPhysicalBlock_length_le_targetTuples
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    (globalInwardMateTargetPhysicalBlockRepresentatives
        K hK target).length ≤
      (cubeInwardMateFixedOrderTargetTuples K target).length := by
  let block := globalInwardMateTargetPhysicalBlockRepresentatives K hK target
  let sourceCodes := block.map
    globalInwardMateTargetRepresentativeResidualCode
  let targetCodes := cubeInwardMateFixedOrderTargetResidualCodes K target
  have hsourceNodup : sourceCodes.Nodup :=
    globalInwardMateTargetPhysicalBlock_residualCodes_nodup
      K hK target htarget
  have hsubset : ∀ code, code ∈ sourceCodes → code ∈ targetCodes := by
    intro code hcode
    obtain ⟨representative, hrepresentative, rfl⟩ := List.mem_map.mp hcode
    exact globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
      htarget representative hrepresentative
  have hlength := nodup_subset_length_le
    sourceCodes targetCodes hsourceNodup hsubset
  calc
    (globalInwardMateTargetPhysicalBlockRepresentatives K hK target).length =
        sourceCodes.length := (List.length_map _).symm
    _ ≤ targetCodes.length := hlength
    _ = (cubeInwardMateFixedOrderTargetTuples K target).length :=
      cubeInwardMateFixedOrderTargetResidualCodes_length K target

#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetPresented_order
#print axioms globalInwardMateTargetPhysicalBlockRepresentatives
#print axioms globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
#print axioms globalInwardMateTargetRepresentativeResidualCode
#print axioms globalInwardMateTargetPhysicalBlock_residualCode_injective
#print axioms globalInwardMateTargetPhysicalBlock_residualCodes_nodup
#print axioms globalInwardMateTargetPhysicalBlock_residualCode_mem_targetCodes
#print axioms globalInwardMateTargetPhysicalBlock_length_le_targetTuples

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
