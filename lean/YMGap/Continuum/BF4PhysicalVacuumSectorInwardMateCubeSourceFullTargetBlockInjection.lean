/-
# Fixed physical-target/root/size injection

Realized lowered targets are partitioned by their physical spin field,
literal cube root, and peel size.  Inside one such block, the finite presented
order and auxiliary words complete the exact target key.  Distinct realized
representatives therefore have distinct residual word codes.

For a fixed physical target, every residual code lies in a flat Cartesian
product of the accepted local auxiliary-word rows, paired with the one common
order word.  This flat carrier has exactly the same cardinality as the genuine
heterogeneous SU(2) target tuple carrier.  Hence every fixed
target/root/size block has cardinality at most the physical production
multiplicity appearing in the BF4 term.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrder
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetOrderWords
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
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

/-! ## 1. Literal fixed target/root/size blocks -/

/-- Select exactly those realized representatives with the displayed root,
peel size, and finite physical target word. -/
def cubeInwardMateFullPeelTargetBlockRepresentatives
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    List (EnumeratedCubeInwardMateFullSource K physical hK hbounded) :=
  (cubeInwardMateFullPeelTargetRepresentatives
      K physical hK hbounded).filter fun representative =>
    decide
      (representative.adaptiveInverseData.rootFaceId = rootFaceId ∧
       representative.adaptiveInverseData.peelSize = peelSize ∧
       finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          representative.adaptiveInverseData.lowerPhysical =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target)

/-- Membership exposes the three literal block coordinates. -/
theorem cubeInwardMateFullPeelTargetBlockRepresentatives_spec
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hrepresentative : representative ∈
      cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize) :
    representative.adaptiveInverseData.rootFaceId = rootFaceId ∧
      representative.adaptiveInverseData.peelSize = peelSize ∧
      finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
          representative.adaptiveInverseData.lowerPhysical =
        finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target := by
  exact of_decide_eq_true (List.mem_filter.mp hrepresentative).2

/-- A representative in the block has literally the selected physical
target, not merely the same finite word. -/
theorem cubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hrepresentative : representative ∈
      cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize) :
    representative.adaptiveInverseData.lowerPhysical = target := by
  apply edgeLabelling_eq_of_word_eq_of_supported
    (slabPhysicalFaceEdges 1)
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      representative.adaptiveInverseData.lowerPhysical
      (EnumeratedCubeInwardMateFullSource.lowerPhysical_mem
        representative hphysical)).2
  · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
      target htarget).2
  · exact
      (cubeInwardMateFullPeelTargetBlockRepresentatives_spec
        representative hrepresentative).2.2

/-! ## 2. A flat Cartesian residual-code carrier -/

/-- Accepted auxiliary words at one fixed-order target link. -/
def cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
    (K : Nat) (target : EdgeLabelling)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    List (List Nat) :=
  (cubeInwardMateFixedOrderTargetWitnesses K target linked).map fun witness =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1).length)
      witness.val

/-- Flat Cartesian enumeration of one value from every row. -/
def finiteRowAssignments {A B : Type} (rows : A → List B) :
    List A → List (List B)
  | [] => [[]]
  | head :: tail =>
      (rows head).flatMap fun value =>
        (finiteRowAssignments rows tail).map fun rest => value :: rest

private theorem flatMap_cons_words_length {B : Type}
    (heads : List B) (tails : List (List B)) :
    (heads.flatMap fun head => tails.map fun tail => head :: tail).length =
      heads.length * tails.length := by
  induction heads with
  | nil => simp
  | cons head rest ih =>
      simp only [List.flatMap_cons, List.length_append,
        List.length_map, List.length_cons]
      rw [ih, Nat.succ_mul, Nat.add_comm]

/-- The flat enumeration has the expected product cardinality. -/
theorem finiteRowAssignments_length {A B : Type} (rows : A → List B) :
    ∀ items : List A,
      (finiteRowAssignments rows items).length =
        natListProduct (fun item => (rows item).length) items
  | [] => rfl
  | head :: tail => by
      unfold finiteRowAssignments natListProduct
      rw [flatMap_cons_words_length,
        finiteRowAssignments_length rows tail]

/-- Pointwise row membership places the written choice word in the flat
Cartesian enumeration. -/
theorem finiteRowAssignments_choice_mem {A B : Type}
    (rows : A → List B) : ∀ (items : List A) (choice : A → B),
    (∀ item, choice item ∈ rows item) →
      items.map choice ∈ finiteRowAssignments rows items
  | [], _, _ => List.mem_cons_self
  | head :: tail, choice, hchoice => by
      unfold finiteRowAssignments
      apply List.mem_flatMap.mpr
      refine ⟨choice head, hchoice head, ?_⟩
      apply List.mem_map.mpr
      exact ⟨tail.map choice,
        finiteRowAssignments_choice_mem rows tail choice hchoice, rfl⟩

/-- Auxiliary-word Cartesian carrier for one physical target. -/
def cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
    (K : Nat) (target : EdgeLabelling) : List (List (List Nat)) :=
  finiteRowAssignments
    (cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target)
    (boundaryCompleteSlabLinks 1).attach

/-- Pair every auxiliary assignment with the one common order word. -/
def cubeInwardMateFixedOrderTargetResidualCodes
    (K : Nat) (target : EdgeLabelling) :
    List (List (List Nat) × List (List Nat)) :=
  (cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments K target).map
    (fun auxiliaryWords =>
      (cubeInwardMateFixedOrderTargetOrderWords, auxiliaryWords))

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

/-- Inside a fixed target/root/size block, residual-code equality recovers
the entire exact target key and hence the realized representative. -/
theorem cubeInwardMateFullPeelTargetBlock_residualCode_injective
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (left : EnumeratedCubeInwardMateFullSource K physical hK hbounded)
    (hleft : left ∈ cubeInwardMateFullPeelTargetBlockRepresentatives
      K physical hK hbounded target rootFaceId peelSize)
    (right : EnumeratedCubeInwardMateFullSource K physical hK hbounded)
    (hright : right ∈ cubeInwardMateFullPeelTargetBlockRepresentatives
      K physical hK hbounded target rootFaceId peelSize)
    (hcode : cubeInwardMateFullPeelRepresentativeResidualCode left =
      cubeInwardMateFullPeelRepresentativeResidualCode right) :
    left = right := by
  have hleftSpec :=
    cubeInwardMateFullPeelTargetBlockRepresentatives_spec left hleft
  have hrightSpec :=
    cubeInwardMateFullPeelTargetBlockRepresentatives_spec right hright
  have horderCode :
      presentedSlabFusionWitnessAssignmentOrderWords
          (boundaryCompleteSlabLinks 1)
          left.adaptiveInverseData.lowerAssignment =
        presentedSlabFusionWitnessAssignmentOrderWords
          (boundaryCompleteSlabLinks 1)
          right.adaptiveInverseData.lowerAssignment := by
    exact (enumeratedCubeInwardMateFullSource_lowerOrderWords_eq left).trans
      (cubeInwardMateFixedOrderTargetOrderWords_eq_enumerated right)
  have hauxiliaryCode :
      presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          left.adaptiveInverseData.lowerAssignment =
        presentedSlabFusionWitnessAssignmentAuxiliaryWords
          (boundaryCompleteSlabLinks 1)
          right.adaptiveInverseData.lowerAssignment := by
    have hprojection := congrArg
      (fun code : List (List Nat) × List (List Nat) => code.2) hcode
    simpa only [cubeInwardMateFullPeelRepresentativeResidualCode] using
      hprojection
  have hkey : EnumeratedCubeInwardMateFullSource.targetKey left =
      EnumeratedCubeInwardMateFullSource.targetKey right := by
    apply EnumeratedCubeInwardMateFullSource.targetKey_eq_of_serialized_fields_eq
    · exact hleftSpec.1.trans hrightSpec.1.symm
    · exact hleftSpec.2.1.trans hrightSpec.2.1.symm
    · exact hleftSpec.2.2.trans hrightSpec.2.2.symm
    · exact horderCode
    · exact hauxiliaryCode
  apply map_injective_on_of_map_nodup
    EnumeratedCubeInwardMateFullSource.targetKey
    (cubeInwardMateFullPeelTargetRepresentatives
      K physical hK hbounded)
    (keyRepresentatives_keys_nodup
      EnumeratedCubeInwardMateFullSource.targetKey
      (enumeratedCubeInwardMateFullSources K physical hK hbounded))
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

/-- The fixed block's residual codes are duplicate-free. -/
theorem cubeInwardMateFullPeelTargetBlock_residualCodes_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (target : EdgeLabelling) (rootFaceId peelSize : Nat) :
    ((cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize).map
      cubeInwardMateFullPeelRepresentativeResidualCode).Nodup := by
  apply nodup_map_of_injOn
  · unfold cubeInwardMateFullPeelTargetBlockRepresentatives
    apply List.filter_sublist.nodup
    apply nodup_of_map_nodup EnumeratedCubeInwardMateFullSource.targetKey
    exact keyRepresentatives_keys_nodup
      EnumeratedCubeInwardMateFullSource.targetKey
      (enumeratedCubeInwardMateFullSources K physical hK hbounded)
  · intro left hleft right hright hcode
    exact cubeInwardMateFullPeelTargetBlock_residualCode_injective
      left hleft right hright hcode

/-! ## 3. Every block code occurs in the flat target carrier -/

private theorem presentedAuxiliary_mem_fixed_target
    {K : Nat} {leftPhysical target : EdgeLabelling}
    {link : SlabLink}
    (presented : PresentedSlabLinkFusionWitness
      K 1 leftPhysical link)
    (hphysical : leftPhysical = target)
    (order : SlabLinkFaceOrder 1 link)
    (horder : presented.order = order) :
    presented.auxiliary ∈ orderedSlabLinkFusionWitnesses K target order := by
  cases hphysical
  rw [← horder]
  exact presented.auxiliary_mem

/-- Every representative code in a fixed block is an actual member of the
flat Cartesian residual-code carrier. -/
theorem cubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hrepresentative : representative ∈
      cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize) :
    cubeInwardMateFullPeelRepresentativeResidualCode representative ∈
      cubeInwardMateFixedOrderTargetResidualCodes K target := by
  let auxiliaryChoice := fun
      linked : {link // link ∈ boundaryCompleteSlabLinks 1} =>
    finiteEdgeLabellingWord
      (canonicalUsedAuxiliaryCoordinates
        (slabIncidentPlaqIds 1 linked.1).length)
      (representative.adaptiveInverseData.lowerAssignment linked).auxiliary
  have hphysicalTarget :=
    cubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
      hphysical htarget representative hrepresentative
  have hchoice : ∀ linked,
      auxiliaryChoice linked ∈
        cubeInwardMateFixedOrderTargetAuxiliaryCodeRow K target linked := by
    intro linked
    have hauxiliary := presentedAuxiliary_mem_fixed_target
      (representative.adaptiveInverseData.lowerAssignment linked)
      hphysicalTarget (cubeInwardMateCompleteSourceFaceOrder linked)
      (EnumeratedCubeInwardMateFullSource.adaptiveInverseData_lowerAssignment_order
        representative linked)
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

/-! ## 4. Exact finite SU(2) capacity -/

/-- The flat residual-code carrier has the same cardinality as the exact
heterogeneous target tuple carrier. -/
theorem cubeInwardMateFixedOrderTargetResidualCodes_length
    (K : Nat) (target : EdgeLabelling) :
    (cubeInwardMateFixedOrderTargetResidualCodes K target).length =
      (cubeInwardMateFixedOrderTargetTuples K target).length := by
  unfold cubeInwardMateFixedOrderTargetResidualCodes
    cubeInwardMateFixedOrderTargetAuxiliaryCodeAssignments
    cubeInwardMateFixedOrderTargetTuples
  rw [List.length_map, finiteRowAssignments_length,
    dependentFiniteAssignments_length]
  apply natListProduct_congr
  intro linked _hlinked
  unfold cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
  exact List.length_map _

/-- The number of realized representatives in one fixed target/root/size
block is bounded by the exact Cartesian target-fiber cardinality. -/
theorem cubeInwardMateFullPeelTargetBlock_length_le_targetTuples
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    (cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize).length ≤
      (cubeInwardMateFixedOrderTargetTuples K target).length := by
  let representatives := cubeInwardMateFullPeelTargetBlockRepresentatives
    K physical hK hbounded target rootFaceId peelSize
  let sourceCodes := representatives.map
    cubeInwardMateFullPeelRepresentativeResidualCode
  let targetCodes := cubeInwardMateFixedOrderTargetResidualCodes K target
  have hsourceNodup : sourceCodes.Nodup :=
    cubeInwardMateFullPeelTargetBlock_residualCodes_nodup
      K physical hK hbounded target rootFaceId peelSize
  have hsubset : ∀ code, code ∈ sourceCodes → code ∈ targetCodes := by
    intro code hcode
    obtain ⟨representative, hrepresentative, rfl⟩ :=
      List.mem_map.mp hcode
    exact cubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
      hphysical htarget representative hrepresentative
  have hlength := nodup_subset_length_le
    sourceCodes targetCodes hsourceNodup hsubset
  calc
    (cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize).length =
        sourceCodes.length := (List.length_map _).symm
    _ ≤ targetCodes.length := hlength
    _ = (cubeInwardMateFixedOrderTargetTuples K target).length :=
      cubeInwardMateFixedOrderTargetResidualCodes_length K target

/-- **Genuine SU(2) fixed-block capacity.**  Each fixed
physical-target/root/size block contains at most the true production
multiplicity appearing in the BF4 term. -/
theorem cubeInwardMateFullPeelTargetBlock_length_le_physicalMultiplicity
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    (cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize).length ≤
      slabExplicitLinkMultiplicityProduct K 1 target := by
  refine Nat.le_trans
    (cubeInwardMateFullPeelTargetBlock_length_le_targetTuples
      hphysical htarget) ?_
  apply Nat.le_of_eq
  apply cubeInwardMateFixedOrderTargetTuples_length
  intro faceId hface
  exact Nat.lt_succ_iff.mp ((boundedEdgeLabellings_sound K
    (slabPhysicalFaceEdges 1) target htarget).1 faceId hface)

#print axioms cubeInwardMateFullPeelTargetBlockRepresentatives
#print axioms cubeInwardMateFullPeelTargetBlockRepresentatives_spec
#print axioms cubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
#print axioms cubeInwardMateFixedOrderTargetAuxiliaryCodeRow
#print axioms finiteRowAssignments_length
#print axioms finiteRowAssignments_choice_mem
#print axioms cubeInwardMateFixedOrderTargetResidualCodes
#print axioms cubeInwardMateFullPeelTargetBlock_residualCode_injective
#print axioms cubeInwardMateFullPeelTargetBlock_residualCodes_nodup
#print axioms cubeInwardMateFullPeelTargetBlock_residualCode_mem_targetCodes
#print axioms cubeInwardMateFixedOrderTargetResidualCodes_length
#print axioms cubeInwardMateFullPeelTargetBlock_length_le_targetTuples
#print axioms cubeInwardMateFullPeelTargetBlock_length_le_physicalMultiplicity

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
