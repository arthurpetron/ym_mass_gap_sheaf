/-
# Recover complete source data from the no-overcount raw assignment

The complete first-stretched source compiler is injective for two independent
reasons.  On the twelve cube links, its presented auxiliaries are the decoded
certified classifier input; membership in the enumerated first-stretched list
identifies that input with an actual source-classifier preimage.  Off the cube,
its auxiliaries are exactly the Cartesian production assignment, and the
standard assignment-from-lookups theorem reconstructs that whole list.

Thus equality of the raw complete assignment recovers both factors of the
nonredundant Cartesian source.  Mapping the explicit full-source family to
physical/raw source pairs therefore preserves duplicate-freeness.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
import YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceAssignmentPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFirstStretched
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAssignment
open YMGap.Continuum.CompactDualSlabFaceStrandComponentReconstruction
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Raw equality is pointwise presented-auxiliary equality -/

private theorem listMap_functions_eq_on_mem
    {A B : Type} (items : List A) (left right : A -> B)
    (hmap : items.map left = items.map right) :
    forall item, item ∈ items -> left item = right item := by
  induction items with
  | nil =>
      intro item hitem
      exact False.elim (List.not_mem_nil hitem)
  | cons head tail ih =>
      simp only [List.map_cons] at hmap
      have hhead : left head = right head := by
        injection hmap
      have htail : tail.map left = tail.map right := by
        injection hmap
      intro item hitem
      rcases List.mem_cons.mp hitem with heq | htailMem
      · exact heq ▸ hhead
      · exact ih htail item htailMem

/-- Equality after forgetting presentation implies equality of the auxiliary
payload at every attached displayed link. -/
theorem presentedSlabFusionWitnessAssignmentRaw_auxiliary_eq_of_eq
    {K extent : Nat} {physical : EdgeLabelling} {links : List SlabLink}
    (left right : PresentedSlabFusionWitnessAssignment
      K extent physical links)
    (hraw : presentedSlabFusionWitnessAssignmentRaw links left =
      presentedSlabFusionWitnessAssignmentRaw links right)
    (linked : {link // link ∈ links}) :
    (left linked).auxiliary = (right linked).auxiliary := by
  unfold presentedSlabFusionWitnessAssignmentRaw at hraw
  have hentry := listMap_functions_eq_on_mem links.attach
    (fun item => (item.1, (left item).auxiliary))
    (fun item => (item.1, (right item).auxiliary))
    hraw linked (List.mem_attach links linked)
  exact congrArg Prod.snd hentry

/-! ## 2. Exact cube and complement lookup for one full source -/

theorem CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : CubeProductionIncidenceMember) :
    source.toPresented (cubeProductionIncidenceSlabLink linked) =
      cubeInwardMatePresentedSourceAssignmentOfCertified
        K physical hK hbounded source.1.certified linked := by
  exact
    completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_cube
      K physical hK hbounded source.1.certified
        source.2.1 source.2.2 linked

theorem CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_not_cube
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1})
    (hnot : linked.1 ∉ coarseCubeBoundaryLinks) :
    (source.toPresented linked).auxiliary =
      slabFusionWitnessAssignmentAt linked.1 source.2.1 := by
  exact
    completePresentedSlabSourceOfCertifiedCubeAndOffAssignment_at_not_cube
      K physical hK hbounded source.1.certified
        source.2.1 source.2.2 linked hnot

/-! ## 3. Recover both factors from one raw complete assignment -/

/-- **No-overcount source injectivity.**  On the explicit finite family,
equality of raw complete slab assignments forces equality of both the
certified first-stretched cube source and the off-cube production assignment. -/
theorem CubeInwardMateCertifiedFirstStretchedFullSource.toRaw_injOn
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    forall (left : CubeInwardMateCertifiedFirstStretchedFullSource
        K physical hK hbounded),
      left ∈ cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded ->
      forall (right : CubeInwardMateCertifiedFirstStretchedFullSource
        K physical hK hbounded),
      right ∈ cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded ->
      left.toRaw = right.toRaw -> left = right := by
  intro left hleft right hright hraw
  have hleftParts :=
    (mem_cubeInwardMateCertifiedFirstStretchedFullSources_iff
      K physical hK hbounded left).mp hleft
  have hrightParts :=
    (mem_cubeInwardMateCertifiedFirstStretchedFullSources_iff
      K physical hK hbounded right).mp hright
  have hleftOutcome : Sum.inr left.1 ∈
      cubeInwardMateCertifiedSourceOutcomes K physical hK hbounded :=
    (mem_sumInrValues_iff
      (cubeInwardMateCertifiedSourceOutcomes
        K physical hK hbounded)).mp hleftParts.1
  have hrightOutcome : Sum.inr right.1 ∈
      cubeInwardMateCertifiedSourceOutcomes K physical hK hbounded :=
    (mem_sumInrValues_iff
      (cubeInwardMateCertifiedSourceOutcomes
        K physical hK hbounded)).mp hrightParts.1
  obtain ⟨leftCubeSource, _, hleftClassified⟩ :=
    List.mem_map.mp hleftOutcome
  obtain ⟨rightCubeSource, _, hrightClassified⟩ :=
    List.mem_map.mp hrightOutcome
  have hleftForget :
      forgetCubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded left.1.certified =
        cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded leftCubeSource := by
    calc
      forgetCubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded left.1.certified =
        unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded (Sum.inr left.1) := rfl
      _ = unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded
          (cubeInwardMateCertifiedSourceTargetOrFirstStretched
            K physical hK hbounded leftCubeSource) :=
        congrArg
          (unsplitCubeInwardMateCertifiedSource
            K physical hK hbounded) hleftClassified.symm
      _ = cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded leftCubeSource :=
        unsplit_certifiedSourceTargetOrFirstStretched
          K physical hK hbounded leftCubeSource
  have hrightForget :
      forgetCubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded right.1.certified =
        cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded rightCubeSource := by
    calc
      forgetCubeInwardMateCertifiedClassifiedAssignment
          K physical hK hbounded right.1.certified =
        unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded (Sum.inr right.1) := rfl
      _ = unsplitCubeInwardMateCertifiedSource
          K physical hK hbounded
          (cubeInwardMateCertifiedSourceTargetOrFirstStretched
            K physical hK hbounded rightCubeSource) :=
        congrArg
          (unsplitCubeInwardMateCertifiedSource
            K physical hK hbounded) hrightClassified.symm
      _ = cubeInwardMateSourceAssignmentPartition
          K physical hK hbounded rightCubeSource :=
        unsplit_certifiedSourceTargetOrFirstStretched
          K physical hK hbounded rightCubeSource
  have hrawPresented :
      presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1) left.toPresented =
        presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1) right.toPresented := by
    exact hraw
  have hcubeSource : leftCubeSource = rightCubeSource := by
    funext linked
    apply Subtype.ext
    have hcompleteAux :=
      presentedSlabFusionWitnessAssignmentRaw_auxiliary_eq_of_eq
        left.toPresented right.toPresented hrawPresented
        (cubeProductionIncidenceSlabLink linked)
    have hleftAux :
        (cubeInwardMatePresentedSourceAssignmentOfCertified
          K physical hK hbounded left.1.certified linked).auxiliary =
          (leftCubeSource linked).1 := by
      change recoverCubeInwardMateSourceAssignmentPartitionAt
          K physical hK hbounded
          (forgetCubeInwardMateCertifiedClassifiedAssignment
            K physical hK hbounded left.1.certified) linked = _
      rw [hleftForget]
      exact recoverCubeInwardMateSourceAssignmentPartitionAt_apply
        K physical hK hbounded leftCubeSource linked
    have hrightAux :
        (cubeInwardMatePresentedSourceAssignmentOfCertified
          K physical hK hbounded right.1.certified linked).auxiliary =
          (rightCubeSource linked).1 := by
      change recoverCubeInwardMateSourceAssignmentPartitionAt
          K physical hK hbounded
          (forgetCubeInwardMateCertifiedClassifiedAssignment
            K physical hK hbounded right.1.certified) linked = _
      rw [hrightForget]
      exact recoverCubeInwardMateSourceAssignmentPartitionAt_apply
        K physical hK hbounded rightCubeSource linked
    calc
      (leftCubeSource linked).1 =
          (cubeInwardMatePresentedSourceAssignmentOfCertified
            K physical hK hbounded left.1.certified linked).auxiliary :=
        hleftAux.symm
      _ = (left.toPresented
          (cubeProductionIncidenceSlabLink linked)).auxiliary :=
        congrArg
          (fun presented : PresentedSlabLinkFusionWitness
              K 1 physical linked.1.link => presented.auxiliary)
          (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
            left linked).symm
      _ = (right.toPresented
          (cubeProductionIncidenceSlabLink linked)).auxiliary :=
        hcompleteAux
      _ = (cubeInwardMatePresentedSourceAssignmentOfCertified
            K physical hK hbounded right.1.certified linked).auxiliary :=
        congrArg
          (fun presented : PresentedSlabLinkFusionWitness
              K 1 physical linked.1.link => presented.auxiliary)
          (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
            right linked)
      _ = (rightCubeSource linked).1 := hrightAux
  have hstretched : left.1 = right.1 := by
    apply Sum.inr.inj
    calc
      Sum.inr left.1 =
          cubeInwardMateCertifiedSourceTargetOrFirstStretched
            K physical hK hbounded leftCubeSource :=
        hleftClassified.symm
      _ = cubeInwardMateCertifiedSourceTargetOrFirstStretched
            K physical hK hbounded rightCubeSource :=
        congrArg
          (cubeInwardMateCertifiedSourceTargetOrFirstStretched
            K physical hK hbounded) hcubeSource
      _ = Sum.inr right.1 := hrightClassified
  have hoffLookup : forall link,
      link ∈ cubeInwardMateOffCubeSlabLinks ->
      slabFusionWitnessAssignmentAt link left.2.1 =
        slabFusionWitnessAssignmentAt link right.2.1 := by
    intro link hlink
    let linked : {link // link ∈ cubeInwardMateOffCubeSlabLinks} :=
      ⟨link, hlink⟩
    let complete := cubeInwardMateOffCubeSlabLinkToComplete linked
    have hnot : link ∉ coarseCubeBoundaryLinks :=
      (mem_cubeInwardMateOffCubeSlabLinks_iff link).mp hlink |>.2
    have hcompleteAux :=
      presentedSlabFusionWitnessAssignmentRaw_auxiliary_eq_of_eq
        left.toPresented right.toPresented hrawPresented complete
    calc
      slabFusionWitnessAssignmentAt link left.2.1 =
          (left.toPresented complete).auxiliary :=
        (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_not_cube
          left complete hnot).symm
      _ = (right.toPresented complete).auxiliary := hcompleteAux
      _ = slabFusionWitnessAssignmentAt link right.2.1 :=
        CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_not_cube
          right complete hnot
  have hoffAssignment : left.2.1 = right.2.1 := by
    calc
      left.2.1 = slabFusionWitnessAssignmentFrom
          cubeInwardMateOffCubeSlabLinks
          (fun link => slabFusionWitnessAssignmentAt link left.2.1) :=
        (slabFusionWitnessAssignmentFrom_at_eq
          K 1 physical cubeInwardMateOffCubeSlabLinks left.2.1
          ((boundaryCompleteSlabLinks_nodup 1).filter _)
          left.2.2).symm
      _ = slabFusionWitnessAssignmentFrom
          cubeInwardMateOffCubeSlabLinks
          (fun link => slabFusionWitnessAssignmentAt link right.2.1) := by
        unfold slabFusionWitnessAssignmentFrom
        apply List.map_congr_left
        intro link hlink
        exact congrArg (fun auxiliary => (link, auxiliary))
          (hoffLookup link hlink)
      _ = right.2.1 :=
        slabFusionWitnessAssignmentFrom_at_eq
          K 1 physical cubeInwardMateOffCubeSlabLinks right.2.1
          ((boundaryCompleteSlabLinks_nodup 1).filter _)
          right.2.2
  apply Prod.ext
  · exact hstretched
  · exact Subtype.ext hoffAssignment

/-! ## 4. Duplicate-free physical/raw source image -/

def cubeInwardMateCertifiedFirstStretchedRawSourcePairs
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (EdgeLabelling × SlabFusionWitnessAssignment) :=
  (cubeInwardMateCertifiedFirstStretchedFullSources
    K physical hK hbounded).map fun source =>
      (physical, source.toRaw)

theorem cubeInwardMateCertifiedFirstStretchedRawSourcePairs_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedFirstStretchedRawSourcePairs
      K physical hK hbounded).length =
      (cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded).length := by
  unfold cubeInwardMateCertifiedFirstStretchedRawSourcePairs
  rw [List.length_map]

/-- The complete physical/raw source image loses no enumerated source. -/
theorem cubeInwardMateCertifiedFirstStretchedRawSourcePairs_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (cubeInwardMateCertifiedFirstStretchedRawSourcePairs
      K physical hK hbounded).Nodup := by
  unfold cubeInwardMateCertifiedFirstStretchedRawSourcePairs
  apply CayleyPruferInjection.nodup_map_of_injOn
  · exact cubeInwardMateCertifiedFirstStretchedFullSources_nodup
      K physical hK hbounded
  · intro left hleft right hright heq
    apply CubeInwardMateCertifiedFirstStretchedFullSource.toRaw_injOn
      K physical hK hbounded left hleft right hright
    injection heq

#print axioms presentedSlabFusionWitnessAssignmentRaw_auxiliary_eq_of_eq
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_not_cube
#print axioms CubeInwardMateCertifiedFirstStretchedFullSource.toRaw_injOn
#print axioms cubeInwardMateCertifiedFirstStretchedRawSourcePairs_length
#print axioms cubeInwardMateCertifiedFirstStretchedRawSourcePairs_nodup

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity
