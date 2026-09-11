/-
# Exact all-physical lowered-target fibers

The global complete first-stretched carrier ranges over every genuine bounded
physical source before normalization.  This module partitions that carrier by
its exact lowered presented target.  Equal serialized target keys now suffice
even when the source physical fields differ: bounded support makes both
lowered physical fields vanish off the slab, while the global key theorem
recovers the dependent target on the slab.

Consequently every realized global target fiber has an explicit adaptive
inverse, is duplicate-free after forgetting to raw physical/source pairs, and
obeys the same `(8/25)^peelSize` weighted contraction as a fixed-physical
fiber.  No global target-congestion, total-mass identity, conditional
minorization, posterior, operator, or continuum claim is made here.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalFullSource
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Realized representatives and literal global fibers -/

/-- One actual global source representative for every realized exact lowered
target key. -/
def globalCubeInwardMateFullPeelTargetRepresentatives
    (K : Nat) (hK : 1 ≤ K) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  keyRepresentatives
    GlobalEnumeratedCubeInwardMateFullSource.targetKey
    (globalEnumeratedCubeInwardMateFullSources K hK)

/-- The literal all-physical source fiber over one realized lowered target. -/
def globalCubeInwardMateFullPeelTargetFiber
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    List (GlobalEnumeratedCubeInwardMateFullSource K hK) :=
  representativeFiber
    (globalEnumeratedCubeInwardMateFullSources K hK)
    GlobalEnumeratedCubeInwardMateFullSource.targetKey representative

/-- Forget a realized global fiber to the physical/raw pairs reconstructed by
the adaptive inverse. -/
def globalCubeInwardMateFullPeelTargetRawSources
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (globalCubeInwardMateFullPeelTargetFiber representative).map
    GlobalEnumeratedCubeInwardMateFullSource.rawSource

/-- The attached global target fiber remains duplicate-free. -/
theorem globalCubeInwardMateFullPeelTargetFiber_nodup
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (globalCubeInwardMateFullPeelTargetFiber representative).Nodup := by
  unfold globalCubeInwardMateFullPeelTargetFiber representativeFiber
  exact List.filter_sublist.nodup
    (globalEnumeratedCubeInwardMateFullSources_nodup K hK)

/-- Exact recovery from physical/raw pairs makes the forgotten global fiber
duplicate-free as well. -/
theorem globalCubeInwardMateFullPeelTargetRawSources_nodup
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (globalCubeInwardMateFullPeelTargetRawSources representative).Nodup := by
  unfold globalCubeInwardMateFullPeelTargetRawSources
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · exact globalCubeInwardMateFullPeelTargetFiber_nodup representative
  · intro left _ right _ hraw
    exact GlobalEnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
      left right hraw

/-! ## 2. Common-target inverse and anchor-payment witnesses -/

private theorem presentedTargetWeight_eq_of_target_eq
    (D : SlabPhysicalData)
    {leftPhysical rightPhysical : SlabLabelling}
    (left : PresentedSlabFusionWitnessAssignment D.cutoff D.extent
      leftPhysical (boundaryCompleteSlabLinks D.extent))
    (right : PresentedSlabFusionWitnessAssignment D.cutoff D.extent
      rightPhysical (boundaryCompleteSlabLinks D.extent))
    (hphysical : leftPhysical = rightPhysical)
    (hassignment : HEq left right) :
    presentedSlabFusionWitnessAssignmentFiberWeight D leftPhysical left =
      presentedSlabFusionWitnessAssignmentFiberWeight
        D rightPhysical right := by
  cases hphysical
  have hassignmentEq : left = right := eq_of_heq hassignment
  cases hassignmentEq
  rfl

/-- Equal realized global keys compile one member into an adaptive inverse
over the representative's concrete dependent lowered target. -/
def globalEnumeratedCubeInwardMateFullSourceRemovalWitness
    {K : Nat} {hK : 1 ≤ K}
    (representative entry : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hkey : representative.targetKey = entry.targetKey) :
    PresentedAdaptiveRemovalWitness K 1
      representative.adaptiveInverseData.rootFaceId
      representative.adaptiveInverseData.peelSize
      representative.adaptiveInverseData.lowerPhysical
      representative.adaptiveInverseData.lowerAssignment
      entry.rawSource :=
  let htarget :=
    GlobalEnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
      representative entry hkey
  { data := entry.adaptiveInverseData
    source_eq := entry.adaptiveInverseData_source_eq
    rootFaceId_eq := htarget.1.symm
    peelSize_eq := htarget.2.1.symm
    lowerPhysical_eq := htarget.2.2.1.symm
    lowerAssignment_heq := htarget.2.2.2.symm }

/-- The pointwise SU(2) anchor payment transports across a global exact target
fiber, including fibers containing distinct source physical fields. -/
def globalEnumeratedCubeInwardMateFullSourceAnchorRemovalWitness
    {K : Nat} {hK : 1 ≤ K}
    (representative entry : GlobalEnumeratedCubeInwardMateFullSource K hK)
    (hkey : representative.targetKey = entry.targetKey) :
    PresentedAdaptiveAnchorRemovalWitness K
      representative.adaptiveInverseData.rootFaceId
      representative.adaptiveInverseData.peelSize
      representative.adaptiveInverseData.lowerPhysical
      representative.adaptiveInverseData.lowerAssignment
      entry.rawSource where
  removal := globalEnumeratedCubeInwardMateFullSourceRemovalWitness
    representative entry hkey
  weight_le := by
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    have htarget :=
      GlobalEnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
        representative entry hkey
    have hweight :=
      certifiedStretchedComponentUnion_expandedFiberWeight_le
        entry.entry.source.1 entry.entry.source.toPresented
    change retainedFineIntertwinerPhysicalFiberWeight D entry.physical
        (presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1)
          (completePresentedSlabSourceOfCertifiedCube
            K entry.physical hK
              (cubeInwardMatePhysicalBoundedOfMem
                K entry.physical entry.physicalSource.2)
              entry.entry.source.1.certified
              entry.entry.source.toPresented)) ≤
      anchorFaceCoefficient ^ entry.adaptiveInverseData.peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          entry.adaptiveInverseData.lowerPhysical
          entry.adaptiveInverseData.lowerAssignment at hweight
    dsimp only [GlobalEnumeratedCubeInwardMateFullSource.physical] at hweight
    rw [completePresentedSlabSourceOfCertifiedCube_on_fullSource_raw
      entry.entry.source, ← entry.entry.raw_eq] at hweight
    dsimp only [GlobalEnumeratedCubeInwardMateFullSource.rawSource,
      GlobalEnumeratedCubeInwardMateFullSource.physical] at hweight ⊢
    have htargetWeight := presentedTargetWeight_eq_of_target_eq D
      representative.adaptiveInverseData.lowerAssignment
      entry.adaptiveInverseData.lowerAssignment
      htarget.2.2.1 htarget.2.2.2
    exact Q'.le_trans' _ _ _ hweight
      (Q'.le_of_eqv (Q'.eqv_of_eq (by
        rw [htarget.2.1, htargetWeight])))

/-! ## 3. Global fixed-target cardinality and weight contraction -/

/-- The all-physical adaptive inverse remains injective on one realized target
fiber, so its cardinality is bounded by the usual entropy carrier. -/
theorem globalCubeInwardMateFullPeelTargetFiber_length_le
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    (globalCubeInwardMateFullPeelTargetFiber representative).length ≤
      componentAdaptiveEntropyBase ^
        representative.adaptiveInverseData.peelSize := by
  let sources := globalCubeInwardMateFullPeelTargetFiber representative
  let encode : GlobalEnumeratedCubeInwardMateFullSource K hK ->
      ComponentAdaptiveEntropyCode :=
    fun entry => entry.adaptiveInverseData.code
  have hencodedNodup : (sources.map encode).Nodup := by
    apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    · exact globalCubeInwardMateFullPeelTargetFiber_nodup representative
    · intro left hleft right hright hcode
      have hleftKey : representative.targetKey = left.targetKey :=
        of_decide_eq_true (List.mem_filter.mp hleft).2
      have hrightKey : representative.targetKey = right.targetKey :=
        of_decide_eq_true (List.mem_filter.mp hright).2
      have hraw := PresentedAdaptiveRemovalWitness.source_eq_of_code_eq
        (globalEnumeratedCubeInwardMateFullSourceRemovalWitness
          representative left hleftKey)
        (globalEnumeratedCubeInwardMateFullSourceRemovalWitness
          representative right hrightKey) hcode
      exact GlobalEnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
        left right hraw
  have hsubset : forall code, code ∈ sources.map encode ->
      code ∈ componentAdaptiveEntropyCarrier 1
        representative.adaptiveInverseData.rootFaceId
        representative.adaptiveInverseData.peelSize := by
    intro code hcode
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcode
    have hkey : representative.targetKey = entry.targetKey :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact (globalEnumeratedCubeInwardMateFullSourceRemovalWitness
      representative entry hkey).code_mem_carrier
  have hbound := YMGap.Continuum.CayleyPruferInjection.nodup_subset_length_le
    (sources.map encode)
    (componentAdaptiveEntropyCarrier 1
      representative.adaptiveInverseData.rootFaceId
      representative.adaptiveInverseData.peelSize)
    hencodedNodup hsubset
  calc
    sources.length = (sources.map encode).length := (List.length_map _).symm
    _ ≤ (componentAdaptiveEntropyCarrier 1
        representative.adaptiveInverseData.rootFaceId
        representative.adaptiveInverseData.peelSize).length := hbound
    _ ≤ componentAdaptiveEntropyBase ^
        representative.adaptiveInverseData.peelSize :=
      componentAdaptiveEntropyCarrier_length_le 1
        representative.adaptiveInverseData.rootFaceId
        representative.adaptiveInverseData.peelSize

/-- **Global realized fixed-fiber contraction.**  Every exact lowered-target
fiber across all bounded source physical fields pays at most
`(8/25)^peelSize` times the representative target weight. -/
theorem globalCubeInwardMateFullPeelTargetFiber_weight_sum_le
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalEnumeratedCubeInwardMateFullSource K hK) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    listQSum GlobalEnumeratedCubeInwardMateFullSource.weight
        (globalCubeInwardMateFullPeelTargetFiber representative) ≤
      componentAdaptiveEntropyAnchorRatio ^
          representative.adaptiveInverseData.peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          representative.adaptiveInverseData.lowerPhysical
          representative.adaptiveInverseData.lowerAssignment := by
  dsimp only
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact globalCubeInwardMateFullPeelTargetFiber_length_le representative
  · decide
  · unfold presentedSlabFusionWitnessAssignmentFiberWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      K 0 representative.adaptiveInverseData.lowerPhysical
        (presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1)
          representative.adaptiveInverseData.lowerAssignment)
  · intro entry hentry
    have hkey : representative.targetKey = entry.targetKey :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact (globalEnumeratedCubeInwardMateFullSourceAnchorRemovalWitness
      representative entry hkey).weight_le

#print axioms globalCubeInwardMateFullPeelTargetRepresentatives
#print axioms globalCubeInwardMateFullPeelTargetRawSources_nodup
#print axioms globalEnumeratedCubeInwardMateFullSourceRemovalWitness
#print axioms globalEnumeratedCubeInwardMateFullSourceAnchorRemovalWitness
#print axioms globalCubeInwardMateFullPeelTargetFiber_length_le
#print axioms globalCubeInwardMateFullPeelTargetFiber_weight_sum_le

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetFiber
