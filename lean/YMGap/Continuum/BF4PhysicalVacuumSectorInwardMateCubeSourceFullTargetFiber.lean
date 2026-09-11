/-
# Exact realized lowered-target fibers for complete cube sources

The preceding finite key is exact on the complete first-stretched source
family.  This module uses actual realized-key representatives, filters the
complete family into literal fibers, and compiles every fiber member into the
fixed dependent target interface required by the established weighted
contraction theorem.

The raw source list of each realized fiber stays duplicate-free.  Its total
anchor weight is therefore bounded by `(8/25)^peelSize` times the weight of
the representative's lowered presented target.  Summation across distinct
realized targets is deliberately left to the next module.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight
import YMGap.Continuum.FiniteKeyRepresentativePartition

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveFiberWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetKey
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveFiberWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteKeyRepresentativePartition
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. The raw source projection is exact and injective -/

/-- The flat inverse record's source fields are exactly the complete source
pair retained by the no-overcount enumeration. -/
theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_source_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    (entry.adaptiveInverseData.sourcePhysical,
        entry.adaptiveInverseData.sourceRaw) =
      (physical, entry.raw) := by
  apply Prod.ext
  · exact entry.adaptiveInverseData_sourcePhysical
  · exact entry.adaptiveInverseData_sourceRaw

/-- Forget an attached entry to the physical/raw pair consumed by the
fixed-fiber weight theorem. -/
def EnumeratedCubeInwardMateFullSource.rawSource
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    SlabLabelling × SlabFusionWitnessAssignment :=
  (physical, entry.raw)

/-- Raw equality recovers an attached enumerated entry, because its retained
source is a member of the exact full-source family. -/
theorem EnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (left right : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hraw : EnumeratedCubeInwardMateFullSource.rawSource left =
      EnumeratedCubeInwardMateFullSource.rawSource right) : left = right := by
  have hrawField : left.raw = right.raw := congrArg Prod.snd hraw
  have hrawToRaw : left.source.toRaw = right.source.toRaw :=
    left.raw_eq.symm.trans (hrawField.trans right.raw_eq)
  have hsource := CubeInwardMateCertifiedFirstStretchedFullSource.toRaw_injOn
    K physical hK hbounded left.source left.source_mem
      right.source right.source_mem hrawToRaw
  cases left with
  | mk leftSource leftMem leftRaw leftRawEq =>
      cases right with
      | mk rightSource rightMem rightRaw rightRawEq =>
          dsimp only at hsource hrawField
          cases hsource
          cases hrawField
          rfl

/-! ## 2. Actual representatives and their literal fibers -/

/-- One actual source representative for every realized exact target key. -/
def cubeInwardMateFullPeelTargetRepresentatives
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (EnumeratedCubeInwardMateFullSource K physical hK hbounded) :=
  keyRepresentatives
    EnumeratedCubeInwardMateFullSource.targetKey
    (enumeratedCubeInwardMateFullSources K physical hK hbounded)

/-- The literal attached-source fiber over one realized representative. -/
def cubeInwardMateFullPeelTargetFiber
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    List (EnumeratedCubeInwardMateFullSource K physical hK hbounded) :=
  representativeFiber
    (enumeratedCubeInwardMateFullSources K physical hK hbounded)
    EnumeratedCubeInwardMateFullSource.targetKey representative

/-- The raw physical/auxiliary source list underlying one realized fiber. -/
def cubeInwardMateFullPeelTargetRawSources
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    List (SlabLabelling × SlabFusionWitnessAssignment) :=
  (cubeInwardMateFullPeelTargetFiber representative).map
    EnumeratedCubeInwardMateFullSource.rawSource

/-- Filtering preserves duplicate-freeness, and the exact raw projection is
injective on every filtered complete-source fiber. -/
theorem cubeInwardMateFullPeelTargetRawSources_nodup
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    (cubeInwardMateFullPeelTargetRawSources representative).Nodup := by
  unfold cubeInwardMateFullPeelTargetRawSources
  apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
  · unfold cubeInwardMateFullPeelTargetFiber representativeFiber
    exact List.filter_sublist.nodup
      (enumeratedCubeInwardMateFullSources_nodup
        K physical hK hbounded)
  · intro left _ right _ hraw
    exact EnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
      left right hraw

/-! ## 3. Compile common-target removal and weight witnesses -/

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

/-- Equal realized keys turn one fiber member's flat inverse data into a
removal witness over the representative's concrete dependent target. -/
def enumeratedCubeInwardMateFullSourceRemovalWitness
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hkey : EnumeratedCubeInwardMateFullSource.targetKey representative =
      EnumeratedCubeInwardMateFullSource.targetKey entry) :
    PresentedAdaptiveRemovalWitness K 1
      representative.adaptiveInverseData.rootFaceId
      representative.adaptiveInverseData.peelSize
      representative.adaptiveInverseData.lowerPhysical
      representative.adaptiveInverseData.lowerAssignment
      (EnumeratedCubeInwardMateFullSource.rawSource entry) :=
  let htarget := EnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
    representative entry hkey
  { data := entry.adaptiveInverseData
    source_eq :=
      EnumeratedCubeInwardMateFullSource.adaptiveInverseData_source_eq entry
    rootFaceId_eq := htarget.1.symm
    peelSize_eq := htarget.2.1.symm
    lowerPhysical_eq := htarget.2.2.1.symm
    lowerAssignment_heq := htarget.2.2.2.symm }

/-- The same exact-key identification transports the pointwise anchor payment
to the representative's common dependent target. -/
def enumeratedCubeInwardMateFullSourceAnchorRemovalWitness
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hkey : EnumeratedCubeInwardMateFullSource.targetKey representative =
      EnumeratedCubeInwardMateFullSource.targetKey entry) :
    PresentedAdaptiveAnchorRemovalWitness K
      representative.adaptiveInverseData.rootFaceId
      representative.adaptiveInverseData.peelSize
      representative.adaptiveInverseData.lowerPhysical
      representative.adaptiveInverseData.lowerAssignment
      (EnumeratedCubeInwardMateFullSource.rawSource entry) where
  removal := enumeratedCubeInwardMateFullSourceRemovalWitness
    representative entry hkey
  weight_le := by
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    have htarget := EnumeratedCubeInwardMateFullSource.target_eq_of_key_eq
      representative entry hkey
    have hweight :=
      certifiedStretchedComponentUnion_expandedFiberWeight_le
        entry.source.1 entry.source.toPresented
    change retainedFineIntertwinerPhysicalFiberWeight D physical
        (presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1)
          (completePresentedSlabSourceOfCertifiedCube
            K physical hK hbounded entry.source.1.certified
              entry.source.toPresented)) ≤
      anchorFaceCoefficient ^ entry.adaptiveInverseData.peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          entry.adaptiveInverseData.lowerPhysical
          entry.adaptiveInverseData.lowerAssignment at hweight
    rw [completePresentedSlabSourceOfCertifiedCube_on_fullSource_raw
      entry.source, ← entry.raw_eq] at hweight
    dsimp only [EnumeratedCubeInwardMateFullSource.rawSource] at hweight ⊢
    have htargetWeight := presentedTargetWeight_eq_of_target_eq D
      representative.adaptiveInverseData.lowerAssignment
      entry.adaptiveInverseData.lowerAssignment
      htarget.2.2.1 htarget.2.2.2
    exact Q'.le_trans' _ _ _ hweight
      (Q'.le_of_eqv (Q'.eqv_of_eq (by
        rw [htarget.2.1, htargetWeight])))

/-- The attached-source fiber itself is duplicate-free. -/
theorem cubeInwardMateFullPeelTargetFiber_nodup
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    (cubeInwardMateFullPeelTargetFiber representative).Nodup := by
  unfold cubeInwardMateFullPeelTargetFiber representativeFiber
  exact List.filter_sublist.nodup
    (enumeratedCubeInwardMateFullSources_nodup K physical hK hbounded)

/-- The exact adaptive code is injective on one realized key fiber, so its
cardinality is at most `10240000^peelSize`. -/
theorem cubeInwardMateFullPeelTargetFiber_length_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    (cubeInwardMateFullPeelTargetFiber representative).length ≤
      componentAdaptiveEntropyBase ^
        representative.adaptiveInverseData.peelSize := by
  let sources := cubeInwardMateFullPeelTargetFiber representative
  let encode : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded -> ComponentAdaptiveEntropyCode :=
    fun entry => entry.adaptiveInverseData.code
  have hencodedNodup : (sources.map encode).Nodup := by
    apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
    · exact cubeInwardMateFullPeelTargetFiber_nodup representative
    · intro left hleft right hright hcode
      have hleftKey :
          EnumeratedCubeInwardMateFullSource.targetKey representative =
            EnumeratedCubeInwardMateFullSource.targetKey left :=
        of_decide_eq_true (List.mem_filter.mp hleft).2
      have hrightKey :
          EnumeratedCubeInwardMateFullSource.targetKey representative =
            EnumeratedCubeInwardMateFullSource.targetKey right :=
        of_decide_eq_true (List.mem_filter.mp hright).2
      have hraw := PresentedAdaptiveRemovalWitness.source_eq_of_code_eq
        (enumeratedCubeInwardMateFullSourceRemovalWitness
          representative left hleftKey)
        (enumeratedCubeInwardMateFullSourceRemovalWitness
          representative right hrightKey) hcode
      exact EnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
        left right hraw
  have hsubset : forall code, code ∈ sources.map encode ->
      code ∈ componentAdaptiveEntropyCarrier 1
        representative.adaptiveInverseData.rootFaceId
        representative.adaptiveInverseData.peelSize := by
    intro code hcode
    obtain ⟨entry, hentry, rfl⟩ := List.mem_map.mp hcode
    have hkey :
        EnumeratedCubeInwardMateFullSource.targetKey representative =
          EnumeratedCubeInwardMateFullSource.targetKey entry :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact (enumeratedCubeInwardMateFullSourceRemovalWitness
      representative entry hkey).code_mem_carrier
  have hbound := nodup_subset_length_le
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

/-- **Realized fixed-fiber contraction.**  Every exact representative fiber
is now a concrete input to the established `(8/25)^peelSize` counting and
pointwise-payment compiler. -/
theorem cubeInwardMateFullPeelTargetFiber_weight_sum_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    let D : SlabPhysicalData :=
      { coupling := anchorCoupling
        coupling_nonnegative := by decide
        cutoff := K
        half := 0 }
    listQSum
        (fun entry => retainedFineIntertwinerPhysicalFiberWeight
          D physical entry.raw)
        (cubeInwardMateFullPeelTargetFiber representative) ≤
      componentAdaptiveEntropyAnchorRatio ^
          representative.adaptiveInverseData.peelSize *
        presentedSlabFusionWitnessAssignmentFiberWeight D
          representative.adaptiveInverseData.lowerPhysical
          representative.adaptiveInverseData.lowerAssignment := by
  dsimp only
  unfold componentAdaptiveEntropyAnchorRatio
  apply fixedCardinalityWeightedSum_le
  · exact cubeInwardMateFullPeelTargetFiber_length_le representative
  · decide
  · unfold presentedSlabFusionWitnessAssignmentFiberWeight
    exact retainedFineIntertwinerPhysicalFiberWeight_anchor_nonnegative
      K 0 representative.adaptiveInverseData.lowerPhysical
        (presentedSlabFusionWitnessAssignmentRaw
          (boundaryCompleteSlabLinks 1)
          representative.adaptiveInverseData.lowerAssignment)
  · intro entry hentry
    have hkey : EnumeratedCubeInwardMateFullSource.targetKey representative =
        EnumeratedCubeInwardMateFullSource.targetKey entry :=
      of_decide_eq_true (List.mem_filter.mp hentry).2
    exact (enumeratedCubeInwardMateFullSourceAnchorRemovalWitness
      representative entry hkey).weight_le

#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_source_eq
#print axioms EnumeratedCubeInwardMateFullSource.rawSource
#print axioms EnumeratedCubeInwardMateFullSource.eq_of_rawSource_eq
#print axioms cubeInwardMateFullPeelTargetRepresentatives
#print axioms cubeInwardMateFullPeelTargetFiber
#print axioms cubeInwardMateFullPeelTargetRawSources
#print axioms cubeInwardMateFullPeelTargetRawSources_nodup
#print axioms enumeratedCubeInwardMateFullSourceRemovalWitness
#print axioms enumeratedCubeInwardMateFullSourceAnchorRemovalWitness
#print axioms cubeInwardMateFullPeelTargetFiber_nodup
#print axioms cubeInwardMateFullPeelTargetFiber_length_le
#print axioms cubeInwardMateFullPeelTargetFiber_weight_sum_le

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFiber
