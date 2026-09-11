/-
# Attach deterministic two-root peel data to every complete source

Every nonredundant complete first-stretched source already determines the
certified two-root component union.  This file feeds its own complete
presented assignment back into that compiler and records the resulting flat
adaptive inverse data.

The older component compiler defensively overwrites the cube entries of any
supplied background.  The new complete source is already cube-correct, so that
second overwrite is raw-idempotent.  The finite attachment retains each
upstream source itself as an injective key and exposes the already-proved flat
inverse record as a separate projection.  The source-with-peel family
consequently remains duplicate-free, and every member carries inverse data
with peel size at least two.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData

set_option autoImplicit false

open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveInverseFiber
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedAdaptiveEntropyCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPeel
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedPhysicalMultiplicityCode
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCertifiedRootPresentedWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCertifiedClassification
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceCompletePresentation
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullEnumeration
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullInjectivity
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceOffCubeCompletion
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalDebtProfile
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabPresentedFaceStrandComponentDropCode
open YMGap.Continuum.CompactDualSlabPresentedFusionGlobalFaceStrandEdges
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabCubeCoupledConditionalKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

/-! ## 1. Completing an already complete source is raw-idempotent -/

/-- Reapplying the defensive cube override to a no-overcount complete source
changes no auxiliary coordinate. -/
theorem completePresentedSlabSourceOfCertifiedCube_on_fullSource_auxiliary
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 1}) :
    (completePresentedSlabSourceOfCertifiedCube
        K physical hK hbounded source.1.certified source.toPresented
        linked).auxiliary =
      (source.toPresented linked).auxiliary := by
  cases hfind : cubeProductionIncidenceForLink? linked.1 with
  | none =>
    unfold completePresentedSlabSourceOfCertifiedCube
    split
    · rfl
    · rename_i incidence hsome
      rw [hfind] at hsome
      cases hsome
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
    let completed := completePresentedSlabSourceOfCertifiedCube
      K physical hK hbounded source.1.certified source.toPresented
    calc
      (completePresentedSlabSourceOfCertifiedCube
          K physical hK hbounded source.1.certified source.toPresented
          linked).auxiliary =
          (completed
            (cubeProductionIncidenceSlabLink cubeLinked)).auxiliary :=
        (congrArg
          (fun item => (completed item).auxiliary)
          hlinked).symm
      _ = (cubeInwardMatePresentedSourceAssignmentOfCertified
            K physical hK hbounded source.1.certified
            cubeLinked).auxiliary :=
        congrArg
          (fun presented : PresentedSlabLinkFusionWitness
            K 1 physical cubeLinked.1.link => presented.auxiliary)
          (completePresentedSlabSourceOfCertifiedCube_at_cube
            K physical hK hbounded source.1.certified
              source.toPresented cubeLinked)
      _ = (source.toPresented
            (cubeProductionIncidenceSlabLink cubeLinked)).auxiliary :=
        congrArg
          (fun presented : PresentedSlabLinkFusionWitness
            K 1 physical cubeLinked.1.link => presented.auxiliary)
          (CubeInwardMateCertifiedFirstStretchedFullSource.toPresented_at_cube
            source cubeLinked).symm
      _ = (source.toPresented linked).auxiliary :=
        congrArg (fun item => (source.toPresented item).auxiliary) hlinked

/-- The second defensive completion is literally idempotent after forgetting
presentation proof fields, which is the source interface used by the weight
and inverse compilers. -/
theorem completePresentedSlabSourceOfCertifiedCube_on_fullSource_raw
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded) :
    presentedSlabFusionWitnessAssignmentRaw
        (boundaryCompleteSlabLinks 1)
        (completePresentedSlabSourceOfCertifiedCube
          K physical hK hbounded source.1.certified source.toPresented) =
      source.toRaw := by
  unfold CubeInwardMateCertifiedFirstStretchedFullSource.toRaw
    presentedSlabFusionWitnessAssignmentRaw
  apply List.map_congr_left
  intro linked _
  exact congrArg (fun auxiliary => (linked.1, auxiliary))
    (completePresentedSlabSourceOfCertifiedCube_on_fullSource_auxiliary
      source linked)

/-! ## 2. Attach the deterministic peel without normalizing its large record -/

/-- Compile one already-complete source directly into the flat inverse
interface.  Unlike the older defensive compiler, the `sourceRaw` field is the
retained no-overcount raw source itself; reconstruction composes the generic
presented-selection theorem with the raw-idempotence theorem above. -/
def completeFullSourceAdaptiveInverseData
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (source : CubeInwardMateCertifiedFirstStretchedFullSource
      K physical hK hbounded)
    (raw : SlabFusionWitnessAssignment)
    (hraw : raw = source.toRaw) : PresentedAdaptiveInverseData K 1 where
  rootFaceId := (certifiedStretchedComponentUnionShapePhysicalData
    source.1 source.toPresented).rootFaceId
  peelSize := (certifiedStretchedComponentUnionShapePhysicalData
    source.1 source.toPresented).budget
  shapeCode := certifiedStretchedComponentUnionConnectedShapeCode
    source.1 source.toPresented
  physicalMultiplicityCode :=
    certifiedStretchedComponentUnionPhysicalMultiplicityBinaryCode
      source.1 source.toPresented
  auxiliaryRows := certifiedStretchedComponentUnionAdaptiveAuxiliaryRows
    source.1 source.toPresented
  sourcePhysical := physical
  lowerPhysical := CertifiedStretchedComponentUnionLowerPhysical
    source.1 source.toPresented
  lowerAssignment := certifiedStretchedComponentUnionLoweredAssignment
    source.1 source.toPresented
  sourceRaw := raw
  physicalDrop := slabFaceStrandSelectionCount
    (certifiedStretchedComponentUnionSupportedSelection
      source.1 source.toPresented).closed.selected
  peelCount := fun faceId =>
    (certifiedStretchedComponentUnionSupportedSelection
      source.1 source.toPresented).peelFaces.count faceId
  physicalDrop_decode :=
    certifiedStretchedComponentUnionPhysicalDropDecode
      source.1 source.toPresented
  peelCount_eq_physicalDrop :=
    (certifiedStretchedComponentUnionSupportedSelection
      source.1 source.toPresented).peelFaces_count
  code_mem_carrier :=
    certifiedStretchedComponentUnionAdaptiveEntropyCode_mem_carrier
      source.1 source.toPresented
  reconstructPhysical :=
    certifiedStretchedComponentUnion_reconstructPhysical
      source.1 source.toPresented
  reconstructRaw :=
    (presentedSelectionAdaptiveAuxiliaryRows_reconstructRaw
      (certifiedStretchedComponentUnionSupportedSelection
        source.1 source.toPresented)).trans
      ((completePresentedSlabSourceOfCertifiedCube_on_fullSource_raw
        source).trans hraw.symm)

/-- One literal member of the nonredundant full-source family.  Its adaptive
inverse data are defined as a projection below, so the finite enumeration
retains the source itself as the injective key. -/
structure EnumeratedCubeInwardMateFullSource
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Type where
  source : CubeInwardMateCertifiedFirstStretchedFullSource
    K physical hK hbounded
  source_mem : source ∈ cubeInwardMateCertifiedFirstStretchedFullSources
    K physical hK hbounded
  raw : SlabFusionWitnessAssignment
  raw_eq : raw = source.toRaw

/-- Run the already-proved deterministic two-root peel on the retained source
and its own complete presented assignment. -/
def EnumeratedCubeInwardMateFullSource.adaptiveInverseData
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) : PresentedAdaptiveInverseData K 1 :=
  completeFullSourceAdaptiveInverseData
    entry.source entry.raw entry.raw_eq

@[simp] theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_sourcePhysical
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    entry.adaptiveInverseData.sourcePhysical = physical := rfl

@[simp] theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_sourceRaw
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    entry.adaptiveInverseData.sourceRaw = entry.raw := rfl

/-- The attached flat record exposes its rooted-shape face without
normalizing the rest of the adaptive inverse payload. -/
@[simp] theorem EnumeratedCubeInwardMateFullSource.adaptiveInverseData_rootFaceId
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource K physical hK hbounded) :
    entry.adaptiveInverseData.rootFaceId =
      (certifiedStretchedComponentUnionShapePhysicalData
        entry.source.1 entry.source.toPresented).rootFaceId :=
  rfl

/-- Both distinct stretched root faces occur in the deterministic peel, so
every attached flat record has positive size, in fact size at least two. -/
theorem EnumeratedCubeInwardMateFullSource.two_le_adaptiveInverseData_peelSize
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (entry : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :
    2 ≤ entry.adaptiveInverseData.peelSize := by
  unfold EnumeratedCubeInwardMateFullSource.adaptiveInverseData
    completeFullSourceAdaptiveInverseData
  exact certifiedStretchedComponentUnion_two_le_peelFaces_length
    entry.source.1 entry.source.toPresented

/-! ## 3. Exact duplicate-free attached family -/

/-- Attach membership evidence to every full source without changing the
finite cardinality. -/
def enumeratedCubeInwardMateFullSources
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    List (EnumeratedCubeInwardMateFullSource
      K physical hK hbounded) :=
  (cubeInwardMateCertifiedFirstStretchedFullSources
    K physical hK hbounded).attach.map fun source =>
      { source := source.1
        source_mem := source.2
        raw := source.1.toRaw
        raw_eq := rfl }

theorem enumeratedCubeInwardMateFullSources_length
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (enumeratedCubeInwardMateFullSources
      K physical hK hbounded).length =
      (cubeInwardMateCertifiedFirstStretchedFullSources
        K physical hK hbounded).length := by
  unfold enumeratedCubeInwardMateFullSources
  rw [List.length_map, List.length_attach]

/-- The attached family remains duplicate-free because its source projection
is exactly the attached upstream member. -/
theorem enumeratedCubeInwardMateFullSources_nodup
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) :
    (enumeratedCubeInwardMateFullSources
      K physical hK hbounded).Nodup := by
  unfold enumeratedCubeInwardMateFullSources
  apply CayleyPruferInjection.nodup_map_of_injOn
  · exact attach_nodup_of_nodup _
      (cubeInwardMateCertifiedFirstStretchedFullSources_nodup
        K physical hK hbounded)
  · intro left _ right _ heq
    apply Subtype.ext
    exact congrArg EnumeratedCubeInwardMateFullSource.source heq

#print axioms completePresentedSlabSourceOfCertifiedCube_on_fullSource_auxiliary
#print axioms completePresentedSlabSourceOfCertifiedCube_on_fullSource_raw
#print axioms completeFullSourceAdaptiveInverseData
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_sourcePhysical
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_sourceRaw
#print axioms EnumeratedCubeInwardMateFullSource.adaptiveInverseData_rootFaceId
#print axioms EnumeratedCubeInwardMateFullSource.two_le_adaptiveInverseData_peelSize
#print axioms enumeratedCubeInwardMateFullSources_length
#print axioms enumeratedCubeInwardMateFullSources_nodup

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
