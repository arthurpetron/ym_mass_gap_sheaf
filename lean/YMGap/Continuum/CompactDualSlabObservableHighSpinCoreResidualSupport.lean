/-
# The residual-dominant far branch is a literal low-spin path

The entropy-paid branch is now geometrically summable.  In the complementary
branch, the far geometry forces a long residual word, but its positive weight
is not contractive.  The honest content available before a non-abelian
finite-core coercivity estimate is that every face touched by this word has
already been lowered to the moving finite-core threshold.

This module proves that statement pointwise and after every arbitrary prefix
of the residual word, then packages the result with the existing distance
floor.  It introduces no coercivity constant and claims no decay for this
branch.

Constructive contract: exact natural subtraction, serialized drop
multiplicity, and data-bearing finite certificates only.  No `Classical.*`,
choice, `native_decide`, `sorry`, custom axiom, noncomputable declaration, or
enlarged heartbeat budget.
-/

import YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropyTargetTail

namespace YMGap.Continuum.CompactDualSlabObservableHighSpinCoreResidualSupport

set_option autoImplicit false

open YMGap.Continuum.CompactDualSlabFaceStrandComponentHighSpinCoreSplitWeight
open YMGap.Continuum.CompactDualSlabFaceStrandComponentDrop
open YMGap.Continuum.CompactDualSlabFaceStrandComponentWeight
open YMGap.Continuum.CompactDualSlabFaceStrandSeedComponent
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabGlobalFaceStrandEdges
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreEntropySplit
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreGeometry
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4FiniteBoxPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. A positive residual count forces the intermediate label below the
threshold -/

/-- If a face has a positive core-residual decrement, then the paid exterior
has already lowered its intermediate physical label to at most `threshold`. -/
theorem highSpinCorePhysical_le_threshold_of_coreResidualDropCount_pos
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : forall faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId)
    (faceId : Nat) (hface : faceId ∈ slabPhysicalFaceEdges extent)
    (hpositive : 0 <
      coreResidualDropCount physical threshold drop faceId) :
    highSpinCorePhysical extent physical threshold drop faceId <=
      threshold := by
  unfold highSpinCorePhysical highSpinExteriorDropFaces
    lowerSlabFacesByList
  rw [slabFaceDropList_count_of_mem extent
    (exteriorDropCount physical threshold drop) hface]
  have hcapacity := hdrop faceId hface
  unfold coreResidualDropCount exteriorDropCount at hpositive
  unfold exteriorDropCount
  by_cases hthreshold : threshold <= physical faceId
  · by_cases hsmall : drop faceId <= physical faceId - threshold
    · rw [Nat.min_eq_left hsmall] at hpositive
      omega
    · have hlarge : physical faceId - threshold <= drop faceId := by
        omega
      rw [Nat.min_eq_right hlarge]
      omega
  · have hzero : physical faceId - threshold = 0 := by omega
    rw [hzero, Nat.min_eq_right (Nat.zero_le _)]
    omega

/-- Membership in the serialized residual word exposes both physical-face
membership and a positive residual multiplicity. -/
theorem highSpinCoreResidualFaces_mem_data
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat) (faceId : Nat)
    (hmem : faceId ∈
      highSpinCoreResidualFaces extent physical threshold drop) :
    faceId ∈ slabPhysicalFaceEdges extent ∧
      0 < coreResidualDropCount physical threshold drop faceId := by
  have hface : faceId ∈ slabPhysicalFaceEdges extent :=
    mem_slabFaceDropList hmem
  have hcountNe :
      (highSpinCoreResidualFaces extent physical threshold drop).count
          faceId ≠ 0 := by
    intro hzero
    exact (List.count_eq_zero.mp hzero) hmem
  unfold highSpinCoreResidualFaces at hcountNe
  rw [slabFaceDropList_count_of_mem extent
    (coreResidualDropCount physical threshold drop) hface] at hcountNe
  exact ⟨hface, by omega⟩

/-- Every face occurring in the residual word is genuinely in the finite
low-spin core at the start of the residual path. -/
theorem highSpinCorePhysical_le_threshold_of_mem_coreResidualFaces
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : forall faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId)
    (faceId : Nat)
    (hmem : faceId ∈
      highSpinCoreResidualFaces extent physical threshold drop) :
    highSpinCorePhysical extent physical threshold drop faceId <=
      threshold := by
  have hdata := highSpinCoreResidualFaces_mem_data
    extent physical threshold drop faceId hmem
  exact highSpinCorePhysical_le_threshold_of_coreResidualDropCount_pos
    extent physical threshold drop hdrop faceId hdata.1 hdata.2

/-! ## 2. The whole residual path remains inside the low-spin sector -/

/-- Lowering an arbitrary list of faces never raises any face label. -/
theorem lowerSlabFacesByList_le
    (physical : SlabLabelling) (faces : List Nat) (faceId : Nat) :
    lowerSlabFacesByList physical faces faceId <= physical faceId := by
  unfold lowerSlabFacesByList
  exact Nat.sub_le _ _

/-- After any arbitrary prefix (indeed, any arbitrary list of already removed
faces), every face belonging to the residual word still has label at most the
finite-core threshold. -/
theorem highSpinCoreResidualPath_prefix_le_threshold
    (extent : Nat) (physical : SlabLabelling) (threshold : Nat)
    (drop : Nat -> Nat)
    (hdrop : forall faceId, faceId ∈ slabPhysicalFaceEdges extent ->
      drop faceId <= physical faceId)
    (removed : List Nat) (faceId : Nat)
    (hmem : faceId ∈
      highSpinCoreResidualFaces extent physical threshold drop) :
    lowerSlabFacesByList
        (highSpinCorePhysical extent physical threshold drop)
        removed faceId <= threshold := by
  exact Nat.le_trans
    (lowerSlabFacesByList_le
      (highSpinCorePhysical extent physical threshold drop) removed faceId)
    (highSpinCorePhysical_le_threshold_of_mem_coreResidualFaces
      extent physical threshold drop hdrop faceId hmem)

/-- Seed-specialized low-spin support theorem for the actual observable-rooted
strand component. -/
theorem SlabFusionWitnessFaceStrandSeed.corePhysical_le_threshold_of_mem_residual
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold faceId : Nat)
    (hmem : faceId ∈
      SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold) :
    SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold faceId <=
      threshold := by
  exact highSpinCorePhysical_le_threshold_of_mem_coreResidualFaces
    extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)
    (fun id _ => slabFaceStrandSelectionCount_le seed.selected id)
    faceId hmem

/-- Seed-specialized prefix form: every intermediate field along the actual
residual word stays below threshold on every face that the word touches. -/
theorem SlabFusionWitnessFaceStrandSeed.coreResidualPath_prefix_le_threshold
    {K extent : Nat} {physical : SlabLabelling}
    {links : List SlabLink} {assignment : SlabFusionWitnessAssignment}
    {hassignment : assignment ∈
      slabFusionWitnessAssignmentsOn K extent physical links}
    (seed : SlabFusionWitnessFaceStrandSeed
      K extent physical links assignment hassignment)
    (threshold : Nat) (removed : List Nat) (faceId : Nat)
    (hmem : faceId ∈
      SlabFusionWitnessFaceStrandSeed.coreResidualFaces seed threshold) :
    lowerSlabFacesByList
        (SlabFusionWitnessFaceStrandSeed.corePhysical seed threshold)
        removed faceId <= threshold := by
  exact highSpinCoreResidualPath_prefix_le_threshold
    extent physical threshold
    (slabFaceStrandSelectionCount seed.selected)
    (fun id _ => slabFaceStrandSelectionCount_le seed.selected id)
    removed faceId hmem

/-! ## 3. Data-bearing certificate for the analytic finite-core frontier -/

/-- Exact finite-core data carried by one residual-dominant far certificate.
The long word and all of its low-spin support facts are fields; no coercive
estimate is assumed or hidden here. -/
structure SlabObservableLowSpinResidualCertificate
    (D : SlabPhysicalData) (faceId : Nat)
    (hface : faceId ∈ slabPhysicalFaceEdges D.extent)
    (threshold radius : Nat) : Type where
  source : SlabObservableHighSpinCoreCertificate
    D faceId hface threshold
  source_mem : source ∈
    slabObservableHighSpinFarCoreEntropyResidualCertificates
      D faceId hface threshold radius
  length_floor : radius + 2 <=
    16 * (SlabFusionWitnessFaceStrandSeed.coreResidualFaces
      (source.sourceEntry.seed D faceId hface) threshold).length
  face_mem_physical : forall residualFace,
    residualFace ∈ SlabFusionWitnessFaceStrandSeed.coreResidualFaces
      (source.sourceEntry.seed D faceId hface) threshold ->
    residualFace ∈ slabPhysicalFaceEdges D.extent
  prefix_low_spin : forall (removed : List Nat) residualFace,
    residualFace ∈ SlabFusionWitnessFaceStrandSeed.coreResidualFaces
      (source.sourceEntry.seed D faceId hface) threshold ->
    lowerSlabFacesByList
        (SlabFusionWitnessFaceStrandSeed.corePhysical
          (source.sourceEntry.seed D faceId hface) threshold)
        removed residualFace <= threshold

/-- Every member of the residual-dominant far list constructively produces
the exact low-spin path certificate required by the next analytic step. -/
def slabObservableLowSpinResidualCertificateOfMem
    {D : SlabPhysicalData} {faceId : Nat}
    {hface : faceId ∈ slabPhysicalFaceEdges D.extent}
    {threshold radius : Nat}
    (source : SlabObservableHighSpinCoreCertificate
      D faceId hface threshold)
    (hsource : source ∈
      slabObservableHighSpinFarCoreEntropyResidualCertificates
        D faceId hface threshold radius) :
    SlabObservableLowSpinResidualCertificate
      D faceId hface threshold radius where
  source := source
  source_mem := hsource
  length_floor :=
    slabObservableHighSpinFarCoreEntropyResidual_length_floor source hsource
  face_mem_physical := fun residualFace hmem =>
    (highSpinCoreResidualFaces_mem_data
      D.extent source.sourceEntry.1.1 threshold
      (slabFaceStrandSelectionCount
        (source.sourceEntry.seed D faceId hface).selected)
      residualFace hmem).1
  prefix_low_spin := fun removed residualFace hmem =>
    SlabFusionWitnessFaceStrandSeed.coreResidualPath_prefix_le_threshold
      (source.sourceEntry.seed D faceId hface)
      threshold removed residualFace hmem

#print axioms highSpinCorePhysical_le_threshold_of_coreResidualDropCount_pos
#print axioms highSpinCoreResidualFaces_mem_data
#print axioms highSpinCorePhysical_le_threshold_of_mem_coreResidualFaces
#print axioms lowerSlabFacesByList_le
#print axioms highSpinCoreResidualPath_prefix_le_threshold
#print axioms SlabFusionWitnessFaceStrandSeed.corePhysical_le_threshold_of_mem_residual
#print axioms SlabFusionWitnessFaceStrandSeed.coreResidualPath_prefix_le_threshold
#print axioms SlabObservableLowSpinResidualCertificate
#print axioms slabObservableLowSpinResidualCertificateOfMem

end YMGap.Continuum.CompactDualSlabObservableHighSpinCoreResidualSupport
