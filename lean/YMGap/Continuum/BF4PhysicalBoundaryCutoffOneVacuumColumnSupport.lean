/-
# Exact cutoff-one vacuum-column support

The 72-face cutoff-one slab has 128 closed binary surface labellings.  When
the fixed interface and reflected upper source are both vacuum, the checked
surface list leaves exactly two possibilities on the lower source: the empty
surface and the central six-face cube.

This file first certifies that finite geometric exhaustiveness and then
translates it through the actual three-part slab assembly.  It is a support
classification, not yet the weighted two-term column-sum identity; the latter
also requires the local statement that every nonclosed source summand is
annihilated by an odd link multiplicity.

No `Classical.*`, `native_decide`, `sorry`, custom axiom, choice, or
noncomputable declaration.
-/

import YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
import YMGap.Continuum.BF4PhysicalBoundaryCutoffOneDeltaRowCertificate

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport

set_option maxRecDepth 200000
set_option maxHeartbeats 12000000

open YMGap.Continuum.BF4CanonicalFiniteNumeratorPartitionBudget
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4CutoffOneBinarySurfaceCertificate
open YMGap.Continuum.BF4CutoffOneBinarySurfaceEmbedding
open YMGap.Continuum.BF4ExactCutoffOneSurfaceCharacterReindex
open YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumElimination
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneLabellings
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex

/-! ## 1. The finite closed-surface restriction -/

/-- Executable condition that both the fixed interface and upper reflected
source coordinates of a full cutoff-one slab labelling are vacuum. -/
def slabFixedUpperVacuum (physical : EdgeLabelling) : Bool :=
  (centralFixedFaceIds 0 ++ centralUpperFaceIds 0).all fun faceId =>
    decide (physical faceId = 0)

def embeddedSurfaceFixedUpperVacuum (compactMask : Nat) : Bool :=
  slabFixedUpperVacuum (embeddedSurfaceLabelling compactMask)

/-- Compact masks for the empty lower source and central six-face cube. -/
def vacuumColumnSurfaceMasks : List Nat := [0, 270859]

/-- Direct kernel certificate: restricting all 128 exact closed surfaces to
vacuum fixed/upper data leaves exactly the two displayed compact masks. -/
theorem binarySurfaceMasks_filter_fixedUpperVacuum :
    binarySurfaceMasks.filter embeddedSurfaceFixedUpperVacuum =
      vacuumColumnSurfaceMasks := by
  decide

theorem compactMask_eq_vacuum_or_cube_of_fixedUpperVacuum
    {compactMask : Nat}
    (hmask : compactMask ∈ binarySurfaceMasks)
    (hvacuum : embeddedSurfaceFixedUpperVacuum compactMask = true) :
    compactMask = 0 ∨ compactMask = 270859 := by
  have hfiltered : compactMask ∈
      binarySurfaceMasks.filter embeddedSurfaceFixedUpperVacuum :=
    List.mem_filter.mpr ⟨hmask, hvacuum⟩
  rw [binarySurfaceMasks_filter_fixedUpperVacuum] at hfiltered
  simpa [vacuumColumnSurfaceMasks] using hfiltered

/-! ## 2. Translation to the actual central assembly -/

theorem slabFixedUpperVacuum_assemble_source
    (source : EdgeLabelling) :
    slabFixedUpperVacuum
        (assembleReflectedSlabLabelling 0 source
          zeroEdgeLabelling zeroEdgeLabelling) = true := by
  unfold slabFixedUpperVacuum
  apply List.all_eq_true.mpr
  intro faceId hfaceId
  rcases List.mem_append.mp hfaceId with hfixed | hupper
  · have hparts := mem_centralFixedFaceIds.mp hfixed
    rw [assembleReflectedSlabLabelling_fixed hparts.1 hparts.2]
    rfl
  · have hparts := mem_centralUpperFaceIds.mp hupper
    rw [assembleReflectedSlabLabelling_upper hparts.1 hparts.2]
    rfl

theorem embeddedClosedSurfaceLabellings_eq_compact_map :
    embeddedClosedSurfaceLabellings =
      binarySurfaceMasks.map embeddedSurfaceLabelling := by
  unfold embeddedClosedSurfaceLabellings embeddedBinarySurfaceMasks
  rw [List.map_map]
  rfl

private theorem zero_full_mem :
    zeroEdgeLabelling ∈ cutoffOneFullSlabLabellings := by
  unfold cutoffOneFullSlabLabellings
  simpa only [show centralExtent 0 = 1 from rfl,
      assembleReflectedSlabLabelling_zero] using
    (assembleReflectedSlabLabelling_mem_full
      (zeroEdgeLabelling_mem_centralHalfStates 1 0)
      (zeroEdgeLabelling_mem_centralBoundaryChannels 1 0)
      (zeroEdgeLabelling_mem_centralHalfStates 1 0))

private theorem cube_full_mem :
    centralLowerCubePhysical ∈ cutoffOneFullSlabLabellings := by
  unfold cutoffOneFullSlabLabellings centralLowerCubePhysical
  exact assembleReflectedSlabLabelling_mem_full
    (centralLowerCubeState_mem_centralHalfStates (by decide))
    (zeroEdgeLabelling_mem_centralBoundaryChannels 1 0)
    (zeroEdgeLabelling_mem_centralHalfStates 1 0)

private theorem cutoffOneSlabMask_eq_of_bits
    (physical : EdgeLabelling) (mask : Nat)
    (hmask : mask < 2 ^ 72)
    (hagrees : ∀ faceId, faceId < 72 →
      decide (physical faceId = 1) = mask.testBit faceId) :
    cutoffOneSlabMask physical = mask := by
  apply Nat.eq_of_testBit_eq
  intro faceId
  by_cases hfaceId : faceId < 72
  · rw [cutoffOneSlabMask_testBit physical faceId hfaceId,
      hagrees faceId hfaceId]
  · have hpow : 2 ^ 72 ≤ 2 ^ faceId :=
      Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (cutoffOneSlabMask_lt physical) hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hmask hpow)]

def cubeCompactMaskAgreementCheck : Bool :=
  (List.range 72).all fun faceId =>
    decide
      (decide (centralLowerCubePhysical faceId = 1) =
        (embedBinarySurfaceMask 270859).testBit faceId)

theorem cubeCompactMaskAgreementCheck_true :
    cubeCompactMaskAgreementCheck = true := by
  decide

theorem embeddedSurfaceLabelling_zero_eq :
    embeddedSurfaceLabelling 0 = zeroEdgeLabelling := by
  rw [embeddedSurfaceLabelling_eq_slabMaskLabelling]
  have hdecode := slabMaskLabelling_cutoffOneSlabMask_eq
    zeroEdgeLabelling zero_full_mem
  have hmask : cutoffOneSlabMask zeroEdgeLabelling =
      embedBinarySurfaceMask 0 := by
    have hembed : embedBinarySurfaceMask 0 = 0 := by
      simp [embedBinarySurfaceMask, embedSurfaceMaskFrom,
        activeHypercubeSlabFaceIds]
    rw [hembed]
    exact cutoffOneSlabMask_eq_of_bits zeroEdgeLabelling 0
      (by decide) (by
        intro faceId _
        simp [zeroEdgeLabelling])
  rw [hmask] at hdecode
  exact hdecode

theorem embeddedSurfaceLabelling_cube_eq :
    embeddedSurfaceLabelling 270859 = centralLowerCubePhysical := by
  rw [embeddedSurfaceLabelling_eq_slabMaskLabelling]
  have hdecode := slabMaskLabelling_cutoffOneSlabMask_eq
    centralLowerCubePhysical cube_full_mem
  have hmask : cutoffOneSlabMask centralLowerCubePhysical =
      embedBinarySurfaceMask 270859 := by
    apply cutoffOneSlabMask_eq_of_bits
    · decide
    · intro faceId hfaceId
      exact of_decide_eq_true
        (List.all_eq_true.mp cubeCompactMaskAgreementCheck_true
          faceId (List.mem_range.mpr hfaceId))
  rw [hmask] at hdecode
  exact hdecode

/-! ## 3. Exhaustiveness for assembled source/vacuum/vacuum data -/

/-- If an assembled cutoff-one source with vacuum fixed and upper data is a
closed 72-face binary surface, then its lower source is exactly vacuum or the
central six-face cube. -/
theorem source_eq_vacuum_or_cube_of_assembled_closed
    (source : EdgeLabelling)
    (hsource : source ∈ centralHalfStates 1 0)
    (hclosed :
      slabSurfaceIsClosed
        (cutoffOneSlabMask
          (assembleReflectedSlabLabelling 0 source
            zeroEdgeLabelling zeroEdgeLabelling)) = true) :
    source = zeroEdgeLabelling ∨ source = centralLowerCubeState := by
  let physical := assembleReflectedSlabLabelling 0 source
    zeroEdgeLabelling zeroEdgeLabelling
  have hphysical : physical ∈ cutoffOneFullSlabLabellings := by
    unfold physical cutoffOneFullSlabLabellings
    exact assembleReflectedSlabLabelling_mem_full hsource
      (zeroEdgeLabelling_mem_centralBoundaryChannels 1 0)
      (zeroEdgeLabelling_mem_centralHalfStates 1 0)
  have hclosedMem : physical ∈ cutoffOneClosedSlabLabellings := by
    apply List.mem_filter.mpr
    exact ⟨hphysical, hclosed⟩
  have hembedded : physical ∈ embeddedClosedSurfaceLabellings :=
    (mem_cutoffOneClosedSlabLabellings_iff physical).mp hclosedMem
  rw [embeddedClosedSurfaceLabellings_eq_compact_map] at hembedded
  obtain ⟨compactMask, hmask, heq⟩ := List.mem_map.mp hembedded
  have hvacuum : embeddedSurfaceFixedUpperVacuum compactMask = true := by
    unfold embeddedSurfaceFixedUpperVacuum
    rw [heq]
    exact slabFixedUpperVacuum_assemble_source source
  rcases compactMask_eq_vacuum_or_cube_of_fixedUpperVacuum
      hmask hvacuum with hzero | hcube
  · left
    subst compactMask
    have hphysicalZero : physical = zeroEdgeLabelling := by
      rw [← heq, embeddedSurfaceLabelling_zero_eq]
    have hsourceTriple :
        (source, (zeroEdgeLabelling, zeroEdgeLabelling)) ∈
          centralReflectionTriples 1 0 := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨hsource, zeroEdgeLabelling_mem_centralHalfStates 1 0,
        zeroEdgeLabelling_mem_centralBoundaryChannels 1 0⟩
    have hzeroTriple :
        (zeroEdgeLabelling,
          (zeroEdgeLabelling, zeroEdgeLabelling)) ∈
            centralReflectionTriples 1 0 := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨zeroEdgeLabelling_mem_centralHalfStates 1 0,
        zeroEdgeLabelling_mem_centralHalfStates 1 0,
        zeroEdgeLabelling_mem_centralBoundaryChannels 1 0⟩
    have htriple := assembleCentralReflectionTriple_injective_on
      hsourceTriple hzeroTriple (by
        unfold assembleCentralReflectionTriple
        simp only
        rw [assembleReflectedSlabLabelling_zero]
        exact hphysicalZero)
    exact congrArg Prod.fst htriple
  · right
    subst compactMask
    have hphysicalCube : physical = centralLowerCubePhysical := by
      rw [← heq, embeddedSurfaceLabelling_cube_eq]
    have hsourceTriple :
        (source, (zeroEdgeLabelling, zeroEdgeLabelling)) ∈
          centralReflectionTriples 1 0 := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨hsource, zeroEdgeLabelling_mem_centralHalfStates 1 0,
        zeroEdgeLabelling_mem_centralBoundaryChannels 1 0⟩
    have hcubeTriple :
        (centralLowerCubeState,
          (zeroEdgeLabelling, zeroEdgeLabelling)) ∈
            centralReflectionTriples 1 0 := by
      apply mem_centralReflectionTriples.mpr
      exact ⟨centralLowerCubeState_mem_centralHalfStates (by decide),
        zeroEdgeLabelling_mem_centralHalfStates 1 0,
        zeroEdgeLabelling_mem_centralBoundaryChannels 1 0⟩
    have htriple := assembleCentralReflectionTriple_injective_on
      hsourceTriple hcubeTriple (by
        unfold assembleCentralReflectionTriple
        simp only
        change physical = centralLowerCubePhysical
        exact hphysicalCube)
    exact congrArg Prod.fst htriple

end YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport.binarySurfaceMasks_filter_fixedUpperVacuum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport.compactMask_eq_vacuum_or_cube_of_fixedUpperVacuum
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffOneVacuumColumnSupport.source_eq_vacuum_or_cube_of_assembled_closed
