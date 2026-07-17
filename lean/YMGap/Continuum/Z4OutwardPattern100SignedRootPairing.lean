/-
# Minimal-root obstruction and signed-path search for outward pattern `100`

The tempting equal-size partner for the six-face fine-child disagreement
witness does not reverse its sign.  The ordinary outward x cube contains both
the coarse x query and its distinguished fine child, so it is `100` for both
query triples.  This module banks that exact obstruction before searching for
a longer signed path through other cells.
-/

import YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
import YMGap.Continuum.Z4OutwardFineCoarseSignedGeometryCancellation

namespace YMGap.Continuum.Z4OutwardPattern100SignedRootPairing

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.PenroseDomInduction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CoarseUnitCubeBlockGeometry
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneEventBridge
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4DyadicSU2ParityGlobalPushforward
open YMGap.Continuum.Z4DyadicPlaquetteBlockGeometry
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4EvenIncidenceCanonicalActivityPositive
open YMGap.Continuum.Z4ExplicitLinkSpinFoamFormula
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4OutwardChildQueryDisagreementWitness
open YMGap.Continuum.Z4OutwardChildQuerySmallLiftWitness
open YMGap.Continuum.Z4OutwardFineCoarseDisagreementInjectionInterface
open YMGap.Continuum.Z4OutwardFineCoarseSignedGeometryCancellation
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasCrossDifference
open YMGap.Continuum.Z4OutwardFineCoarseSupportGasEventDifference
open YMGap.Continuum.Z4OutwardThreeCubeFineSubsupportPatterns
open YMGap.Continuum.Z4OutwardThreeCubeFullRootQueries
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardThreeCubeSubsupportPatterns
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4PhysicalSurfaceComponentLabels
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4SpinSummedDyadicUnitCubeUniformOccurrenceFloor
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4ThreeBlockFiberConditionalKernel
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand
open YMGap.Continuum.Z4ThreeCubeComponentSubsupportObservable
open YMGap.Continuum.Z4UnitCubeSurfaceGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The coarse x root remains fine-pattern `100` -/

theorem outwardXFineQueryFace_mem_coarseXSurface :
    outwardXFineQueryFace ∈ outwardXSurface := by
  simp [outwardXFineQueryFace, outwardXSurface, axisCubeSurface,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, dyadicCell,
    dyadicVertex, zeroAxisOffset, xAxisOffset, cubeFace]

theorem outwardYFineQueryFace_not_mem_coarseXSurface :
    outwardYFineQueryFace ∉ outwardXSurface := by
  simp [outwardYFineQueryFace, outwardXSurface, axisCubeSurface,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, dyadicCell,
    dyadicVertex, zeroAxisOffset, xAxisOffset, cubeFace]

theorem outwardZFineQueryFace_not_mem_coarseXSurface :
    outwardZFineQueryFace ∉ outwardXSurface := by
  simp [outwardZFineQueryFace, outwardXSurface, axisCubeSurface,
    unitCubeSurface, axisShiftPlaquette, axisShiftVertex, dyadicCell,
    dyadicVertex, zeroAxisOffset, xAxisOffset, cubeFace]


private theorem xFineQuery_subset_coarseX :
    ∀ id, id ∈ outwardXFineQuery → id ∈ outwardXRoot := by
  unfold outwardXRoot
  rw [outwardXFineQuery_eq_geometric]
  exact fineFaceQuerySupport_subset_geometricRoot
    zeroAxisOffset .rightYZ .origin outwardXSurface
    outwardXFineQueryFace_mem_coarseXSurface

private theorem yFineQuery_not_subset_coarseX :
    ¬ (∀ id, id ∈ outwardYFineQuery → id ∈ outwardXRoot) := by
  unfold outwardXRoot
  rw [outwardYFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .backXZ .origin outwardXSurface
    outwardXSurface_subset_box_six
    outwardYFineQueryFace_not_mem_coarseXSurface

private theorem zFineQuery_not_subset_coarseX :
    ¬ (∀ id, id ∈ outwardZFineQuery → id ∈ outwardXRoot) := by
  unfold outwardXRoot
  rw [outwardZFineQuery_eq_geometric]
  exact fineFaceQuerySupport_not_subset_geometricRoot
    zeroAxisOffset (Or.inl rfl) .topXY .origin outwardXSurface
    outwardXSurface_subset_box_six
    outwardZFineQueryFace_not_mem_coarseXSurface

theorem outwardXRoot_finePattern_100 :
    physicalComponentSubsupportPattern 6 outwardFineQueries
        (componentLabel outwardXRoot) = (true, false, false) := by
  apply outwardFinePattern_eq_of_events
  · exact componentLabel_subsupportEvent_true
      outwardXRoot_mem_canonical xFineQuery_subset_coarseX
  · exact componentLabel_subsupportEvent_false
      outwardXRoot_mem_canonical yFineQuery_not_subset_coarseX
  · exact componentLabel_subsupportEvent_false
      outwardXRoot_mem_canonical zFineQuery_not_subset_coarseX

theorem outwardXRoot_coarseFamilyPattern_100 :
    outwardComponentSubsupportFamilyPattern outwardCoarseQueries
        [outwardXRoot] = (true, false, false) := by
  have hpattern := outwardXRoot_pattern_100
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    outwardXRoot_mem_canonical] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem outwardXRoot_fineFamilyPattern_100 :
    outwardComponentSubsupportFamilyPattern outwardFineQueries
        [outwardXRoot] = (true, false, false) := by
  have hpattern := outwardXRoot_finePattern_100
  unfold physicalComponentSubsupportPattern
    physicalComponentSubsupportEvent at hpattern
  rw [componentLabelAmbientFamily_eq_singleton
    outwardXRoot_mem_canonical] at hpattern
  simpa only [outwardComponentSubsupportFamilyPattern] using hpattern

theorem outwardXRoot_coarsePattern100Event_true :
    outwardComponentSubsupportFamilyPatternEvent outwardCoarseQueries
        (true, false, false) [outwardXRoot] = true := by
  unfold outwardComponentSubsupportFamilyPatternEvent
  exact decide_eq_true outwardXRoot_coarseFamilyPattern_100

theorem outwardXRoot_finePattern100Event_true :
    outwardComponentSubsupportFamilyPatternEvent outwardFineQueries
        (true, false, false) [outwardXRoot] = true := by
  unfold outwardComponentSubsupportFamilyPatternEvent
  exact decide_eq_true outwardXRoot_fineFamilyPattern_100

/-- The naive equal-size candidate is not sign reversing: both pattern-100
event bits are true on its singleton family. -/
theorem outwardXRoot_pattern100_same_sign :
    outwardComponentSubsupportFamilyPatternEvent outwardCoarseQueries
          (true, false, false) [outwardXRoot] = true ∧
      outwardComponentSubsupportFamilyPatternEvent outwardFineQueries
          (true, false, false) [outwardXRoot] = true :=
  ⟨outwardXRoot_coarsePattern100Event_true,
    outwardXRoot_finePattern100Event_true⟩


/-! ## 2. The genuine one-sided small-lift witness -/

def outwardPatternCoarseOnlyFamilies
    (pattern : ThreeBlockPattern) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies 6).filter (fun family =>
    outwardComponentSubsupportFamilyPatternEvent
        outwardCoarseQueries pattern family &&
      !(outwardComponentSubsupportFamilyPatternEvent
        outwardFineQueries pattern family))

def outwardPatternFineOnlyFamilies
    (pattern : ThreeBlockPattern) : List (List (List Nat)) :=
  (canonicalCompatibleAmbientFamilies 6).filter (fun family =>
    outwardComponentSubsupportFamilyPatternEvent
        outwardFineQueries pattern family &&
      !(outwardComponentSubsupportFamilyPatternEvent
        outwardCoarseQueries pattern family))

private theorem nil_mem_sublists_local {A : Type} :
    ∀ ambient : List A, [] ∈ sublists ambient
  | [] => List.mem_cons_self
  | _ :: tail => by
      rw [sublists_cons']
      exact List.mem_append_left _ (nil_mem_sublists_local tail)

private theorem singleton_mem_sublists_of_mem_local {A : Type} :
    ∀ (ambient : List A) (item : A), item ∈ ambient →
      [item] ∈ sublists ambient
  | [], _, hmem => absurd hmem List.not_mem_nil
  | head :: tail, item, hmem => by
      rw [sublists_cons']
      rcases List.mem_cons.mp hmem with hhead | htail
      · subst item
        apply List.mem_append_right
        exact List.mem_map.mpr
          ⟨[], nil_mem_sublists_local tail, rfl⟩
      · exact List.mem_append_left _
          (singleton_mem_sublists_of_mem_local tail item htail)

theorem outwardXRoot_singleton_mem_compatible :
    [outwardXRoot] ∈ canonicalCompatibleAmbientFamilies 6 := by
  unfold canonicalCompatibleAmbientFamilies
  apply List.mem_filter.mpr
  exact ⟨singleton_mem_sublists_of_mem_local
      (canonicalSurfacePolymers 6) outwardXRoot
      outwardXRoot_mem_canonical, rfl⟩


theorem outwardXFineSmallLift_singleton_mem_pattern100_fineOnly :
    [outwardXFineSmallLiftRoot] ∈
      outwardPatternFineOnlyFamilies (true, false, false) := by
  unfold outwardPatternFineOnlyFamilies
  apply List.mem_filter.mpr
  exact ⟨outwardXFineSmallLift_singleton_mem_compatible,
    by rw [outwardXFineSmallLift_familyPatternEvent_100,
      outwardXFineSmallLift_coarsePattern100Event_false]
       rfl⟩

#print axioms outwardXRoot_finePattern_100
#print axioms outwardXRoot_coarseFamilyPattern_100
#print axioms outwardXRoot_fineFamilyPattern_100
#print axioms outwardXRoot_pattern100_same_sign
#print axioms outwardXFineSmallLift_singleton_mem_pattern100_fineOnly

end YMGap.Continuum.Z4OutwardPattern100SignedRootPairing
