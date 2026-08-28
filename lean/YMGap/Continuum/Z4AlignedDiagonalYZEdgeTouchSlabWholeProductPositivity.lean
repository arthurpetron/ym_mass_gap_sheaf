/-
# The aligned diagonal cut row is positive in every product column

The aligned diagonal carrier has the already-certified valence-five
fundamental/vacuum pivot word and sparse fundamental words everywhere else.
Specialize the exact quarter-floor at the pivot, use the sparse identities at
all nonpivot links, and contract the coordinatewise statements into strict
positivity of every finite product column.

Constructive contract: exact finite geometry and proved local SU(2) matrix
entries only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile

namespace YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.CompactDualSlabBinarySupportLinkCoherence
open YMGap.Continuum.CompactDualSlabBinarySupportSparseRecouplingWord
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

/-! ## 1. Literal physical pair and pivot quarter-floor -/

def alignedDiagonalSwitchLeftPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 alignedDiagonalSwitchSurface

def alignedDiagonalSwitchRightPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 []

def alignedDiagonalSwitchPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := alignedDiagonalSwitchLeftPhysical
  rightPhysical := alignedDiagonalSwitchRightPhysical
  link := alignedDiagonalSwitchPivot
  degree_eq := alignedDiagonalSwitchPivot_degree_five

private theorem alignedDiagonalSwitchLeftExternalSpins_eq :
    slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
        alignedDiagonalSwitchPivot =
      externalSpinsOfList [1, 1, 1, 1, 0] := by
  unfold slabLinkExternalSpins alignedDiagonalSwitchLeftPhysical
  rw [alignedDiagonalSwitchPivot_spinList]

theorem alignedDiagonalSwitchPivot_leftExternal_zero :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot) 0 = 1 := by
  rw [alignedDiagonalSwitchLeftExternalSpins_eq]
  rfl

theorem alignedDiagonalSwitchPivot_leftExternal_one :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot) 1 = 1 := by
  rw [alignedDiagonalSwitchLeftExternalSpins_eq]
  rfl

theorem alignedDiagonalSwitchPivot_leftExternal_two :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot) 2 = 1 := by
  rw [alignedDiagonalSwitchLeftExternalSpins_eq]
  rfl

theorem alignedDiagonalSwitchPivot_leftExternal_three :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot) 3 = 1 := by
  rw [alignedDiagonalSwitchLeftExternalSpins_eq]
  rfl

theorem alignedDiagonalSwitchPivot_leftExternal_four :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchLeftPhysical
      alignedDiagonalSwitchPivot) 4 = 0 := by
  rw [alignedDiagonalSwitchLeftExternalSpins_eq]
  rfl

theorem alignedDiagonalSwitchPivot_rightExternal_zero :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchPivot) 0 = 0 := by decide

theorem alignedDiagonalSwitchPivot_rightExternal_one :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchPivot) 1 = 0 := by decide

theorem alignedDiagonalSwitchPivot_rightExternal_two :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchPivot) 2 = 0 := by decide

theorem alignedDiagonalSwitchPivot_rightExternal_three :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchPivot) 3 = 0 := by decide

theorem alignedDiagonalSwitchPivot_rightExternal_four :
    (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical
      alignedDiagonalSwitchPivot) 4 = 0 := by decide

theorem alignedDiagonalSwitchPivot_kernel_floor
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        alignedDiagonalSwitchPivotRecouplingData).kernel.weight
          source target :=
  slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
    alignedDiagonalSwitchPivotRecouplingData
    alignedDiagonalSwitchPivot_leftExternal_zero
    alignedDiagonalSwitchPivot_leftExternal_one
    alignedDiagonalSwitchPivot_leftExternal_two
    alignedDiagonalSwitchPivot_leftExternal_three
    alignedDiagonalSwitchPivot_leftExternal_four
    alignedDiagonalSwitchPivot_rightExternal_zero
    alignedDiagonalSwitchPivot_rightExternal_one
    alignedDiagonalSwitchPivot_rightExternal_two
    alignedDiagonalSwitchPivot_rightExternal_three
    alignedDiagonalSwitchPivot_rightExternal_four source target

theorem alignedDiagonalSwitchPivot_kernel_pos
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      alignedDiagonalSwitchPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        alignedDiagonalSwitchPivotRecouplingData).kernel.weight
          source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (alignedDiagonalSwitchPivot_kernel_floor source target)

/-! ## 2. Sparse nonpivot coordinates -/

theorem alignedDiagonalSwitchRight_sparseFundamentalWord (link : Z4Link) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5 alignedDiagonalSwitchRightPhysical link) := by
  change SparseFundamentalWord
    (slabIncidentPlaqIds 5 link).length
    (slabLinkExternalSpins 5 (slabBinarySupportLabelling 5 []) link)
  exact slabBinarySupport_sparseFundamentalWord
    (extent := 5) (support := [])
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)
    link (by change 0 ≤ 2; omega)

theorem alignedDiagonalSwitchPivot_mem_boundaryCompleteSlabLinks :
    alignedDiagonalSwitchPivot ∈ boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff
    5 alignedDiagonalSwitchPivot).mpr
  refine ⟨axisShiftPlaquette zeroAxisOffset (cubeFace .topXY), ?_, ?_⟩
  · apply alignedDiagonalSwitchSurface_subset_slab_five
    decide
  · decide

def alignedDiagonalSwitchPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨alignedDiagonalSwitchPivot,
    alignedDiagonalSwitchPivot_mem_boundaryCompleteSlabLinks⟩

private theorem alignedDiagonalSwitchPackageAtPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = alignedDiagonalSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
        linked).kernel.weight source target := by
  have hlinked : linked = alignedDiagonalSwitchPivotLinked := Subtype.ext hlink
  subst linked
  simpa only [alignedDiagonalSwitchPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    alignedDiagonalSwitchPivot_degree_five] using
      (alignedDiagonalSwitchPivot_kernel_pos source target)

private theorem alignedDiagonalSwitchPackageAtNonpivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 ≠ alignedDiagonalSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
        linked).kernel.weight source target := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackage_sparse_pos
    (slabPhysicalPairRecouplingDataAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked)
    (alignedDiagonalSwitch_nonpivot_sparseFundamentalWord linked.1 hlink)
    (alignedDiagonalSwitchRight_sparseFundamentalWord linked.1)
    source target

theorem alignedDiagonalSwitchPackageAtLink_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        alignedDiagonalSwitchLeftPhysical alignedDiagonalSwitchRightPhysical
        linked).kernel.weight source target := by
  by_cases hlink : linked.1 = alignedDiagonalSwitchPivot
  · exact alignedDiagonalSwitchPackageAtPivot_pos
      linked hlink source target
  · exact alignedDiagonalSwitchPackageAtNonpivot_pos
      linked hlink source target

/-! ## 3. Complete heterogeneous products -/

theorem alignedDiagonalSwitchCoordinatewisePositive :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          alignedDiagonalSwitchLeftPhysical
          alignedDiagonalSwitchRightPhysical linked)) ->
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          alignedDiagonalSwitchLeftPhysical
          alignedDiagonalSwitchRightPhysical linked)) ->
    FiniteBistochasticCoordinatewisePositive source target
  | [], _, _ => True.intro
  | linked :: rest, source, target =>
      ⟨alignedDiagonalSwitchPackageAtLink_pos
          linked source.1 target.1,
        alignedDiagonalSwitchCoordinatewisePositive
          rest source.2 target.2⟩

theorem alignedDiagonalSwitchProductWeight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          alignedDiagonalSwitchLeftPhysical
          alignedDiagonalSwitchRightPhysical linked))
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          alignedDiagonalSwitchLeftPhysical
          alignedDiagonalSwitchRightPhysical linked)) :
    (0 : Q') < finiteBistochasticProductWeight source target :=
  finiteBistochasticProductWeight_pos_of_coordinatewise source target
    (alignedDiagonalSwitchCoordinatewisePositive
      linkedList source target)

#print axioms alignedDiagonalSwitchPivotRecouplingData
#print axioms alignedDiagonalSwitchPivot_kernel_floor
#print axioms alignedDiagonalSwitchRight_sparseFundamentalWord
#print axioms alignedDiagonalSwitchPackageAtLink_pos
#print axioms alignedDiagonalSwitchCoordinatewisePositive
#print axioms alignedDiagonalSwitchProductWeight_pos

end YMGap.Continuum.Z4AlignedDiagonalYZEdgeTouchSlabWholeProductPositivity
