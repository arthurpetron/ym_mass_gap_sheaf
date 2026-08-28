/-
# The outward Y/Z cut-carrier row is positive in every product column

The edge-touch carrier has the same exact local production word as the
previous valence-five calculation, but now its unique four-incidence link is
a genuine geometric cut.  Specialize the proved SU(2) quarter-floor at that
link and the exact sparse identities everywhere else, then contract the
coordinates into positivity of the complete finite recoupling product.

Constructive contract: exact finite geometry and proved local matrix entries
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom, or unbounded
heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile

namespace YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity

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
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardThreeCubeLinkCarrier
open YMGap.Continuum.Z4OutwardYZEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ThreeCubeAxisOverlapPhysicalSummand

/-! ## 1. The literal physical pair and its pivot package -/

def outwardYZSwitchLeftPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 outwardYZSwitchSurface

def outwardYZSwitchRightPhysical : SlabLabelling :=
  slabBinarySupportLabelling 5 []

def outwardYZSwitchPivotRecouplingData :
    SlabPhysicalPairRecouplingData 5 5 where
  leftPhysical := outwardYZSwitchLeftPhysical
  rightPhysical := outwardYZSwitchRightPhysical
  link := outwardYZSwitchPivot
  degree_eq := outwardYZSwitchPivot_degree_five

private theorem outwardYZSwitchLeftExternalSpins_eq :
    slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
        outwardYZSwitchPivot =
      externalSpinsOfList [1, 1, 1, 1, 0] := by
  unfold slabLinkExternalSpins outwardYZSwitchLeftPhysical
  rw [outwardYZSwitchPivot_spinList]

theorem outwardYZSwitchPivot_leftExternal_zero :
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot) 0 = 1 := by
  rw [outwardYZSwitchLeftExternalSpins_eq]
  rfl

theorem outwardYZSwitchPivot_leftExternal_one :
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot) 1 = 1 := by
  rw [outwardYZSwitchLeftExternalSpins_eq]
  rfl

theorem outwardYZSwitchPivot_leftExternal_two :
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot) 2 = 1 := by
  rw [outwardYZSwitchLeftExternalSpins_eq]
  rfl

theorem outwardYZSwitchPivot_leftExternal_three :
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot) 3 = 1 := by
  rw [outwardYZSwitchLeftExternalSpins_eq]
  rfl

theorem outwardYZSwitchPivot_leftExternal_four :
    (slabLinkExternalSpins 5 outwardYZSwitchLeftPhysical
      outwardYZSwitchPivot) 4 = 0 := by
  rw [outwardYZSwitchLeftExternalSpins_eq]
  rfl

theorem outwardYZSwitchPivot_rightExternal_zero :
    (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical
      outwardYZSwitchPivot) 0 = 0 := by decide

theorem outwardYZSwitchPivot_rightExternal_one :
    (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical
      outwardYZSwitchPivot) 1 = 0 := by decide

theorem outwardYZSwitchPivot_rightExternal_two :
    (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical
      outwardYZSwitchPivot) 2 = 0 := by decide

theorem outwardYZSwitchPivot_rightExternal_three :
    (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical
      outwardYZSwitchPivot) 3 = 0 := by decide

theorem outwardYZSwitchPivot_rightExternal_four :
    (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical
      outwardYZSwitchPivot) 4 = 0 := by decide

theorem outwardYZSwitchPivot_kernel_floor
    (source :
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).Source)
    (target :
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).kernel.weight source target :=
  slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
    outwardYZSwitchPivotRecouplingData
    outwardYZSwitchPivot_leftExternal_zero
    outwardYZSwitchPivot_leftExternal_one
    outwardYZSwitchPivot_leftExternal_two
    outwardYZSwitchPivot_leftExternal_three
    outwardYZSwitchPivot_leftExternal_four
    outwardYZSwitchPivot_rightExternal_zero
    outwardYZSwitchPivot_rightExternal_one
    outwardYZSwitchPivot_rightExternal_two
    outwardYZSwitchPivot_rightExternal_three
    outwardYZSwitchPivot_rightExternal_four source target

theorem outwardYZSwitchPivot_kernel_pos
    (source :
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).Source)
    (target :
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZSwitchPivotRecouplingData).kernel.weight source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (outwardYZSwitchPivot_kernel_floor source target)

/-! ## 2. Every other coordinate is sparse and positive -/

theorem outwardYZSwitchRight_sparseFundamentalWord (link : Z4Link) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5 outwardYZSwitchRightPhysical link) := by
  change SparseFundamentalWord
    (slabIncidentPlaqIds 5 link).length
    (slabLinkExternalSpins 5 (slabBinarySupportLabelling 5 []) link)
  exact slabBinarySupport_sparseFundamentalWord
    (extent := 5) (support := [])
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)
    link (by change 0 ≤ 2; omega)

theorem outwardYZSwitchPivot_mem_boundaryCompleteSlabLinks :
    outwardYZSwitchPivot ∈ boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff 5 outwardYZSwitchPivot).mpr
  refine ⟨axisShiftPlaquette yAxisOffset (cubeFace .topXY), ?_, ?_⟩
  · apply outwardYZSwitchSurface_subset_slab_five
    exact List.mem_append.mpr (Or.inl outwardYTopBridge_mem)
  · exact of_decide_eq_true outwardYZAdjacent.on_p

def outwardYZSwitchPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨outwardYZSwitchPivot,
    outwardYZSwitchPivot_mem_boundaryCompleteSlabLinks⟩

private theorem outwardYZSwitchPackageAtPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = outwardYZSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).kernel.weight
          source target := by
  have hlinked : linked = outwardYZSwitchPivotLinked := Subtype.ext hlink
  subst linked
  simpa only [outwardYZSwitchPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    outwardYZSwitchPivot_degree_five] using
      (outwardYZSwitchPivot_kernel_pos source target)

private theorem outwardYZSwitchPackageAtNonpivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 ≠ outwardYZSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).kernel.weight
          source target := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackage_sparse_pos
    (slabPhysicalPairRecouplingDataAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)
    (outwardYZSwitch_nonpivot_sparseFundamentalWord linked.1 hlink)
    (outwardYZSwitchRight_sparseFundamentalWord linked.1)
    source target

theorem outwardYZSwitchPackageAtLink_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked).kernel.weight
          source target := by
  by_cases hlink : linked.1 = outwardYZSwitchPivot
  · exact outwardYZSwitchPackageAtPivot_pos linked hlink source target
  · exact outwardYZSwitchPackageAtNonpivot_pos linked hlink source target

/-! ## 3. Contract the complete product -/

theorem outwardYZSwitchCoordinatewisePositive :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)) ->
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)) ->
    FiniteBistochasticCoordinatewisePositive source target
  | [], _, _ => True.intro
  | linked :: rest, source, target =>
      ⟨outwardYZSwitchPackageAtLink_pos linked source.1 target.1,
        outwardYZSwitchCoordinatewisePositive rest source.2 target.2⟩

theorem outwardYZSwitchProductWeight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked))
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZSwitchLeftPhysical outwardYZSwitchRightPhysical linked)) :
    (0 : Q') < finiteBistochasticProductWeight source target :=
  finiteBistochasticProductWeight_pos_of_coordinatewise source target
    (outwardYZSwitchCoordinatewisePositive linkedList source target)

#print axioms outwardYZSwitchPivotRecouplingData
#print axioms outwardYZSwitchPivot_kernel_floor
#print axioms outwardYZSwitchRight_sparseFundamentalWord
#print axioms outwardYZSwitchPackageAtLink_pos
#print axioms outwardYZSwitchCoordinatewisePositive
#print axioms outwardYZSwitchProductWeight_pos

end YMGap.Continuum.Z4OutwardYZEdgeTouchSlabWholeProductPositivity
