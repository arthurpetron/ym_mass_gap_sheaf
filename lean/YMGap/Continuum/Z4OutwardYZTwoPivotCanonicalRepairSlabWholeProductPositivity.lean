/-
# Strict positivity of the two-pivot outward repair recoupling product

The spatial pivot has the four-fundamental word `(1,1,1,1,0)` and the
temporal pivot has the middle-vacuum word `(1,1,0,1,1)`.  Their complete
two-replica matrices have the exact `1/4` entrywise floor.  Every other link
is sparse fundamental in both replicas and hence has a strictly positive
entry.  Structural recursion contracts these facts to strict positivity of
every complete product column, including the selected repair target.

Constructive contract: proved local SU(2) floors and finite products only;
no choice, `Classical`, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabFundamentalVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.SU2SlabMiddleVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing

namespace YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabWholeProductPositivity

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
open YMGap.Continuum.SU2SlabMiddleVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairCutCarrier
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabPivotPairing
open YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabSwitchingProfile

/-! ## 1. Exact pivot words and local floors -/

private theorem outwardYZCanonicalRepairSpatialLeftExternalSpins_eq :
    slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchSpatialPivot =
      externalSpinsOfList [1, 1, 1, 1, 0] := by
  unfold slabLinkExternalSpins
    outwardYZCanonicalRepairSwitchLeftPhysical
  rw [outwardYZCanonicalRepairSwitchSpatialPivot_spinList]

private theorem outwardYZCanonicalRepairTemporalLeftExternalSpins_eq :
    slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchTemporalPivot =
      externalSpinsOfList [1, 1, 0, 1, 1] := by
  unfold slabLinkExternalSpins
    outwardYZCanonicalRepairSwitchLeftPhysical
  rw [outwardYZCanonicalRepairSwitchTemporalPivot_spinList]

private theorem outwardYZCanonicalRepairSwitchRightExternal_zero
    (link : Z4Link) (position : Nat) :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchRightPhysical link) position = 0 := by
  unfold slabLinkExternalSpins
    outwardYZCanonicalRepairSwitchRightPhysical
    slabBinarySupportLabelling
    externalSpinsOfList
  simp
  cases hget : (slabIncidentPlaqIds 5 link)[position]? with
  | none => simp
  | some id => simp

private theorem outwardYZCanonicalRepairSpatialLeftExternal_zero :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot) 0 = 1 := by
  rw [outwardYZCanonicalRepairSpatialLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairSpatialLeftExternal_one :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot) 1 = 1 := by
  rw [outwardYZCanonicalRepairSpatialLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairSpatialLeftExternal_two :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot) 2 = 1 := by
  rw [outwardYZCanonicalRepairSpatialLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairSpatialLeftExternal_three :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot) 3 = 1 := by
  rw [outwardYZCanonicalRepairSpatialLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairSpatialLeftExternal_four :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchSpatialPivot) 4 = 0 := by
  rw [outwardYZCanonicalRepairSpatialLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairTemporalLeftExternal_zero :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot) 0 = 1 := by
  rw [outwardYZCanonicalRepairTemporalLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairTemporalLeftExternal_one :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot) 1 = 1 := by
  rw [outwardYZCanonicalRepairTemporalLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairTemporalLeftExternal_two :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot) 2 = 0 := by
  rw [outwardYZCanonicalRepairTemporalLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairTemporalLeftExternal_three :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot) 3 = 1 := by
  rw [outwardYZCanonicalRepairTemporalLeftExternalSpins_eq]
  rfl

private theorem outwardYZCanonicalRepairTemporalLeftExternal_four :
    (slabLinkExternalSpins 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchTemporalPivot) 4 = 1 := by
  rw [outwardYZCanonicalRepairTemporalLeftExternalSpins_eq]
  rfl

theorem outwardYZCanonicalRepairSpatialPivot_kernel_floor
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairSpatialPivotRecouplingData).kernel.weight
          source target :=
  slabPhysicalPairRecouplingKernelPackageFive_fundamentalVacuum_floor
    outwardYZCanonicalRepairSpatialPivotRecouplingData
    outwardYZCanonicalRepairSpatialLeftExternal_zero
    outwardYZCanonicalRepairSpatialLeftExternal_one
    outwardYZCanonicalRepairSpatialLeftExternal_two
    outwardYZCanonicalRepairSpatialLeftExternal_three
    outwardYZCanonicalRepairSpatialLeftExternal_four
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchSpatialPivot 0)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchSpatialPivot 1)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchSpatialPivot 2)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchSpatialPivot 3)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchSpatialPivot 4)
    source target

theorem outwardYZCanonicalRepairTemporalPivot_kernel_floor
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairTemporalPivotRecouplingData).kernel.weight
          source target :=
  slabPhysicalPairRecouplingKernelPackageFive_middleVacuum_floor
    outwardYZCanonicalRepairTemporalPivotRecouplingData
    outwardYZCanonicalRepairTemporalLeftExternal_zero
    outwardYZCanonicalRepairTemporalLeftExternal_one
    outwardYZCanonicalRepairTemporalLeftExternal_two
    outwardYZCanonicalRepairTemporalLeftExternal_three
    outwardYZCanonicalRepairTemporalLeftExternal_four
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchTemporalPivot 0)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchTemporalPivot 1)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchTemporalPivot 2)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchTemporalPivot 3)
    (outwardYZCanonicalRepairSwitchRightExternal_zero
      outwardYZCanonicalRepairSwitchTemporalPivot 4)
    source target

theorem outwardYZCanonicalRepairSpatialPivot_kernel_pos
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairSpatialPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairSpatialPivotRecouplingData).kernel.weight
          source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (outwardYZCanonicalRepairSpatialPivot_kernel_floor source target)

theorem outwardYZCanonicalRepairTemporalPivot_kernel_pos
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      outwardYZCanonicalRepairTemporalPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        outwardYZCanonicalRepairTemporalPivotRecouplingData).kernel.weight
          source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (outwardYZCanonicalRepairTemporalPivot_kernel_floor source target)

/-! ## 2. Sparse nonpivot coordinates -/

theorem outwardYZCanonicalRepairSwitchRight_sparseFundamentalWord
    (link : Z4Link) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5
        outwardYZCanonicalRepairSwitchRightPhysical link) := by
  change SparseFundamentalWord
    (slabIncidentPlaqIds 5 link).length
    (slabLinkExternalSpins 5
      (slabBinarySupportLabelling 5 []) link)
  exact slabBinarySupport_sparseFundamentalWord
    (extent := 5) (support := [])
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl) link (by change 0 ≤ 2; omega)

theorem outwardYZCanonicalRepairSpatialPivot_mem_boundaryCompleteSlabLinks :
    outwardYZCanonicalRepairSwitchSpatialPivot ∈
      boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff 5
    outwardYZCanonicalRepairSwitchSpatialPivot).mpr
  refine ⟨((0, 1, 1, 0), .p01), ?_, ?_⟩
  · apply outwardYZCanonicalRepairSwitchSurface_subset_slab_five
    exact List.mem_append.mpr
      (Or.inl (by decide : ((0, 1, 1, 0), .p01) ∈
        outwardYZCanonicalRepairTargetLobe))
  · decide

theorem outwardYZCanonicalRepairTemporalPivot_mem_boundaryCompleteSlabLinks :
    outwardYZCanonicalRepairSwitchTemporalPivot ∈
      boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff 5
    outwardYZCanonicalRepairSwitchTemporalPivot).mpr
  refine ⟨((0, 1, 1, 0), .p13), ?_, ?_⟩
  · apply outwardYZCanonicalRepairSwitchSurface_subset_slab_five
    exact List.mem_append.mpr
      (Or.inl (by decide : ((0, 1, 1, 0), .p13) ∈
        outwardYZCanonicalRepairTargetLobe))
  · decide

def outwardYZCanonicalRepairSpatialPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨outwardYZCanonicalRepairSwitchSpatialPivot,
    outwardYZCanonicalRepairSpatialPivot_mem_boundaryCompleteSlabLinks⟩

def outwardYZCanonicalRepairTemporalPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨outwardYZCanonicalRepairSwitchTemporalPivot,
    outwardYZCanonicalRepairTemporalPivot_mem_boundaryCompleteSlabLinks⟩

private theorem outwardYZCanonicalRepairPackageAtSpatialPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical linked).kernel.weight
          source target := by
  have hlinked : linked = outwardYZCanonicalRepairSpatialPivotLinked :=
    Subtype.ext hlink
  subst linked
  simpa only [outwardYZCanonicalRepairSpatialPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    outwardYZCanonicalRepairSwitchSpatialPivot_degree_five] using
      (outwardYZCanonicalRepairSpatialPivot_kernel_pos source target)

private theorem outwardYZCanonicalRepairPackageAtTemporalPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical linked).kernel.weight
          source target := by
  have hlinked : linked = outwardYZCanonicalRepairTemporalPivotLinked :=
    Subtype.ext hlink
  subst linked
  simpa only [outwardYZCanonicalRepairTemporalPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    outwardYZCanonicalRepairSwitchTemporalPivot_degree_five] using
      (outwardYZCanonicalRepairTemporalPivot_kernel_pos source target)

private theorem outwardYZCanonicalRepairPackageAtNonpivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hneSpatial : linked.1 ≠
      outwardYZCanonicalRepairSwitchSpatialPivot)
    (hneTemporal : linked.1 ≠
      outwardYZCanonicalRepairSwitchTemporalPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical linked).kernel.weight
          source target := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackage_sparse_pos
    (slabPhysicalPairRecouplingDataAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked)
    (outwardYZCanonicalRepairSwitch_nonpivot_sparseFundamentalWord
      linked.1 hneSpatial hneTemporal)
    (outwardYZCanonicalRepairSwitchRight_sparseFundamentalWord linked.1)
    source target

theorem outwardYZCanonicalRepairSwitchPackageAtLink_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      outwardYZCanonicalRepairSwitchLeftPhysical
      outwardYZCanonicalRepairSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        outwardYZCanonicalRepairSwitchLeftPhysical
        outwardYZCanonicalRepairSwitchRightPhysical linked).kernel.weight
          source target := by
  by_cases hspatial :
      linked.1 = outwardYZCanonicalRepairSwitchSpatialPivot
  · exact outwardYZCanonicalRepairPackageAtSpatialPivot_pos
      linked hspatial source target
  · by_cases htemporal :
        linked.1 = outwardYZCanonicalRepairSwitchTemporalPivot
    · exact outwardYZCanonicalRepairPackageAtTemporalPivot_pos
        linked htemporal source target
    · exact outwardYZCanonicalRepairPackageAtNonpivot_pos
        linked hspatial htemporal source target

/-! ## 3. Complete heterogeneous products -/

theorem outwardYZCanonicalRepairSwitchCoordinatewisePositive :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) →
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchRightPhysical linked)) →
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchRightPhysical linked)) →
    FiniteBistochasticCoordinatewisePositive source target
  | [], _, _ => True.intro
  | linked :: rest, source, target =>
      ⟨outwardYZCanonicalRepairSwitchPackageAtLink_pos
          linked source.1 target.1,
        outwardYZCanonicalRepairSwitchCoordinatewisePositive
          rest source.2 target.2⟩

theorem outwardYZCanonicalRepairSwitchProductWeight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchRightPhysical linked))
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          outwardYZCanonicalRepairSwitchLeftPhysical
          outwardYZCanonicalRepairSwitchRightPhysical linked)) :
    (0 : Q') < finiteBistochasticProductWeight source target :=
  finiteBistochasticProductWeight_pos_of_coordinatewise source target
    (outwardYZCanonicalRepairSwitchCoordinatewisePositive
      linkedList source target)

#print axioms outwardYZCanonicalRepairSpatialPivot_kernel_floor
#print axioms outwardYZCanonicalRepairTemporalPivot_kernel_floor
#print axioms outwardYZCanonicalRepairSwitchRight_sparseFundamentalWord
#print axioms outwardYZCanonicalRepairSwitchPackageAtLink_pos
#print axioms outwardYZCanonicalRepairSwitchCoordinatewisePositive
#print axioms outwardYZCanonicalRepairSwitchProductWeight_pos

end YMGap.Continuum.Z4OutwardYZTwoPivotCanonicalRepairSlabWholeProductPositivity
