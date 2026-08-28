/-
# Every column of the reflected bent-cube recoupling row is positive

At the unique pivot, the internal-vacuum valence-five theorem gives the exact
`1/4` floor for the word `(1,0,1,1,1)` against vacuum.  Every other link has
sparse fundamental words in both replicas and hence a strictly positive
local entry.  Structural recursion contracts these statements to strict
positivity of every selected finite product column.

Constructive contract: exact finite geometry and proved local SU(2) entries
only; no choice, `Classical`, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabInternalVacuumValenceFiveRecouplingFloor
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

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
open YMGap.Continuum.SU2SlabInternalVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4DyadicUnitCubeBlockGeometry
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchCutCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile

/-! ## 1. Literal pivot labels and their quarter-floor -/

private theorem reflectedBentSwitchLeftExternalSpins_eq :
    slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
        reflectedBentSwitchPivot =
      externalSpinsOfList [1, 0, 1, 1, 1] := by
  unfold slabLinkExternalSpins reflectedBentSwitchLeftPhysical
  change externalSpinsOfList
      ((slabIncidentPlaqIds 5 reflectedBentSwitchPivot).map
        (slabBinarySupportLabelling 5
          YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface)) =
    externalSpinsOfList [1, 0, 1, 1, 1]
  rw [reflectedBentSwitchPivot_spinList]

theorem reflectedBentSwitchPivot_leftExternal_zero :
    (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
      reflectedBentSwitchPivot) 0 = 1 := by
  rw [reflectedBentSwitchLeftExternalSpins_eq]
  rfl

theorem reflectedBentSwitchPivot_leftExternal_one :
    (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
      reflectedBentSwitchPivot) 1 = 0 := by
  rw [reflectedBentSwitchLeftExternalSpins_eq]
  rfl

theorem reflectedBentSwitchPivot_leftExternal_two :
    (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
      reflectedBentSwitchPivot) 2 = 1 := by
  rw [reflectedBentSwitchLeftExternalSpins_eq]
  rfl

theorem reflectedBentSwitchPivot_leftExternal_three :
    (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
      reflectedBentSwitchPivot) 3 = 1 := by
  rw [reflectedBentSwitchLeftExternalSpins_eq]
  rfl

theorem reflectedBentSwitchPivot_leftExternal_four :
    (slabLinkExternalSpins 5 reflectedBentSwitchLeftPhysical
      reflectedBentSwitchPivot) 4 = 1 := by
  rw [reflectedBentSwitchLeftExternalSpins_eq]
  rfl

theorem reflectedBentSwitchPivot_rightExternal_zero :
    (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
      reflectedBentSwitchPivot) 0 = 0 := by decide

theorem reflectedBentSwitchPivot_rightExternal_one :
    (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
      reflectedBentSwitchPivot) 1 = 0 := by decide

theorem reflectedBentSwitchPivot_rightExternal_two :
    (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
      reflectedBentSwitchPivot) 2 = 0 := by decide

theorem reflectedBentSwitchPivot_rightExternal_three :
    (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
      reflectedBentSwitchPivot) 3 = 0 := by decide

theorem reflectedBentSwitchPivot_rightExternal_four :
    (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical
      reflectedBentSwitchPivot) 4 = 0 := by decide

theorem reflectedBentSwitchPivot_kernel_floor
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Target) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingKernelPackageFive
        reflectedBentSwitchPivotRecouplingData).kernel.weight
          source target :=
  slabPhysicalPairRecouplingKernelPackageFive_internalVacuum_floor
    reflectedBentSwitchPivotRecouplingData
    reflectedBentSwitchPivot_leftExternal_zero
    reflectedBentSwitchPivot_leftExternal_one
    reflectedBentSwitchPivot_leftExternal_two
    reflectedBentSwitchPivot_leftExternal_three
    reflectedBentSwitchPivot_leftExternal_four
    reflectedBentSwitchPivot_rightExternal_zero
    reflectedBentSwitchPivot_rightExternal_one
    reflectedBentSwitchPivot_rightExternal_two
    reflectedBentSwitchPivot_rightExternal_three
    reflectedBentSwitchPivot_rightExternal_four source target

theorem reflectedBentSwitchPivot_kernel_pos
    (source : (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Source)
    (target : (slabPhysicalPairRecouplingKernelPackageFive
      reflectedBentSwitchPivotRecouplingData).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingKernelPackageFive
        reflectedBentSwitchPivotRecouplingData).kernel.weight
          source target :=
  Q'.pos_of_lt_of_le (by decide : (0 : Q') < oneQuarter)
    (reflectedBentSwitchPivot_kernel_floor source target)

/-! ## 2. Sparse nonpivot coordinates -/

theorem reflectedBentSwitchRight_sparseFundamentalWord (link : Z4Link) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5 reflectedBentSwitchRightPhysical link) := by
  change SparseFundamentalWord
    (slabIncidentPlaqIds 5 link).length
    (slabLinkExternalSpins 5 (slabBinarySupportLabelling 5 []) link)
  exact slabBinarySupport_sparseFundamentalWord
    (extent := 5) (support := [])
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil (fun _ => rfl)
    link (by change 0 ≤ 2; omega)

theorem reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks :
    reflectedBentSwitchPivot ∈ boundaryCompleteSlabLinks 5 := by
  apply (mem_boundaryCompleteSlabLinks_iff
    5 reflectedBentSwitchPivot).mpr
  refine ⟨reflectedBentRootPlaquette, ?_, ?_⟩
  · apply YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile.reflectedBentSwitchSurface_subset_slab_five
    exact List.mem_append.mpr (Or.inl reflectedBentRoot_mem)
  · decide

def reflectedBentSwitchPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨reflectedBentSwitchPivot,
    reflectedBentSwitchPivot_mem_boundaryCompleteSlabLinks⟩

private theorem reflectedBentSwitchPackageAtPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = reflectedBentSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
        linked).kernel.weight source target := by
  have hlinked : linked = reflectedBentSwitchPivotLinked := Subtype.ext hlink
  subst linked
  simpa only [reflectedBentSwitchPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    reflectedBentSwitchPivot_degree_five] using
      (reflectedBentSwitchPivot_kernel_pos source target)

private theorem reflectedBentSwitchPackageAtNonpivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 ≠ reflectedBentSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
        linked).kernel.weight source target := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackage_sparse_pos
    (slabPhysicalPairRecouplingDataAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked)
    (reflectedBentSwitch_nonpivot_sparseFundamentalWord linked.1 hlink)
    (reflectedBentSwitchRight_sparseFundamentalWord linked.1)
    source target

theorem reflectedBentSwitchPackageAtLink_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
      linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
        linked).kernel.weight source target := by
  by_cases hlink : linked.1 = reflectedBentSwitchPivot
  · exact reflectedBentSwitchPackageAtPivot_pos linked hlink source target
  · exact reflectedBentSwitchPackageAtNonpivot_pos
      linked hlink source target

/-! ## 3. Complete heterogeneous products -/

theorem reflectedBentSwitchCoordinatewisePositive :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) ->
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical linked)) ->
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical linked)) ->
    FiniteBistochasticCoordinatewisePositive source target
  | [], _, _ => True.intro
  | linked :: rest, source, target =>
      ⟨reflectedBentSwitchPackageAtLink_pos linked source.1 target.1,
        reflectedBentSwitchCoordinatewisePositive rest source.2 target.2⟩

theorem reflectedBentSwitchProductWeight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical linked))
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical linked)) :
    (0 : Q') < finiteBistochasticProductWeight source target :=
  finiteBistochasticProductWeight_pos_of_coordinatewise source target
    (reflectedBentSwitchCoordinatewisePositive linkedList source target)

#print axioms reflectedBentSwitchPivot_kernel_floor
#print axioms reflectedBentSwitchRight_sparseFundamentalWord
#print axioms reflectedBentSwitchPackageAtLink_pos
#print axioms reflectedBentSwitchCoordinatewisePositive
#print axioms reflectedBentSwitchProductWeight_pos

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity
