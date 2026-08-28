/-
# The seven-cube switching row is positive in every whole-product column

The selected seven-cube surface has one exceptional slab link.  Every other
link carries a sparse word on the left replica and the vacuum sparse word on
the right, so its complete local recoupling matrix is pointwise the identity.
At the exceptional link the concrete valence-five theorem supplies the sole
nontrivial lower bound `1/4`.

This module performs the dependent finite-product contraction.  It proves
coordinatewise positivity for every target column above the seven-cube
physical pair, independently of the accepted auxiliary assignments selecting
the source row.  The remaining positive-channel obligation is therefore
purely topological: exhibit a compatible target whose realized strand graph
disconnects the marked faces.

Constructive contract: structural recursion over the literal attached slab
links, exact finite geometry, and proved SU(2) matrix entries only; no choice,
`Classical`, `native_decide`, `sorry`, new axiom, or unbounded heartbeat.
-/

import YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
import YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
import YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor

namespace YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity

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
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabSparseFundamentalPairedRecouplingIdentity
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4OutwardSevenCubeSlabPivotRecouplingFloor
open YMGap.Continuum.Z4OutwardSevenCubeSlabSwitchingProfile
open YMGap.Continuum.Z4OutwardSevenCubeCycleGeometry
open YMGap.Continuum.Z4ExplicitCutoffOneSurfaceSelection
open YMGap.Continuum.Z4CutoffOneLocalMultiplicityCount
open YMGap.Continuum.Z4FusionPathZeroInsertion
open YMGap.Continuum.Z4UnitCubeIncidenceParity
open YMGap.Continuum.Z4ValenceFusionCutoffIndependence

/-! ## 1. The vacuum replica is sparse at every link -/

theorem sevenCubeSwitchRight_sparseFundamentalWord (link : Z4Link) :
    SparseFundamentalWord
      (slabIncidentPlaqIds 5 link).length
      (slabLinkExternalSpins 5 sevenCubeSwitchRightPhysical link) := by
  change SparseFundamentalWord
    (slabIncidentPlaqIds 5 link).length
    (slabLinkExternalSpins 5 (slabBinarySupportLabelling 5 []) link)
  exact slabBinarySupport_sparseFundamentalWord
    (extent := 5) (support := [])
    (fun plaquette hmem => False.elim (List.not_mem_nil hmem))
    List.nodup_nil
    (fun _ => rfl)
    link (by change 0 ≤ 2; omega)

/-! ## 2. Each literal local coordinate is positive -/

theorem sevenCubeSwitchPivot_mem_boundaryCompleteSlabLinks :
    sevenCubeSwitchPivot ∈ boundaryCompleteSlabLinks 5 := by
  obtain ⟨plaquette, hplaquette, hedge⟩ :=
    mem_geometricTouchedLinks.mp sevenCubeCycle_fourLinks_mem_touched.1
  apply (mem_boundaryCompleteSlabLinks_iff 5 sevenCubeSwitchPivot).mpr
  exact ⟨plaquette,
    sevenCubeSwitchSurface_subset_slab_five plaquette hplaquette, hedge⟩

def sevenCubeSwitchPivotLinked :
    {link // link ∈ boundaryCompleteSlabLinks 5} :=
  ⟨sevenCubeSwitchPivot,
    sevenCubeSwitchPivot_mem_boundaryCompleteSlabLinks⟩

private theorem sevenCubeSwitchPackageAtPivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 = sevenCubeSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).kernel.weight
          source target := by
  have hlinked : linked = sevenCubeSwitchPivotLinked :=
    Subtype.ext hlink
  subst linked
  simpa only [sevenCubeSwitchPivotLinked,
    slabPhysicalPairRecouplingPackageAtLink,
    slabPhysicalPairRecouplingDataAtLink,
    sevenCubeSwitchPivot_degree_five] using
      (sevenCubeSwitchPivot_kernel_pos source target)

private theorem sevenCubeSwitchPackageAtNonpivot_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hlink : linked.1 ≠ sevenCubeSwitchPivot)
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).kernel.weight
          source target := by
  unfold slabPhysicalPairRecouplingPackageAtLink
  exact slabPhysicalPairRecouplingKernelPackage_sparse_pos
    (slabPhysicalPairRecouplingDataAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked)
    (sevenCubeSwitch_nonpivot_sparseFundamentalWord linked.1 hlink)
    (sevenCubeSwitchRight_sparseFundamentalWord linked.1)
    source target

theorem sevenCubeSwitchPackageAtLink_pos
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Source)
    (target : (slabPhysicalPairRecouplingPackageAtLink 5
      sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).Target) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked).kernel.weight
          source target := by
  by_cases hlink : linked.1 = sevenCubeSwitchPivot
  · exact sevenCubeSwitchPackageAtPivot_pos linked hlink source target
  · exact sevenCubeSwitchPackageAtNonpivot_pos linked hlink source target

/-! ## 3. Contract the literal whole product -/

theorem sevenCubeSwitchCoordinatewisePositive :
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5}) →
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked)) →
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked)) →
    FiniteBistochasticCoordinatewisePositive source target
  | [], _, _ => True.intro
  | linked :: rest, source, target =>
      ⟨sevenCubeSwitchPackageAtLink_pos linked source.1 target.1,
        sevenCubeSwitchCoordinatewisePositive rest source.2 target.2⟩

/-- The exact product entry is positive over every displayed sublist of actual
slab links.  Instantiating `linkedList` with
`(boundaryCompleteSlabLinks 5).attach` is the literal whole-slab matrix. -/
theorem sevenCubeSwitchProductWeight_pos
    (linkedList : List {link // link ∈ boundaryCompleteSlabLinks 5})
    (source : FiniteBistochasticSourceAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked))
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          sevenCubeSwitchLeftPhysical sevenCubeSwitchRightPhysical linked)) :
    (0 : Q') < finiteBistochasticProductWeight source target := by
  exact finiteBistochasticProductWeight_pos_of_coordinatewise
    source target
    (sevenCubeSwitchCoordinatewisePositive linkedList source target)

end YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity

#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity.sevenCubeSwitchRight_sparseFundamentalWord
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity.sevenCubeSwitchPackageAtLink_pos
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity.sevenCubeSwitchCoordinatewisePositive
#print axioms YMGap.Continuum.Z4OutwardSevenCubeSlabWholeProductPositivity.sevenCubeSwitchProductWeight_pos
