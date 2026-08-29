/-
# The guarded observable graft is a connected source

The guarded graft retains the complete reflected-bent support path joining
the two marked faces.  Its peeled exterior background may add support
vertices, but it cannot remove any vertex of that path.  Monotonicity of a
finite graph chain therefore places the marked root in the target-rooted
component of the grafted union support.

This packages the guarded observable `11 x 00` pair as the literal connected
strand source consumed by the good-source repair interface, uniformly over
the input accepted state.

Constructive contract: explicit finite graph chains and rooted-component
closure only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource
open YMGap.Continuum.CompactDualSlabBinarySupportConnectedSource.SlabBinarySupportConnectedCarrier
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabPivotCarrier

/-! ## 1. A chain remains inside its rooted component -/

private def chainLast_mem_rootComponent
    {A : Type} [DecidableEq A]
    (adjacent : A → A → Bool) (hsymmetric : SymmetricAdj adjacent)
    (vertices : List A) (root : A) (hroot : root ∈ vertices) :
    {first last : A} → ChainIn adjacent vertices first last →
      first ∈ rootComponent adjacent vertices root →
      last ∈ rootComponent adjacent vertices root
  | _, _, .refl _, hfirst => hfirst
  | _, _, .step hedge hnext rest, hfirst =>
      chainLast_mem_rootComponent adjacent hsymmetric vertices root hroot
        rest
        (rootComponent_closed_under_edge adjacent hsymmetric
          hroot hfirst hnext hedge)

/-! ## 2. The old marked path survives in the graft -/

private theorem reflectedBentPatternComponent_subset_graftSupport
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ faceId,
      faceId ∈ slabTwoReplicaTargetSupportComponent 5
          reflectedBentSwitchLeftPhysical
          reflectedBentSwitchRightPhysical
          reflectedBentTargetFaceId →
        faceId ∈ slabTwoReplicaSupportFaceVertices 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state) := by
  intro faceId hcomponent
  have htargetOld : reflectedBentTargetFaceId ∈
      slabTwoReplicaSupportFaceVertices 5
        reflectedBentSwitchLeftPhysical
        reflectedBentSwitchRightPhysical := by
    exact mem_slabTwoReplicaSupportFaceVertices
      reflectedBentTargetFaceId_physical
      (Or.inl ((mem_reflectedBentPatternFaceIds_iff
        reflectedBentTargetFaceId_physical).mp
          reflectedBentTargetFaceId_mem_pattern))
  have hsupportOld := rootComponent_subset
    (slabSupportFaceAdjacentB 5) htargetOld hcomponent
  have hparts := List.mem_filter.mp hsupportOld
  have hpositiveOld :
      0 < reflectedBentSwitchLeftPhysical faceId ∨
        0 < reflectedBentSwitchRightPhysical faceId := by
    exact of_decide_eq_true hparts.2
  have hleftPositive : 0 < reflectedBentSwitchLeftPhysical faceId := by
    rcases hpositiveOld with hleft | hright
    · exact hleft
    · rw [reflectedBentSwitchRightPhysical_eq_zero] at hright
      omega
  have hgraftPositive :
      0 < reflectedBentGuardGraftLeftPhysical D hextent state faceId := by
    unfold reflectedBentGuardGraftLeftPhysical
    rw [if_pos hleftPositive]
    exact hleftPositive
  exact mem_slabTwoReplicaSupportFaceVertices hparts.1
    (Or.inl hgraftPositive)

theorem reflectedBentGuardGraft_root_mem_targetSupportComponent
    (D : SlabPhysicalData) (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentRootFaceId ∈
      slabTwoReplicaTargetSupportComponent 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        reflectedBentTargetFaceId := by
  let adjacent := slabSupportFaceAdjacentB 5
  let oldVertices := slabTwoReplicaSupportFaceVertices 5
    reflectedBentSwitchLeftPhysical reflectedBentSwitchRightPhysical
  let newVertices := slabTwoReplicaSupportFaceVertices 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
  have htargetOld : reflectedBentTargetFaceId ∈ oldVertices := by
    exact mem_slabTwoReplicaSupportFaceVertices
      reflectedBentTargetFaceId_physical
      (Or.inl ((mem_reflectedBentPatternFaceIds_iff
        reflectedBentTargetFaceId_physical).mp
          reflectedBentTargetFaceId_mem_pattern))
  have hrootOld : reflectedBentRootFaceId ∈
      rootComponent adjacent oldVertices reflectedBentTargetFaceId := by
    have hcomponent :=
      reflectedBentBinaryConnectedCarrier.root_mem_targetSupportComponent
    rw [reflectedBentCarrier_leftPhysical,
      reflectedBentCarrier_rightPhysical] at hcomponent
    exact hcomponent
  have hchainOld : ChainIn adjacent
      (rootComponent adjacent oldVertices reflectedBentTargetFaceId)
      reflectedBentTargetFaceId reflectedBentRootFaceId :=
    rootComponent_connected adjacent
      (slabSupportFaceAdjacentB_symmetric 5)
      htargetOld reflectedBentTargetFaceId reflectedBentRootFaceId
      (root_mem_rootComponent adjacent htargetOld) hrootOld
  have hchainNew : ChainIn adjacent newVertices
      reflectedBentTargetFaceId reflectedBentRootFaceId :=
    ChainIn.mono
      (reflectedBentPatternComponent_subset_graftSupport
        D hextent state) hchainOld
  have htargetNew : reflectedBentTargetFaceId ∈ newVertices := by
    exact mem_slabTwoReplicaSupportFaceVertices
      reflectedBentTargetFaceId_physical
      (Or.inl
        (reflectedBentGuardGraftLeftPhysical_target_pos
          D hextent state))
  exact chainLast_mem_rootComponent adjacent
    (slabSupportFaceAdjacentB_symmetric 5)
    newVertices reflectedBentTargetFaceId htargetNew hchainNew
    (root_mem_rootComponent adjacent htargetNew)

/-! ## 3. Literal connected-source packaging -/

theorem reflectedBentGuardGraftObservableSourcePair_connected
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableSourcePair
        D hcutoff hextent state) = true := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask
    reflectedBentGuardGraftObservableSourcePair
  rw [reflectedBentGuardGraftLeftPositiveEntry_physical,
    reflectedBentGuardGraftRightExpandedEntry_physical]
  rw [hextent]
  exact decide_eq_true
    (reflectedBentGuardGraft_root_mem_targetSupportComponent
      D hextent state)

theorem reflectedBentGuardGraftObservableSourcePair_mem_connected
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableSourcePair D hcutoff hextent state ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        D reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  exact ⟨reflectedBentGuardGraftObservableSourcePair_mem_fourCell
      D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePair_connected
      D hcutoff hextent state⟩

def reflectedBentGuardGraftConnectedStrandSource
    (D : SlabPhysicalData) (hcutoff : D.cutoff = 1)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  ⟨reflectedBentGuardGraftObservableSourcePair D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePair_mem_connected
      D hcutoff hextent state⟩

#print axioms reflectedBentGuardGraft_root_mem_targetSupportComponent
#print axioms reflectedBentGuardGraftObservableSourcePair_connected
#print axioms reflectedBentGuardGraftObservableSourcePair_mem_connected
#print axioms reflectedBentGuardGraftConnectedStrandSource

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
