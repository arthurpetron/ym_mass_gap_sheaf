/-
# Every target in the pivot cylinder disconnects the marked faces

Every projected edge in the parametric realized graph preserves the near/far
color.  Hence every finite graph chain preserves that color, while the marked
root and target faces have opposite colors.  This contracts the local strand
geometry into a data-bearing disconnection certificate for each cylinder
target.

Constructive contract: finite Boolean adjacency and structural recursion on
explicit chains only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderAbstractGraph
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedFaceSupportRefinement
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderAbstractGraph
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderWeight
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetDisconnection
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetEdges
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

def reflectedBentGuardGraftPivotCylinderFaceVerticesFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : List Nat :=
  (reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
    D hcutoff hextent state linkedList target).flatMap fun edge =>
      [edge.source, edge.target]

def reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (left right : Nat) : Bool :=
  slabProjectedFaceAdjacentB
    (reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target) left right

theorem reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (hcylinder : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList)
    {left right : Nat}
    (hadj : reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTargetAtCutoff
      D hcutoff hextent state linkedList target left right = true) :
    reflectedBentGuardTargetFaceColorB left =
      reflectedBentGuardTargetFaceColorB right := by
  obtain ⟨projected, hprojected, horientation⟩ :=
    slabProjectedFaceAdjacentEdgeWitness left right
      (reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) hadj
  have hcolor :=
    reflectedBentGuardGraftPivotCylinderProjectedFaceEdgeFromTarget_color_eq
      D hcutoff hextent state linkedList target hnodup hpivot hcylinder
        projected hprojected
  cases horientation with
  | inl hforward =>
      rw [← hforward.1, ← hforward.2]
      exact hcolor
  | inr hreverse =>
      rw [← hreverse.2, ← hreverse.1]
      exact hcolor.symm

theorem reflectedBentGuardGraftPivotCylinderChainFromTarget_color_eq
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (hcylinder : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList)
    {first last : Nat}
    (path : ChainIn
      (reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      (reflectedBentGuardGraftPivotCylinderFaceVerticesFromTargetAtCutoff
        D hcutoff hextent state linkedList target) first last) :
    reflectedBentGuardTargetFaceColorB first =
      reflectedBentGuardTargetFaceColorB last := by
  induction path with
  | refl => rfl
  | step hadj _ rest ih =>
      exact
        (reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTarget_color_eq
          D hcutoff hextent state linkedList target hnodup hpivot
            hcylinder hadj).trans ih

def reflectedBentGuardGraftPivotCylinderTarget_noMarkedFaceChainAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (hcylinder : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList) :
    ChainIn
      (reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      (reflectedBentGuardGraftPivotCylinderFaceVerticesFromTargetAtCutoff
        D hcutoff hextent state linkedList target)
      reflectedBentRootFaceId reflectedBentTargetFaceId → False :=
  fun path => by
    have hcolor :=
      reflectedBentGuardGraftPivotCylinderChainFromTarget_color_eq
        D hcutoff hextent state linkedList target hnodup hpivot
          hcylinder path
    rw [reflectedBentGuardGraftPositiveTargetRootFace_color,
      reflectedBentGuardGraftPositiveTargetTargetFace_color] at hcolor
    cases hcolor

structure ReflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked)) : Type where
  targetEdges : List SlabProjectedFaceEdge
  targetEdges_eq : targetEdges =
    reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  everyTargetEdgePreservesColor : ∀ edge, edge ∈ targetEdges →
    reflectedBentGuardTargetFaceColorB edge.source =
      reflectedBentGuardTargetFaceColorB edge.target
  markedDisconnected : ChainIn
    (reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTargetAtCutoff
      D hcutoff hextent state linkedList target)
    (reflectedBentGuardGraftPivotCylinderFaceVerticesFromTargetAtCutoff
      D hcutoff hextent state linkedList target)
    reflectedBentRootFaceId reflectedBentTargetFaceId → False

def reflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (target : FiniteBistochasticTargetAssignment
      (linkedList.map fun linked =>
        slabPhysicalPairRecouplingPackageAtLink 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          linked))
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (hcylinder : target ∈
      reflectedBentGuardGraftPivotCylinderTargetsFromAtCutoff
        D hcutoff hextent state linkedList) :
    ReflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff
      D hcutoff hextent state linkedList target where
  targetEdges :=
    reflectedBentGuardGraftPivotCylinderProjectedFaceEdgesFromTargetAtCutoff
      D hcutoff hextent state linkedList target
  targetEdges_eq := rfl
  everyTargetEdgePreservesColor :=
    reflectedBentGuardGraftPivotCylinderProjectedFaceEdgeFromTarget_color_eq
      D hcutoff hextent state linkedList target hnodup hpivot hcylinder
  markedDisconnected :=
    reflectedBentGuardGraftPivotCylinderTarget_noMarkedFaceChainAtCutoff
      D hcutoff hextent state linkedList target hnodup hpivot hcylinder

#print axioms reflectedBentGuardGraftPivotCylinderFaceAdjacentBFromTarget_color_eq
#print axioms reflectedBentGuardGraftPivotCylinderChainFromTarget_color_eq
#print axioms reflectedBentGuardGraftPivotCylinderTarget_noMarkedFaceChainAtCutoff
#print axioms reflectedBentGuardGraftPivotCylinderTargetDisconnectionAtCutoff

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderDisconnection
