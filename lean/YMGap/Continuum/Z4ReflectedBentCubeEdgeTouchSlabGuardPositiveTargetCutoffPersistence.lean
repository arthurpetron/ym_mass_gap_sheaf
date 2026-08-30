/-
# Positive guarded-graft rows at every cutoff at least one

The reflected graft is now an accepted source at every ambient cutoff at
least one.  Use that ambient-cutoff acceptance to form the actual local
recoupling source at every slab link.  The existing positive-target selector
then applies without changing its mathematics: at the exceptional pivot it
uses the explicit component-preserving low-spin column, and elsewhere it uses
finite bistochastic row positivity for the actual ambient source.

This proves a strictly positive target product at each finite cutoff.  It is
qualitative positivity, not a cutoff-uniform positive lower bound.

Constructive contract: accepted ambient-cutoff sources, the existing explicit
pivot column, normalized finite-row search, and finite product recursion only;
no `Classical`, choice, `native_decide`, `sorry`, new axiom, noncomputable
declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabFineIntertwinerWitness
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.FiniteBistochasticQKernelProductPositivity
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingKernel
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingSourceCompleteness
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingProduct
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetNodup
open YMGap.Continuum.SU2SlabPhysicalPairRecouplingTargetRealization
open YMGap.Continuum.SU2SlabInternalVacuumValenceFiveRecouplingFloor
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4HalfTimeReflectionIncidenceReindex
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPhysicalGraft
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTarget
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabSwitchingProfile
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

/-! ## 1. The actual ambient-cutoff graft row -/

theorem reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLeftAssignment D hextent state ∈
      slabFusionWitnessAssignmentsOn D.cutoff 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (boundaryCompleteSlabLinks 5) := by
  have hmem := reflectedBentGuardGraftLeftAssignment_mem_of_one_le
    D hcutoff hextent state
  unfold slabFineFusionWitnesses at hmem
  simpa only [hextent] using hmem

theorem reflectedBentGuardGraftRightAssignment_mem_at_cutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftRightAssignment D hextent state ∈
      slabFusionWitnessAssignmentsOn D.cutoff 5
        (reflectedBentGuardGraftRightPhysical D hextent state)
        (boundaryCompleteSlabLinks 5) := by
  have hmem := reflectedBentGuardGraftRightAssignment_mem_of_one_le
    D hcutoff hextent state
  unfold slabFineFusionWitnesses at hmem
  simpa only [hextent] using hmem

def reflectedBentGuardGraftLocalAnchorAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingWitnessDataAtLink D.cutoff 5
    (reflectedBentGuardGraftLeftPhysical D hextent state)
    (reflectedBentGuardGraftRightPhysical D hextent state)
    (reflectedBentGuardGraftLeftAssignment D hextent state)
    (reflectedBentGuardGraftRightAssignment D hextent state)
    (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
      D hcutoff hextent state)
    (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
      D hcutoff hextent state) linked

def reflectedBentGuardGraftLocalSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  slabPhysicalPairRecouplingProductionSource
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    (reflectedBentGuardGraftLocalAnchorAtCutoff
      D hcutoff hextent state linked)

/-! ## 2. Reuse the positive target selector at the ambient source -/

def reflectedBentGuardGraftLocalTargetAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :=
  reflectedBentGuardGraftTargetForData D hextent state
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    rfl rfl
    (reflectedBentGuardGraftLocalSourceAtCutoff
      D hcutoff hextent state linked)

theorem reflectedBentGuardGraftLocalTargetAtCutoff_pos
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (0 : Q') <
      (slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked).kernel.weight
        (reflectedBentGuardGraftLocalSourceAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked) :=
  reflectedBentGuardGraftTargetForData_pos D hextent state
    (slabIncidentPlaqIds 5 linked.1).length
    (reflectedBentGuardGraftLocalData D hextent state linked)
    rfl rfl
    (reflectedBentGuardGraftLocalSourceAtCutoff
      D hcutoff hextent state linked)

/-- At the unique non-abelian pivot, the actual ambient-cutoff production row
retains the explicit quarter floor.  The estimate is independent of every
auxiliary spin admitted by the ambient cutoff. -/
theorem reflectedBentGuardGraftLocalTargetAtCutoff_floor_of_pivot
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linked : {link // link ∈ boundaryCompleteSlabLinks 5})
    (hpivot : linked.1 = reflectedBentSwitchPivot) :
    oneQuarter ≤
      (slabPhysicalPairRecouplingPackageAtLink 5
        (reflectedBentGuardGraftLeftPhysical D hextent state)
        (reflectedBentGuardGraftRightPhysical D hextent state)
        linked).kernel.weight
        (reflectedBentGuardGraftLocalSourceAtCutoff
          D hcutoff hextent state linked)
        (reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked) := by
  have hlinked : linked = reflectedBentSwitchPivotLinked :=
    Subtype.ext hpivot
  subst linked
  unfold slabPhysicalPairRecouplingPackageAtLink
    reflectedBentSwitchPivotLinked
  have hdegree : 5 =
      (slabIncidentPlaqIds 5 reflectedBentSwitchPivot).length :=
    reflectedBentSwitchPivot_degree_five.symm
  cases hdegree
  change oneQuarter ≤
    (slabPhysicalPairRecouplingKernelPackageFive
      (reflectedBentGuardGraftPivotRecouplingData
        D hextent state)).kernel.weight _ _
  exact reflectedBentGuardGraftPivot_kernel_floor
    D hextent state
    (reflectedBentGuardGraftLocalSourceAtCutoff
      D hcutoff hextent state reflectedBentSwitchPivotLinked)
    (reflectedBentGuardGraftLocalTargetAtCutoff
      D hcutoff hextent state reflectedBentSwitchPivotLinked)

/-! ## 3. The positive whole-slab product at ambient cutoff -/

def reflectedBentGuardGraftTargetAssignmentFromAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) →
      FiniteBistochasticTargetAssignment
        (linkedList.map fun linked =>
          slabPhysicalPairRecouplingPackageAtLink 5
            (reflectedBentGuardGraftLeftPhysical D hextent state)
            (reflectedBentGuardGraftRightPhysical D hextent state)
            linked)
  | [] => ()
  | linked :: rest =>
      (reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked,
        reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state rest)

theorem reflectedBentGuardGraftTargetAssignmentFromAtCutoff_mem
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5},
      reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state linkedList ∈
        finiteBistochasticTargetAssignments
          (linkedList.map fun linked =>
            slabPhysicalPairRecouplingPackageAtLink 5
              (reflectedBentGuardGraftLeftPhysical D hextent state)
              (reflectedBentGuardGraftRightPhysical D hextent state)
              linked)
  | [] => List.mem_cons_self
  | linked :: rest => by
      simp only [List.map_cons, finiteBistochasticTargetAssignments,
        reflectedBentGuardGraftTargetAssignmentFromAtCutoff]
      apply List.mem_flatMap.mpr
      refine ⟨reflectedBentGuardGraftLocalTargetAtCutoff
          D hcutoff hextent state linked, ?_, ?_⟩
      · unfold slabPhysicalPairRecouplingPackageAtLink
        exact slabPhysicalPairRecouplingTarget_mem
          (slabIncidentPlaqIds 5 linked.1).length
          (reflectedBentGuardGraftLocalData D hextent state linked)
          (reflectedBentGuardGraftLocalTargetAtCutoff
            D hcutoff hextent state linked)
      · exact List.mem_map.mpr
          ⟨reflectedBentGuardGraftTargetAssignmentFromAtCutoff
              D hcutoff hextent state rest,
            reflectedBentGuardGraftTargetAssignmentFromAtCutoff_mem
              D hcutoff hextent state rest, rfl⟩

theorem reflectedBentGuardGraftTargetAssignmentFromAtCutoff_coordinatewise_pos
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ∀ linkedList : List
        {link // link ∈ boundaryCompleteSlabLinks 5},
      FiniteBistochasticCoordinatewisePositive
        (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (reflectedBentGuardGraftLeftAssignment D hextent state)
          (reflectedBentGuardGraftRightAssignment D hextent state)
          (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
            D hcutoff hextent state)
          (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
            D hcutoff hextent state)
          linkedList)
        (reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state linkedList)
  | [] => True.intro
  | linked :: rest => by
      constructor
      · exact reflectedBentGuardGraftLocalTargetAtCutoff_pos
          D hcutoff hextent state linked
      · exact
          reflectedBentGuardGraftTargetAssignmentFromAtCutoff_coordinatewise_pos
            D hcutoff hextent state rest

theorem reflectedBentGuardGraftTargetAssignmentFromAtCutoff_weight_pos
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5}) :
    (0 : Q') <
      finiteBistochasticProductWeight
        (slabPhysicalPairRecouplingProductionSourceFrom D.cutoff 5
          (reflectedBentGuardGraftLeftPhysical D hextent state)
          (reflectedBentGuardGraftRightPhysical D hextent state)
          (reflectedBentGuardGraftLeftAssignment D hextent state)
          (reflectedBentGuardGraftRightAssignment D hextent state)
          (reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
            D hcutoff hextent state)
          (reflectedBentGuardGraftRightAssignment_mem_at_cutoff
            D hcutoff hextent state)
          linkedList)
        (reflectedBentGuardGraftTargetAssignmentFromAtCutoff
          D hcutoff hextent state linkedList) :=
  finiteBistochasticProductWeight_pos_of_coordinatewise _ _
    (reflectedBentGuardGraftTargetAssignmentFromAtCutoff_coordinatewise_pos
      D hcutoff hextent state linkedList)

#print axioms reflectedBentGuardGraftLeftAssignment_mem_at_cutoff
#print axioms reflectedBentGuardGraftRightAssignment_mem_at_cutoff
#print axioms reflectedBentGuardGraftLocalTargetAtCutoff_pos
#print axioms reflectedBentGuardGraftLocalTargetAtCutoff_floor_of_pivot
#print axioms reflectedBentGuardGraftTargetAssignmentFromAtCutoff_mem
#print axioms reflectedBentGuardGraftTargetAssignmentFromAtCutoff_coordinatewise_pos
#print axioms reflectedBentGuardGraftTargetAssignmentFromAtCutoff_weight_pos

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetCutoffPersistence
