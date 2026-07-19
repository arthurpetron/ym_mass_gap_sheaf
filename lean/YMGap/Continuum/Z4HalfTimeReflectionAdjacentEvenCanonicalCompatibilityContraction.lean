/-
# Canonical incoming/outgoing compatibility contraction

This leaf inserts the choice-free incidence partitions around every literal
mixed trajectory.  The resulting finite expression sums over the canonical
incoming and outgoing assignment carriers and then over the original
trajectory list.  Both assignment sums collapse exactly, preserving the
trajectory list and hence every multiplicity.

The result is the first global reindexing step needed by the rankwise SOS.  It
does not yet regroup the trajectory-major expression by fixed-face Gram rank
or factor the remaining compatibility contraction.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityPartition
import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityContraction

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityPartition
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceBijection
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceChannelCarrier
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryFieldRealization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTrajectoryTerminalField

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Assignment-indexed fixed-face entries -/

/-- The production fixed-face kernel evaluated on two literal symbolic
incidence assignments. -/
def adjacentEvenAssignmentFixedFaceKernel
    (K radius : Nat)
    (incoming outgoing : FixedFaceLinkIncidence → Nat) : Q' :=
  adjacentEvenGlobalDependentFixedFaceChannelKernel K radius
    (adjacentEvenFixedIncidenceAssignmentField radius incoming)
    (adjacentEvenFixedIncidenceAssignmentField radius outgoing)

private theorem assignmentField_congr_on_incidences
    (radius : Nat)
    (left right : FixedFaceLinkIncidence → Nat)
    (hagree : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        left incidence = right incidence) :
    ∀ id link,
      (id, link) ∈ adjacentEvenFixedFaceMajorIncidences radius →
      adjacentEvenFixedIncidenceAssignmentField radius left id link =
        adjacentEvenFixedIncidenceAssignmentField radius right id link := by
  intro id link hincidence
  rw [adjacentEvenFixedIncidenceAssignmentField_of_mem
      radius left hincidence,
    adjacentEvenFixedIncidenceAssignmentField_of_mem
      radius right hincidence]
  exact hagree (id, link) hincidence

theorem adjacentEvenAssignmentFixedFaceKernel_congr_incoming
    (K radius : Nat)
    (incoming incoming' outgoing : FixedFaceLinkIncidence → Nat)
    (hagree : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        incoming incidence = incoming' incidence) :
    adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing ≈
      adjacentEvenAssignmentFixedFaceKernel K radius incoming' outgoing := by
  unfold adjacentEvenAssignmentFixedFaceKernel
  exact adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
    K radius _ _ _ _
    (assignmentField_congr_on_incidences radius incoming incoming' hagree)
    (fun _ _ _ => rfl)

theorem adjacentEvenAssignmentFixedFaceKernel_congr_outgoing
    (K radius : Nat)
    (incoming outgoing outgoing' : FixedFaceLinkIncidence → Nat)
    (hagree : ∀ incidence,
      incidence ∈ adjacentEvenFixedFaceMajorIncidences radius →
        outgoing incidence = outgoing' incidence) :
    adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing ≈
      adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing' := by
  unfold adjacentEvenAssignmentFixedFaceKernel
  exact adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
    K radius _ _ _ _ (fun _ _ _ => rfl)
    (assignmentField_congr_on_incidences radius outgoing outgoing' hagree)

/-! ## 2. The two exact assignment collapses around one trajectory -/

theorem adjacentEvenOutgoingAssignmentDelta_collapse
    {K radius : Nat} {source target : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius)
    (incoming : FixedFaceLinkIncidence → Nat) :
    listQSum
        (fun outgoing =>
          adjacentEvenCanonicalIncidenceDelta radius outgoing
              (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                radius trajectory) *
            (adjacentEvenAssignmentFixedFaceKernel
                K radius incoming outgoing *
              adjacentEvenLinkTerminalProduct
                radius source target trajectory))
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈
      adjacentEvenAssignmentFixedFaceKernel K radius incoming
          (adjacentEvenTrajectoryOutgoingIncidenceAssignment
            radius trajectory) *
        adjacentEvenLinkTerminalProduct
          radius source target trajectory := by
  apply adjacentEvenCanonicalIncidenceDelta_weighted_collapse
    K radius
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
    (adjacentEvenTrajectoryOutgoingIncidenceAssignment_le htrajectory)
  intro candidate hagree
  exact Q'.mul_eqv_congr_right _ _ _
    (adjacentEvenAssignmentFixedFaceKernel_congr_outgoing
      K radius incoming candidate
      (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
      hagree)

theorem adjacentEvenIncomingAssignmentDelta_collapse
    {K radius : Nat} {source target : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    listQSum
        (fun incoming =>
          adjacentEvenCanonicalIncidenceDelta radius incoming
              (adjacentEvenTrajectoryIncomingIncidenceAssignment
                radius source trajectory) *
            (adjacentEvenAssignmentFixedFaceKernel K radius incoming
                (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                  radius trajectory) *
              adjacentEvenLinkTerminalProduct
                radius source target trajectory))
        (adjacentEvenFixedIncidenceChannelAssignments K radius) ≈
      adjacentEvenAssignmentFixedFaceKernel K radius
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory)
          (adjacentEvenTrajectoryOutgoingIncidenceAssignment
            radius trajectory) *
        adjacentEvenLinkTerminalProduct
          radius source target trajectory := by
  apply adjacentEvenCanonicalIncidenceDelta_weighted_collapse
    K radius
    (adjacentEvenTrajectoryIncomingIncidenceAssignment
      radius source trajectory)
    (adjacentEvenTrajectoryIncomingIncidenceAssignment_le
      hsource htrajectory)
  intro candidate hagree
  exact Q'.mul_eqv_congr_right _ _ _
    (adjacentEvenAssignmentFixedFaceKernel_congr_incoming
      K radius candidate
      (adjacentEvenTrajectoryIncomingIncidenceAssignment
        radius source trajectory)
      (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory)
      hagree)

/-- The nested incoming/outgoing canonical partition around one trajectory. -/
def adjacentEvenCanonicalTrajectoryAssignmentTerm
    (K radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQSum
    (fun incoming =>
      adjacentEvenCanonicalIncidenceDelta radius incoming
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory) *
        listQSum
          (fun outgoing =>
            adjacentEvenCanonicalIncidenceDelta radius outgoing
                (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                  radius trajectory) *
              (adjacentEvenAssignmentFixedFaceKernel
                  K radius incoming outgoing *
                adjacentEvenLinkTerminalProduct
                  radius source target trajectory))
          (adjacentEvenFixedIncidenceChannelAssignments K radius))
    (adjacentEvenFixedIncidenceChannelAssignments K radius)

theorem adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_literal
    {K radius : Nat} {source target : Z4Link → Nat}
    {trajectory : FixedIncidenceTrajectoryState}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K)
    (htrajectory : trajectory ∈
      adjacentEvenFixedIncidenceTrajectoryStates K radius) :
    adjacentEvenCanonicalTrajectoryAssignmentTerm
        K radius source target trajectory ≈
      adjacentEvenTrajectoryFixedFaceResummedKernel
          K radius source trajectory *
        adjacentEvenLinkTerminalProduct
          radius source target trajectory := by
  unfold adjacentEvenCanonicalTrajectoryAssignmentTerm
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun incoming =>
        Q'.mul_eqv_congr_left
          (adjacentEvenCanonicalIncidenceDelta radius incoming
            (adjacentEvenTrajectoryIncomingIncidenceAssignment
              radius source trajectory)) _ _
          (adjacentEvenOutgoingAssignmentDelta_collapse
            htrajectory incoming))
      (adjacentEvenFixedIncidenceChannelAssignments K radius)) ?_
  refine Q'.eqv_trans _ _ _
    (adjacentEvenIncomingAssignmentDelta_collapse
      hsource htrajectory) ?_
  apply Q'.mul_eqv_congr_right
  unfold adjacentEvenTrajectoryFixedFaceResummedKernel
  exact adjacentEvenGlobalDependentFixedFaceChannelKernel_congr_on_incidences
      K radius
      (adjacentEvenFixedIncidenceAssignmentField radius
        (adjacentEvenTrajectoryIncomingIncidenceAssignment
          radius source trajectory))
      (adjacentEvenTrajectoryIncomingField radius source trajectory)
      (adjacentEvenFixedIncidenceAssignmentField radius
        (adjacentEvenTrajectoryOutgoingIncidenceAssignment
          radius trajectory))
      (adjacentEvenTrajectoryOutgoingField trajectory)
      (fun id link hincidence =>
        adjacentEvenTrajectoryIncomingAssignmentField_eq
          radius source trajectory hincidence)
      (fun id link hincidence =>
        adjacentEvenTrajectoryOutgoingAssignmentField_eq
          radius trajectory hincidence)

/-! ## 3. Exact trajectory-major canonical contraction -/

/-- The original trajectory list with a complete canonical incoming/outgoing
resolution of the identity inserted around each summand. -/
def adjacentEvenCanonicalTrajectoryMajorContraction
    (K radius : Nat) (source target : Z4Link → Nat) : Q' :=
  listQSum
    (adjacentEvenCanonicalTrajectoryAssignmentTerm K radius source target)
    (adjacentEvenFixedIncidenceTrajectoryStates K radius)

/-- Exact global choice-free reindexing.  The theorem does not quotient or
deduplicate the literal trajectory carrier, so all physical multiplicities
are retained. -/
theorem adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalTrajectoryMajor
    {K radius : Nat} {source target : Z4Link → Nat}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K) :
    adjacentEvenEndpointTrajectoryFaceKernel K radius source target ≈
      adjacentEvenCanonicalTrajectoryMajorContraction
        K radius source target := by
  unfold adjacentEvenEndpointTrajectoryFaceKernel
    adjacentEvenCanonicalTrajectoryMajorContraction
  apply listQSum_congr_on
  intro trajectory htrajectory
  exact Q'.eqv_symm
    (adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_literal
      hsource htrajectory)

/-! ## 4. Assignment-major compatibility and exact Fubini regrouping -/

/-- Exact predecessor/terminal compatibility of two canonical incidence
assignments.  It is defined as a weighted sum over the original trajectory
list, so repeated trajectory occurrences remain repeated. -/
def adjacentEvenCanonicalAssignmentCompatibility
    (K radius : Nat) (source target : Z4Link → Nat)
    (incoming outgoing : FixedFaceLinkIncidence → Nat) : Q' :=
  listQSum
    (fun trajectory =>
      adjacentEvenCanonicalIncidenceDelta radius incoming
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory) *
        (adjacentEvenCanonicalIncidenceDelta radius outgoing
            (adjacentEvenTrajectoryOutgoingIncidenceAssignment
              radius trajectory) *
          adjacentEvenLinkTerminalProduct
            radius source target trajectory))
    (adjacentEvenFixedIncidenceTrajectoryStates K radius)

/-- The exact canonical compatibility contraction, now grouped first by the
incoming and outgoing fixed-incidence fields. -/
def adjacentEvenCanonicalAssignmentMajorContraction
    (K radius : Nat) (source target : Z4Link → Nat) : Q' :=
  listQSum
    (fun incoming =>
      listQSum
        (fun outgoing =>
          adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing *
            adjacentEvenCanonicalAssignmentCompatibility
              K radius source target incoming outgoing)
        (adjacentEvenFixedIncidenceChannelAssignments K radius))
    (adjacentEvenFixedIncidenceChannelAssignments K radius)

private theorem delta_face_terminal_reorder
    (incomingDelta outgoingDelta face terminal : Q') :
    incomingDelta * (outgoingDelta * (face * terminal)) ≈
      face * (incomingDelta * (outgoingDelta * terminal)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (Q'.mul_assoc_eqv incomingDelta outgoingDelta (face * terminal))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv (incomingDelta * outgoingDelta) (face * terminal)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv face terminal (incomingDelta * outgoingDelta)) ?_
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (Q'.mul_comm_eqv terminal (incomingDelta * outgoingDelta)) ?_
  exact Q'.mul_assoc_eqv incomingDelta outgoingDelta terminal

/-- Algebraic normal form of one trajectory term with the fixed-face entry
outside both Kronecker factors. -/
def adjacentEvenCanonicalReorderedTrajectoryAssignmentTerm
    (K radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) : Q' :=
  listQSum
    (fun incoming =>
      listQSum
        (fun outgoing =>
          adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing *
            (adjacentEvenCanonicalIncidenceDelta radius incoming
                (adjacentEvenTrajectoryIncomingIncidenceAssignment
                  radius source trajectory) *
              (adjacentEvenCanonicalIncidenceDelta radius outgoing
                  (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                    radius trajectory) *
                adjacentEvenLinkTerminalProduct
                  radius source target trajectory)))
        (adjacentEvenFixedIncidenceChannelAssignments K radius))
    (adjacentEvenFixedIncidenceChannelAssignments K radius)

theorem adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_reordered
    (K radius : Nat) (source target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenCanonicalTrajectoryAssignmentTerm
        K radius source target trajectory ≈
      adjacentEvenCanonicalReorderedTrajectoryAssignmentTerm
        K radius source target trajectory := by
  unfold adjacentEvenCanonicalTrajectoryAssignmentTerm
    adjacentEvenCanonicalReorderedTrajectoryAssignmentTerm
  apply listQSum_congr
  intro incoming
  refine Q'.eqv_trans _ _ _
    (Q'.eqv_symm
      (listQSum_mul_left
        (adjacentEvenCanonicalIncidenceDelta radius incoming
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory))
        (fun outgoing =>
          adjacentEvenCanonicalIncidenceDelta radius outgoing
              (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                radius trajectory) *
            (adjacentEvenAssignmentFixedFaceKernel
                K radius incoming outgoing *
              adjacentEvenLinkTerminalProduct
                radius source target trajectory))
        (adjacentEvenFixedIncidenceChannelAssignments K radius))) ?_
  apply listQSum_congr
  intro outgoing
  exact delta_face_terminal_reorder
    (adjacentEvenCanonicalIncidenceDelta radius incoming
      (adjacentEvenTrajectoryIncomingIncidenceAssignment
        radius source trajectory))
    (adjacentEvenCanonicalIncidenceDelta radius outgoing
      (adjacentEvenTrajectoryOutgoingIncidenceAssignment radius trajectory))
    (adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing)
    (adjacentEvenLinkTerminalProduct radius source target trajectory)

/-- Pure finite Fubini regroups the trajectory-major partition into the
canonical incoming/outgoing compatibility contraction. -/
theorem adjacentEvenCanonicalTrajectoryMajor_eqv_assignmentMajor
    (K radius : Nat) (source target : Z4Link → Nat) :
    adjacentEvenCanonicalTrajectoryMajorContraction
        K radius source target ≈
      adjacentEvenCanonicalAssignmentMajorContraction
        K radius source target := by
  let assignments :=
    adjacentEvenFixedIncidenceChannelAssignments K radius
  let trajectories :=
    adjacentEvenFixedIncidenceTrajectoryStates K radius
  let core := fun
      (incoming outgoing : FixedFaceLinkIncidence → Nat)
      (trajectory : FixedIncidenceTrajectoryState) =>
    adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing *
      (adjacentEvenCanonicalIncidenceDelta radius incoming
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory) *
        (adjacentEvenCanonicalIncidenceDelta radius outgoing
            (adjacentEvenTrajectoryOutgoingIncidenceAssignment
              radius trajectory) *
          adjacentEvenLinkTerminalProduct
            radius source target trajectory))
  refine Q'.eqv_trans _ _ _
    (listQSum_congr
      (fun trajectory =>
        adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_reordered
          K radius source target trajectory)
      trajectories) ?_
  change listQSum
      (fun trajectory =>
        listQSum (fun incoming =>
          listQSum (fun outgoing => core incoming outgoing trajectory)
            assignments) assignments)
      trajectories ≈
    listQSum (fun incoming =>
      listQSum (fun outgoing =>
        adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing *
          listQSum (fun trajectory =>
            adjacentEvenCanonicalIncidenceDelta radius incoming
                (adjacentEvenTrajectoryIncomingIncidenceAssignment
                  radius source trajectory) *
              (adjacentEvenCanonicalIncidenceDelta radius outgoing
                  (adjacentEvenTrajectoryOutgoingIncidenceAssignment
                    radius trajectory) *
                adjacentEvenLinkTerminalProduct
                  radius source target trajectory)) trajectories)
        assignments) assignments
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun incoming trajectory =>
        listQSum (fun outgoing => core incoming outgoing trajectory)
          assignments)
      assignments trajectories) ?_
  apply listQSum_congr
  intro incoming
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun outgoing trajectory => core incoming outgoing trajectory)
      assignments trajectories) ?_
  apply listQSum_congr
  intro outgoing
  exact listQSum_mul_left
    (adjacentEvenAssignmentFixedFaceKernel K radius incoming outgoing)
    (fun trajectory =>
      adjacentEvenCanonicalIncidenceDelta radius incoming
          (adjacentEvenTrajectoryIncomingIncidenceAssignment
            radius source trajectory) *
        (adjacentEvenCanonicalIncidenceDelta radius outgoing
            (adjacentEvenTrajectoryOutgoingIncidenceAssignment
              radius trajectory) *
          adjacentEvenLinkTerminalProduct
            radius source target trajectory))
    trajectories

/-- Headline exact canonical compatibility identity for the mixed-trajectory
endpoint kernel. -/
theorem adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalCompatibility
    {K radius : Nat} {source target : Z4Link → Nat}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K) :
    adjacentEvenEndpointTrajectoryFaceKernel K radius source target ≈
      adjacentEvenCanonicalAssignmentMajorContraction
        K radius source target := by
  exact Q'.eqv_trans _ _ _
    (adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalTrajectoryMajor
      hsource)
    (adjacentEvenCanonicalTrajectoryMajor_eqv_assignmentMajor
      K radius source target)

/-- Literal production endpoint-kernel form of the same compatibility
contraction. -/
theorem adjacentEvenFixedInterfaceEndpointKernel_eqv_canonicalCompatibility
    {K radius : Nat} {source target : Z4Link → Nat}
    (hsource : ∀ link, link ∈ adjacentEvenFixedLinks radius →
      source link ≤ linkAuxiliaryCutoff K) :
    adjacentEvenFixedInterfaceEndpointKernel K radius source target ≈
      adjacentEvenCanonicalAssignmentMajorContraction
        K radius source target := by
  exact Q'.eqv_trans _ _ _
    (adjacentEvenFixedInterfaceEndpointKernel_eqv_trajectoryFaceKernel
      K radius source target)
    (adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalCompatibility
      hsource)

#print axioms adjacentEvenAssignmentFixedFaceKernel_congr_incoming
#print axioms adjacentEvenAssignmentFixedFaceKernel_congr_outgoing
#print axioms adjacentEvenOutgoingAssignmentDelta_collapse
#print axioms adjacentEvenIncomingAssignmentDelta_collapse
#print axioms adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_literal
#print axioms adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalTrajectoryMajor
#print axioms adjacentEvenCanonicalTrajectoryAssignmentTerm_eqv_reordered
#print axioms adjacentEvenCanonicalTrajectoryMajor_eqv_assignmentMajor
#print axioms adjacentEvenEndpointTrajectoryFaceKernel_eqv_canonicalCompatibility
#print axioms adjacentEvenFixedInterfaceEndpointKernel_eqv_canonicalCompatibility

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCanonicalCompatibilityContraction
