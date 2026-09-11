/-
# Mixed-trajectory normal form of the adjacent-even endpoint operator

The literal fixed-interface endpoint operator sums fixed-face labels and
incidence trajectories.  This leaf swaps those finite symbolic sums, regroups
each link-major trajectory into its face-major transition and terminal delta,
and performs the fixed-face label sum with the existing resummed-face theorem.

The result isolates the remaining common-middle problem exactly.  It does not
claim that the mixed incoming/outgoing trajectory kernel is Gram.
-/

import YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality
import YMGap.Continuum.HeatKernelGramSOS

namespace YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.ClusterCount4DProgress
open YMGap.Continuum.FusedFreeSplit
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteBoxFusionCompleteCutoff
open YMGap.Continuum.Z4ExplicitValenceFusionMultiplicity
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenAssembledSlabFactorization
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenCrossPlaneGeometry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenDeterministicLowerEndpoint
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedFaceCoefficientAttachment
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidencePointwiseRegroup
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedIncidenceTrajectoryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedInterfaceEndpointOperator
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkEndpointFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedLinkGlobalTrajectoryIntegration
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenFixedWordTrajectoryFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceDependentChannels
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenJointFaceSlabFubini
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPalindromicSandwich
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenPhysicalKernelSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReachableFixedWordSymmetry
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenReflectedBoundaryAssembly
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenSlabIncidenceBridge
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenTerminalDeltaCollapse
open YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenOuterFactorLocality
open YMGap.Continuum.Z4HalfTimeReflectionLinkMultiplicity
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-- The endpoint operator after fixed-face labels have been resummed inside
each incidence trajectory.  The terminal product still couples the source,
target, and trajectory exactly. -/
def adjacentEvenEndpointTrajectoryFaceKernel
    (K radius : Nat) (source target : Z4Link → Nat) : Q' :=
  listQSum (fun trajectory =>
    adjacentEvenTrajectoryFixedFaceResummedKernel
        K radius source trajectory *
      adjacentEvenLinkTerminalProduct
        radius source target trajectory)
    (adjacentEvenFixedIncidenceTrajectoryStates K radius)

/-- Exact mixed-trajectory normal form of the literal endpoint kernel. -/
theorem adjacentEvenFixedInterfaceEndpointKernel_eqv_trajectoryFaceKernel
    (K radius : Nat) (source target : Z4Link → Nat) :
    adjacentEvenFixedInterfaceEndpointKernel
        K radius source target ≈
      adjacentEvenEndpointTrajectoryFaceKernel
        K radius source target := by
  let physicals := boundedEdgeLabellings K
    (adjacentEvenFixedFaceIds radius)
  let trajectories :=
    adjacentEvenFixedIncidenceTrajectoryStates K radius
  let coefficient :=
    adjacentEvenFixedFaceCoefficientProduct K radius
  let linkProduct : EdgeLabelling → FixedIncidenceTrajectoryState → Q' :=
    fun physical trajectory =>
      adjacentEvenTrajectoryLinkProduct
        radius physical source target trajectory
  let faceProduct : EdgeLabelling → FixedIncidenceTrajectoryState → Q' :=
    fun physical trajectory =>
      adjacentEvenFaceTransitionProduct
        radius physical source trajectory
  let terminal : FixedIncidenceTrajectoryState → Q' :=
    fun trajectory => adjacentEvenLinkTerminalProduct
      radius source target trajectory
  change listQSum (fun physical =>
      coefficient physical *
        listQSum (fun trajectory => linkProduct physical trajectory)
          trajectories) physicals ≈
    listQSum (fun trajectory =>
      adjacentEvenTrajectoryFixedFaceResummedKernel
          K radius source trajectory * terminal trajectory)
      trajectories
  have hdistribute :
      listQSum (fun physical =>
          coefficient physical *
            listQSum (fun trajectory => linkProduct physical trajectory)
              trajectories) physicals ≈
        listQSum (fun physical =>
          listQSum (fun trajectory =>
            coefficient physical * linkProduct physical trajectory)
            trajectories) physicals := by
    apply listQSum_congr_on
    intro physical _
    exact Q'.eqv_symm
      (listQSum_mul_left (coefficient physical)
        (fun trajectory => linkProduct physical trajectory)
        trajectories)
  refine Q'.eqv_trans _ _ _ hdistribute ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun trajectory physical =>
        coefficient physical * linkProduct physical trajectory)
      trajectories physicals) ?_
  apply listQSum_congr_on
  intro trajectory _
  have hpoint : ∀ physical,
      coefficient physical * linkProduct physical trajectory ≈
        (coefficient physical * faceProduct physical trajectory) *
          terminal trajectory := by
    intro physical
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left (coefficient physical) _ _
        (adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal
          radius physical source target trajectory)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (coefficient physical)
        (faceProduct physical trajectory) (terminal trajectory))
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hpoint physicals) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_right
      (fun physical =>
        coefficient physical * faceProduct physical trajectory)
      (terminal trajectory) physicals) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (adjacentEvenFixedFaceCoefficientTransitionSum_eqv_resummedKernel
      K radius source trajectory)

/-! ## Symbolic collapse of the deterministic lower source -/

private theorem listQProduct_pointwise_mul_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    listQProduct (fun item => left item * right item) items ≈
      listQProduct left items * listQProduct right items
  | [] => Q'.eqv_symm (Q'.mul_one_eqv 1)
  | head :: tail => by
      simp only [listQProduct]
      refine Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left (left head * right head) _ _
          (listQProduct_pointwise_mul_local left right tail)) ?_
      exact YMGap.Continuum.RingNormaliser.q_mul4_swap
        (left head) (right head)
        (listQProduct left tail) (listQProduct right tail)

/-- The lower endpoint assignment is a literal delta on every fixed link, so
the complete bounded source-assignment sum selects that endpoint exactly.
Only the fixed-link coordinates are read; no global endpoint list is built. -/
theorem adjacentEvenLowerSourceTrajectorySum_eqv_endpoint
    {K radius : Nat} {left : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius)
    (boundary : EdgeLabelling) (target : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    listQSum (fun source =>
        adjacentEvenLowerAmplitudeProduct K radius left source *
          adjacentEvenTrajectoryLinkProduct
            radius boundary source target trajectory)
      (boundedLabellingsOn (linkAuxiliaryCutoff K)
        (adjacentEvenFixedLinks radius)) ≈
      adjacentEvenTrajectoryLinkProduct radius boundary
        (adjacentEvenHalfStateEndpointAssignment radius left)
        target trajectory := by
  let links := adjacentEvenFixedLinks radius
  let endpoint := adjacentEvenHalfStateEndpointAssignment radius left
  let lower : Z4Link → Nat → Q' := fun link channel =>
    adjacentEvenLowerLinkAmplitude K radius left link channel
  let transition : Z4Link → Nat → Q' := fun link channel =>
    Q'.ofNat (fixedIdTrajectoryMultiplicity boundary (trajectory link)
      channel (target link)
      (adjacentEvenIncidentFixedFaceIds radius link))
  have hcombine : ∀ source : Z4Link → Nat,
      adjacentEvenLowerAmplitudeProduct K radius left source *
          adjacentEvenTrajectoryLinkProduct
            radius boundary source target trajectory ≈
        listQProduct (fun link =>
          lower link (source link) * transition link (source link)) links := by
    intro source
    unfold adjacentEvenLowerAmplitudeProduct
      adjacentEvenTrajectoryLinkProduct
    exact Q'.eqv_symm
      (listQProduct_pointwise_mul_local
        (fun link => lower link (source link))
        (fun link => transition link (source link)) links)
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hcombine
      (boundedLabellingsOn (linkAuxiliaryCutoff K) links)) ?_
  refine Q'.eqv_trans _ _ _
    (boundedLabellingsOn_product_fubini
      (linkAuxiliaryCutoff K)
      (fun link channel =>
        lower link channel * transition link channel)
      links (adjacentEvenFixedLinks_nodup radius)) ?_
  unfold adjacentEvenTrajectoryLinkProduct
  apply listQProduct_congr_eqv
  intro link hlink
  have hendpoint : endpoint link ≤ linkAuxiliaryCutoff K :=
    Nat.le_trans
      (adjacentEvenHalfStateEndpointAssignment_le hleft link)
      (externalCutoff_le_linkAuxiliaryCutoff K)
  have hpoint : ∀ channel,
      lower link channel * transition link channel ≈
        (if channel = endpoint link then (1 : Q') else 0) *
          transition link channel := by
    intro channel
    by_cases heq : channel = endpoint link
    · rw [if_pos heq]
      apply Q'.mul_eqv_congr_right
      subst channel
      unfold lower endpoint adjacentEvenHalfStateEndpointAssignment
      rw [adjacentEvenLowerLinkAmplitude_eq_indicator
        K radius left hlink]
      simp [boolMultiplicity]
      decide
    · rw [if_neg heq]
      apply Q'.mul_eqv_congr_right
      unfold lower endpoint adjacentEvenHalfStateEndpointAssignment at *
      rw [adjacentEvenLowerLinkAmplitude_eq_indicator
        K radius left hlink]
      simp [heq, boolMultiplicity]
      exact Q'.ofNat_zero_eqv
  refine Q'.eqv_trans _ _ _
    (YMGap.Continuum.CubeRatioBounds.fsum_eqv_congr
      (fun channel => lower link channel * transition link channel)
      (fun channel =>
        (if channel = endpoint link then (1 : Q') else 0) *
          transition link channel)
      hpoint (linkAuxiliaryCutoff K + 1)) ?_
  exact delta_fsum (transition link) (endpoint link)
    (linkAuxiliaryCutoff K + 1) (by omega)

/-! ## Collapse of an assembled interface to its two physical endpoints -/

theorem adjacentEvenFaceTransitionProduct_assemble_only_boundary
    (radius : Nat) (left boundary right : EdgeLabelling)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenFaceTransitionProduct radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right) source trajectory =
      adjacentEvenFaceTransitionProduct
        radius boundary source trajectory := by
  unfold adjacentEvenFaceTransitionProduct
  apply listQProduct_congr
  intro id hid
  have hparts := mem_adjacentEvenFixedFaceIds.mp hid
  rw [assembleAdjacentEvenReflectedSlabLabelling_fixed
    hparts.1 hparts.2]

/-- Evaluating the right lower endpoint amplitude at a trajectory's final
channel is exactly the trajectory's terminal delta for that right endpoint. -/
theorem adjacentEvenLowerFinalAmplitude_eqv_terminal
    (K radius : Nat) (right : EdgeLabelling)
    (source : Z4Link → Nat)
    (trajectory : FixedIncidenceTrajectoryState) :
    adjacentEvenLowerAmplitudeProduct K radius right
        (fun link => adjacentEvenTrajectoryFinalChannel
          radius source trajectory link) ≈
      adjacentEvenLinkTerminalProduct radius source
        (adjacentEvenHalfStateEndpointAssignment radius right)
        trajectory := by
  unfold adjacentEvenLowerAmplitudeProduct
    adjacentEvenLinkTerminalProduct
  apply listQProduct_congr_eqv
  intro link hlink
  let final := adjacentEvenTrajectoryFinalChannel
    radius source trajectory link
  let endpoint := adjacentEvenHalfStateEndpointAssignment radius right link
  have hlowerDelta :
      adjacentEvenLowerLinkAmplitude K radius right link final ≈
        (if endpoint = final then (1 : Q') else 0) := by
    rw [adjacentEvenLowerLinkAmplitude_eq_indicator
      K radius right hlink final]
    unfold endpoint adjacentEvenHalfStateEndpointAssignment
    by_cases heq : final =
        adjacentEvenCommonLowerEndpoint radius right link
    · rw [if_pos heq.symm]
      simp [heq, boolMultiplicity]
      decide
    · rw [if_neg (fun h => heq h.symm)]
      simp [heq, boolMultiplicity]
      exact Q'.ofNat_zero_eqv
  refine Q'.eqv_trans _ _ _ hlowerDelta ?_
  exact Q'.eqv_symm
    (adjacentEvenTerminalDeltaFactor_eqv_delta
      radius source
      (adjacentEvenHalfStateEndpointAssignment radius right)
      trajectory link)

theorem adjacentEvenCommonLowerInterfaceSum_assembled_eqv_endpoint
    {K radius : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius)
    (boundary : EdgeLabelling) :
    adjacentEvenCommonLowerInterfaceSum K radius
        (assembleAdjacentEvenReflectedSlabLabelling
          radius left boundary right)
        (assembleAdjacentEvenReflectedSlabLabelling
          radius right boundary left) ≈
      listQSum (fun trajectory =>
        adjacentEvenTrajectoryLinkProduct radius boundary
          (adjacentEvenHalfStateEndpointAssignment radius left)
          (adjacentEvenHalfStateEndpointAssignment radius right)
          trajectory)
        (adjacentEvenFixedIncidenceTrajectoryStates K radius) := by
  let sources := boundedLabellingsOn (linkAuxiliaryCutoff K)
    (adjacentEvenFixedLinks radius)
  let trajectories :=
    adjacentEvenFixedIncidenceTrajectoryStates K radius
  let physical := assembleAdjacentEvenReflectedSlabLabelling
    radius left boundary right
  let reflected := assembleAdjacentEvenReflectedSlabLabelling
    radius right boundary left
  let rightEndpoint :=
    adjacentEvenHalfStateEndpointAssignment radius right
  change listQSum (fun source =>
      listQSum (fun trajectory =>
        (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenFaceTransitionProduct
            radius physical source trajectory) *
          adjacentEvenLowerAmplitudeProduct K radius reflected
            (fun link => adjacentEvenTrajectoryFinalChannel
              radius source trajectory link)) trajectories) sources ≈ _
  refine Q'.eqv_trans _ _ _
    (listQSum_swap
      (fun trajectory source =>
        (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenFaceTransitionProduct
            radius physical source trajectory) *
          adjacentEvenLowerAmplitudeProduct K radius reflected
            (fun link => adjacentEvenTrajectoryFinalChannel
              radius source trajectory link))
      trajectories sources) ?_
  apply listQSum_congr_on
  intro trajectory _
  have hpoint : ∀ source,
      (adjacentEvenLowerAmplitudeProduct K radius physical source *
          adjacentEvenFaceTransitionProduct
            radius physical source trajectory) *
          adjacentEvenLowerAmplitudeProduct K radius reflected
            (fun link => adjacentEvenTrajectoryFinalChannel
              radius source trajectory link) ≈
        adjacentEvenLowerAmplitudeProduct K radius left source *
          adjacentEvenTrajectoryLinkProduct radius boundary source
            rightEndpoint trajectory := by
    intro source
    rw [adjacentEvenLowerAmplitudeProduct_assemble_only_left,
      adjacentEvenFaceTransitionProduct_assemble_only_boundary]
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left
        (adjacentEvenLowerAmplitudeProduct K radius left source *
          adjacentEvenFaceTransitionProduct
            radius boundary source trajectory) _ _
        (Q'.eqv_trans _ _ _
          (Q'.eqv_of_eq
            (adjacentEvenLowerAmplitudeProduct_assemble_only_left
              K radius right boundary left
              (fun link => adjacentEvenTrajectoryFinalChannel
                radius source trajectory link)))
          (adjacentEvenLowerFinalAmplitude_eqv_terminal
            K radius right source trajectory))) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_assoc_eqv
        (adjacentEvenLowerAmplitudeProduct K radius left source)
        (adjacentEvenFaceTransitionProduct
          radius boundary source trajectory)
        (adjacentEvenLinkTerminalProduct radius source
          rightEndpoint trajectory)) ?_
    exact Q'.mul_eqv_congr_left
      (adjacentEvenLowerAmplitudeProduct K radius left source) _ _
      (Q'.eqv_symm
        (adjacentEvenTrajectoryLinkProduct_eqv_faceProduct_mul_terminal
          radius boundary source rightEndpoint trajectory))
  refine Q'.eqv_trans _ _ _
    (listQSum_congr hpoint sources) ?_
  exact adjacentEvenLowerSourceTrajectorySum_eqv_endpoint
    hleft boundary rightEndpoint trajectory

/-- Summing the assembled common interface over its literal fixed-boundary
labelling is exactly the fixed-interface endpoint operator at the two
deterministic half-state endpoints. -/
theorem adjacentEvenAssembledInterfaceBoundarySum_eqv_endpointKernel
    {K radius : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius) :
    listQSum (fun boundary =>
        adjacentEvenAssembledInterface
          K radius left boundary right)
      (adjacentEvenBoundaryChannels K radius) ≈
      adjacentEvenFixedInterfaceEndpointKernel K radius
        (adjacentEvenHalfStateEndpointAssignment radius left)
        (adjacentEvenHalfStateEndpointAssignment radius right) := by
  unfold adjacentEvenAssembledInterface
    adjacentEvenFixedInterfaceEndpointKernel
    adjacentEvenBoundaryChannels
  apply listQSum_congr_on
  intro boundary _
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (adjacentEvenCommonLowerInterfaceSum_assembled_eqv_endpoint
      hleft boundary) ?_
  apply listQSum_congr_on
  intro trajectory _
  unfold adjacentEvenTrajectoryLinkProduct
    adjacentEvenFixedIncidenceTrajectoryFactor
  exact Q'.eqv_refl _

/-- Exact outer factorization of the literal physical reflected kernel.  The
only two factors outside the reachable endpoint operator are the same lower
half amplitude on the left and right configurations. -/
theorem adjacentEvenPhysicalReflectedKernel_anchor_eqv_reachableFactors
    {K radius : Nat} {left right : EdgeLabelling}
    (hleft : left ∈ adjacentEvenHalfStates K radius)
    (hright : right ∈ adjacentEvenHalfStates K radius) :
    adjacentEvenPhysicalReflectedKernel
        anchorCoupling K radius left right ≈
      adjacentEvenLowerFactor anchorCoupling K radius left *
        (adjacentEvenFixedInterfaceEndpointKernel K radius
            (adjacentEvenHalfStateEndpointAssignment radius left)
            (adjacentEvenHalfStateEndpointAssignment radius right) *
          adjacentEvenLowerFactor anchorCoupling K radius right) := by
  let boundaries := adjacentEvenBoundaryChannels K radius
  let leftFactor :=
    adjacentEvenLowerFactor anchorCoupling K radius left
  let rightFactor :=
    adjacentEvenLowerFactor anchorCoupling K radius right
  let interface : EdgeLabelling → Q' := fun boundary =>
    adjacentEvenAssembledInterface K radius left boundary right
  unfold adjacentEvenPhysicalReflectedKernel
  have hpoint : ∀ boundary, boundary ∈ boundaries →
      slabParametricKPhysicalTerm anchorCoupling K
          (adjacentEvenExtent radius)
          (assembleAdjacentEvenReflectedSlabLabelling
            radius left boundary right) ≈
        leftFactor * (interface boundary * rightFactor) := by
    intro boundary hboundary
    dsimp only [leftFactor, rightFactor, interface]
    refine Q'.eqv_trans _ _ _
      (adjacentEvenAssembledSlabNumerator_eqv_lower_interface_upper
        hleft hboundary hright) ?_
    unfold adjacentEvenAssembledPhysical
    rw [adjacentEvenLowerFactor_assemble_only_left]
    apply Q'.mul_eqv_congr_left
    apply Q'.mul_eqv_congr_left
    exact adjacentEvenUpperFactor_assemble_only_right
      anchorCoupling hleft hboundary hright
  refine Q'.eqv_trans _ _ _
    (listQSum_congr_on
      (fun boundary =>
        slabParametricKPhysicalTerm anchorCoupling K
          (adjacentEvenExtent radius)
          (assembleAdjacentEvenReflectedSlabLabelling
            radius left boundary right))
      (fun boundary =>
        leftFactor * (interface boundary * rightFactor))
      boundaries hpoint) ?_
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_left leftFactor
      (fun boundary => interface boundary * rightFactor)
      boundaries) ?_
  apply Q'.mul_eqv_congr_left
  refine Q'.eqv_trans _ _ _
    (listQSum_mul_right interface rightFactor boundaries) ?_
  apply Q'.mul_eqv_congr_right
  exact adjacentEvenAssembledInterfaceBoundarySum_eqv_endpointKernel
    hleft

/-! ## Constructive adapter for the remaining common-middle theorem -/

/-- Sufficient data for expressing the reachable endpoint pullback as a
finite sandwich of the already proved dependent fixed-face Gram.  This is an
honest Type-valued residual: no inhabitant is asserted here. -/
structure AdjacentEvenReachableCommonMiddleData
    (K radius : Nat) : Type where
  middleCount : Nat
  middleField : Nat → FixedFaceChannelField
  middleField_le : ∀ middle id link,
    middleField middle id link ≤ linkAuxiliaryCutoff K
  halfAmplitude : Nat → Nat → Q'
  factorization : ∀ left right,
    adjacentEvenReachableFixedInterfaceMatrix K radius left right ≈
      finiteKernelSandwich
        (adjacentEvenGlobalDependentFixedFaceChannelMatrix
          K radius middleField)
        halfAmplitude middleCount left right

/-- Once common-middle data are supplied, the reachable interface Gram is a
mechanical constructive sandwich of the production fixed-face Gram. -/
def AdjacentEvenReachableCommonMiddleData.toGramRep
    {K radius : Nat}
    (data : AdjacentEvenReachableCommonMiddleData K radius) :
    AdjacentEvenReachableFixedInterfaceGramWitness K radius :=
  gramRep_of_eqv
    (finiteKernelSandwichGramRep
      (adjacentEvenProductionDependentFixedFaceChannelGramRep
        K radius data.middleField data.middleField_le)
      data.halfAmplitude data.middleCount)
    data.factorization

#print axioms adjacentEvenFixedInterfaceEndpointKernel_eqv_trajectoryFaceKernel
#print axioms adjacentEvenLowerSourceTrajectorySum_eqv_endpoint
#print axioms adjacentEvenFaceTransitionProduct_assemble_only_boundary
#print axioms adjacentEvenLowerFinalAmplitude_eqv_terminal
#print axioms adjacentEvenCommonLowerInterfaceSum_assembled_eqv_endpoint
#print axioms adjacentEvenAssembledInterfaceBoundarySum_eqv_endpointKernel
#print axioms adjacentEvenPhysicalReflectedKernel_anchor_eqv_reachableFactors
#print axioms AdjacentEvenReachableCommonMiddleData.toGramRep

end YMGap.Continuum.Z4HalfTimeReflectionAdjacentEvenEndpointTrajectoryNormalForm
