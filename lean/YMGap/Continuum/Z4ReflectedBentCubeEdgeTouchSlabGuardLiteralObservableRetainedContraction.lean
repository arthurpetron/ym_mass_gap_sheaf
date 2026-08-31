/-
# The guarded literal row seeds a strict finite retained contraction

The literal guarded source has at least one quarter of its normalized row in
positive successful choices.  Hence its positive-choice list is nonempty.
This supplies the one explicit connected channel required by the generic
first-source positivity theorem: even if the guarded source itself loses its
receiver column to an earlier row, the selected row reaching that column has
a positive channel which survives canonical thinning.

At positive coupling the resulting Gibbs-weighted transported mass is
strictly positive.  Dividing it by the complete connected source mass gives
the existing exact finite retained fraction and therefore a strict finite
face-covariance and same-object Markov-moment contraction at every positive
representation cutoff.

The retained fraction is computed from the full finite datum and is not
proved to retain the literal numerical quarter.  No lower bound uniform in
cutoff, coupling, volume, or lattice spacing is asserted.  Constructive
contract: finite list cases, exact rational order, and the checked posterior
compiler only; no `Classical`, choice, `native_decide`, `sorry`, new axiom,
noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedMassPositivity
open YMGap.Continuum.CompactDualSlabObservablePairedSplitRetainedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionCrossPlaneFactorization
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction

/-! ## 1. One literal positive channel -/

/-- The quarter-mass row is nonempty after zero-weight successful choices are
removed, so its head is a literal positive connected channel.  The opaque
boundary prevents dependent list-case transports from leaking downstream. -/
opaque reflectedBentGuardGraftLiteralObservablePositiveChannelWitnessAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedConnectedPositiveChannelWitness
      D reflectedBentRootFaceId reflectedBentTargetFaceId := by
  let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
    D hcutoff hextent state
  have hfloor : oneQuarter ≤
      listQSum
        (slabObservablePairedConnectedStrandWeight D
          reflectedBentRootFaceId reflectedBentTargetFaceId source)
        (slabObservablePairedConnectedStrandChoices D
          reflectedBentRootFaceId reflectedBentTargetFaceId source) := by
    simpa only [source] using
      (reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_quarter
        D hcutoff hextent state)
  cases hchoices : slabObservablePairedConnectedStrandChoices D
      reflectedBentRootFaceId reflectedBentTargetFaceId source with
  | nil =>
      have himpossible : oneQuarter ≤ (0 : Q') := by
        simpa only [hchoices, listQSum] using hfloor
      exact False.elim ((by decide : ¬ oneQuarter ≤ (0 : Q')) himpossible)
  | cons choice rest =>
      exact
        { source := source
          choice := choice
          choice_mem := by
            rw [hchoices]
            exact List.mem_cons_self }

/-! ## 2. The exact finite retained fraction -/

theorem reflectedBentTargetFaceId_physical_at_extent
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    reflectedBentTargetFaceId ∈ slabPhysicalFaceEdges D.extent := by
  simpa only [hextent] using reflectedBentTargetFaceId_physical

/-- The exact aggregate retained fraction obtained after receiver-aware
first-source thinning.  It is positive but intentionally datum-dependent. -/
def reflectedBentGuardGraftLiteralObservableRetainedFractionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedConnectedRetainedFractionCertificate
      D reflectedBentRootFaceId reflectedBentTargetFaceId
        (reflectedBentTargetFaceId_physical_at_extent D hextent) :=
  slabObservablePairedConnectedRetainedFractionCertificate
    D hcoupling reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentTargetFaceId_physical_at_extent D hextent)
    (reflectedBentGuardGraftLiteralObservablePositiveChannelWitnessAtCutoff
      D hcutoff hextent state)

theorem reflectedBentGuardGraftLiteralObservableRetainedFractionAtCutoff_pos
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    (0 : Q') <
      (reflectedBentGuardGraftLiteralObservableRetainedFractionAtCutoff
        D hcutoff hextent hcoupling state).delta :=
  (reflectedBentGuardGraftLiteralObservableRetainedFractionAtCutoff
    D hcutoff hextent hcoupling state).delta_pos

/-! ## 3. Strict finite posterior contraction -/

/-- The split disconnected/connected posterior uses one shared target budget.
Its retained fraction is the exact positive quotient above, not `1/4`. -/
def reflectedBentGuardGraftLiteralObservableSplitRetainedContractionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedSplitRetainedContraction
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  slabObservablePairedSplitRetainedContraction
    D hcoupling reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentTargetFaceId_physical_at_extent D hextent)
    (reflectedBentGuardGraftLiteralObservablePositiveChannelWitnessAtCutoff
      D hcutoff hextent state)

/-- **Arbitrary-positive-cutoff strict finite covariance.** -/
theorem reflectedBentGuardGraftLiteralObservableFaceBooleanCovarianceAtCutoff_lt_one
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    slabObservableFaceBooleanCovariance D
        reflectedBentRootFaceId reflectedBentTargetFaceId < (1 : Q') :=
  (reflectedBentGuardGraftLiteralObservableSplitRetainedContractionAtCutoff
    D hcutoff hextent hcoupling state).faceBooleanCovariance_lt_one

theorem reflectedBentTargetFaceId_eq_reflect_at_extent
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    reflectedBentTargetFaceId =
      slabFaceReflectId D.extent reflectedBentRootFaceId := by
  rw [hextent]
  decide

theorem reflectedBentRootFaceId_lower_at_extent
    (D : SlabPhysicalData) (hextent : D.extent = 5) :
    reflectedBentRootFaceId ∈ centralLowerFaceIds D.half := by
  have hhalf : D.half = 2 := by
    unfold SlabPhysicalData.extent centralExtent at hextent
    omega
  rw [hhalf]
  decide

/-- At the reflected face pair, the finite contraction is a strict bound for
the genuine same-object connected physical Markov moment. -/
theorem reflectedBentGuardGraftLiteralObservableSameObjectConnectedMarkovMomentAtCutoff_lt_one
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5) (hcoupling : (0 : Q') < D.coupling)
    (state : SlabAcceptedTwoReplicaState D) :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        D reflectedBentRootFaceId < (1 : Q') := by
  have retained : SlabObservablePairedSplitRetainedContraction D
      reflectedBentRootFaceId
      (slabFaceReflectId D.extent reflectedBentRootFaceId) := by
    rw [← reflectedBentTargetFaceId_eq_reflect_at_extent D hextent]
    exact
      reflectedBentGuardGraftLiteralObservableSplitRetainedContractionAtCutoff
        D hcutoff hextent hcoupling state
  exact retained.sameObjectConnectedMarkovMoment_lt_one
    (reflectedBentRootFaceId_lower_at_extent D hextent)

#print axioms reflectedBentGuardGraftLiteralObservablePositiveChannelWitnessAtCutoff
#print axioms reflectedBentGuardGraftLiteralObservableRetainedFractionAtCutoff_pos
#print axioms reflectedBentGuardGraftLiteralObservableFaceBooleanCovarianceAtCutoff_lt_one
#print axioms reflectedBentGuardGraftLiteralObservableSameObjectConnectedMarkovMomentAtCutoff_lt_one

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRetainedContraction
