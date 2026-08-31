/-
# Why the whole-link support involution cannot decode the guarded event

There are two canonical masks in the current receiver problem.  The physical
union-support mask depends only on the two spin labellings.  The successful
observable mask is the finer component of the realized assignment-dependent
strand graph.  Whole-link transposition is involutive for the first mask, but
the successful recoupling event is defined by disconnection for the second.

On every successful guarded literal choice these masks disagree already at
the root face: physical support still connects root to target because
recoupling leaves both physical fields unchanged, whereas success says the
realized strand component does not.  Thus the existing whole-link involution
cannot be substituted for the production face switch in this row.  Together
with the explicit two-vertex additive collision, this localizes the remaining
decoder work to guarded global provenance or a quantitative collision bound.

Constructive contract: definitional physical preservation and Boolean
disconnection only; no `Classical`, choice, `native_decide`, `sorry`, new
axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.SU2TwoVertexFusionSumRewiring
import YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardWholeLinkDecoderObstruction

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Continuum.CompactDualSlabObservablePairedFaceComponent
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2TwoVertexFusionSumRewiring

/-! ## 1. Physical support remains connected after recoupling -/

/-- Recoupling changes only the two auxiliary assignments.  Therefore any
support-connected source remains support-connected at every realized target
column, including every successful column. -/
theorem slabObservablePairedSuccessfulRecoupledPair_supportConnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (hsource : slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source.1 = true)
    (choice : SlabObservablePairedStrandSuccessfulChoice D
      rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedStrandRecoupledPair D
          rootFaceId targetFaceId source choice.1) = true := by
  simpa only [slabObservableTwoReplicaPairPairedSupportConnectedB,
      slabObservableTwoReplicaPairPairedSupportSwapMask,
      slabObservablePairedStrandRecoupledPair_leftPhysical,
      slabObservablePairedStrandRecoupledPair_rightPhysical] using hsource

/-! ## 2. The successful face mask is genuinely different -/

theorem slabObservablePairedSuccessfulRecoupledPair_faceDisconnected
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (choice : SlabObservablePairedStrandSuccessfulChoice D
      rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedFaceConnectedB
        D rootFaceId targetFaceId
        (slabObservablePairedStrandRecoupledPair D
          rootFaceId targetFaceId source choice.1) = false :=
  choice.disconnected

/-- **Guarded mask obstruction.**  The physical union-support mask used by
the accepted whole-link involution is not the successful realized-strand
mask used by the observable face switch. -/
theorem slabObservablePairedSuccessful_supportMask_ne_faceMask
    (D : SlabPhysicalData) (rootFaceId targetFaceId : Nat)
    (source : SlabObservablePairedStrandRecouplingSource
      D rootFaceId targetFaceId)
    (hsource : slabObservableTwoReplicaPairPairedSupportConnectedB
      D rootFaceId targetFaceId source.1 = true)
    (choice : SlabObservablePairedStrandSuccessfulChoice D
      rootFaceId targetFaceId source) :
    slabObservableTwoReplicaPairPairedSupportSwapMask
        D (slabObservablePairedStrandRecoupledPair D
          rootFaceId targetFaceId source choice.1) targetFaceId ≠
      slabObservableTwoReplicaPairPairedFaceSwapMask
        D (slabObservablePairedStrandRecoupledPair D
          rootFaceId targetFaceId source choice.1) targetFaceId := by
  let pair := slabObservablePairedStrandRecoupledPair D
    rootFaceId targetFaceId source choice.1
  intro heq
  have hatRoot := congrFun heq rootFaceId
  have hsupport :=
    slabObservablePairedSuccessfulRecoupledPair_supportConnected
      D rootFaceId targetFaceId source hsource choice
  have hface :=
    slabObservablePairedSuccessfulRecoupledPair_faceDisconnected
      D rootFaceId targetFaceId source choice
  change slabObservableTwoReplicaPairPairedSupportSwapMask
      D pair targetFaceId rootFaceId = true
    at hsupport
  change slabObservableTwoReplicaPairPairedFaceSwapMask
      D pair targetFaceId rootFaceId = false
    at hface
  rw [hsupport, hface] at hatRoot
  exact Bool.noConfusion hatRoot

/-- The separate local obstruction remains available at the guarded decoder
boundary: vertexwise summed resolutions alone cannot recover their colored
source decomposition. -/
theorem reflectedBentGuard_localAdditiveOutput_not_injective :
    ¬ Function.Injective twoVertexAdditiveOutput :=
  twoVertexAdditiveOutput_not_injective

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardWholeLinkDecoderObstruction

#print axioms YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardWholeLinkDecoderObstruction.slabObservablePairedSuccessfulRecoupledPair_supportConnected
#print axioms YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardWholeLinkDecoderObstruction.slabObservablePairedSuccessful_supportMask_ne_faceMask
#print axioms YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardWholeLinkDecoderObstruction.reflectedBentGuard_localAdditiveOutput_not_injective
