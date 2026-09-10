/-
# Integrated retained landing mass in the enriched target four-cell

The retained positive-incoherent connected source rows force the literal
enriched target `11 x 00` event with conditional mass one.  This module sums
that rowwise identity against the normalized accepted two-replica Gibbs law.

The resulting source-target joint event mass is exactly the previously
identified retained connected mass and therefore inherits its explicit SU(2)
corridor rate.  This supplies a direct observable interpretation of that
sector, rather than only a scalar comparison after forgetting the target.

The coherent/coarse rows are not included.  No target covariance equality,
reflection identity, strict form bound, continuum limit, or Clay theorem is
asserted here.

## Axiom gate

Exact finite Fubini, positive rational division, and the rowwise target-event
identity only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellLandingMass

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The normalized source-target joint event mass -/

def slabObservableTwoReplicaPairNormalizedMass
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (source : SlabObservableTwoReplicaPair D rootFaceId) : Q' :=
  Q'.divPos
    (slabObservableTwoReplicaPairWeight D source)
    (D.physicalPartition * D.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent)
      (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))

/-- Joint mass of one source row landing in the literal enriched target
four-cell. -/
def allCutoffRetainedSourceFourCellLandingMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) : Q' :=
  listQSum
    (fun target =>
      slabObservableTwoReplicaPairNormalizedMass S.fine source *
        (allCutoffRetainedTwoReplicaKernel S source target *
          rationalBoolIndicator
            (allCutoffRetainedBranchFourCellB M target)))
    (allCutoffRetainedTwoReplicaTargets S)

/-- Total source-target joint event mass over the positive-incoherent
support-connected source carrier. -/
def allCutoffRetainedConnectedFourCellLandingMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (allCutoffRetainedSourceFourCellLandingMass S M)
    (slabObservableRetainedIncoherentConnectedPairs
      S M.fineRoot M.fineTarget)

/-! ## 2. Row normalization inside the observable event -/

/-- A retained connected source row contributes exactly its normalized Gibbs
mass to the target four-cell landing event. -/
theorem allCutoffRetainedSourceFourCellLandingMass_eqv_normalizedMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈ slabObservableRetainedIncoherentConnectedPairs
      S M.fineRoot M.fineTarget) :
    allCutoffRetainedSourceFourCellLandingMass S M source ≈
      slabObservableTwoReplicaPairNormalizedMass S.fine source := by
  unfold allCutoffRetainedSourceFourCellLandingMass
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairNormalizedMass S.fine source *
      allCutoffRetainedTwoReplicaFourCellEventMoment S M source) _ ?_ ?_
  · exact listQSum_mul_left
      (slabObservableTwoReplicaPairNormalizedMass S.fine source)
      (fun target =>
        allCutoffRetainedTwoReplicaKernel S source target *
          rationalBoolIndicator
            (allCutoffRetainedBranchFourCellB M target))
      (allCutoffRetainedTwoReplicaTargets S)
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairNormalizedMass S.fine source * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (allCutoffRetainedTwoReplicaFourCellEventMoment_eq_one
        S M hcoupling source hsource)
  · exact Q'.mul_one_eqv _

/-! ## 3. Exact identification and inherited decay -/

private theorem normalizedPairMass_sum_eqv_divPos
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    listQSum
        (slabObservableTwoReplicaPairNormalizedMass S.fine)
        (slabObservableRetainedIncoherentConnectedPairs
          S M.fineRoot M.fineTarget) ≈
      Q'.divPos
        (listQSum (slabObservableTwoReplicaPairWeight S.fine)
          (slabObservableRetainedIncoherentConnectedPairs
            S M.fineRoot M.fineTarget))
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative
            S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative
            S.fine.cutoff S.fine.extent)) := by
  unfold slabObservableTwoReplicaPairNormalizedMass Q'.divPos
  exact listQSum_mul_right
    (slabObservableTwoReplicaPairWeight S.fine)
    (Q'.recipPos
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative
          S.fine.cutoff S.fine.extent)
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative
          S.fine.cutoff S.fine.extent)))
    (slabObservableRetainedIncoherentConnectedPairs
      S M.fineRoot M.fineTarget)

/-- **Integrated observable identity.**  The normalized joint mass of
retained connected rows landing in the literal target four-cell is exactly
the genuine retained connected mass previously extracted from the enriched
blocked law. -/
theorem allCutoffRetainedConnectedFourCellLandingMass_eqv_connectedMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling) :
    allCutoffRetainedConnectedFourCellLandingMass S M ≈
      slabObservableRetainedIncoherentConnectedMass
        S M.fineRoot M.fineTarget := by
  refine Q'.eqv_trans _
    (listQSum
      (slabObservableTwoReplicaPairNormalizedMass S.fine)
      (slabObservableRetainedIncoherentConnectedPairs
        S M.fineRoot M.fineTarget)) _ ?_ ?_
  · unfold allCutoffRetainedConnectedFourCellLandingMass
    apply listQSum_congr_on _ _
      (slabObservableRetainedIncoherentConnectedPairs
        S M.fineRoot M.fineTarget)
    intro source hsource
    exact allCutoffRetainedSourceFourCellLandingMass_eqv_normalizedMass
      S M hcoupling source hsource
  refine Q'.eqv_trans _
    (Q'.divPos
      (listQSum (slabObservableTwoReplicaPairWeight S.fine)
        (slabObservableRetainedIncoherentConnectedPairs
          S M.fineRoot M.fineTarget))
      (S.fine.physicalPartition * S.fine.physicalPartition)
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative
          S.fine.cutoff S.fine.extent)
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative
          S.fine.cutoff S.fine.extent))) _
    (normalizedPairMass_sum_eqv_divPos S M) ?_
  exact Q'.eqv_symm
    (slabObservableRetainedIncoherentConnectedMass_eqv_normalizedWeight
      S M.fineRoot M.fineTarget hcoupling)

/-- The observable landing mass inherits the explicit SU(2) component rate
throughout the fully named strong-coupling corridor. -/
theorem allCutoffRetainedConnectedFourCellLandingMass_le_corridorRate
    (S : SlabScalePair)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (M : SlabFaceBlockMap S) :
    allCutoffRetainedConnectedFourCellLandingMass S M <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine M.fineRoot M.fineTarget :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (allCutoffRetainedConnectedFourCellLandingMass_eqv_connectedMass
        S M hw0))
    (slabObservableRetainedIncoherentConnectedMass_le_corridorRate
      S hw0 hw1 hwAnchor M.fineRoot M.fineTarget M.fineTarget_mem)

/-! ## Axiom audit -/

#print axioms allCutoffRetainedSourceFourCellLandingMass_eqv_normalizedMass
#print axioms allCutoffRetainedConnectedFourCellLandingMass_eqv_connectedMass
#print axioms allCutoffRetainedConnectedFourCellLandingMass_le_corridorRate

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellLandingMass
