/-
# Observable events in the enriched connected target submeasure

The support-connected source sector now defines a nonnegative submeasure on
the complete coarse-or-retained target square.  This module makes that result
usable by observables: restriction to any decidable target event remains below
the total connected mass and therefore inherits the explicit SU(2) corridor
rate.

The enriched carrier has two genuinely different physical coordinate systems.
Accordingly the face observable below accepts a fine and a coarse face index
separately.  A `SlabFaceBlockMap` supplies the four in-carrier indices used by
the root/target four-cell event.  No equality between the fine and coarse
observables is asserted here; such an equality requires an additional
geometric pullback or a quantitatively controlled defect.

This is a positive connected-submeasure estimate, not an identification with
target covariance, an OS reflection identity, a strict form bound, a
continuum limit, or the Clay theorem.

## Axiom gate

Boolean filtering, nonnegative finite sums, and the preceding exact target
mass theorem only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetMass
import YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetMass
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

/-! ## 1. Arbitrary observable restriction -/

/-- Mass of the connected enriched target submeasure restricted to an
arbitrary decidable event on the ordered target pair. -/
def allCutoffConnectedExpandedTargetEventMass
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (event : AllCutoffRetainedTarget × AllCutoffRetainedTarget → Bool) : Q' :=
  listQSum
    (allCutoffConnectedExpandedTargetContribution
      S rootFaceId targetFaceId)
    ((allCutoffRetainedTwoReplicaTargets S).filter event)

/-- Every observable restriction is a nonnegative part of the total
connected target submeasure. -/
theorem allCutoffConnectedExpandedTargetEventMass_interval
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (event : AllCutoffRetainedTarget × AllCutoffRetainedTarget → Bool) :
    (0 : Q') <=
        allCutoffConnectedExpandedTargetEventMass
          S rootFaceId targetFaceId event ∧
      allCutoffConnectedExpandedTargetEventMass
          S rootFaceId targetFaceId event <=
        allCutoffConnectedExpandedTargetTotalMass
          S rootFaceId targetFaceId := by
  constructor
  · unfold allCutoffConnectedExpandedTargetEventMass
    apply listQSum_nonnegative_on
    intro target _
    exact (allCutoffConnectedExpandedTargetContribution_interval
      S rootFaceId targetFaceId target).1
  · unfold allCutoffConnectedExpandedTargetEventMass
      allCutoffConnectedExpandedTargetTotalMass
    apply listQSum_filter_le_of_nonnegative
    intro target
    exact (allCutoffConnectedExpandedTargetContribution_interval
      S rootFaceId targetFaceId target).1

/-- An arbitrary enriched target event inherits the explicit SU(2) connected
rate, uniformly over the named cutoff and finite slab volume in the stated
strong-coupling corridor. -/
theorem allCutoffConnectedExpandedTargetEventMass_le_corridorRate
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (event : AllCutoffRetainedTarget × AllCutoffRetainedTarget → Bool) :
    allCutoffConnectedExpandedTargetEventMass
        S rootFaceId targetFaceId event <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine rootFaceId targetFaceId :=
  Q'.le_trans' _ _ _
    (allCutoffConnectedExpandedTargetEventMass_interval
      S rootFaceId targetFaceId event).2
    (allCutoffConnectedExpandedTargetTotalMass_le_corridorRate
      S hfineCutoff hw0 hw1 hwAnchor
      rootFaceId targetFaceId htarget)

/-! ## 2. A branch-explicit physical face event -/

/-- The positive-face event on the physical state carried by an enriched
target.  The fine and coarse indices are separate because the two sum branches
live on different lattice extents. -/
def allCutoffRetainedBranchFacePositiveB
    (fineFaceId coarseFaceId : Nat) : AllCutoffRetainedTarget → Bool
  | Sum.inl coarsePhysical =>
      slabPhysicalFacePositiveB coarseFaceId coarsePhysical
  | Sum.inr retainedFine =>
      slabPhysicalFacePositiveB fineFaceId retainedFine.1

/-- The literal `11 × 00` Boolean four-cell on the enriched two-replica
target, using all four indices carried by the physical face block map. -/
def allCutoffRetainedBranchFourCellB
    {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) : Bool :=
  (allCutoffRetainedBranchFacePositiveB
      M.fineRoot M.coarseRoot target.1 &&
    allCutoffRetainedBranchFacePositiveB
      M.fineTarget M.coarseTarget target.1) &&
  ((!allCutoffRetainedBranchFacePositiveB
      M.fineRoot M.coarseRoot target.2) &&
    (!allCutoffRetainedBranchFacePositiveB
      M.fineTarget M.coarseTarget target.2))

/-- The portion of the connected target submeasure landing in its literal
branch-explicit observable four-cell. -/
def allCutoffConnectedExpandedTargetFourCellMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) : Q' :=
  allCutoffConnectedExpandedTargetEventMass
    S M.fineRoot M.fineTarget
    (allCutoffRetainedBranchFourCellB M)

/-- The branch-explicit target four-cell inherits the same explicit SU(2)
connected rate.  This does not assert that the stochastic block row preserves
the four-cell event. -/
theorem allCutoffConnectedExpandedTargetFourCellMass_le_corridorRate
    (S : SlabScalePair) (hfineCutoff : 1 <= S.fine.cutoff)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (M : SlabFaceBlockMap S) :
    allCutoffConnectedExpandedTargetFourCellMass S M <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine M.fineRoot M.fineTarget := by
  unfold allCutoffConnectedExpandedTargetFourCellMass
  exact allCutoffConnectedExpandedTargetEventMass_le_corridorRate
    S hfineCutoff hw0 hw1 hwAnchor M.fineRoot M.fineTarget
    M.fineTarget_mem (allCutoffRetainedBranchFourCellB M)

/-! ## Axiom audit -/

#print axioms allCutoffConnectedExpandedTargetEventMass_interval
#print axioms allCutoffConnectedExpandedTargetEventMass_le_corridorRate
#print axioms allCutoffRetainedBranchFourCellB
#print axioms allCutoffConnectedExpandedTargetFourCellMass_le_corridorRate

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
