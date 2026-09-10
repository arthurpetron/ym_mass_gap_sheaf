/-
# Exact coherent excess in the connected target four-cell

The retained-incoherent landing mass is a target-major submass of the full
connected target `11 x 00` event.  This module partitions the connected source
carrier by the same decidable branch test and names the complementary mass.

The result is an exact nonnegative decomposition:

  full connected target four-cell mass
    = retained landing mass + coherent-or-mixed excess.

The excess is also rewritten source-first as a sum of normalized joint event
masses over precisely those connected source pairs for which at least one raw
recoupling partition is positive.  This is the finite observable obstruction
that must be estimated next.

No smallness estimate for the excess, covariance equality, reflection
identity, strict form bound, continuum limit, or Clay theorem is asserted.

## Axiom gate

Decidable finite partitioning, exact Fubini, and nonnegative finite sums only.
No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellSubmass

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentExcess

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellLandingMass
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellSubmass
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complementary connected source carrier -/

/-- Connected source pairs for which at least one enriched kernel row takes
the coherent coarse branch.  The name says `orMixed` because the other row may
still be retained. -/
def coherentOrMixedConnectedSourcePairs
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    List (SlabObservableTwoReplicaPair S.fine M.fineRoot) :=
  (slabObservablePairedSupportConnectedFourCellSourcePairs
    S.fine M.fineRoot M.fineTarget).filter
      (fun source => !(slabObservablePairRetainedIncoherentB S source))

/-- The full connected target four-cell joint mass, written using the
original observable source-pair carrier before attaching grouped entries. -/
def allCutoffConnectedOriginalTargetFourCellMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun target =>
      listQSum
        (fun source =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.fine M.fineRoot M.fineTarget))
    (retainedTargetFourCellPairs S M)

/-- Target-major connected four-cell mass carried by sources with at least
one coherent coarse row. -/
def allCutoffCoherentOrMixedTargetFourCellExcess
    (S : SlabScalePair) (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun target =>
      listQSum
        (fun source =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        (coherentOrMixedConnectedSourcePairs S M))
    (retainedTargetFourCellPairs S M)

/-! ## 2. Original-pair and attached-entry presentations agree -/

theorem allCutoffConnectedOriginalTargetFourCellMass_eqv_targetEventMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffConnectedOriginalTargetFourCellMass S M ≈
      allCutoffConnectedExpandedTargetFourCellMass S M := by
  unfold allCutoffConnectedOriginalTargetFourCellMass
    allCutoffConnectedExpandedTargetFourCellMass
    allCutoffConnectedExpandedTargetEventMass
    retainedTargetFourCellPairs
  apply listQSum_congr_on _ _
    ((allCutoffRetainedTwoReplicaTargets S).filter
      (allCutoffRetainedBranchFourCellB M))
  intro target _
  exact Q'.eqv_symm
    (connectedTargetContribution_eqv_originalSourcePairs
      S M.fineRoot M.fineTarget target)

/-! ## 3. Exact retained plus coherent partition -/

/-- The original source-pair presentation partitions exactly into the
retained target submass and the coherent-or-mixed excess. -/
theorem allCutoffConnectedOriginalTargetFourCellMass_partition
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffConnectedOriginalTargetFourCellMass S M ≈
      allCutoffRetainedConnectedTargetFourCellSubmass S M +
        allCutoffCoherentOrMixedTargetFourCellExcess S M := by
  let fullSources :=
    slabObservablePairedSupportConnectedFourCellSourcePairs
      S.fine M.fineRoot M.fineTarget
  let retainedTest :
      SlabObservableTwoReplicaPair S.fine M.fineRoot → Bool :=
    slabObservablePairRetainedIncoherentB S
  let targetPairs := retainedTargetFourCellPairs S M
  let weight :
      (AllCutoffRetainedTarget × AllCutoffRetainedTarget) →
        SlabObservableTwoReplicaPair S.fine M.fineRoot → Q' :=
    fun target source =>
      allCutoffExpandedSourceEntryPairTargetWeight S target
        (slabObservablePairExpandedSourceEntries S.fine source)
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        listQSum (weight target) (fullSources.filter retainedTest) +
          listQSum (weight target)
            (fullSources.filter (fun source => !(retainedTest source))))
      targetPairs) _ ?_ ?_
  · unfold allCutoffConnectedOriginalTargetFourCellMass
    apply listQSum_congr_on _ _ targetPairs
    intro target _
    exact listQSum_filter_partition
      (weight target) retainedTest fullSources
  refine Q'.eqv_trans _
    (listQSum
        (fun target => listQSum (weight target)
          (fullSources.filter retainedTest)) targetPairs +
      listQSum
        (fun target => listQSum (weight target)
          (fullSources.filter (fun source => !(retainedTest source))))
        targetPairs) _ ?_ ?_
  · exact listQSum_add _ _ targetPairs
  · unfold allCutoffRetainedConnectedTargetFourCellSubmass
      allCutoffCoherentOrMixedTargetFourCellExcess
      retainedConnectedSourcePairs coherentOrMixedConnectedSourcePairs
    unfold fullSources retainedTest targetPairs weight
    exact Q'.eqv_refl _

/-- **Exact observable obstruction.**  The full connected target four-cell
mass is the already-identified retained landing mass plus a nonnegative mass
carried exactly by sources with at least one coherent coarse row. -/
theorem allCutoffConnectedTargetFourCellMass_eqv_landing_add_coherentExcess
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffConnectedExpandedTargetFourCellMass S M ≈
      allCutoffRetainedConnectedFourCellLandingMass S M +
        allCutoffCoherentOrMixedTargetFourCellExcess S M := by
  refine Q'.eqv_trans _
    (allCutoffConnectedOriginalTargetFourCellMass S M) _
    (Q'.eqv_symm
      (allCutoffConnectedOriginalTargetFourCellMass_eqv_targetEventMass
        S M)) ?_
  refine Q'.eqv_trans _
    (allCutoffRetainedConnectedTargetFourCellSubmass S M +
      allCutoffCoherentOrMixedTargetFourCellExcess S M) _
    (allCutoffConnectedOriginalTargetFourCellMass_partition S M) ?_
  exact Q'.add_eqv_congr'
    (allCutoffRetainedConnectedTargetFourCellSubmass_eqv_landingMass S M)
    (Q'.eqv_refl _)

/-! ## 4. Positivity and source-major presentation of the excess -/

theorem allCutoffCoherentOrMixedTargetFourCellExcess_nonnegative
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    (0 : Q') <= allCutoffCoherentOrMixedTargetFourCellExcess S M := by
  unfold allCutoffCoherentOrMixedTargetFourCellExcess
  apply listQSum_nonnegative_on
  intro target _
  apply listQSum_nonnegative_on
  intro source _
  exact allCutoffExpandedSourceEntryPairTargetWeight_nonnegative
    S target (slabObservablePairExpandedSourceEntries S.fine source)

/-- The same coherent-or-mixed excess written source-first as a sum of the
literal normalized target-event landing masses. -/
theorem allCutoffCoherentOrMixedTargetFourCellExcess_eqv_sourceLandingSum
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffCoherentOrMixedTargetFourCellExcess S M ≈
      listQSum
        (allCutoffRetainedSourceFourCellLandingMass S M)
        (coherentOrMixedConnectedSourcePairs S M) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            allCutoffExpandedSourceEntryPairTargetWeight S target
              (slabObservablePairExpandedSourceEntries S.fine source))
          (retainedTargetFourCellPairs S M))
      (coherentOrMixedConnectedSourcePairs S M)) _ ?_ ?_
  · unfold allCutoffCoherentOrMixedTargetFourCellExcess
    exact Q'.eqv_symm
      (listQSum_swap
        (fun target source =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        (retainedTargetFourCellPairs S M)
        (coherentOrMixedConnectedSourcePairs S M))
  · apply listQSum_congr_on _ _
      (coherentOrMixedConnectedSourcePairs S M)
    intro source _
    unfold retainedTargetFourCellPairs
    exact allCutoffObservablePairExpandedTargetFourCellMass_eqv_landingMass
      S M source

/-! ## Axiom audit -/

#print axioms allCutoffConnectedOriginalTargetFourCellMass_eqv_targetEventMass
#print axioms allCutoffConnectedTargetFourCellMass_eqv_landing_add_coherentExcess
#print axioms allCutoffCoherentOrMixedTargetFourCellExcess_nonnegative
#print axioms allCutoffCoherentOrMixedTargetFourCellExcess_eqv_sourceLandingSum

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentExcess
