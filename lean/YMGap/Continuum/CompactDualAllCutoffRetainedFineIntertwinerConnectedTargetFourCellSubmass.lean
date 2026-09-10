/-
# The retained landing mass inside the target-major connected submeasure

The retained connected four-cell landing mass was defined source-first.  The
connected target submeasure was defined target-first.  This module proves
that these are two Fubini presentations of the same restricted joint law and
that the retained landing mass is a genuine submass of the full
branch-explicit connected target event.

The proof also identifies the grouped expanded-source density with normalized
accepted-pair mass times the actual two-replica enriched kernel.  Thus the
observable path now remains inside one literal joint law throughout.

No lower bound, covariance equality, reflection identity, strict form bound,
continuum limit, or Clay theorem is asserted here.  In particular, the
coherent/coarse contribution to the full target event remains an uncontrolled
nonnegative remainder.

## Axiom gate

Finite filtering, exact Fubini, nonnegative subset summation, and rational
product rearrangement only.  No classical choice, placeholder, trusted
external computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellLandingMass
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellSubmass

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellLandingMass
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetMass
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite event and monotonicity algebra -/

private theorem listQSum_mul_indicator_eqv_filter
    {A : Type} (weight : A → Q') (event : A → Bool) :
    ∀ items : List A,
      listQSum
          (fun item => weight item * rationalBoolIndicator (event item))
          items ≈
        listQSum weight (items.filter event)
  | [] => Q'.eqv_refl 0
  | head :: tail => by
      have ih := listQSum_mul_indicator_eqv_filter weight event tail
      cases hevent : event head with
      | false =>
          simp only [listQSum, rationalBoolIndicator, hevent,
            Bool.false_eq_true, if_false, List.filter_cons]
          refine Q'.eqv_trans _ (0 + listQSum weight (tail.filter event)) _ ?_ ?_
          · exact Q'.add_eqv_congr' (Q'.mul_zero_eqv _) ih
          · exact Q'.eqv_of_eq (Q'.zero_add' _)
      | true =>
          simp only [listQSum, rationalBoolIndicator, hevent,
            if_true, List.filter_cons]
          exact Q'.add_eqv_congr' (Q'.mul_one_eqv _) ih

private theorem listQSum_mono_local
    {A : Type} (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item <= upper item) →
        listQSum lower items <= listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

private theorem mul4_rearrange_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
        (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
          (Q'.mul_eqv_congr_right (b * c) (c * b) d
            (Q'.mul_comm_eqv b c)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
            (Q'.mul_assoc_eqv c b d))
          (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))))))

/-! ## 2. One literal joint density in its two presentations -/

/-- The grouped expanded-source target density of an observable pair is the
pair's normalized accepted Gibbs mass times its genuine two-replica enriched
kernel row. -/
theorem allCutoffObservablePairExpandedTargetWeight_eqv_normalizedKernel
    (S : SlabScalePair) {rootFaceId : Nat}
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    allCutoffExpandedSourceEntryPairTargetWeight S target
        (slabObservablePairExpandedSourceEntries S.fine source) ≈
      slabObservableTwoReplicaPairNormalizedMass S.fine source *
        allCutoffRetainedTwoReplicaKernel S source target := by
  unfold allCutoffExpandedSourceEntryPairTargetWeight
    allCutoffExpandedSourceJointWeight allCutoffExpandedSourceKernel
    allCutoffRetainedTwoReplicaKernel
  refine Q'.eqv_trans _
    ((allCutoffExpandedSourceNormalizedMass S.fine
          (slabObservablePairLeftExpandedSourceEntry S.fine source).1 *
        allCutoffExpandedSourceNormalizedMass S.fine
          (slabObservablePairRightExpandedSourceEntry S.fine source).1) *
      (allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairLeftPhysicalSource S.fine source) target.1 *
        allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairRightPhysicalSource S.fine source) target.2)) _
    (mul4_rearrange_local _ _ _ _) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (by
      simpa only [slabObservableTwoReplicaPairNormalizedMass] using
        slabObservablePairExpandedNormalizedMass_eqv S.fine source)

/-- For one retained connected source, summing the target-major expanded
density over the literal target four-cell gives its source-major landing
mass. -/
theorem allCutoffObservablePairExpandedTargetFourCellMass_eqv_landingMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) :
    listQSum
        (fun target =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        ((allCutoffRetainedTwoReplicaTargets S).filter
          (allCutoffRetainedBranchFourCellB M)) ≈
      allCutoffRetainedSourceFourCellLandingMass S M source := by
  refine Q'.eqv_trans _
    (listQSum
      (fun target =>
        slabObservableTwoReplicaPairNormalizedMass S.fine source *
          allCutoffRetainedTwoReplicaKernel S source target)
      ((allCutoffRetainedTwoReplicaTargets S).filter
        (allCutoffRetainedBranchFourCellB M))) _ ?_ ?_
  · apply listQSum_congr_on _ _
      ((allCutoffRetainedTwoReplicaTargets S).filter
        (allCutoffRetainedBranchFourCellB M))
    intro target _
    exact allCutoffObservablePairExpandedTargetWeight_eqv_normalizedKernel
      S source target
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairNormalizedMass S.fine source *
      listQSum
        (allCutoffRetainedTwoReplicaKernel S source)
        ((allCutoffRetainedTwoReplicaTargets S).filter
          (allCutoffRetainedBranchFourCellB M))) _ ?_ ?_
  · exact listQSum_mul_left
      (slabObservableTwoReplicaPairNormalizedMass S.fine source)
      (allCutoffRetainedTwoReplicaKernel S source)
      ((allCutoffRetainedTwoReplicaTargets S).filter
        (allCutoffRetainedBranchFourCellB M))
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairNormalizedMass S.fine source *
      listQSum
        (fun target =>
          allCutoffRetainedTwoReplicaKernel S source target *
            rationalBoolIndicator
              (allCutoffRetainedBranchFourCellB M target))
        (allCutoffRetainedTwoReplicaTargets S)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (Q'.eqv_symm
        (listQSum_mul_indicator_eqv_filter
          (allCutoffRetainedTwoReplicaKernel S source)
          (allCutoffRetainedBranchFourCellB M)
          (allCutoffRetainedTwoReplicaTargets S)))
  · unfold allCutoffRetainedSourceFourCellLandingMass
    exact Q'.eqv_symm
      (listQSum_mul_left
        (slabObservableTwoReplicaPairNormalizedMass S.fine source)
        (fun target =>
          allCutoffRetainedTwoReplicaKernel S source target *
            rationalBoolIndicator
              (allCutoffRetainedBranchFourCellB M target))
        (allCutoffRetainedTwoReplicaTargets S))

/-! ## 3. Target-major retained source restriction -/

/-- The retained-incoherent part of the observable connected source carrier,
named separately to keep the Fubini statement small. -/
def retainedConnectedSourcePairs
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    List (SlabObservableTwoReplicaPair S.fine M.fineRoot) :=
  slabObservableRetainedIncoherentConnectedPairs
    S M.fineRoot M.fineTarget

/-- The branch-explicit target four-cell carrier. -/
def retainedTargetFourCellPairs
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    List (AllCutoffRetainedTarget × AllCutoffRetainedTarget) :=
  (allCutoffRetainedTwoReplicaTargets S).filter
    (allCutoffRetainedBranchFourCellB M)

/-- The literal expanded source-target density used in the restricted
target-major joint mass. -/
def retainedConnectedExpandedJointWeight
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) : Q' :=
  allCutoffExpandedSourceEntryPairTargetWeight S target
    (slabObservablePairExpandedSourceEntries S.fine source)

/-- The target-first joint mass obtained by restricting both the connected
source carrier to its retained-incoherent part and the target carrier to the
literal branch-explicit four-cell. -/
def allCutoffRetainedConnectedTargetFourCellSubmass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) : Q' :=
  listQSum
    (fun target =>
      listQSum
        (retainedConnectedExpandedJointWeight S M target)
        (retainedConnectedSourcePairs S M))
    (retainedTargetFourCellPairs S M)

/-- Finite Fubini identifies the target-major retained restriction with the
source-major landing mass. -/
theorem allCutoffRetainedConnectedTargetFourCellSubmass_eqv_landingMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffRetainedConnectedTargetFourCellSubmass S M ≈
      allCutoffRetainedConnectedFourCellLandingMass S M := by
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target => retainedConnectedExpandedJointWeight S M target source)
          (retainedTargetFourCellPairs S M))
      (retainedConnectedSourcePairs S M)) _ ?_ ?_
  · unfold allCutoffRetainedConnectedTargetFourCellSubmass
    exact Q'.eqv_symm
      (listQSum_swap (retainedConnectedExpandedJointWeight S M)
        (retainedTargetFourCellPairs S M)
        (retainedConnectedSourcePairs S M))
  · unfold allCutoffRetainedConnectedFourCellLandingMass
    unfold retainedConnectedSourcePairs retainedTargetFourCellPairs
      retainedConnectedExpandedJointWeight
    apply listQSum_congr_on _ _
      (slabObservableRetainedIncoherentConnectedPairs
        S M.fineRoot M.fineTarget)
    intro source _
    exact allCutoffObservablePairExpandedTargetFourCellMass_eqv_landingMass
      S M source

/-! ## 4. Inclusion in the full connected target event -/

private theorem connectedTargetContribution_eqv_originalSourcePairs
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    allCutoffConnectedExpandedTargetContribution
        S rootFaceId targetFaceId target ≈
      listQSum
        (fun source =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.fine rootFaceId targetFaceId) := by
  unfold allCutoffConnectedExpandedTargetContribution
    allCutoffConnectedExpandedSourceEntryPairs
  rw [listQSum_map]
  exact Q'.eqv_refl _

private theorem retainedSourceTargetMass_le_connectedContribution
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    listQSum
        (fun source =>
          allCutoffExpandedSourceEntryPairTargetWeight S target
            (slabObservablePairExpandedSourceEntries S.fine source))
        (slabObservableRetainedIncoherentConnectedPairs
          S M.fineRoot M.fineTarget) <=
      allCutoffConnectedExpandedTargetContribution
        S M.fineRoot M.fineTarget target := by
  refine Q'.le_trans' _
    (listQSum
      (fun source =>
        allCutoffExpandedSourceEntryPairTargetWeight S target
          (slabObservablePairExpandedSourceEntries S.fine source))
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget)) _ ?_ ?_
  · unfold slabObservableRetainedIncoherentConnectedPairs
    apply listQSum_filter_le_of_nonnegative
    intro source
    exact allCutoffExpandedSourceEntryPairTargetWeight_nonnegative
      S target (slabObservablePairExpandedSourceEntries S.fine source)
  · exact Q'.ge_of_eqv
      (connectedTargetContribution_eqv_originalSourcePairs
        S M.fineRoot M.fineTarget target)

/-- **Target-submeasure inclusion.**  The retained source-target landing mass
is a genuine submass of the full branch-explicit connected target event. -/
theorem allCutoffRetainedConnectedFourCellLandingMass_le_targetEventMass
    (S : SlabScalePair) (M : SlabFaceBlockMap S) :
    allCutoffRetainedConnectedFourCellLandingMass S M <=
      allCutoffConnectedExpandedTargetFourCellMass S M := by
  refine Q'.le_trans' _
    (allCutoffRetainedConnectedTargetFourCellSubmass S M) _ ?_ ?_
  · exact Q'.ge_of_eqv
      (allCutoffRetainedConnectedTargetFourCellSubmass_eqv_landingMass S M)
  · unfold allCutoffRetainedConnectedTargetFourCellSubmass
      allCutoffConnectedExpandedTargetFourCellMass
      allCutoffConnectedExpandedTargetEventMass
    apply listQSum_mono_local
    intro target _
    exact retainedSourceTargetMass_le_connectedContribution S M target

/-! ## Axiom audit -/

#print axioms allCutoffObservablePairExpandedTargetWeight_eqv_normalizedKernel
#print axioms allCutoffRetainedConnectedTargetFourCellSubmass_eqv_landingMass
#print axioms allCutoffRetainedConnectedFourCellLandingMass_le_targetEventMass

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellSubmass
