/-
# Constructive branch cases for the coherent target-event excess

The coherent-or-mixed excess is supported on connected source pairs for which
at least one raw whole-slab recoupling partition is positive.  This module
classifies each such pair constructively into the three possible cases and
computes its two-replica target four-cell moment exactly:

* left coherent, right retained: one left coarse event moment;
* left retained, right coherent: one right coarse event moment;
* both coherent: the product of the two coarse event moments.

Fine determinant-cell membership makes every retained factor exactly one.
Consequently no retained observable error remains inside the excess.  The
only open analytic quantities are literal event moments of the genuine
whole-slab coarse recoupling rows.

No smallness estimate, covariance equality, reflection identity, strict form
bound, continuum limit, or Clay theorem is asserted.

## Axiom gate

Decidable branch classification, source-carrier membership, and exact event
moment identities only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentExcess

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentCases

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentExcess
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fine determinant-cell facts and physical positivity -/

private theorem connectedSource_mem_fourCell
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget) :
    source ∈ slabObservableFourCellSourcePairs
      S.fine M.fineRoot M.fineTarget :=
  (List.mem_filter.mp hsource).1

theorem connectedSource_leftFineEvent_true
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget) :
    finePositivePairB M source.1.1.1 = true := by
  have hcell := (mem_cartesian_iff _ _ source).mp
    (connectedSource_mem_fourCell S M source hsource)
  have htarget := (List.mem_filter.mp hcell.1).2
  have hroot :
      slabPhysicalFacePositiveB M.fineRoot source.1.1.1 = true := by
    unfold slabPhysicalFacePositiveB
    exact decide_eq_true source.1.source_positive
  have htarget' :
      slabPhysicalFacePositiveB M.fineTarget source.1.1.1 = true :=
    htarget
  unfold finePositivePairB
  rw [hroot, htarget']
  decide

theorem connectedSource_rightFineEvent_true
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget) :
    fineZeroPairB M source.2.1.1 = true := by
  have hcell := (mem_cartesian_iff _ _ source).mp
    (connectedSource_mem_fourCell S M source hsource)
  have hzero := (List.mem_filter.mp hcell.2).2
  have hparts := (Bool.and_eq_true _ _).mp hzero
  have hroot :
      (!slabPhysicalFacePositiveB M.fineRoot source.2.1.1) = true :=
    hparts.1
  have htarget :
      (!slabPhysicalFacePositiveB M.fineTarget source.2.1.1) = true :=
    hparts.2
  unfold fineZeroPairB
  rw [hroot, htarget]
  decide

theorem connectedSource_leftPhysicalTerm_pos
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) :
    (0 : Q') < S.fine.physicalTerm source.1.1.1 := by
  have htarget : (Sum.inr source.1.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S source.1.1).mpr
      source.1.source_mem_expanded
  exact retainedFineTargetPhysicalTerm_pos_of_coupling_pos
    S source.1.1 htarget hcoupling

theorem connectedSource_rightPhysicalTerm_pos
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) :
    (0 : Q') < S.fine.physicalTerm source.2.1.1 := by
  have htarget : (Sum.inr source.2.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S source.2.1).mpr source.2.2
  exact retainedFineTargetPhysicalTerm_pos_of_coupling_pos
    S source.2.1 htarget hcoupling

/-! ## 2. The two literal coarse recoupling event moments -/

def leftCoherentPositivePairMoment
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hcoherent : (0 : Q') <
      wholeSlabRawRowPartition S source.1.1.1) : Q' :=
  listQSum
    (fun coarseState =>
      wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.1.1.1 source.1.physical_mem hcoherent) coarseState *
        rationalBoolIndicator (coarsePositivePairB M coarseState))
    S.coarse.physicalLabellings

def rightCoherentZeroPairMoment
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hcoherent : (0 : Q') <
      wholeSlabRawRowPartition S source.2.1.1) : Q' :=
  listQSum
    (fun coarseState =>
      wholeSlabRecouplingConditionalKernel
          (coherentSlabRecouplingSourceOfRawPartitionPos
            S source.2.1.1
            (mem_slabExpandedFineSources_iff.mp source.2.2).1
            hcoherent) coarseState *
        rationalBoolIndicator (coarseZeroPairB M coarseState))
    S.coarse.physicalLabellings

/-! ## 3. Exact three-case two-replica identities -/

theorem twoReplicaFourCellMoment_eqv_leftCoherent
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget)
    (hleft : (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
    (hright : ¬ (0 : Q') < wholeSlabRawRowPartition S source.2.1.1) :
    allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
      leftCoherentPositivePairMoment S M source hleft := by
  refine Q'.eqv_trans _
    (allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairLeftPhysicalSource S.fine source)
        (finePositivePairB M) (coarsePositivePairB M) *
      allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairRightPhysicalSource S.fine source)
        (fineZeroPairB M) (coarseZeroPairB M)) _
    (allCutoffRetainedTwoReplicaFourCellEventMoment_factorization
      S M source) ?_
  refine Q'.eqv_trans _
    (leftCoherentPositivePairMoment S M source hleft *
      rationalBoolIndicator (fineZeroPairB M source.2.1.1)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (by
          unfold leftCoherentPositivePairMoment
          exact allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
            S (slabObservablePairLeftPhysicalSource S.fine source)
            (connectedSource_leftPhysicalTerm_pos S M hcoupling source)
            hleft (finePositivePairB M) (coarsePositivePairB M)))
      (Q'.mul_eqv_congr_left _ _ _
        (allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
          S (slabObservablePairRightPhysicalSource S.fine source)
          (connectedSource_rightPhysicalTerm_pos S M hcoupling source)
          hright (fineZeroPairB M) (coarseZeroPairB M)))
  · rw [connectedSource_rightFineEvent_true S M source hsource]
    exact Q'.mul_one_eqv _

theorem twoReplicaFourCellMoment_eqv_rightCoherent
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine M.fineRoot M.fineTarget)
    (hleft : ¬ (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
    (hright : (0 : Q') < wholeSlabRawRowPartition S source.2.1.1) :
    allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
      rightCoherentZeroPairMoment S M source hright := by
  refine Q'.eqv_trans _
    (allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairLeftPhysicalSource S.fine source)
        (finePositivePairB M) (coarsePositivePairB M) *
      allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairRightPhysicalSource S.fine source)
        (fineZeroPairB M) (coarseZeroPairB M)) _
    (allCutoffRetainedTwoReplicaFourCellEventMoment_factorization
      S M source) ?_
  refine Q'.eqv_trans _
    (rationalBoolIndicator (finePositivePairB M source.1.1.1) *
      rightCoherentZeroPairMoment S M source hright) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
          S (slabObservablePairLeftPhysicalSource S.fine source)
          (connectedSource_leftPhysicalTerm_pos S M hcoupling source)
          hleft (finePositivePairB M) (coarsePositivePairB M)))
      (Q'.mul_eqv_congr_left _ _ _
        (by
          unfold rightCoherentZeroPairMoment
          exact allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
            S (slabObservablePairRightPhysicalSource S.fine source)
            (connectedSource_rightPhysicalTerm_pos S M hcoupling source)
            hright (fineZeroPairB M) (coarseZeroPairB M)))
  · rw [connectedSource_leftFineEvent_true S M source hsource]
    exact Q'.one_mul_eqv _

theorem twoReplicaFourCellMoment_eqv_bothCoherent
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hleft : (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
    (hright : (0 : Q') < wholeSlabRawRowPartition S source.2.1.1) :
    allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
      leftCoherentPositivePairMoment S M source hleft *
        rightCoherentZeroPairMoment S M source hright := by
  refine Q'.eqv_trans _
    (allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairLeftPhysicalSource S.fine source)
        (finePositivePairB M) (coarsePositivePairB M) *
      allCutoffRetainedFineIntertwinerEventMoment S
        (slabObservablePairRightPhysicalSource S.fine source)
        (fineZeroPairB M) (coarseZeroPairB M)) _
    (allCutoffRetainedTwoReplicaFourCellEventMoment_factorization
      S M source) ?_
  exact Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _
      (by
        unfold leftCoherentPositivePairMoment
        exact allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
          S (slabObservablePairLeftPhysicalSource S.fine source)
          (connectedSource_leftPhysicalTerm_pos S M hcoupling source)
          hleft (finePositivePairB M) (coarsePositivePairB M)))
    (Q'.mul_eqv_congr_left _ _ _
      (by
        unfold rightCoherentZeroPairMoment
        exact allCutoffRetainedFineIntertwinerEventMoment_eq_coarse_of_coherent
          S (slabObservablePairRightPhysicalSource S.fine source)
          (connectedSource_rightPhysicalTerm_pos S M hcoupling source)
          hright (fineZeroPairB M) (coarseZeroPairB M)))

/-! ## 4. A constructive exhaustive certificate -/

inductive CoherentOrMixedFourCellMomentCase
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot) : Type where
  | leftCoherentRightRetained
      (hleft : (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
      (hright : ¬ (0 : Q') < wholeSlabRawRowPartition S source.2.1.1)
      (moment_eq :
        allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
          leftCoherentPositivePairMoment S M source hleft)
  | leftRetainedRightCoherent
      (hleft : ¬ (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
      (hright : (0 : Q') < wholeSlabRawRowPartition S source.2.1.1)
      (moment_eq :
        allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
          rightCoherentZeroPairMoment S M source hright)
  | bothCoherent
      (hleft : (0 : Q') < wholeSlabRawRowPartition S source.1.1.1)
      (hright : (0 : Q') < wholeSlabRawRowPartition S source.2.1.1)
      (moment_eq :
        allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
          leftCoherentPositivePairMoment S M source hleft *
            rightCoherentZeroPairMoment S M source hright)

/-- Every source in the coherent-or-mixed excess returns an explicit branch
certificate and the corresponding exact coarse-moment formula. -/
def coherentOrMixedFourCellMomentCase
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈ coherentOrMixedConnectedSourcePairs S M) :
    CoherentOrMixedFourCellMomentCase S M source := by
  have hparts := List.mem_filter.mp hsource
  have hconnected := hparts.1
  have hnotRetained := hparts.2
  by_cases hleft : (0 : Q') <
      wholeSlabRawRowPartition S source.1.1.1
  · by_cases hright : (0 : Q') <
        wholeSlabRawRowPartition S source.2.1.1
    · exact CoherentOrMixedFourCellMomentCase.bothCoherent
        hleft hright
        (twoReplicaFourCellMoment_eqv_bothCoherent
          S M hcoupling source hleft hright)
    · exact CoherentOrMixedFourCellMomentCase.leftCoherentRightRetained
        hleft hright
        (twoReplicaFourCellMoment_eqv_leftCoherent
          S M hcoupling source hconnected hleft hright)
  · by_cases hright : (0 : Q') <
        wholeSlabRawRowPartition S source.2.1.1
    · exact CoherentOrMixedFourCellMomentCase.leftRetainedRightCoherent
        hleft hright
        (twoReplicaFourCellMoment_eqv_rightCoherent
          S M hcoupling source hconnected hleft hright)
    · simp [slabObservablePairRetainedIncoherentB, hleft, hright]
        at hnotRetained

/-- Proposition-valued gate wrapper for the explicit case certificate. -/
theorem coherentOrMixedFourCellMomentCase_nonempty
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈ coherentOrMixedConnectedSourcePairs S M) :
    Nonempty (CoherentOrMixedFourCellMomentCase S M source) :=
  ⟨coherentOrMixedFourCellMomentCase S M hcoupling source hsource⟩

/-! ## Axiom audit -/

#print axioms connectedSource_leftFineEvent_true
#print axioms twoReplicaFourCellMoment_eqv_leftCoherent
#print axioms twoReplicaFourCellMoment_eqv_rightCoherent
#print axioms twoReplicaFourCellMoment_eqv_bothCoherent
#print axioms coherentOrMixedFourCellMomentCase_nonempty

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellCoherentCases
