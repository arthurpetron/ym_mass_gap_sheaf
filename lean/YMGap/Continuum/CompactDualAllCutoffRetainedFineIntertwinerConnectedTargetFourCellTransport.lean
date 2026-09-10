/-
# Exact retained transport into the enriched observable four-cell

The one-copy retained branch preserves every fine physical Boolean event.
Here that identity is contracted with the independent two-replica kernel and
the literal source determinant cell.  A support-connected source pair whose
two raw recoupling partitions are nonpositive lands in the branch-explicit
enriched target `11 x 00` event with conditional mass exactly one.

Thus the retained connected observable sector is not merely bounded by an
abstract target event: the event is forced rowwise.  The theorem deliberately
does not say this for a coherent source row; its coarse observable moment is
the remaining transport defect identified in the preceding module.

No covariance equality, reflection identity, strict form bound, continuum
limit, or Clay theorem is asserted here.

## Axiom gate

Boolean determinant-cell membership, exact product-row Fubini, and retained
event preservation only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetEvent
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTargetEventTransport
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The two one-copy events making up `11 x 00` -/

def finePositivePairB {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (physical : EdgeLabelling) : Bool :=
  slabPhysicalFacePositiveB M.fineRoot physical &&
    slabPhysicalFacePositiveB M.fineTarget physical

def coarsePositivePairB {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (physical : EdgeLabelling) : Bool :=
  slabPhysicalFacePositiveB M.coarseRoot physical &&
    slabPhysicalFacePositiveB M.coarseTarget physical

def fineZeroPairB {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (physical : EdgeLabelling) : Bool :=
  (!slabPhysicalFacePositiveB M.fineRoot physical) &&
    (!slabPhysicalFacePositiveB M.fineTarget physical)

def coarseZeroPairB {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (physical : EdgeLabelling) : Bool :=
  (!slabPhysicalFacePositiveB M.coarseRoot physical) &&
    (!slabPhysicalFacePositiveB M.coarseTarget physical)

private theorem rationalBoolIndicator_and (left right : Bool) :
    rationalBoolIndicator (left && right) ≈
      rationalBoolIndicator left * rationalBoolIndicator right := by
  cases left <;> cases right <;> decide

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

private theorem branchFourCellIndicator_eqv_product
    {S : SlabScalePair} (M : SlabFaceBlockMap S)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    rationalBoolIndicator (allCutoffRetainedBranchFourCellB M target) ≈
      allCutoffRetainedBranchEventIndicator
          (finePositivePairB M) (coarsePositivePairB M) target.1 *
        allCutoffRetainedBranchEventIndicator
          (fineZeroPairB M) (coarseZeroPairB M) target.2 := by
  rcases target with ⟨left, right⟩
  cases left <;> cases right <;>
    exact rationalBoolIndicator_and _ _

/-! ## 2. Product-row factorization of the literal target event -/

/-- Conditional mass of the literal enriched target `11 x 00` event in the
two-copy kernel row above one observable source pair. -/
def allCutoffRetainedTwoReplicaFourCellEventMoment
    (S : SlabScalePair) {rootFaceId : Nat}
    (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId) : Q' :=
  listQSum
    (fun target =>
      allCutoffRetainedTwoReplicaKernel S source target *
        rationalBoolIndicator
          (allCutoffRetainedBranchFourCellB M target))
    (allCutoffRetainedTwoReplicaTargets S)

private theorem twoReplicaFourCell_term_factorization
    (S : SlabScalePair) {rootFaceId : Nat}
    (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) :
    allCutoffRetainedTwoReplicaKernel S source target *
        rationalBoolIndicator
          (allCutoffRetainedBranchFourCellB M target) ≈
      (allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairLeftPhysicalSource S.fine source) target.1 *
        allCutoffRetainedBranchEventIndicator
          (finePositivePairB M) (coarsePositivePairB M) target.1) *
      (allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairRightPhysicalSource S.fine source) target.2 *
        allCutoffRetainedBranchEventIndicator
          (fineZeroPairB M) (coarseZeroPairB M) target.2) := by
  unfold allCutoffRetainedTwoReplicaKernel
  refine Q'.eqv_trans _
    ((allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairLeftPhysicalSource S.fine source) target.1 *
      allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairRightPhysicalSource S.fine source) target.2) *
      (allCutoffRetainedBranchEventIndicator
          (finePositivePairB M) (coarsePositivePairB M) target.1 *
        allCutoffRetainedBranchEventIndicator
          (fineZeroPairB M) (coarseZeroPairB M) target.2)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (branchFourCellIndicator_eqv_product M target)
  · exact mul4_rearrange_local _ _ _ _

/-- The literal two-replica target event factors into the two independent
one-copy branch-explicit event moments. -/
theorem allCutoffRetainedTwoReplicaFourCellEventMoment_factorization
    (S : SlabScalePair) {rootFaceId : Nat}
    (M : SlabFaceBlockMap S)
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId) :
    allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈
      allCutoffRetainedFineIntertwinerEventMoment S
          (slabObservablePairLeftPhysicalSource S.fine source)
          (finePositivePairB M) (coarsePositivePairB M) *
      allCutoffRetainedFineIntertwinerEventMoment S
          (slabObservablePairRightPhysicalSource S.fine source)
          (fineZeroPairB M) (coarseZeroPairB M) := by
  let leftWeight : AllCutoffRetainedTarget → Q' := fun target =>
    allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairLeftPhysicalSource S.fine source) target *
      allCutoffRetainedBranchEventIndicator
        (finePositivePairB M) (coarsePositivePairB M) target
  let rightWeight : AllCutoffRetainedTarget → Q' := fun target =>
    allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairRightPhysicalSource S.fine source) target *
      allCutoffRetainedBranchEventIndicator
        (fineZeroPairB M) (coarseZeroPairB M) target
  unfold allCutoffRetainedTwoReplicaFourCellEventMoment
    allCutoffRetainedTwoReplicaTargets
  refine Q'.eqv_trans _
    (listQSum
      (fun target => leftWeight target.1 * rightWeight target.2)
      (cartesian (allCutoffRetainedTargets S)
        (allCutoffRetainedTargets S))) _ ?_ ?_
  · apply listQSum_congr_on _ _
      (cartesian (allCutoffRetainedTargets S)
        (allCutoffRetainedTargets S))
    intro target _
    unfold leftWeight rightWeight
    exact twoReplicaFourCell_term_factorization S M source target
  refine Q'.eqv_trans _
    (listQSum leftWeight (allCutoffRetainedTargets S) *
      listQSum rightWeight (allCutoffRetainedTargets S)) _ ?_ ?_
  · exact listQSum_cartesian_product leftWeight rightWeight
      (allCutoffRetainedTargets S) (allCutoffRetainedTargets S)
  · unfold leftWeight rightWeight
    exact Q'.eqv_refl _

/-! ## 3. Retained connected rows force the target four-cell -/

/-- Every positive-incoherent connected source pair lands in the literal
branch-explicit enriched target `11 x 00` event with conditional mass one. -/
theorem allCutoffRetainedTwoReplicaFourCellEventMoment_eq_one
    (S : SlabScalePair) (M : SlabFaceBlockMap S)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (source : SlabObservableTwoReplicaPair S.fine M.fineRoot)
    (hsource : source ∈ slabObservableRetainedIncoherentConnectedPairs
      S M.fineRoot M.fineTarget) :
    allCutoffRetainedTwoReplicaFourCellEventMoment S M source ≈ 1 := by
  have hincoherent := (List.mem_filter.mp hsource).2
  have hleftIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S source.1.1.1 := by
    intro hpositive
    simp [slabObservablePairRetainedIncoherentB, hpositive] at hincoherent
  have hrightIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S source.2.1.1 := by
    intro hpositive
    simp [slabObservablePairRetainedIncoherentB, hpositive] at hincoherent
  have hleftTarget : (Sum.inr source.1.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S source.1.1).mpr
      source.1.source_mem_expanded
  have hrightTarget : (Sum.inr source.2.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S source.2.1).mpr source.2.2
  have hleftPositive : (0 : Q') < S.fine.physicalTerm source.1.1.1 :=
    retainedFineTargetPhysicalTerm_pos_of_coupling_pos
      S source.1.1 hleftTarget hcoupling
  have hrightPositive : (0 : Q') < S.fine.physicalTerm source.2.1.1 :=
    retainedFineTargetPhysicalTerm_pos_of_coupling_pos
      S source.2.1 hrightTarget hcoupling
  have hconnected := (List.mem_filter.mp hsource).1
  have hfourCell := (List.mem_filter.mp hconnected).1
  have hcell := (mem_cartesian_iff _ _ source).mp hfourCell
  have hleftTargetPositive := (List.mem_filter.mp hcell.1).2
  have hrightZero := (List.mem_filter.mp hcell.2).2
  have hleftRootB :
      slabPhysicalFacePositiveB M.fineRoot source.1.1.1 = true := by
    unfold slabPhysicalFacePositiveB
    exact decide_eq_true source.1.source_positive
  have hleftTargetB :
      slabPhysicalFacePositiveB M.fineTarget source.1.1.1 = true := by
    exact hleftTargetPositive
  have hrightZeroParts := (Bool.and_eq_true _ _).mp hrightZero
  have hrightRootB :
      (!slabPhysicalFacePositiveB M.fineRoot source.2.1.1) = true := by
    exact hrightZeroParts.1
  have hrightTargetB :
      (!slabPhysicalFacePositiveB M.fineTarget source.2.1.1) = true := by
    exact hrightZeroParts.2
  have hleftEvent : finePositivePairB M source.1.1.1 = true := by
    unfold finePositivePairB
    rw [hleftRootB, hleftTargetB]
    decide
  have hrightEvent : fineZeroPairB M source.2.1.1 = true := by
    unfold fineZeroPairB
    rw [hrightRootB, hrightTargetB]
    decide
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
      rationalBoolIndicator (fineZeroPairB M source.2.1.1)) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
          S (slabObservablePairLeftPhysicalSource S.fine source)
          hleftPositive hleftIncoherent
          (finePositivePairB M) (coarsePositivePairB M)))
      (Q'.mul_eqv_congr_left _ _ _
        (allCutoffRetainedFineIntertwinerEventMoment_eq_fine_of_incoherent
          S (slabObservablePairRightPhysicalSource S.fine source)
          hrightPositive hrightIncoherent
          (fineZeroPairB M) (coarseZeroPairB M)))
  · rw [hleftEvent, hrightEvent]
    exact Q'.one_mul_eqv 1

/-! ## Axiom audit -/

#print axioms allCutoffRetainedTwoReplicaFourCellEventMoment_factorization
#print axioms allCutoffRetainedTwoReplicaFourCellEventMoment_eq_one

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetFourCellTransport
