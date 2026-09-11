/-
# Finite disconnected cancellation for the connected-observable gradients

The root and target pieces of the exact symmetric-gradient factorization each
live on an existing one-face active carrier.  On its disconnected branch the
observable-rooted component swap permutes the carrier and sends the complete
gradient-weighted summand to its exact negative.  This file performs the
finite reindexing and proves that both disconnected sums vanish.

Thus each complete active gradient sum contracts exactly to its connected
carrier before any absolute-value estimate.  No connected-carrier envelope,
posterior-variance bound for the connected observable, dense form bound,
completed gap, thermodynamic limit, continuum theory, or Clay theorem is
asserted here.

Constructive contract: finite list permutations and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientDisconnectedCancellation

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
      listQSum (fun item => -(value item)) items ≈
        -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem two_mul_eqv_add_self_local (value : Q') :
    Q'.ofNat 2 * value ≈ value + value := by
  refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * value) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * value + Q'.ofNat 1 * value) _
    (Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) value) ?_
  exact Q'.add_eqv_congr' (Q'.one_mul_eqv value)
    (Q'.one_mul_eqv value)

private theorem eqv_neg_self_implies_zero_local
    (value : Q') (hneg : value ≈ -value) : value ≈ 0 := by
  have hadd : value + value ≈ 0 := by
    refine Q'.eqv_trans _ (value + (-value)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left value value (-value) hneg
    · exact Q'.add_neg_self_eqv value
  have htwice : Q'.ofNat 2 * value ≈ 0 :=
    Q'.eqv_trans _ _ _ (two_mul_eqv_add_self_local value) hadd
  exact Q'.mul_eqv_zero_of_pos (Q'.ofNat_succ_pos 1) htwice

/-! ## 1. A reusable finite cancellation contraction -/

/-- A finite sum is zero when a self-permutation sends every summand to its
exact negative.  The permutation and pointwise sign law are explicit inputs;
no quotient by orbits or excluded middle is used. -/
theorem listQSum_eqv_zero_of_perm_negation
    {A : Type} (carrier : List A) (swap : A → A) (term : A → Q')
    (hperm : (carrier.map swap).Perm carrier)
    (hsign : ∀ item, item ∈ carrier → term (swap item) ≈ -(term item)) :
    listQSum term carrier ≈ 0 := by
  have hreindex : listQSum term carrier ≈
      listQSum (fun item => term (swap item)) carrier := by
    refine Q'.eqv_trans _ (listQSum term (carrier.map swap)) _ ?_ ?_
    · exact listQSum_perm term hperm.symm
    · exact Q'.eqv_of_eq (listQSum_map term swap carrier)
  have hpointwise : listQSum (fun item => term (swap item)) carrier ≈
      listQSum (fun item => -(term item)) carrier := by
    apply listQSum_congr_on
    exact hsign
  have hneg : listQSum (fun item => -(term item)) carrier ≈
      -(listQSum term carrier) := listQSum_neg_local term carrier
  have hselfNeg : listQSum term carrier ≈ -(listQSum term carrier) :=
    Q'.eqv_trans _ _ _ hreindex (Q'.eqv_trans _ _ _ hpointwise hneg)
  exact eqv_neg_self_implies_zero_local (listQSum term carrier) hselfNeg

private theorem disconnectedActivePair_parts_local
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseDisconnectedActivePairs
      S first second observableFaceId) :
    finePacketLocalizedResponsePairActiveB S first second
          (slabPhysicalFacePositiveB observableFaceId) pair = true ∧
      finePacketObservableConnectedDisagreementB
          S first second observableFaceId pair = false := by
  have hparts := List.mem_filter.mp hpair
  have hactiveParts := List.mem_filter.mp hparts.1
  refine ⟨hactiveParts.2, ?_⟩
  cases htest : finePacketObservableConnectedDisagreementB
      S first second observableFaceId pair with
  | false => rfl
  | true =>
      have hbad : !true = true := by
        simpa [htest] using hparts.2
      exact False.elim (Bool.noConfusion hbad)

/-! ## 2. Root- and target-gradient disconnected sums vanish -/

theorem connectedRootGradientDisconnectedPairSum_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedRootGradientPairTerm
          K M first second)
        (finePacketFaceResponseDisconnectedActivePairs
          S first second M.coarseRoot) ≈ 0 := by
  apply listQSum_eqv_zero_of_perm_negation
    (finePacketFaceResponseDisconnectedActivePairs
      S first second M.coarseRoot)
    (finePacketObservableComponentSwap S M.coarseRoot)
    (finePacketLocalizedConnectedRootGradientPairTerm K M first second)
  · exact finePacketObservableComponentSwap_disconnected_perm
      S first second M.coarseRoot
  · intro pair hpair
    have hparts := disconnectedActivePair_parts_local
      S first second M.coarseRoot pair hpair
    exact localizedConnectedRootGradientPairTerm_componentSwap
      K M first second pair hparts.1 hparts.2

theorem connectedTargetGradientDisconnectedPairSum_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedTargetGradientPairTerm
          K M first second)
        (finePacketFaceResponseDisconnectedActivePairs
          S first second M.coarseTarget) ≈ 0 := by
  apply listQSum_eqv_zero_of_perm_negation
    (finePacketFaceResponseDisconnectedActivePairs
      S first second M.coarseTarget)
    (finePacketObservableComponentSwap S M.coarseTarget)
    (finePacketLocalizedConnectedTargetGradientPairTerm K M first second)
  · exact finePacketObservableComponentSwap_disconnected_perm
      S first second M.coarseTarget
  · intro pair hpair
    have hparts := disconnectedActivePair_parts_local
      S first second M.coarseTarget pair hpair
    exact localizedConnectedTargetGradientPairTerm_componentSwap
      K M first second pair hparts.1 hparts.2

/-! ## 3. Complete active sums contract to connected carriers -/

theorem connectedRootGradientActivePairSum_eqv_connected
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedRootGradientPairTerm
          K M first second)
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB M.coarseRoot)) ≈
      listQSum
        (finePacketLocalizedConnectedRootGradientPairTerm
          K M first second)
        (finePacketFaceResponseConnectedActivePairs
          S first second M.coarseRoot) := by
  let term := finePacketLocalizedConnectedRootGradientPairTerm
    K M first second
  let connected := finePacketFaceResponseConnectedActivePairs
    S first second M.coarseRoot
  let disconnected := finePacketFaceResponseDisconnectedActivePairs
    S first second M.coarseRoot
  refine Q'.eqv_trans _
    (listQSum term connected + listQSum term disconnected) _ ?_ ?_
  · exact listQSum_filter_partition term
      (finePacketObservableConnectedDisagreementB
        S first second M.coarseRoot)
      (finePacketLocalizedResponseActivePairs S first second
        (slabPhysicalFacePositiveB M.coarseRoot))
  refine Q'.eqv_trans _ (listQSum term connected + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (connectedRootGradientDisconnectedPairSum_eqv_zero
        K M first second)
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

theorem connectedTargetGradientActivePairSum_eqv_connected
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling) :
    listQSum
        (finePacketLocalizedConnectedTargetGradientPairTerm
          K M first second)
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB M.coarseTarget)) ≈
      listQSum
        (finePacketLocalizedConnectedTargetGradientPairTerm
          K M first second)
        (finePacketFaceResponseConnectedActivePairs
          S first second M.coarseTarget) := by
  let term := finePacketLocalizedConnectedTargetGradientPairTerm
    K M first second
  let connected := finePacketFaceResponseConnectedActivePairs
    S first second M.coarseTarget
  let disconnected := finePacketFaceResponseDisconnectedActivePairs
    S first second M.coarseTarget
  refine Q'.eqv_trans _
    (listQSum term connected + listQSum term disconnected) _ ?_ ?_
  · exact listQSum_filter_partition term
      (finePacketObservableConnectedDisagreementB
        S first second M.coarseTarget)
      (finePacketLocalizedResponseActivePairs S first second
        (slabPhysicalFacePositiveB M.coarseTarget))
  refine Q'.eqv_trans _ (listQSum term connected + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (connectedTargetGradientDisconnectedPairSum_eqv_zero
        K M first second)
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

/-! ## 4. Axiom audit -/

#print axioms listQSum_eqv_zero_of_perm_negation
#print axioms connectedRootGradientDisconnectedPairSum_eqv_zero
#print axioms connectedTargetGradientDisconnectedPairSum_eqv_zero
#print axioms connectedRootGradientActivePairSum_eqv_connected
#print axioms connectedTargetGradientActivePairSum_eqv_connected

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableGradientDisconnectedCancellation
