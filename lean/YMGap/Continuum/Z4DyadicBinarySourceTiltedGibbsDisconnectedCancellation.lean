/-
# Exact cancellation of the disconnected tilted-Gibbs response

The observable-rooted component swap is an involution of the disconnected
active target-pair carrier.  Its complete common Gibbs background is
preserved, every source-local tilt is fixed, and the observable difference
changes sign.  This file combines those facts into pointwise antisymmetry and
then reindexes the finite carrier to cancel its total contribution exactly.

This removes the whole disconnected branch before any estimate.  The
connected activity-versus-entropy estimate, uniform response bound, completed
spectral gap, continuum construction, and mass gap remain open.

Constructive contract: finite list permutations and exact rational
equivalence only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsComponentSwapBackground
import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
import YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights
import YMGap.Constructive.CauchyConv

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsComponentSwapBackground
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4SpinDecoratedCrossVolumeWeights

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul_mul_neg_eqv_neg_mul_mul_local
    (a b c : Q') : a * (b * (-c)) ≈ -(a * (b * c)) := by
  refine Q'.eqv_trans _ (a * (-(b * c))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _ (Q'.mul_neg_eqv b c)
  · exact Q'.mul_neg_eqv a (b * c)

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

/-! ## 1. Pointwise sign reversal -/

/-- Every complete localized response term on the disconnected active branch
is sent to its exact negative by the canonical component swap. -/
theorem finePacketLocalizedAntisymmetricResponsePairTerm_componentSwap
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false) :
    finePacketLocalizedAntisymmetricResponsePairTerm S first second
        (slabPhysicalFacePositiveB observableFaceId)
        (finePacketObservableComponentSwap S observableFaceId targetPair) ≈
      -(finePacketLocalizedAntisymmetricResponsePairTerm S first second
        (slabPhysicalFacePositiveB observableFaceId) targetPair) := by
  have hbackground :=
    finePacketCommonExteriorGibbsWeight_pair_componentSwap
      S first second observableFaceId hobservableFace targetPair hactive
  have htiltFirstLeft := finePacketDisagreementTilt_componentSwap_left
    S first first second observableFaceId targetPair hdisconnected
  have htiltSecondLeft := finePacketDisagreementTilt_componentSwap_left
    S second first second observableFaceId targetPair hdisconnected
  have htiltFirstRight := finePacketDisagreementTilt_componentSwap_right
    S first first second observableFaceId targetPair hdisconnected
  have htiltSecondRight := finePacketDisagreementTilt_componentSwap_right
    S second first second observableFaceId targetPair hdisconnected
  have hindicator := finePacketObservableComponentSwap_indicatorDifference
    S first second observableFaceId hobservableFace targetPair hactive
  unfold finePacketLocalizedAntisymmetricResponsePairTerm
    finePacketObservableComponentSwap
  dsimp only [Prod.fst, Prod.snd]
  rw [htiltFirstLeft, htiltSecondLeft,
    htiltFirstRight, htiltSecondRight]
  let background :=
    finePacketCommonExteriorGibbsWeight S first second targetPair.1 *
      finePacketCommonExteriorGibbsWeight S first second targetPair.2
  let determinant :=
    finePacketDisagreementTilt S first first second targetPair.1 *
          finePacketDisagreementTilt S second first second targetPair.2 -
        finePacketDisagreementTilt S second first second targetPair.1 *
          finePacketDisagreementTilt S first first second targetPair.2
  let indicator :=
    booleanEventIndicator
          (slabPhysicalFacePositiveB observableFaceId) targetPair.1 -
        booleanEventIndicator
          (slabPhysicalFacePositiveB observableFaceId) targetPair.2
  refine Q'.eqv_trans _ (background * (determinant * (-indicator))) _ ?_ ?_
  · exact qmul_congr_local hbackground
      (qmul_congr_local (Q'.eqv_refl determinant) hindicator)
  · exact mul_mul_neg_eqv_neg_mul_mul_local
      background determinant indicator

/-! ## 2. Finite involutive cancellation -/

private theorem finePacketObservableComponentSwap_injective_local
    (S : SlabScalePair) (observableFaceId : Nat)
    {left right : EdgeLabelling × EdgeLabelling}
    (heq : finePacketObservableComponentSwap S observableFaceId left =
      finePacketObservableComponentSwap S observableFaceId right) :
    left = right := by
  apply Prod.ext
  · funext faceId
    calc
      left.1 faceId = finePacketObservableComponentSwapLeft S observableFaceId
          (finePacketObservableComponentSwapLeft S observableFaceId left,
            finePacketObservableComponentSwapRight S observableFaceId left)
          faceId := (finePacketObservableComponentSwapLeft_involutive
            S observableFaceId left faceId).symm
      _ = finePacketObservableComponentSwapLeft S observableFaceId
          (finePacketObservableComponentSwapLeft S observableFaceId right,
            finePacketObservableComponentSwapRight S observableFaceId right)
          faceId := congrArg
            (fun pair : EdgeLabelling × EdgeLabelling =>
              finePacketObservableComponentSwapLeft
                S observableFaceId pair faceId) heq
      _ = right.1 faceId := finePacketObservableComponentSwapLeft_involutive
        S observableFaceId right faceId
  · funext faceId
    calc
      left.2 faceId = finePacketObservableComponentSwapRight S observableFaceId
          (finePacketObservableComponentSwapLeft S observableFaceId left,
            finePacketObservableComponentSwapRight S observableFaceId left)
          faceId := (finePacketObservableComponentSwapRight_involutive
            S observableFaceId left faceId).symm
      _ = finePacketObservableComponentSwapRight S observableFaceId
          (finePacketObservableComponentSwapLeft S observableFaceId right,
            finePacketObservableComponentSwapRight S observableFaceId right)
          faceId := congrArg
            (fun pair : EdgeLabelling × EdgeLabelling =>
              finePacketObservableComponentSwapRight
                S observableFaceId pair faceId) heq
      _ = right.2 faceId := finePacketObservableComponentSwapRight_involutive
        S observableFaceId right faceId

private theorem finePacketObservableComponentSwap_involutive_local
    (S : SlabScalePair) (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) :
    finePacketObservableComponentSwap S observableFaceId
        (finePacketObservableComponentSwap
          S observableFaceId targetPair) = targetPair := by
  let twice := finePacketObservableComponentSwap S observableFaceId
    (finePacketObservableComponentSwap S observableFaceId targetPair)
  have hleftPointwise : ∀ faceId, twice.1 faceId = targetPair.1 faceId := by
    intro faceId
    dsimp only [twice, finePacketObservableComponentSwap, Prod.fst]
    exact finePacketObservableComponentSwapLeft_involutive
      S observableFaceId targetPair faceId
  have hrightPointwise : ∀ faceId, twice.2 faceId = targetPair.2 faceId := by
    intro faceId
    dsimp only [twice, finePacketObservableComponentSwap, Prod.snd]
    exact finePacketObservableComponentSwapRight_involutive
      S observableFaceId targetPair faceId
  have hleft : twice.1 = targetPair.1 := funext hleftPointwise
  have hright : twice.2 = targetPair.2 := funext hrightPointwise
  change twice = targetPair
  exact Prod.ext hleft hright

private theorem finePacketFaceResponseDisconnectedActivePairs_nodup_local
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    (finePacketFaceResponseDisconnectedActivePairs
      S first second observableFaceId).Nodup := by
  unfold finePacketFaceResponseDisconnectedActivePairs
    finePacketLocalizedResponseActivePairs
  apply List.filter_sublist.nodup
  apply List.filter_sublist.nodup
  exact cartesian_nodup
    S.coarse.physicalLabellings S.coarse.physicalLabellings
    (slabPhysicalLabellings_nodup S.coarse)
    (slabPhysicalLabellings_nodup S.coarse)

private theorem finePacketObservableComponentSwap_mem_disconnected_local
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hpair : targetPair ∈ finePacketFaceResponseDisconnectedActivePairs
      S first second observableFaceId) :
    finePacketObservableComponentSwap S observableFaceId targetPair ∈
      finePacketFaceResponseDisconnectedActivePairs
        S first second observableFaceId := by
  unfold finePacketObservableComponentSwap
  have hparts := List.mem_filter.mp hpair
  have hactiveParts := List.mem_filter.mp hparts.1
  have hdisconnected : finePacketObservableConnectedDisagreementB
      S first second observableFaceId targetPair = false := by
    cases htest : finePacketObservableConnectedDisagreementB
        S first second observableFaceId targetPair with
    | false => rfl
    | true =>
        have hbad : !true = true := by
          simpa [htest] using hparts.2
        exact False.elim (Bool.noConfusion hbad)
  let swappedPair : EdgeLabelling × EdgeLabelling :=
    (finePacketObservableComponentSwapLeft S observableFaceId targetPair,
      finePacketObservableComponentSwapRight S observableFaceId targetPair)
  have hphysical : swappedPair ∈ cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings := by
    apply (mem_cartesian_iff S.coarse.physicalLabellings
      S.coarse.physicalLabellings swappedPair).mpr
    simpa [swappedPair] using
      (finePacketObservableComponentSwap_mem_physical
        S observableFaceId targetPair hactiveParts.1)
  have hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB observableFaceId) swappedPair = true := by
    dsimp only [swappedPair]
    rw [finePacketLocalizedResponsePairActiveB_componentSwap
      S first second observableFaceId targetPair hdisconnected]
    exact hactiveParts.2
  have hnotConnected : Bool.not
      (finePacketObservableConnectedDisagreementB
        S first second observableFaceId swappedPair) = true := by
    dsimp only [swappedPair]
    change Bool.not
      (finePacketObservableConnectedDisagreementB S first second
        observableFaceId
          (finePacketObservableComponentSwap
            S observableFaceId targetPair)) = true
    rw [finePacketObservableConnectedDisagreementB_componentSwap]
    exact hparts.2
  have hresult : swappedPair ∈ finePacketFaceResponseDisconnectedActivePairs
      S first second observableFaceId := by
    apply List.mem_filter.mpr
    exact ⟨List.mem_filter.mpr ⟨hphysical, hactive⟩, hnotConnected⟩
  simpa only [swappedPair] using hresult

/-- The canonical component swap literally permutes the duplicate-free
disconnected active carrier. -/
theorem finePacketObservableComponentSwap_disconnected_perm
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    ((finePacketFaceResponseDisconnectedActivePairs
        S first second observableFaceId).map
      (finePacketObservableComponentSwap S observableFaceId)).Perm
      (finePacketFaceResponseDisconnectedActivePairs
        S first second observableFaceId) := by
  let carrier := finePacketFaceResponseDisconnectedActivePairs
    S first second observableFaceId
  let swap := finePacketObservableComponentSwap S observableFaceId
  have hcarrier : carrier.Nodup :=
    finePacketFaceResponseDisconnectedActivePairs_nodup_local
      S first second observableFaceId
  apply perm_of_nodup_mem_iff_constructive (carrier.map swap) carrier
  · apply YMGap.Continuum.CayleyPruferInjection.nodup_map_of_injOn
      swap carrier hcarrier
    intro left _hleft right _hright heq
    exact finePacketObservableComponentSwap_injective_local
      S observableFaceId heq
  · exact hcarrier
  · intro targetPair
    constructor
    · intro hpair
      obtain ⟨sourcePair, hsourcePair, hsourceEq⟩ := List.mem_map.mp hpair
      rw [← hsourceEq]
      exact finePacketObservableComponentSwap_mem_disconnected_local
        S first second observableFaceId sourcePair hsourcePair
    · intro hpair
      have hswapped :=
        finePacketObservableComponentSwap_mem_disconnected_local
          S first second observableFaceId targetPair hpair
      apply List.mem_map.mpr
      refine ⟨finePacketObservableComponentSwap
        S observableFaceId targetPair, hswapped, ?_⟩
      exact finePacketObservableComponentSwap_involutive_local
        S observableFaceId targetPair

/-- The entire disconnected active branch cancels exactly under the
component-swap involution. -/
theorem finePacketFaceResponseDisconnectedActivePairSum_eqv_zero
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm S first second
          (slabPhysicalFacePositiveB observableFaceId))
        (finePacketFaceResponseDisconnectedActivePairs
          S first second observableFaceId) ≈ 0 := by
  let carrier := finePacketFaceResponseDisconnectedActivePairs
    S first second observableFaceId
  let swap := finePacketObservableComponentSwap S observableFaceId
  let term := finePacketLocalizedAntisymmetricResponsePairTerm S first second
    (slabPhysicalFacePositiveB observableFaceId)
  have hperm : (carrier.map swap).Perm carrier := by
    exact finePacketObservableComponentSwap_disconnected_perm
      S first second observableFaceId
  have hreindex : listQSum term carrier ≈
      listQSum (fun pair => term (swap pair)) carrier := by
    refine Q'.eqv_trans _ (listQSum term (carrier.map swap)) _ ?_ ?_
    · exact listQSum_perm term hperm.symm
    · exact Q'.eqv_of_eq (listQSum_map term swap carrier)
  have hsign : listQSum (fun pair => term (swap pair)) carrier ≈
      listQSum (fun pair => -(term pair)) carrier := by
    apply listQSum_congr_on
    intro targetPair hpair
    have hparts := List.mem_filter.mp hpair
    have hactiveParts := List.mem_filter.mp hparts.1
    have hdisconnected : finePacketObservableConnectedDisagreementB
        S first second observableFaceId targetPair = false := by
      cases htest : finePacketObservableConnectedDisagreementB
          S first second observableFaceId targetPair with
      | false => rfl
      | true =>
          have hbad : !true = true := by
            simpa [htest] using hparts.2
          exact False.elim (Bool.noConfusion hbad)
    exact finePacketLocalizedAntisymmetricResponsePairTerm_componentSwap
      S first second observableFaceId hobservableFace targetPair
      hactiveParts.2 hdisconnected
  have hneg : listQSum (fun pair => -(term pair)) carrier ≈
      -(listQSum term carrier) := listQSum_neg_local term carrier
  have hselfNeg : listQSum term carrier ≈
      -(listQSum term carrier) :=
    Q'.eqv_trans _ _ _ hreindex (Q'.eqv_trans _ _ _ hsign hneg)
  exact eqv_neg_self_implies_zero_local (listQSum term carrier) hselfNeg

/-- After exact disconnected cancellation, the complete active one-face
response is supported solely on pairs carrying a source-to-observable
connected path certificate. -/
theorem finePacketFaceResponseActivePairSum_eqv_connected
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm S first second
          (slabPhysicalFacePositiveB observableFaceId))
        (finePacketLocalizedResponseActivePairs S first second
          (slabPhysicalFacePositiveB observableFaceId)) ≈
      listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm S first second
          (slabPhysicalFacePositiveB observableFaceId))
        (finePacketFaceResponseConnectedActivePairs
          S first second observableFaceId) := by
  let term := finePacketLocalizedAntisymmetricResponsePairTerm S first second
    (slabPhysicalFacePositiveB observableFaceId)
  let connected := finePacketFaceResponseConnectedActivePairs
    S first second observableFaceId
  let disconnected := finePacketFaceResponseDisconnectedActivePairs
    S first second observableFaceId
  refine Q'.eqv_trans _
    (listQSum term connected + listQSum term disconnected) _ ?_ ?_
  · exact finePacketFaceResponseActivePairSum_partition
      S first second observableFaceId
  refine Q'.eqv_trans _ (listQSum term connected + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (finePacketFaceResponseDisconnectedActivePairSum_eqv_zero
        S first second observableFaceId hobservableFace)
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

/-- Consequently, twice the actual denominator-cleared two-row response
cross is exactly the connected active-pair sum. -/
theorem two_mul_positivePhysicalTiltedGibbsRawCross_eqv_connectedPairSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    (2 : Q') *
        positivePhysicalTiltedGibbsTwoRowRawCrossNumerator
          S first second (slabPhysicalFacePositiveB observableFaceId) ≈
      listQSum
        (finePacketLocalizedAntisymmetricResponsePairTerm
          S first.1 second.1
          (slabPhysicalFacePositiveB observableFaceId))
        (finePacketFaceResponseConnectedActivePairs
          S first.1 second.1 observableFaceId) := by
  exact Q'.eqv_trans _ _ _
    (two_mul_positivePhysicalTiltedGibbsRawCross_eqv_activePairSum
      S hfineCutoff first second
        (slabPhysicalFacePositiveB observableFaceId))
    (finePacketFaceResponseActivePairSum_eqv_connected
      S first.1 second.1 observableFaceId hobservableFace)

/-! ## 3. Axiom audit -/

#print axioms finePacketLocalizedAntisymmetricResponsePairTerm_componentSwap
#print axioms finePacketObservableComponentSwap_disconnected_perm
#print axioms finePacketFaceResponseDisconnectedActivePairSum_eqv_zero
#print axioms finePacketFaceResponseActivePairSum_eqv_connected
#print axioms two_mul_positivePhysicalTiltedGibbsRawCross_eqv_connectedPairSum

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation
