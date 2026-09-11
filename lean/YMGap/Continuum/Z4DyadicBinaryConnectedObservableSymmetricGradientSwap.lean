/-
# Component-swap covariance of the symmetric connected gradients

The denominator-cleared connected-observable difference splits into a root
face term and a target face term.  This file proves that each coefficient is
invariant under the corresponding observable-rooted component swap.  The
reason is exact and local: at any second face the swap either exchanges the
two replica values or leaves both fixed, so their symmetric indicator sum is
unchanged.

Consequently each gradient-weighted face term reverses sign on the existing
disconnected active carrier.  This is the pointwise cancellation theorem
needed before finite reindexing; no absolute value is taken across the
connected observable's joint and marginal cylinder terms.

No disconnected finite-sum cancellation, global posterior estimate, dense
form bound, completed gap, thermodynamic limit, continuum theory, or Clay
theorem is asserted here.

Constructive contract: Boolean component masks and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, enlarged heartbeat budget, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient
import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation

namespace YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalConnectedRemainderObservable
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradient
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedCancellation
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsDisconnectedComponentSwap
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {a a' b b' : Q'} (ha : a ≈ a') (hb : b ≈ b') :
    a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one]; ac_rfl))

/-! ## 1. Gradient-weighted localized determinant terms -/

/-- The fully factored localized determinant paired with the actual connected
observable difference. -/
def finePacketLocalizedConnectedObservableAntisymmetricPairTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  (finePacketCommonExteriorGibbsWeight S first second pair.1 *
      finePacketCommonExteriorGibbsWeight S first second pair.2) *
    ((finePacketDisagreementTilt S first first second pair.1 *
          finePacketDisagreementTilt S second first second pair.2 -
        finePacketDisagreementTilt S second first second pair.1 *
          finePacketDisagreementTilt S first first second pair.2) *
      (connectedRemainderObservable K M pair.1 -
        connectedRemainderObservable K M pair.2))

/-- Root-face determinant term carrying the doubled symmetric gradient. -/
def finePacketLocalizedConnectedRootGradientPairTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketLocalizedAntisymmetricResponsePairTerm
      S first second (slabPhysicalFacePositiveB M.coarseRoot) pair *
    connectedRemainderRootDoubledSymmetricGradient K M pair.1 pair.2

/-- Target-face determinant term carrying the doubled symmetric gradient. -/
def finePacketLocalizedConnectedTargetGradientPairTerm
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketLocalizedAntisymmetricResponsePairTerm
      S first second (slabPhysicalFacePositiveB M.coarseTarget) pair *
    connectedRemainderTargetDoubledSymmetricGradient K M pair.1 pair.2

/-- Pointwise, the doubled connected determinant is exactly the sum of the
two gradient-weighted one-face determinant terms. -/
theorem two_mul_localizedConnectedObservablePairTerm_eqv_gradients
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (2 : Q') *
        finePacketLocalizedConnectedObservableAntisymmetricPairTerm
          K M first second pair ≈
      finePacketLocalizedConnectedRootGradientPairTerm
          K M first second pair +
        finePacketLocalizedConnectedTargetGradientPairTerm
          K M first second pair := by
  let background :=
    finePacketCommonExteriorGibbsWeight S first second pair.1 *
      finePacketCommonExteriorGibbsWeight S first second pair.2
  let determinant :=
    finePacketDisagreementTilt S first first second pair.1 *
          finePacketDisagreementTilt S second first second pair.2 -
        finePacketDisagreementTilt S second first second pair.1 *
          finePacketDisagreementTilt S first first second pair.2
  let observableDifference :=
    connectedRemainderObservable K M pair.1 -
      connectedRemainderObservable K M pair.2
  let rootDifference :=
    booleanEventIndicator (slabPhysicalFacePositiveB M.coarseRoot) pair.1 -
      booleanEventIndicator (slabPhysicalFacePositiveB M.coarseRoot) pair.2
  let targetDifference :=
    booleanEventIndicator (slabPhysicalFacePositiveB M.coarseTarget) pair.1 -
      booleanEventIndicator (slabPhysicalFacePositiveB M.coarseTarget) pair.2
  let rootGradient :=
    connectedRemainderRootDoubledSymmetricGradient K M pair.1 pair.2
  let targetGradient :=
    connectedRemainderTargetDoubledSymmetricGradient K M pair.1 pair.2
  have hobservable :
      (2 : Q') * observableDifference ≈
        rootDifference * rootGradient +
          targetDifference * targetGradient :=
    two_mul_connectedRemainderObservable_sub_eqv_symmetricFaceGradients
      K M pair.1 pair.2
  unfold finePacketLocalizedConnectedObservableAntisymmetricPairTerm
    finePacketLocalizedConnectedRootGradientPairTerm
    finePacketLocalizedConnectedTargetGradientPairTerm
    finePacketLocalizedAntisymmetricResponsePairTerm
  change (2 : Q') * (background * (determinant * observableDifference)) ≈
    (background * (determinant * rootDifference)) * rootGradient +
      (background * (determinant * targetDifference)) * targetGradient
  refine Q'.eqv_trans _
    ((background * determinant) * ((2 : Q') * observableDifference)) _ ?_ ?_
  · ring_qeqv
  refine Q'.eqv_trans _
    ((background * determinant) *
      (rootDifference * rootGradient +
        targetDifference * targetGradient)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (background * determinant) _ _ hobservable
  refine Q'.eqv_trans _
    ((background * determinant) * (rootDifference * rootGradient) +
      (background * determinant) * (targetDifference * targetGradient)) _
    (Q'.mul_add_eqv (background * determinant)
      (rootDifference * rootGradient)
      (targetDifference * targetGradient)) ?_
  ring_qeqv

/-! ## 2. Every symmetric indicator sum is swap-invariant -/

/-- At any face, an observable-component swap preserves the sum of the two
replica face indicators: the mask either fixes both entries or transposes
them. -/
theorem facePositiveIndicatorSum_componentSwap_eqv
    (S : SlabScalePair) (observableFaceId faceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling) :
    booleanEventIndicator (slabPhysicalFacePositiveB faceId)
          (finePacketObservableComponentSwapLeft
            S observableFaceId pair) +
        booleanEventIndicator (slabPhysicalFacePositiveB faceId)
          (finePacketObservableComponentSwapRight
            S observableFaceId pair) ≈
      booleanEventIndicator (slabPhysicalFacePositiveB faceId) pair.1 +
        booleanEventIndicator (slabPhysicalFacePositiveB faceId) pair.2 := by
  cases hmask : finePacketObservableComponentSwapMask
      S observableFaceId pair faceId
  · unfold booleanEventIndicator slabPhysicalFacePositiveB
    rw [finePacketObservableComponentSwapLeft_of_false
        S observableFaceId pair faceId hmask,
      finePacketObservableComponentSwapRight_of_false
        S observableFaceId pair faceId hmask]
    exact Q'.eqv_refl _
  · unfold booleanEventIndicator slabPhysicalFacePositiveB
    rw [finePacketObservableComponentSwapLeft_of_true
        S observableFaceId pair faceId hmask,
      finePacketObservableComponentSwapRight_of_true
        S observableFaceId pair faceId hmask]
    exact Q'.add_comm_eqv _ _

theorem connectedRootDoubledGradient_rootSwap_eqv
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (pair : EdgeLabelling × EdgeLabelling) :
    connectedRemainderRootDoubledSymmetricGradient K M
        (finePacketObservableComponentSwapLeft S M.coarseRoot pair)
        (finePacketObservableComponentSwapRight S M.coarseRoot pair) ≈
      connectedRemainderRootDoubledSymmetricGradient K M pair.1 pair.2 := by
  unfold connectedRemainderRootDoubledSymmetricGradient
    connectedRemainderTargetBitSum
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_eqv_congr _ _
      (facePositiveIndicatorSum_componentSwap_eqv
        S M.coarseRoot M.coarseTarget pair))

theorem connectedTargetDoubledGradient_targetSwap_eqv
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (pair : EdgeLabelling × EdgeLabelling) :
    connectedRemainderTargetDoubledSymmetricGradient K M
        (finePacketObservableComponentSwapLeft S M.coarseTarget pair)
        (finePacketObservableComponentSwapRight S M.coarseTarget pair) ≈
      connectedRemainderTargetDoubledSymmetricGradient K M pair.1 pair.2 := by
  unfold connectedRemainderTargetDoubledSymmetricGradient
    connectedRemainderRootBitSum
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.neg_eqv_congr _ _
      (facePositiveIndicatorSum_componentSwap_eqv
        S M.coarseTarget M.coarseRoot pair))

/-! ## 3. Pointwise sign reversal on each disconnected carrier -/

theorem localizedConnectedRootGradientPairTerm_componentSwap
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseRoot) pair = true)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second M.coarseRoot pair = false) :
    finePacketLocalizedConnectedRootGradientPairTerm K M first second
        (finePacketObservableComponentSwap S M.coarseRoot pair) ≈
      -(finePacketLocalizedConnectedRootGradientPairTerm
        K M first second pair) := by
  unfold finePacketLocalizedConnectedRootGradientPairTerm
    finePacketObservableComponentSwap
  dsimp only [Prod.fst, Prod.snd]
  refine Q'.eqv_trans _
    (-(finePacketLocalizedAntisymmetricResponsePairTerm
        S first second (slabPhysicalFacePositiveB M.coarseRoot) pair) *
      connectedRemainderRootDoubledSymmetricGradient K M pair.1 pair.2) _ ?_ ?_
  · exact qmul_congr_local
      (finePacketLocalizedAntisymmetricResponsePairTerm_componentSwap
        S first second M.coarseRoot M.coarseRoot_mem pair
        hactive hdisconnected)
      (connectedRootDoubledGradient_rootSwap_eqv K M pair)
  exact Q'.neg_mul_eqv _ _

theorem localizedConnectedTargetGradientPairTerm_componentSwap
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB M.coarseTarget) pair = true)
    (hdisconnected : finePacketObservableConnectedDisagreementB
      S first second M.coarseTarget pair = false) :
    finePacketLocalizedConnectedTargetGradientPairTerm K M first second
        (finePacketObservableComponentSwap S M.coarseTarget pair) ≈
      -(finePacketLocalizedConnectedTargetGradientPairTerm
        K M first second pair) := by
  unfold finePacketLocalizedConnectedTargetGradientPairTerm
    finePacketObservableComponentSwap
  dsimp only [Prod.fst, Prod.snd]
  refine Q'.eqv_trans _
    (-(finePacketLocalizedAntisymmetricResponsePairTerm
        S first second (slabPhysicalFacePositiveB M.coarseTarget) pair) *
      connectedRemainderTargetDoubledSymmetricGradient K M pair.1 pair.2) _ ?_ ?_
  · exact qmul_congr_local
      (finePacketLocalizedAntisymmetricResponsePairTerm_componentSwap
        S first second M.coarseTarget M.coarseTarget_mem pair
        hactive hdisconnected)
      (connectedTargetDoubledGradient_targetSwap_eqv K M pair)
  exact Q'.neg_mul_eqv _ _

/-! ## 4. Axiom audit -/

#print axioms finePacketLocalizedConnectedObservableAntisymmetricPairTerm
#print axioms finePacketLocalizedConnectedRootGradientPairTerm
#print axioms finePacketLocalizedConnectedTargetGradientPairTerm
#print axioms two_mul_localizedConnectedObservablePairTerm_eqv_gradients
#print axioms facePositiveIndicatorSum_componentSwap_eqv
#print axioms connectedRootDoubledGradient_rootSwap_eqv
#print axioms connectedTargetDoubledGradient_targetSwap_eqv
#print axioms localizedConnectedRootGradientPairTerm_componentSwap
#print axioms localizedConnectedTargetGradientPairTerm_componentSwap

end YMGap.Continuum.Z4DyadicBinaryConnectedObservableSymmetricGradientSwap
