/-
# Exact normalization of the connected-response envelope

The positive envelope dominating the surviving connected response is not an
opaque majorant.  Pointwise it is exactly the sum of the two oriented products
of the localized raw tilted rows.  Consequently, its sum on the complete
two-replica physical carrier is exactly twice the product of the two positive
row masses.

Restricting that measure to the connected active carrier therefore defines an
explicit rational fraction in `[0,1]`.  The strict response problem is now
isolated: one must prove that this connected-event fraction is bounded by a
rate strictly below one with the required parameter control.

This file proves only exact finite normalization and the unit upper bound.  It
does not assert strictness, beta-uniformity, volume-uniformity, a completed
spectral gap, a continuum theory, or the Clay theorem.

Constructive contract: exact rational identities, finite list sums, and a
finite subcarrier injection only; no `Classical`, choice, `native_decide`,
proof hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
import YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelope
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem paired_background_distribute_local
    (bx by' d1x d2x d1y d2y : Q') :
    (bx * by') * (d1x * d2y + d2x * d1y) ≈
      (bx * d1x) * (by' * d2y) +
        (bx * d2x) * (by' * d1y) := by
  ring_qeqv

private theorem listQSum_symmetrized_cartesian_local
    {A : Type} (firstWeight secondWeight : A → Q') (states : List A) :
    listQSum
        (fun pair =>
          firstWeight pair.1 * secondWeight pair.2 +
            secondWeight pair.1 * firstWeight pair.2)
        (cartesian states states) ≈
      listQSum firstWeight states * listQSum secondWeight states +
        listQSum secondWeight states * listQSum firstWeight states := by
  refine Q'.eqv_trans _
    (listQSum (fun pair => firstWeight pair.1 * secondWeight pair.2)
        (cartesian states states) +
      listQSum (fun pair => secondWeight pair.1 * firstWeight pair.2)
        (cartesian states states)) _ ?_ ?_
  · exact listQSum_add
      (fun pair => firstWeight pair.1 * secondWeight pair.2)
      (fun pair => secondWeight pair.1 * firstWeight pair.2)
      (cartesian states states)
  · exact Q'.add_eqv_congr'
      (listQSum_cartesian_product firstWeight secondWeight states states)
      (listQSum_cartesian_product secondWeight firstWeight states states)

private theorem add_commuted_product_eqv_two_mul_local
    (left right : Q') :
    left * right + right * left ≈ (2 : Q') * (left * right) := by
  let product := left * right
  refine Q'.eqv_trans _ (product + product) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.mul_comm_eqv right left)
  refine Q'.eqv_symm (Q'.eqv_trans _
    ((Q'.ofNat 1 + Q'.ofNat 1) * product) _ ?_ ?_)
  · exact Q'.mul_eqv_congr_right _ _ _
      (Q'.ofNat_add_eqv 1 1)
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * product + Q'.ofNat 1 * product) _ ?_ ?_
  · exact Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) product
  · exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv product) (Q'.one_mul_eqv product)

/-! ## 1. The envelope is the symmetrized raw pair weight -/

/-- The sum of the two orientations of the localized raw row product. -/
def finePacketSymmetrizedLocalizedRawPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketLocalizedTiltedGibbsRawWeight
        S first first second pair.1 *
      finePacketLocalizedTiltedGibbsRawWeight
        S second first second pair.2 +
    finePacketLocalizedTiltedGibbsRawWeight
        S second first second pair.1 *
      finePacketLocalizedTiltedGibbsRawWeight
        S first first second pair.2

/-- The positive determinant envelope is exactly, not merely bounded by, the
symmetrized product of the two localized raw rows. -/
theorem finePacketLocalizedResponsePairEnvelope_eqv_symmetrizedRawPairWeight
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketLocalizedResponsePairEnvelope S first second pair ≈
      finePacketSymmetrizedLocalizedRawPairWeight
        S first second pair := by
  let bx := finePacketCommonExteriorGibbsWeight
    S first second pair.1
  let by' := finePacketCommonExteriorGibbsWeight
    S first second pair.2
  let d1x := finePacketDisagreementTilt
    S first first second pair.1
  let d2x := finePacketDisagreementTilt
    S second first second pair.1
  let d1y := finePacketDisagreementTilt
    S first first second pair.2
  let d2y := finePacketDisagreementTilt
    S second first second pair.2
  change (bx * by') * (d1x * d2y + d2x * d1y) ≈ _
  refine Q'.eqv_trans _
    ((bx * d1x) * (by' * d2y) +
      (bx * d2x) * (by' * d1y)) _ ?_ ?_
  · exact paired_background_distribute_local bx by' d1x d2x d1y d2y
  unfold finePacketSymmetrizedLocalizedRawPairWeight
  exact Q'.add_eqv_congr'
      (mul_eqv_both_local
        (Q'.eqv_symm
          (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
            S first first second pair.1))
        (Q'.eqv_symm
          (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
            S second first second pair.2)))
      (mul_eqv_both_local
        (Q'.eqv_symm
          (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
            S second first second pair.1))
        (Q'.eqv_symm
          (finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
            S first first second pair.2)))

/-! ## 2. Each localized one-row sum is its original row mass -/

theorem firstTiltedGibbsRowMass_eqv_localizedSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S first ≈
      listQSum
        (finePacketLocalizedTiltedGibbsRawWeight
          S first.1 first.1 second.1)
        S.coarse.physicalLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (positivePhysicalSourceTiltedGibbsFullRawWeight S first)
      S.coarse.physicalLabellings) _
    (positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
      S hfineCutoff first) ?_
  apply listQSum_congr
  intro targetState
  exact firstTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 targetState

theorem secondTiltedGibbsRowMass_eqv_localizedSum
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S second ≈
      listQSum
        (finePacketLocalizedTiltedGibbsRawWeight
          S second.1 first.1 second.1)
        S.coarse.physicalLabellings := by
  refine Q'.eqv_trans _
    (listQSum
      (positivePhysicalSourceTiltedGibbsFullRawWeight S second)
      S.coarse.physicalLabellings) _
    (positivePhysicalSourceTiltedGibbsRowMass_eqv_fullCarrier
      S hfineCutoff second) ?_
  apply listQSum_congr
  intro targetState
  exact secondTiltedGibbsRawWeight_eqv_localized
    S first.1 second.1 targetState

/-! ## 3. Exact full-carrier normalization -/

/-- The normalization inherited from the two positive source-dependent rows. -/
def finePacketConnectedEnvelopeNormalizationMass
    (S : SlabScalePair) (first second : PositivePhysicalSource S) : Q' :=
  (2 : Q') *
    (positivePhysicalSourceTiltedGibbsRowMass S first *
      positivePhysicalSourceTiltedGibbsRowMass S second)

/-- Summing the envelope over the complete two-replica carrier gives exactly
twice the product of the two row masses. -/
theorem finePacketFullResponsePairEnvelopeSum_eqv_normalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    listQSum
        (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      finePacketConnectedEnvelopeNormalizationMass
        S first second := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  let states := S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum
      (finePacketSymmetrizedLocalizedRawPairWeight
        S first.1 second.1)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact finePacketLocalizedResponsePairEnvelope_eqv_symmetrizedRawPairWeight
      S first.1 second.1 pair
  refine Q'.eqv_trans _
    (listQSum firstWeight states * listQSum secondWeight states +
      listQSum secondWeight states * listQSum firstWeight states) _ ?_ ?_
  · unfold finePacketSymmetrizedLocalizedRawPairWeight
    exact listQSum_symmetrized_cartesian_local
      firstWeight secondWeight states
  refine Q'.eqv_trans _
    ((2 : Q') *
      (listQSum firstWeight states * listQSum secondWeight states)) _ ?_ ?_
  · exact add_commuted_product_eqv_two_mul_local
      (listQSum firstWeight states) (listQSum secondWeight states)
  unfold finePacketConnectedEnvelopeNormalizationMass
  exact Q'.mul_eqv_congr_left _ _ _
    (mul_eqv_both_local
      (Q'.eqv_symm
        (firstTiltedGibbsRowMass_eqv_localizedSum
          S hfineCutoff first second))
      (Q'.eqv_symm
        (secondTiltedGibbsRowMass_eqv_localizedSum
          S hfineCutoff first second)))

/-! ## 4. The connected restriction is a rational fraction in `[0,1]` -/

theorem finePacketFaceResponseConnectedActivePairs_nodup
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    (finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId).Nodup := by
  unfold finePacketFaceResponseConnectedActivePairs
    YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier.finePacketLocalizedResponseActivePairs
  apply List.filter_sublist.nodup
  apply List.filter_sublist.nodup
  exact cartesian_nodup
    S.coarse.physicalLabellings S.coarse.physicalLabellings
    (slabPhysicalLabellings_nodup S.coarse)
    (slabPhysicalLabellings_nodup S.coarse)

/-- The connected active envelope mass is at most its exact complete-carrier
normalization.  This is a unit bound, not yet a strict contraction. -/
theorem finePacketConnectedEnvelopeSum_le_normalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    listQSum
        (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
        (finePacketFaceResponseConnectedActivePairs
          S first.1 second.1 observableFaceId) ≤
      finePacketConnectedEnvelopeNormalizationMass
        S first second := by
  have hsubset :
      listQSum
          (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
          (finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 observableFaceId) ≤
        listQSum
          (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
          (cartesian S.coarse.physicalLabellings
            S.coarse.physicalLabellings) := by
    apply listQSum_le_of_injective_nodup
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId)
      (cartesian S.coarse.physicalLabellings
        S.coarse.physicalLabellings)
      (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
      (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
      (fun pair => pair)
    · exact finePacketFaceResponseConnectedActivePairs_nodup
        S first.1 second.1 observableFaceId
    · exact cartesian_nodup
        S.coarse.physicalLabellings S.coarse.physicalLabellings
        (slabPhysicalLabellings_nodup S.coarse)
        (slabPhysicalLabellings_nodup S.coarse)
    · intro pair hpair
      have hconnected := (List.mem_filter.mp hpair).1
      exact (List.mem_filter.mp hconnected).1
    · intro left _ right _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact finePacketLocalizedResponsePairEnvelope_nonnegative
        S first.1 second.1 pair
  exact Q'.le_trans' _ _ _ hsubset
    (Q'.le_of_eqv
      (finePacketFullResponsePairEnvelopeSum_eqv_normalizationMass
        S hfineCutoff first second))

theorem finePacketConnectedEnvelopeNormalizationMass_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S) :
    (0 : Q') <
      finePacketConnectedEnvelopeNormalizationMass S first second := by
  unfold finePacketConnectedEnvelopeNormalizationMass
  exact Q'.mul_pos (Q'.ofNat_succ_pos 1)
    (Q'.mul_pos
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling first)
      (positivePhysicalSourceTiltedGibbsRowMass_pos
        S hfineCutoff hcoarseCoupling second))

/-- The exact normalized mass of the connected active event under the
symmetrized product of the two tilted rows. -/
def finePacketConnectedEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (listQSum
      (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId))
    (finePacketConnectedEnvelopeNormalizationMass S first second)
    (finePacketConnectedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

theorem finePacketConnectedEnvelopeFraction_nonnegative
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    (0 : Q') ≤ finePacketConnectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling first second observableFaceId := by
  unfold finePacketConnectedEnvelopeFraction Q'.divPos
  apply Q'.mul_nonneg
  · exact listQSum_nonnegative_on
      (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId)
      (fun pair _ =>
        finePacketLocalizedResponsePairEnvelope_nonnegative
          S first.1 second.1 pair)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _
        (finePacketConnectedEnvelopeNormalizationMass_pos
          S hfineCutoff hcoarseCoupling first second))

theorem finePacketConnectedEnvelopeFraction_le_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketConnectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling first second observableFaceId ≤ 1 := by
  unfold finePacketConnectedEnvelopeFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (finePacketConnectedEnvelopeSum_le_normalizationMass
      S hfineCutoff first second observableFaceId)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (finePacketConnectedEnvelopeNormalizationMass S first second)))

/-! ## 5. Axiom audit -/

#print axioms finePacketSymmetrizedLocalizedRawPairWeight
#print axioms finePacketLocalizedResponsePairEnvelope_eqv_symmetrizedRawPairWeight
#print axioms firstTiltedGibbsRowMass_eqv_localizedSum
#print axioms secondTiltedGibbsRowMass_eqv_localizedSum
#print axioms finePacketConnectedEnvelopeNormalizationMass
#print axioms finePacketFullResponsePairEnvelopeSum_eqv_normalizationMass
#print axioms finePacketFaceResponseConnectedActivePairs_nodup
#print axioms finePacketConnectedEnvelopeSum_le_normalizationMass
#print axioms finePacketConnectedEnvelopeNormalizationMass_pos
#print axioms finePacketConnectedEnvelopeFraction
#print axioms finePacketConnectedEnvelopeFraction_nonnegative
#print axioms finePacketConnectedEnvelopeFraction_le_one

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
