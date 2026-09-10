/-
# Oriented product decomposition of the connected-event fraction

The normalized connected envelope is a symmetric mixture of two source-to-
target assignments.  Relative parity excitation is meaningful only after one
assignment is fixed.  This file therefore separates the forward and reverse
positive product measures exactly.

Each oriented measure has complete-carrier mass equal to the product of the
two tilted row masses.  Its connected restriction defines a probability in
`[0,1]`.  A final two-orientation gluing theorem says that a common rate bound
for both connected restrictions implies the same rate bound for the original
connected-envelope fraction.

No strict rate, beta-uniformity, volume-uniformity, completed spectral gap,
continuum theory, or Clay theorem is asserted here.

Constructive contract: exact rational finite-sum algebra and duplicate-free
subcarrier injections only; no `Classical`, choice, `native_decide`, proof
hole, noncomputable declaration, trusted external computation, enlarged
heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition

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
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedEnvelopeNormalization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseDeterminant
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt

local infix:50 " ≈ " => Q'.eqv

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem two_mul_eqv_add_self_local (value : Q') :
    (2 : Q') * value ≈ value + value := by
  refine Q'.eqv_trans _ ((Q'.ofNat 1 + Q'.ofNat 1) * value) _
    (Q'.mul_eqv_congr_right _ _ _ (Q'.ofNat_add_eqv 1 1)) ?_
  refine Q'.eqv_trans _
    (Q'.ofNat 1 * value + Q'.ofNat 1 * value) _ ?_ ?_
  · exact Q'.add_mul_eqv (Q'.ofNat 1) (Q'.ofNat 1) value
  · exact Q'.add_eqv_congr'
      (Q'.one_mul_eqv value) (Q'.one_mul_eqv value)

/-! ## 1. Exact split on the connected carrier -/

def finePacketForwardConnectedEnvelopeMass
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (finePacketForwardLocalizedRawPairWeight S first second)
    (finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId)

def finePacketReverseConnectedEnvelopeMass
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (finePacketReverseLocalizedRawPairWeight S first second)
    (finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId)

theorem finePacketLocalizedResponsePairEnvelope_eqv_forward_add_reverse
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketLocalizedResponsePairEnvelope S first second pair ≈
      finePacketForwardLocalizedRawPairWeight S first second pair +
        finePacketReverseLocalizedRawPairWeight S first second pair := by
  refine Q'.eqv_trans _
    (finePacketSymmetrizedLocalizedRawPairWeight
      S first second pair) _
    (finePacketLocalizedResponsePairEnvelope_eqv_symmetrizedRawPairWeight
      S first second pair) ?_
  unfold finePacketSymmetrizedLocalizedRawPairWeight
    finePacketForwardLocalizedRawPairWeight
    finePacketReverseLocalizedRawPairWeight
  exact Q'.eqv_refl _

/-- The connected envelope mass is exactly the sum of its two oriented
connected product masses. -/
theorem finePacketConnectedEnvelopeSum_eqv_forward_add_reverse
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) :
    listQSum
        (finePacketLocalizedResponsePairEnvelope S first second)
        (finePacketFaceResponseConnectedActivePairs
          S first second observableFaceId) ≈
      finePacketForwardConnectedEnvelopeMass
          S first second observableFaceId +
        finePacketReverseConnectedEnvelopeMass
          S first second observableFaceId := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        finePacketForwardLocalizedRawPairWeight S first second pair +
          finePacketReverseLocalizedRawPairWeight S first second pair)
      (finePacketFaceResponseConnectedActivePairs
        S first second observableFaceId)) _ ?_ ?_
  · apply listQSum_congr
    intro pair
    exact finePacketLocalizedResponsePairEnvelope_eqv_forward_add_reverse
      S first second pair
  unfold finePacketForwardConnectedEnvelopeMass
    finePacketReverseConnectedEnvelopeMass
  exact listQSum_add
    (finePacketForwardLocalizedRawPairWeight S first second)
    (finePacketReverseLocalizedRawPairWeight S first second)
    (finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId)

/-! ## 2. Each oriented complete measure has one row-product mass -/

def finePacketOrientedEnvelopeNormalizationMass
    (S : SlabScalePair) (first second : PositivePhysicalSource S) : Q' :=
  positivePhysicalSourceTiltedGibbsRowMass S first *
    positivePhysicalSourceTiltedGibbsRowMass S second

theorem finePacketForwardFullEnvelopeSum_eqv_orientedNormalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    listQSum
        (finePacketForwardLocalizedRawPairWeight S first.1 second.1)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  let states := S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum firstWeight states * listQSum secondWeight states) _ ?_ ?_
  · unfold finePacketForwardLocalizedRawPairWeight
    exact listQSum_cartesian_product firstWeight secondWeight states states
  unfold finePacketOrientedEnvelopeNormalizationMass
  exact mul_eqv_both_local
    (Q'.eqv_symm
      (firstTiltedGibbsRowMass_eqv_localizedSum
        S hfineCutoff first second))
    (Q'.eqv_symm
      (secondTiltedGibbsRowMass_eqv_localizedSum
        S hfineCutoff first second))

theorem finePacketReverseFullEnvelopeSum_eqv_orientedNormalizationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S) :
    listQSum
        (finePacketReverseLocalizedRawPairWeight S first.1 second.1)
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) ≈
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  let firstWeight := finePacketLocalizedTiltedGibbsRawWeight
    S first.1 first.1 second.1
  let secondWeight := finePacketLocalizedTiltedGibbsRawWeight
    S second.1 first.1 second.1
  let states := S.coarse.physicalLabellings
  refine Q'.eqv_trans _
    (listQSum secondWeight states * listQSum firstWeight states) _ ?_ ?_
  · unfold finePacketReverseLocalizedRawPairWeight
    exact listQSum_cartesian_product secondWeight firstWeight states states
  refine Q'.eqv_trans _
    (positivePhysicalSourceTiltedGibbsRowMass S second *
      positivePhysicalSourceTiltedGibbsRowMass S first) _ ?_ ?_
  · exact mul_eqv_both_local
      (Q'.eqv_symm
        (secondTiltedGibbsRowMass_eqv_localizedSum
          S hfineCutoff first second))
      (Q'.eqv_symm
        (firstTiltedGibbsRowMass_eqv_localizedSum
          S hfineCutoff first second))
  unfold finePacketOrientedEnvelopeNormalizationMass
  exact Q'.mul_comm_eqv _ _

/-! ## 3. Positivity and connected-subcarrier bounds -/

theorem finePacketLocalizedTiltedGibbsRawWeight_nonnegative
    (S : SlabScalePair) (source first second targetState : EdgeLabelling) :
    (0 : Q') ≤ finePacketLocalizedTiltedGibbsRawWeight
      S source first second targetState := by
  have hfactored :=
    finePacketLocalizedTiltedGibbsRawWeight_eqv_background_mul_tilt
      S source first second targetState
  have hproduct : (0 : Q') ≤
      finePacketCommonExteriorGibbsWeight S first second targetState *
        finePacketDisagreementTilt S source first second targetState :=
    Q'.mul_nonneg _ _
      (finePacketCommonExteriorGibbsWeight_nonnegative
        S first second targetState)
      (finePacketDisagreementTilt_nonnegative
        S source first second targetState)
  exact Q'.le_trans' _ _ _ hproduct (Q'.ge_of_eqv hfactored)

theorem finePacketForwardLocalizedRawPairWeight_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketForwardLocalizedRawPairWeight
      S first second pair := by
  unfold finePacketForwardLocalizedRawPairWeight
  exact Q'.mul_nonneg _ _
    (finePacketLocalizedTiltedGibbsRawWeight_nonnegative
      S first first second pair.1)
    (finePacketLocalizedTiltedGibbsRawWeight_nonnegative
      S second first second pair.2)

theorem finePacketReverseLocalizedRawPairWeight_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketReverseLocalizedRawPairWeight
      S first second pair := by
  unfold finePacketReverseLocalizedRawPairWeight
  exact Q'.mul_nonneg _ _
    (finePacketLocalizedTiltedGibbsRawWeight_nonnegative
      S second first second pair.1)
    (finePacketLocalizedTiltedGibbsRawWeight_nonnegative
      S first first second pair.2)

private theorem connectedSum_le_fullSum_local
    (S : SlabScalePair) (first second : EdgeLabelling)
    (observableFaceId : Nat) (weight : EdgeLabelling × EdgeLabelling → Q')
    (hweight : ∀ pair, (0 : Q') ≤ weight pair) :
    listQSum weight
        (finePacketFaceResponseConnectedActivePairs
          S first second observableFaceId) ≤
      listQSum weight
        (cartesian S.coarse.physicalLabellings
          S.coarse.physicalLabellings) := by
  apply listQSum_le_of_injective_nodup
    (finePacketFaceResponseConnectedActivePairs
      S first second observableFaceId)
    (cartesian S.coarse.physicalLabellings
      S.coarse.physicalLabellings)
    weight weight (fun pair => pair)
  · exact finePacketFaceResponseConnectedActivePairs_nodup
      S first second observableFaceId
  · exact cartesian_nodup
      S.coarse.physicalLabellings S.coarse.physicalLabellings
      (slabPhysicalLabellings_nodup S.coarse)
      (slabPhysicalLabellings_nodup S.coarse)
  · intro pair hpair
    exact (List.mem_filter.mp (List.mem_filter.mp hpair).1).1
  · intro left _ right _ heq
    exact heq
  · intro pair _
    exact Q'.le_refl' _
  · intro pair _
    exact hweight pair

theorem finePacketForwardConnectedEnvelopeMass_le_normalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketForwardConnectedEnvelopeMass
        S first.1 second.1 observableFaceId ≤
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  unfold finePacketForwardConnectedEnvelopeMass
  exact Q'.le_trans' _ _ _
    (connectedSum_le_fullSum_local S first.1 second.1 observableFaceId
      (finePacketForwardLocalizedRawPairWeight S first.1 second.1)
      (finePacketForwardLocalizedRawPairWeight_nonnegative
        S first.1 second.1))
    (Q'.le_of_eqv
      (finePacketForwardFullEnvelopeSum_eqv_orientedNormalizationMass
        S hfineCutoff first second))

theorem finePacketReverseConnectedEnvelopeMass_le_normalization
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketReverseConnectedEnvelopeMass
        S first.1 second.1 observableFaceId ≤
      finePacketOrientedEnvelopeNormalizationMass S first second := by
  unfold finePacketReverseConnectedEnvelopeMass
  exact Q'.le_trans' _ _ _
    (connectedSum_le_fullSum_local S first.1 second.1 observableFaceId
      (finePacketReverseLocalizedRawPairWeight S first.1 second.1)
      (finePacketReverseLocalizedRawPairWeight_nonnegative
        S first.1 second.1))
    (Q'.le_of_eqv
      (finePacketReverseFullEnvelopeSum_eqv_orientedNormalizationMass
        S hfineCutoff first second))

theorem finePacketOrientedEnvelopeNormalizationMass_pos
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S) :
    (0 : Q') < finePacketOrientedEnvelopeNormalizationMass
      S first second := by
  unfold finePacketOrientedEnvelopeNormalizationMass
  exact Q'.mul_pos
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling first)
    (positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling second)

/-! ## 4. The two oriented probabilities and their gluing theorem -/

def finePacketForwardConnectedEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketForwardConnectedEnvelopeMass
      S first.1 second.1 observableFaceId)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

def finePacketReverseConnectedEnvelopeFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketReverseConnectedEnvelopeMass
      S first.1 second.1 observableFaceId)
    (finePacketOrientedEnvelopeNormalizationMass S first second)
    (finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)

theorem finePacketForwardConnectedEnvelopeFraction_le_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketForwardConnectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling first second observableFaceId ≤ 1 := by
  unfold finePacketForwardConnectedEnvelopeFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (finePacketForwardConnectedEnvelopeMass_le_normalization
      S hfineCutoff first second observableFaceId)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (finePacketOrientedEnvelopeNormalizationMass S first second)))

theorem finePacketReverseConnectedEnvelopeFraction_le_one
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) :
    finePacketReverseConnectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling first second observableFaceId ≤ 1 := by
  unfold finePacketReverseConnectedEnvelopeFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (finePacketReverseConnectedEnvelopeMass_le_normalization
      S hfineCutoff first second observableFaceId)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (finePacketOrientedEnvelopeNormalizationMass S first second)))

/-- A common oriented connected-event rate glues back to the original
symmetrized connected fraction with no loss. -/
theorem finePacketConnectedEnvelopeFraction_le_of_oriented_mass_bounds
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat) (rate : Q')
    (hforward : finePacketForwardConnectedEnvelopeMass
        S first.1 second.1 observableFaceId ≤
      rate * finePacketOrientedEnvelopeNormalizationMass S first second)
    (hreverse : finePacketReverseConnectedEnvelopeMass
        S first.1 second.1 observableFaceId ≤
      rate * finePacketOrientedEnvelopeNormalizationMass S first second) :
    finePacketConnectedEnvelopeFraction
      S hfineCutoff hcoarseCoupling first second observableFaceId ≤ rate := by
  let mass := finePacketOrientedEnvelopeNormalizationMass S first second
  have hsum :
      finePacketForwardConnectedEnvelopeMass
          S first.1 second.1 observableFaceId +
        finePacketReverseConnectedEnvelopeMass
          S first.1 second.1 observableFaceId ≤
      rate * mass + rate * mass :=
    Q'.add_le_add hforward hreverse
  have htwice : rate * ((2 : Q') * mass) ≈
      rate * mass + rate * mass := by
    refine Q'.eqv_trans _ (rate * (mass + mass)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (two_mul_eqv_add_self_local mass)
    · exact Q'.mul_add_eqv rate mass mass
  have hnumerator :
      listQSum
          (finePacketLocalizedResponsePairEnvelope S first.1 second.1)
          (finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 observableFaceId) ≤
        rate * finePacketConnectedEnvelopeNormalizationMass
          S first second := by
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (finePacketConnectedEnvelopeSum_eqv_forward_add_reverse
          S first.1 second.1 observableFaceId)) ?_
    refine Q'.le_trans' _ _ _ hsum ?_
    unfold finePacketConnectedEnvelopeNormalizationMass
    exact Q'.ge_of_eqv htwice
  unfold finePacketConnectedEnvelopeFraction
  exact Q'.divPos_le_of_le_mul _ _
    (finePacketConnectedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second)
    hnumerator

/-! ## Axiom audit -/

#print axioms finePacketForwardConnectedEnvelopeMass
#print axioms finePacketReverseConnectedEnvelopeMass
#print axioms finePacketLocalizedResponsePairEnvelope_eqv_forward_add_reverse
#print axioms finePacketConnectedEnvelopeSum_eqv_forward_add_reverse
#print axioms finePacketOrientedEnvelopeNormalizationMass
#print axioms finePacketForwardFullEnvelopeSum_eqv_orientedNormalizationMass
#print axioms finePacketReverseFullEnvelopeSum_eqv_orientedNormalizationMass
#print axioms finePacketLocalizedTiltedGibbsRawWeight_nonnegative
#print axioms finePacketForwardLocalizedRawPairWeight_nonnegative
#print axioms finePacketReverseLocalizedRawPairWeight_nonnegative
#print axioms finePacketForwardConnectedEnvelopeMass_le_normalization
#print axioms finePacketReverseConnectedEnvelopeMass_le_normalization
#print axioms finePacketOrientedEnvelopeNormalizationMass_pos
#print axioms finePacketForwardConnectedEnvelopeFraction
#print axioms finePacketReverseConnectedEnvelopeFraction
#print axioms finePacketForwardConnectedEnvelopeFraction_le_one
#print axioms finePacketReverseConnectedEnvelopeFraction_le_one
#print axioms finePacketConnectedEnvelopeFraction_le_of_oriented_mass_bounds

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
