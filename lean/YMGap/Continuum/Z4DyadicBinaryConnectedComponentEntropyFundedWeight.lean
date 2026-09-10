/-
# Expose the entropy-funded factor in the actual connected mass

The component entropy code has now been constructed and counted.  This file
rewrites the actual refined connected upper weight so that its heat factors
match that code exactly:

`rate^distance`
`  * rate^(2 * componentSize)`
`  * rate^(componentSize - distance)`
`  * rate^(3 * (componentActivity - componentSize))`
`  * rate^complementaryReserve`
`  * groundNormalizedUnitCongestion`.

The first factor is visible correlation decay.  The second pays the
`45000^componentSize` shape/local-code carrier.  The last three heat factors
and the normalized congestion are retained verbatim as the remaining
exterior-fiber obligation.

No summability or fiber-injectivity claim is made here.  The purpose is an
exact, kernel-checked accounting identity that prevents using one heat unit
twice in the next contraction.

Constructive contract: exact rational-power algebra and finite sums only, with
no extension of the repository trust boundary or resource budget.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode

namespace YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyFundedWeight

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyCode
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

/-! ## 1. The old distance/slack pair is the full component heat -/

theorem finePacketGlobalNonzeroConnectedEntry_distanceSlackPower_eqv_componentHeat
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    qpow (finePacketJointDistanceFugacity rate)
          (finePacketGlobalNonzeroConnectedEntryDistance
            S orientation observableFaceId hobservableFace entry) *
        qpow rate
          (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
            S orientation observableFaceId hobservableFace entry) ≈
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
          S orientation observableFaceId entry) := by
  unfold finePacketJointDistanceFugacity
  refine Q'.eqv_trans _
    (qpow rate
        (3 * finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (HeatKernelRGStep.qpow_qpow rate 3
        (finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry))
  refine Q'.eqv_trans _
    (qpow rate
      (3 * finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry +
        finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry)) _
    (Q'.eqv_symm (HeatKernelRGStep.qpow_add rate _ _)) ?_
  have hsplit :=
    finePacketGlobalNonzeroConnectedEntry_distance_add_componentSlack_eq_componentHeat
      S hfineCutoff orientation observableFaceId hobservableFace entry
  change
    3 * finePacketGlobalNonzeroConnectedEntryDistance
          S orientation observableFaceId hobservableFace entry +
        finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
          S orientation observableFaceId hobservableFace entry =
      finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
        S orientation observableFaceId entry at hsplit
  rw [hsplit]
  exact Q'.eqv_refl _

/-! ## 2. The exact entropy-funded pointwise weight -/

def finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Q' :=
  (qpow rate
        (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
          S orientation observableFaceId hobservableFace entry) *
      (qpow rate
          (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
            S orientation observableFaceId entry) *
        (qpow rate
            (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
              S orientation observableFaceId hobservableFace entry) *
          qpow rate
            (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
              S orientation observableFaceId entry)))) *
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
          S orientation observableFaceId entry) *
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation
          entry.1.sources.1 entry.1.sources.2 entry.1.targets)

/-- The already-proved heat-budget weight is exactly the entropy-funded
factorization; no estimate is lost in exposing the code payment. -/
theorem finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_entropyFunded
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry ≈
      finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  unfold finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight
    finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
  let tail :=
    qpow rate
        (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
          S orientation observableFaceId entry) *
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation
          entry.1.sources.1 entry.1.sources.2 entry.1.targets
  change
    qpow (finePacketJointDistanceFugacity rate)
          (finePacketGlobalNonzeroConnectedEntryDistance
            S orientation observableFaceId hobservableFace entry) *
        (qpow rate
            (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
              S orientation observableFaceId hobservableFace entry) * tail) ≈
      (qpow rate
            (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
              S orientation observableFaceId hobservableFace entry) *
          (qpow rate
              (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
                S orientation observableFaceId entry) *
            (qpow rate
                (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
                  S orientation observableFaceId hobservableFace entry) *
              qpow rate
                (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
                  S orientation observableFaceId entry)))) * tail
  refine Q'.eqv_trans _
    ((qpow (finePacketJointDistanceFugacity rate)
          (finePacketGlobalNonzeroConnectedEntryDistance
            S orientation observableFaceId hobservableFace entry) *
        qpow rate
          (finePacketGlobalNonzeroConnectedEntryComponentHeatSlack
            S orientation observableFaceId hobservableFace entry)) * tail) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    (qpow rate
        (finePacketGlobalNonzeroConnectedEntryComponentHeatCharge
          S orientation observableFaceId entry) * tail) _
    (Q'.mul_eqv_congr_right _ _ _
      (finePacketGlobalNonzeroConnectedEntry_distanceSlackPower_eqv_componentHeat
        S hfineCutoff rate orientation observableFaceId hobservableFace
          entry)) ?_
  exact Q'.mul_eqv_congr_right _ _ _
    (finePacketGlobalNonzeroConnectedEntry_componentHeatPower_eqv_rebalanced
      S hfineCutoff rate orientation observableFaceId hobservableFace entry)

/-! ## 3. The actual normalized mass reaches the new frontier -/

def finePacketGlobalNonzeroConnectedEntropyFundedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace)
    (finePacketGlobalOrientedNonzeroConnectedEntries
      S orientation observableFaceId)

theorem finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_entropyFunded
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNonzeroConnectedHeatBudgetMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≈
      finePacketGlobalNonzeroConnectedEntropyFundedMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedHeatBudgetMass
    finePacketGlobalNonzeroConnectedEntropyFundedMass
  apply listQSum_congr
  intro entry
  exact
    finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_entropyFunded
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace entry

/-- Exact handoff: the normalized connected mass is bounded by the carrier in
which visible decay, paid component entropy, and the remaining exterior
payload are separate factors. -/
theorem finePacketGlobalConnectedEntryNormalizedSum_le_entropyFundedMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hcoarseRate : S.coarse.coupling ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    listQSum
        (finePacketGlobalConnectedEntryNormalizedWeight
          S hfineCutoff hcoarseCoupling orientation observableFaceId)
        (finePacketGlobalConnectedEntries S observableFaceId) ≤
      finePacketGlobalNonzeroConnectedEntropyFundedMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalConnectedEntryNormalizedSum_le_heatBudgetMass
      S hfineCutoff hcoarseCoupling rate hfineRate hcoarseRate orientation
        observableFaceId hobservableFace)
    (Q'.le_of_eqv
      (finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_entropyFunded
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace))

/-! ## 4. Axiom audit -/

#print axioms finePacketGlobalNonzeroConnectedEntry_distanceSlackPower_eqv_componentHeat
#print axioms finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
#print axioms finePacketGlobalNonzeroConnectedEntryHeatBudgetWeight_eqv_entropyFunded
#print axioms finePacketGlobalNonzeroConnectedEntropyFundedMass
#print axioms finePacketGlobalNonzeroConnectedHeatBudgetMass_eqv_entropyFunded
#print axioms finePacketGlobalConnectedEntryNormalizedSum_le_entropyFundedMass

end YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyFundedWeight
