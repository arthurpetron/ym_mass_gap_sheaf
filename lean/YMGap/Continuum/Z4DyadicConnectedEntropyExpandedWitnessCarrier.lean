/-
# Flatten connected entries into literal normalized SU(2) witnesses

The connected entropy-funded mass still has two nested meanings: an outer
sum over physical source/target entries, and, inside each entry, the
ground-normalized congestion.  The latter was just identified with a finite
sum over literal accepted fusion and lowering witnesses.

This file performs that expansion on the actual connected carrier.  It also
replaces the separately displayed shape and local-activity heat factors by
the exact weight of the compiled shape-child code.  The result is one
dependent, proof-carrying finite carrier whose total mass is exactly the
existing entropy-funded mass.  No estimate is taken here.

Constructive contract: attached finite lists, dependent finite flattening,
and exact rational algebra only; no classical choice, proof hole, trusted
external computation, computability escape, heartbeat increase, or new
axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
import YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness

namespace YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentEntropyFundedWeight
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentHeatBudget
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentShapeChildWeightedCarrier
open YMGap.Continuum.Z4DyadicBinaryConnectedComponentSlackDecomposition
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedGroundFractionSum
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicNormalizedJointReferenceExpandedWitness

local infix:50 " ≈ " => Q'.eqv

private theorem qmul_congr_local
    {left left' right right' : Q'}
    (hleft : left ≈ left') (hright : right ≈ right') :
    left * right ≈ left' * right' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ hleft)
    (Q'.mul_eqv_congr_left _ _ _ hright)

private theorem listQSum_mul_left_local {A : Type}
    (factor : Q') (weight : A -> Q') :
    forall items : List A,
      listQSum (fun item => factor * weight item) items ≈
        factor * listQSum weight items
  | [] => Q'.eqv_symm (Q'.mul_zero_eqv factor)
  | item :: items => by
      exact Q'.eqv_trans _ _ _
        (Q'.add_eqv_congr' (Q'.eqv_refl _)
          (listQSum_mul_left_local factor weight items))
        (Q'.eqv_symm
          (Q'.mul_add_eqv factor (weight item) (listQSum weight items)))

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one];
             ac_rfl))

private theorem entropyFactorRearrangement_local
    (visible shape residual activity reserve congestion : Q') :
    ((visible * ((shape * activity) * residual)) * reserve) * congestion ≈
      (visible * (shape * (residual * activity))) *
        (reserve * congestion) := by
  ring_qeqv

/-! ## 1. Physical target witnesses already carried by a connected entry -/

theorem finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    entry.1.targets.1 ∈ S.coarse.physicalLabellings := by
  have hactive := (List.mem_filter.mp entry.1.target_mem).1
  have hphysical := (List.mem_filter.mp hactive).1
  exact (mem_cartesian_iff _ _ entry.1.targets).mp hphysical |>.1

theorem finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    entry.1.targets.2 ∈ S.coarse.physicalLabellings := by
  have hactive := (List.mem_filter.mp entry.1.target_mem).1
  have hphysical := (List.mem_filter.mp hactive).1
  exact (mem_cartesian_iff _ _ entry.1.targets).mp hphysical |>.2

/-! ## 2. The dependent expanded carrier -/

def finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    List (FinePacketOrientedJointUnitExpandedWitness S) :=
  finePacketOrientedJointUnitExpandedWitnessCarrier
    S orientation entry.1.sources.1 entry.1.sources.2 entry.1.targets
      (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
        S orientation observableFaceId entry)
      (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
        S orientation observableFaceId entry)

theorem finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier_nodup
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    (finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
      S orientation observableFaceId entry).Nodup := by
  unfold finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
  exact finePacketOrientedJointUnitExpandedWitnessCarrier_nodup
    S orientation entry.1.sources.1 entry.1.sources.2 entry.1.targets _ _

/-- A global connected entry together with one literal accepted joint
witness from its dependent fiber. -/
abbrev FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :=
  Sigma fun entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId =>
    { witness : FinePacketOrientedJointUnitExpandedWitness S //
      witness ∈ finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
        S orientation observableFaceId entry }

def finePacketGlobalNonzeroConnectedExpandedWitnessBlock
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    List (FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :=
  (finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
    S orientation observableFaceId entry).attach.map fun witness =>
      ⟨entry, witness⟩

def finePacketGlobalNonzeroConnectedExpandedWitnessEntries
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    List (FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :=
  (finePacketGlobalOrientedNonzeroConnectedEntries
    S orientation observableFaceId).flatMap
      (finePacketGlobalNonzeroConnectedExpandedWitnessBlock
        S orientation observableFaceId)

/-! ## 3. Exact shape-child and normalized witness weight -/

def finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
    (S : SlabScalePair) (rate : Q')
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) : Q' :=
  (qpow rate
      (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
        S orientation observableFaceId hobservableFace entry) *
    (finePacketConnectedComponentShapeChildWeight rate
      (finePacketGlobalNonzeroConnectedEntryComponentSize
        S orientation observableFaceId entry)
      (finePacketGlobalNonzeroConnectedEntryShapeChildCode
        S orientation observableFaceId hobservableFace entry) *
      qpow rate
        (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
          S orientation observableFaceId hobservableFace entry))) *
    qpow rate
      (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
        S orientation observableFaceId entry)

def finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (witness : FinePacketOrientedJointUnitExpandedWitness S) : Q' :=
  finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
      S rate orientation observableFaceId hobservableFace entry *
    finePacketOrientedNormalizedJointExpandedWitnessWeight
      S hfineCutoff hcoarseCoupling orientation
        entry.1.sources.1 entry.1.sources.2 witness

def finePacketGlobalNonzeroConnectedExpandedWitnessWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) : Q' :=
  finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
    S hfineCutoff hcoarseCoupling rate orientation observableFaceId
      hobservableFace expanded.1 expanded.2.1

/-- Replacing the separate shape and local-activity heat factors by the
compiled shape-child weight is an exact rearrangement. -/
theorem finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_mul_congestion
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
        S rate orientation observableFaceId hobservableFace entry *
      finePacketOrientedGroundNormalizedUnitCongestion
        S hfineCutoff hcoarseCoupling orientation
          entry.1.sources.1 entry.1.sources.2 entry.1.targets ≈
      finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  have hshape :=
    finePacketGlobalNonzeroConnectedEntryShapeChildWeight_eqv_heat
      rate S hfineCutoff orientation observableFaceId hobservableFace entry
  let visible := qpow rate
    (finePacketGlobalNonzeroConnectedEntryVisibleDistanceHeat
      S orientation observableFaceId hobservableFace entry)
  let shape := qpow rate
    (finePacketGlobalNonzeroConnectedEntryShapeLocalEntropyHeat
      S orientation observableFaceId entry)
  let residual := qpow rate
    (finePacketGlobalNonzeroConnectedEntryResidualDetourHeat
      S orientation observableFaceId hobservableFace entry)
  let activity := qpow rate
    (finePacketGlobalNonzeroConnectedEntryLocalActivityExcessHeat
      S orientation observableFaceId entry)
  let reserve := qpow rate
    (finePacketGlobalNonzeroConnectedEntryComplementaryHeatReserve
      S orientation observableFaceId entry)
  let congestion := finePacketOrientedGroundNormalizedUnitCongestion
    S hfineCutoff hcoarseCoupling orientation
      entry.1.sources.1 entry.1.sources.2 entry.1.targets
  change
    ((visible *
        (finePacketConnectedComponentShapeChildWeight rate
          (finePacketGlobalNonzeroConnectedEntryComponentSize
            S orientation observableFaceId entry)
          (finePacketGlobalNonzeroConnectedEntryShapeChildCode
            S orientation observableFaceId hobservableFace entry) *
          residual)) * reserve) * congestion ≈
      (visible * (shape * (residual * activity))) *
        (reserve * congestion)
  refine Q'.eqv_trans _
    (((visible * ((shape * activity) * residual)) * reserve) * congestion) _
    (qmul_congr_local
      (qmul_congr_local
        (qmul_congr_local (Q'.eqv_refl visible)
          (qmul_congr_local hshape (Q'.eqv_refl residual)))
        (Q'.eqv_refl reserve))
      (Q'.eqv_refl congestion)) ?_
  exact entropyFactorRearrangement_local
    visible shape residual activity reserve congestion

/-- The literal joint-witness fiber over one connected entry has exactly the
entropy-funded entry mass. -/
theorem finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier_weight_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listQSum
        (finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace entry)
        (finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
          S orientation observableFaceId entry) ≈
      finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  let carrier := finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
    S orientation observableFaceId entry
  let scalar := finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
    S rate orientation observableFaceId hobservableFace entry
  let normalizedWeight :=
    finePacketOrientedNormalizedJointExpandedWitnessWeight
      S hfineCutoff hcoarseCoupling orientation
        entry.1.sources.1 entry.1.sources.2
  have hsum := listQSum_mul_left_local scalar normalizedWeight carrier
  have hnormalized :=
    finePacketOrientedNormalizedJointExpandedWitnessWeight_total
      S hfineCutoff hcoarseCoupling orientation
        entry.1.sources.1 entry.1.sources.2 entry.1.targets
        (finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
          S orientation observableFaceId entry)
        (finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
          S orientation observableFaceId entry)
  refine Q'.eqv_trans _ (scalar * listQSum normalizedWeight carrier) _ ?_ ?_
  · simpa only [finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight,
      scalar, normalizedWeight, carrier] using hsum
  refine Q'.eqv_trans _
    (scalar * finePacketOrientedGroundNormalizedUnitCongestion
      S hfineCutoff hcoarseCoupling orientation
        entry.1.sources.1 entry.1.sources.2 entry.1.targets) _
    (Q'.mul_eqv_congr_left scalar _ _ hnormalized)
    (finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_mul_congestion
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace entry)

/-- Expanding one connected entry into its attached accepted
fusion/lowering block preserves its entropy-funded weight exactly. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessBlock_weight_total
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId) :
    listQSum
        (finePacketGlobalNonzeroConnectedExpandedWitnessWeight
          S hfineCutoff hcoarseCoupling rate orientation observableFaceId
            hobservableFace)
        (finePacketGlobalNonzeroConnectedExpandedWitnessBlock
          S orientation observableFaceId entry) ≈
      finePacketGlobalNonzeroConnectedEntryEntropyFundedWeight
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry := by
  let carrier := finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
    S orientation observableFaceId entry
  let weight := finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
    S hfineCutoff hcoarseCoupling rate orientation observableFaceId
      hobservableFace entry
  refine Q'.eqv_trans _ (listQSum weight carrier) _ ?_ ?_
  · unfold finePacketGlobalNonzeroConnectedExpandedWitnessBlock
      finePacketGlobalNonzeroConnectedExpandedWitnessWeight
    rw [listQSum_map]
    exact Q'.eqv_of_eq (listQSum_attach weight carrier)
  · exact
      finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier_weight_total
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace entry

/-! ## 4. Flatten every connected entry -/

def finePacketGlobalNonzeroConnectedExpandedWitnessMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) : Q' :=
  listQSum
    (finePacketGlobalNonzeroConnectedExpandedWitnessWeight
      S hfineCutoff hcoarseCoupling rate orientation observableFaceId
        hobservableFace)
    (finePacketGlobalNonzeroConnectedExpandedWitnessEntries
      S orientation observableFaceId)

/-- The single flattened witness mass is exactly the existing
entropy-funded connected mass. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessMass_eqv_entropyFunded
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (rate : Q') (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNonzeroConnectedExpandedWitnessMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace ≈
      finePacketGlobalNonzeroConnectedEntropyFundedMass
        S hfineCutoff hcoarseCoupling rate orientation observableFaceId
          hobservableFace := by
  unfold finePacketGlobalNonzeroConnectedExpandedWitnessMass
    finePacketGlobalNonzeroConnectedExpandedWitnessEntries
    finePacketGlobalNonzeroConnectedEntropyFundedMass
  refine Q'.eqv_trans _
    (listQSum
      (fun entry =>
        listQSum
          (finePacketGlobalNonzeroConnectedExpandedWitnessWeight
            S hfineCutoff hcoarseCoupling rate orientation observableFaceId
              hobservableFace)
          (finePacketGlobalNonzeroConnectedExpandedWitnessBlock
            S orientation observableFaceId entry))
      (finePacketGlobalOrientedNonzeroConnectedEntries
        S orientation observableFaceId)) _
    (listQSum_flatMap _ _ _) ?_
  apply listQSum_congr
  intro entry
  exact finePacketGlobalNonzeroConnectedExpandedWitnessBlock_weight_total
    S hfineCutoff hcoarseCoupling rate orientation observableFaceId
      hobservableFace entry

#print axioms finePacketGlobalNonzeroConnectedEntry_leftTarget_mem_physical
#print axioms finePacketGlobalNonzeroConnectedEntry_rightTarget_mem_physical
#print axioms finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier
#print axioms finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier_nodup
#print axioms FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessBlock
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessEntries
#print axioms finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix
#print axioms finePacketGlobalNonzeroConnectedEntryExpandedWitnessWeight
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessWeight
#print axioms finePacketGlobalNonzeroConnectedEntryExpandedWitnessPrefix_mul_congestion
#print axioms finePacketGlobalNonzeroConnectedEntryJointWitnessCarrier_weight_total
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessBlock_weight_total
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessMass_eqv_entropyFunded

end YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
