/-
# Combine source heat and normalized target excitation on the connected carrier

After target-row normalization, one connected entry is bounded by its literal
fine-source Gibbs pair weight times the complete SU(2) target-excitation rate.
The fine-source pair weight has an exact cutoff-one heat factor.  This file
puts both factors below one common named rate and contracts their exponents to
the connected carrier's joint source-plus-target activity.

At the explicit strong-coupling anchor `1/400`, the complete target rate
`5^9/2^32` is itself below the anchor.  Thus the global connected fraction is
bounded by a single anchor-power joint-activity sum with only the cutoff-one
unit-coupling source weight left as an entropy factor.

Constructive contract: explicit rational rate comparisons, finite power
monotonicity, exact cutoff-one source factorization, and finite-list sums only;
no `Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
trusted external computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedKernelExcitationBound
import YMGap.Continuum.Z4DyadicBinaryJointGibbsSubunitSuppression
import YMGap.Continuum.Z4StrongCouplingParametricAnchor

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedJointActivityBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.FusedAmplitudeDerivation
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedKernelExcitationBound
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinarySourcePacketOccupiedFaceBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

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

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      simp only [listQSum]
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hle item (List.mem_cons_of_mem head hitem)))

private theorem spinFourParityExcitationFullActivityRate_nonnegative
    (w : Q') (hw0 : (0 : Q') ≤ w) :
    (0 : Q') ≤ spinFourParityExcitationFullActivityRate w := by
  unfold spinFourParityExcitationFullActivityRate
    spinFourParityExcitationFaceActivityRate
  exact Q'.mul_nonneg _ _ (zero_le_ofNat _) <|
    Q'.mul_nonneg _ _ (zero_le_ofNat 5) (qpow_nonneg w hw0 8)

private theorem finePacketFineSourceUnitCouplingPairWeight_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling) :
    (0 : Q') ≤ finePacketFineSourceUnitCouplingPairWeight
      S first second := by
  unfold finePacketFineSourceUnitCouplingPairWeight
    fineUnitCouplingPhysicalTerm
  exact Q'.mul_nonneg _ _
    (slabParametricKPhysicalTerm_nonnegative
      (by decide) S.fine.cutoff S.fine.extent first)
    (slabParametricKPhysicalTerm_nonnegative
      (by decide) S.fine.cutoff S.fine.extent second)

/-! ## 1. One common explicit activity rate -/

/-- Throughout the named strong-coupling corridor, the complete cutoff-four
target-excitation rate is no larger than the anchor coupling itself. -/
theorem spinFourParityExcitationFullActivityRate_le_anchorCoupling
    {w : Q'} (hw0 : (0 : Q') ≤ w) (hwAnchor : w ≤ anchorCoupling) :
    spinFourParityExcitationFullActivityRate w ≤ anchorCoupling := by
  have hpower : qpow w 8 ≤ qpow anchorCoupling 8 :=
    HeatKernelGap.qpow_mono hw0 hwAnchor 8
  have hface : spinFourParityExcitationFaceActivityRate w ≤
      spinFourParityExcitationFaceActivityRate anchorCoupling := by
    unfold spinFourParityExcitationFaceActivityRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hpower (zero_le_ofNat 5)
  have hfull : spinFourParityExcitationFullActivityRate w ≤
      spinFourParityExcitationFullActivityRate anchorCoupling := by
    unfold spinFourParityExcitationFullActivityRate
    exact Q'.mul_le_mul_of_nonneg_left _ _ _ hface (zero_le_ofNat _)
  have hanchor : spinFourParityExcitationFullActivityRate anchorCoupling ≤
      anchorCoupling := by
    unfold anchorCoupling
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv spinFourParityExcitationFullActivityRate_anchor_eqv)
      (by decide)
  exact Q'.le_trans' _ _ _ hfull hanchor

/-! ## 2. Contract one source-weighted target activity to joint activity -/

/-- The fine source heat pays oriented source activity, while the complete
target rate pays target excitation.  Their exponents add to the carrier's
exact joint activity; only the fine cutoff-one unit-coupling source weight
remains. -/
theorem finePacketSourceWeight_mul_excitation_le_jointActivity
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hfullRate :
      spinFourParityExcitationFullActivityRate S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling) :
    finePacketFineSourceRawPairWeight S first.1 second.1 *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (finePacketOrientedTotalTargetExcitationActivity
            S orientation first.1 second.1 pair) ≤
      qpow rate
          (finePacketOrientedTotalJointActivity
            S orientation first.1 second.1 pair) *
        finePacketFineSourceUnitCouplingPairWeight
          S first.1 second.1 := by
  let occupied :=
    fineCouplingPhysicalOccupiedFaceCount S first.1 +
      fineCouplingPhysicalOccupiedFaceCount S second.1
  let sourceActivity := finePacketOrientedTotalSourceActivity
    S orientation first.1 second.1
  let targetActivity := finePacketOrientedTotalTargetExcitationActivity
    S orientation first.1 second.1 pair
  let sourcePower := qpow S.fine.coupling (3 * occupied)
  let targetPower := qpow
    (spinFourParityExcitationFullActivityRate S.coarse.coupling)
    targetActivity
  let unitWeight := finePacketFineSourceUnitCouplingPairWeight
    S first.1 second.1
  have hrate0 : (0 : Q') ≤ rate :=
    Q'.le_trans' _ _ _ S.fine.coupling_nonnegative hfineRate
  have hsourceFactor :=
    finePacketFineSourceRawPairWeight_eqv_occupiedPower_mul_unit
      S hfineCutoff first second
  have hsourceBase : sourcePower ≤ qpow rate (3 * occupied) :=
    qpow_mono_base S.fine.coupling_nonnegative hfineRate _
  have hsourceCount : sourceActivity ≤ occupied :=
    finePacketOrientedTotalSourceActivity_le_occupiedFaceCounts
      S hfineCutoff orientation first second
  have hsourceCountThree : sourceActivity ≤ 3 * occupied := by
    omega
  have hsourcePower : sourcePower ≤ qpow rate sourceActivity :=
    Q'.le_trans' _ _ _ hsourceBase
      (qpow_antitone hrate0 (Q'.le_of_lt hrate1)
        sourceActivity (3 * occupied) hsourceCountThree)
  have hfull0 : (0 : Q') ≤
      spinFourParityExcitationFullActivityRate S.coarse.coupling :=
    spinFourParityExcitationFullActivityRate_nonnegative
      S.coarse.coupling S.coarse.coupling_nonnegative
  have htargetPower : targetPower ≤ qpow rate targetActivity :=
    qpow_mono_base hfull0 hfullRate targetActivity
  have htargetPower0 : (0 : Q') ≤ targetPower :=
    qpow_nonneg _ hfull0 targetActivity
  have hrateSourcePower0 : (0 : Q') ≤ qpow rate sourceActivity :=
    qpow_nonneg rate hrate0 sourceActivity
  have hfirstStep : sourcePower * targetPower ≤
      qpow rate sourceActivity * targetPower :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hsourcePower htargetPower0
  have hsecondStep : qpow rate sourceActivity * targetPower ≤
      qpow rate sourceActivity * qpow rate targetActivity :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ htargetPower hrateSourcePower0
  have hcombined : sourcePower * targetPower ≤
      qpow rate (sourceActivity + targetActivity) :=
    Q'.le_trans' _ _ _ hfirstStep
      (Q'.le_trans' _ _ _ hsecondStep
        (Q'.ge_of_eqv (qpow_add rate sourceActivity targetActivity)))
  have hunit0 : (0 : Q') ≤ unitWeight :=
    finePacketFineSourceUnitCouplingPairWeight_nonnegative
      S first.1 second.1
  have hweighted : (sourcePower * targetPower) * unitWeight ≤
      qpow rate (sourceActivity + targetActivity) * unitWeight :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcombined hunit0
  have hleft :
      finePacketFineSourceRawPairWeight S first.1 second.1 *
          targetPower ≈
        (sourcePower * targetPower) * unitWeight := by
    refine Q'.eqv_trans _ ((sourcePower * unitWeight) * targetPower) _ ?_ ?_
    · exact Q'.mul_eqv_congr_right _ _ targetPower hsourceFactor
    · ring_qeqv
  rw [finePacketOrientedTotalJointActivity_eq_source_add_targetExcitation]
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hleft) hweighted

/-! ## 3. Sum and normalize the joint-activity target -/

def finePacketGlobalConnectedJointActivityMass
    (S : SlabScalePair) (rate : Q')
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun entry : FinePacketGlobalConnectedEntry S observableFaceId =>
      qpow rate
          (finePacketOrientedTotalJointActivity
            S orientation entry.sources.1.1 entry.sources.2.1
              entry.targets) *
        finePacketFineSourceUnitCouplingPairWeight
          S entry.sources.1.1 entry.sources.2.1)
    (finePacketGlobalConnectedEntries S observableFaceId)

def finePacketGlobalConnectedJointActivityFraction
    (S : SlabScalePair) (rate : Q')
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketGlobalConnectedJointActivityMass
      S rate orientation observableFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

theorem finePacketGlobalConnectedKernelExcitationMass_le_jointActivityMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hfullRate :
      spinFourParityExcitationFullActivityRate S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalConnectedKernelExcitationMass
        S orientation observableFaceId ≤
      finePacketGlobalConnectedJointActivityMass
        S rate orientation observableFaceId := by
  unfold finePacketGlobalConnectedKernelExcitationMass
    finePacketGlobalConnectedJointActivityMass
  apply listQSum_mono_local
  intro entry _hentry
  exact finePacketSourceWeight_mul_excitation_le_jointActivity
    S hfineCutoff rate hfineRate hfullRate hrate1 orientation
      entry.sources.1 entry.sources.2 entry.targets

theorem finePacketGlobalConnectedKernelExcitationFraction_le_jointActivityFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (rate : Q') (hfineRate : S.fine.coupling ≤ rate)
    (hfullRate :
      spinFourParityExcitationFullActivityRate S.coarse.coupling ≤ rate)
    (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalConnectedKernelExcitationFraction
        S orientation observableFaceId ≤
      finePacketGlobalConnectedJointActivityFraction
        S rate orientation observableFaceId := by
  let sourcePartitionSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hsourcePartitionSquare : (0 : Q') < sourcePartitionSquare :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hmass :=
    finePacketGlobalConnectedKernelExcitationMass_le_jointActivityMass
      S hfineCutoff rate hfineRate hfullRate hrate1 orientation
        observableFaceId
  unfold finePacketGlobalConnectedKernelExcitationFraction
    finePacketGlobalConnectedJointActivityFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hmass
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (finePacketGlobalConnectedJointActivityMass
          S rate orientation observableFaceId)
        sourcePartitionSquare hsourcePartitionSquare))

/-- At the explicit `1/400` corridor, the actual normalized connected
fraction is bounded by one common-rate joint-activity entropy fraction. -/
theorem finePacketGlobalNormalizedConnectedJointFraction_le_anchorJointActivityFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineAnchor : S.fine.coupling ≤ anchorCoupling)
    (hcoarseAnchor : S.coarse.coupling ≤ anchorCoupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketGlobalConnectedJointActivityFraction
        S anchorCoupling orientation observableFaceId := by
  have hanchorOne : anchorCoupling ≤ (1 : Q') := by
    unfold anchorCoupling
    decide
  have hcoarseOne : S.coarse.coupling ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hcoarseAnchor hanchorOne
  have hfullAnchor :
      spinFourParityExcitationFullActivityRate S.coarse.coupling ≤
        anchorCoupling :=
    spinFourParityExcitationFullActivityRate_le_anchorCoupling
      S.coarse.coupling_nonnegative hcoarseAnchor
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNormalizedConnectedJointFraction_le_kernelExcitationFraction
      S hfineCutoff hcoarseCoupling hcoarseOne orientation observableFaceId)
    (finePacketGlobalConnectedKernelExcitationFraction_le_jointActivityFraction
      S hfineCutoff anchorCoupling hfineAnchor hfullAnchor
        (by unfold anchorCoupling; decide) orientation observableFaceId)

#print axioms spinFourParityExcitationFullActivityRate_le_anchorCoupling
#print axioms finePacketSourceWeight_mul_excitation_le_jointActivity
#print axioms finePacketGlobalConnectedJointActivityMass
#print axioms finePacketGlobalConnectedJointActivityFraction
#print axioms finePacketGlobalConnectedKernelExcitationMass_le_jointActivityMass
#print axioms finePacketGlobalConnectedKernelExcitationFraction_le_jointActivityFraction
#print axioms finePacketGlobalNormalizedConnectedJointFraction_le_anchorJointActivityFraction

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedJointActivityBound
