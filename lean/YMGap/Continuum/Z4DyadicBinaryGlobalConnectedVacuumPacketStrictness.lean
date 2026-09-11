/-
# Strict connected-row mass from a positive vacuum-packet sector

The normalized connected target carrier is a conditional probability over
two production rows.  Consequently target labels outside the observable
event must be summed by row normalization, rather than enumerated as contour
entropy.  The only source pairs that can contribute have at least one
nonempty four-face dyadic packet above the observable face: when both packets
are empty, every nonzero lowering row forces both observable target spins to
be zero, contradicting the connected carrier.

At the named SU(2) anchor the probability `p` that one fine packet is
nonempty is at most `256/425`.  For two independent fine sources the active
source-pair probability is exactly

  `p + (1-p) * p`.

The elementary square inequality `p(1-p) <= 1/4` therefore gives the explicit
strict rate `256/425 + 1/4 = 1449/1700 < 1`.  This avoids any count of target
labels outside the observable component.

Constructive contract: exact normalized production rows, finite Boolean
partitions, and rational square nonnegativity only; no `Classical`, choice,
`native_decide`, proof hole, noncomputable declaration, trusted external
computation, enlarged heartbeat budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinaryGlobalConnectedJointActivityBound
import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation
import YMGap.Constructive.SumOfSquares

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.SumOfSquares
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeAnchorPacketOccupation
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPositiveTimeDyadicSupport
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelGap
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4ActivityMatchedFiniteConfigurationKernel
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectivityPartition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (try unfold Q'.sub;
             show _ * (_ : Int) = _ * (_ : Int);
             try simp only [Q'.sub, Q'.add_num_cast, Q'.add_den_cast,
               Q'.mul_num_cast, Q'.mul_den_cast, Q'.neg_den,
               Q'.ofNat_num_cast, Q'.ofNat_den_cast,
               Q'.mkPos_num, Q'.mkPos_den,
               neg_num_cast_local, Int.add_mul, Int.mul_add, Int.neg_mul,
               Int.mul_neg, Int.neg_add, Int.neg_neg, Int.one_mul,
               Int.mul_one];
             ac_rfl))

private theorem qmul_congr_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem two_mul_eqv_add_local (x : Q') :
    Q'.ofNat 2 * x ≈ x + x := by
  refine Q'.eqv_trans _ (((1 : Q') + 1) * x) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  · refine Q'.eqv_trans _ (1 * x + 1 * x) _
      (Q'.add_mul_eqv 1 1 x) ?_
    exact Q'.add_eqv_congr' (Q'.one_mul_eqv x) (Q'.one_mul_eqv x)

private theorem four_mul_eqv_four_add_local (x : Q') :
    Q'.ofNat 4 * x ≈ (x + x) + (x + x) := by
  refine Q'.eqv_trans _
    ((Q'.ofNat 2 + Q'.ofNat 2) * x) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _ (by decide)
  · refine Q'.eqv_trans _
      (Q'.ofNat 2 * x + Q'.ofNat 2 * x) _
      (Q'.add_mul_eqv _ _ _) ?_
    exact Q'.add_eqv_congr'
      (two_mul_eqv_add_local x) (two_mul_eqv_add_local x)

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
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

private theorem finiteEventMass_add_complement_eqv_total
    {A : Type} (mass : A → Q') (states : List A)
    (event : A → Bool) :
    finiteEventMass mass states event +
        finiteEventMass mass states (fun state => !(event state)) ≈
      listQSum mass states := by
  unfold finiteEventMass
  refine Q'.eqv_trans _
    (listQSum
      (fun state =>
        (if event state then mass state else 0) +
          (if !(event state) then mass state else 0))
      states) _ ?_ ?_
  · exact Q'.eqv_symm
      (listQSum_add
        (fun state => if event state then mass state else 0)
        (fun state => if !(event state) then mass state else 0)
        states)
  · apply listQSum_congr_on
    intro state _
    cases hevent : event state
    · simp only [Bool.not_false, Bool.false_eq_true, if_false, if_true]
      exact Q'.eqv_of_eq (Q'.zero_add' (mass state))
    · simp only [Bool.not_true, if_true]
      exact Q'.eqv_of_eq (Q'.add_zero' (mass state))

/-! ## 1. Empty fine packets kill the connected target row -/

private theorem sourcePacketTotal_eq_zero_of_empty
    (S : SlabScalePair) (source : EdgeLabelling)
    (observableFaceId : Nat)
    (hempty : dyadicFinePacketPositiveB
      S observableFaceId source = false) :
    wholeSlabFinePacketTotalLabelling
        S source observableFaceId = 0 := by
  apply Nat.eq_zero_of_not_pos
  unfold dyadicFinePacketPositiveB at hempty
  exact of_decide_eq_false hempty

private theorem finePacketOrientedRawPairWeight_eqv_zero_of_both_empty
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hfirstEmpty : dyadicFinePacketPositiveB
      S observableFaceId first.1 = false)
    (hsecondEmpty : dyadicFinePacketPositiveB
      S observableFaceId second.1 = false)
    (pair : EdgeLabelling × EdgeLabelling)
    (hpair : pair ∈ finePacketFaceResponseConnectedActivePairs
      S first.1 second.1 observableFaceId) :
    finePacketOrientedLocalizedRawPairWeight
        S orientation first.1 second.1 pair ≈ 0 := by
  by_cases hzero : finePacketOrientedLocalizedRawPairWeight
      S orientation first.1 second.1 pair ≈ 0
  · exact hzero
  · have hphysical := (List.mem_filter.mp (List.mem_filter.mp hpair).1).1
    have hpath := finePacketFaceResponseConnectedActivePairPath
      S first.1 second.1 observableFaceId hobservableFace pair hpair
    have hfirstZero := sourcePacketTotal_eq_zero_of_empty
      S first.1 observableFaceId hfirstEmpty
    have hsecondZero := sourcePacketTotal_eq_zero_of_empty
      S second.1 observableFaceId hsecondEmpty
    cases orientation with
    | forward =>
        have hlowering :=
          finePacketForwardLocalizedRawPairWeight_ne_zero_implies_lowering
            S hfineCutoff first second pair hphysical hzero
        have hleft :=
          ((mem_spinFourLoweringTargets_iff S
            (wholeSlabFinePacketTotalLabelling S first.1) pair.1).mp
              hlowering.1).2 observableFaceId hobservableFace
        have hright :=
          ((mem_spinFourLoweringTargets_iff S
            (wholeSlabFinePacketTotalLabelling S second.1) pair.2).mp
              hlowering.2).2 observableFaceId hobservableFace
        have hleftZero : pair.1 observableFaceId = 0 := by omega
        have hrightZero : pair.2 observableFaceId = 0 := by omega
        exact False.elim
          (hpath.observable_targetStates_ne (hleftZero.trans hrightZero.symm))
    | reverse =>
        have hlowering :=
          finePacketReverseLocalizedRawPairWeight_ne_zero_implies_lowering
            S hfineCutoff first second pair hphysical hzero
        have hleft :=
          ((mem_spinFourLoweringTargets_iff S
            (wholeSlabFinePacketTotalLabelling S second.1) pair.1).mp
              hlowering.1).2 observableFaceId hobservableFace
        have hright :=
          ((mem_spinFourLoweringTargets_iff S
            (wholeSlabFinePacketTotalLabelling S first.1) pair.2).mp
              hlowering.2).2 observableFaceId hobservableFace
        have hleftZero : pair.1 observableFaceId = 0 := by omega
        have hrightZero : pair.2 observableFaceId = 0 := by omega
        exact False.elim
          (hpath.observable_targetStates_ne (hleftZero.trans hrightZero.symm))

/-- If both fine packets above the observable face are empty, the complete
normalized connected target-pair row is exactly zero. -/
theorem finePacketOrientedNormalizedConnectedJointMass_eqv_zero_of_both_empty
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hfirstEmpty : dyadicFinePacketPositiveB
      S observableFaceId first.1 = false)
    (hsecondEmpty : dyadicFinePacketPositiveB
      S observableFaceId second.1 = false) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≈ 0 := by
  unfold finePacketOrientedNormalizedConnectedJointMass
  refine Q'.eqv_trans _
    (listQSum
      (fun _entry : {pair // pair ∈
          finePacketFaceResponseConnectedActivePairs
            S first.1 second.1 observableFaceId} => (0 : Q'))
      (finePacketFaceResponseConnectedActivePairs
        S first.1 second.1 observableFaceId).attach) _ ?_ ?_
  · apply listQSum_congr
    intro entry
    apply finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
    exact finePacketOrientedRawPairWeight_eqv_zero_of_both_empty
      S hfineCutoff orientation first second observableFaceId hobservableFace
        hfirstEmpty hsecondEmpty entry.1 entry.2
  · exact listQSum_zero _

/-! ## 2. Normalize the source-pair complement -/

def finePacketObservablePositiveNormalizedSourceWeight
    (S : SlabScalePair) (observableFaceId : Nat)
    (source : EdgeLabelling) : Q' :=
  if dyadicFinePacketPositiveB S observableFaceId source then
    S.fine.normalizedMass source
  else
    0

def finePacketObservableEmptyNormalizedSourceWeight
    (S : SlabScalePair) (observableFaceId : Nat)
    (source : EdgeLabelling) : Q' :=
  if dyadicFinePacketPositiveB S observableFaceId source then
    0
  else
    S.fine.normalizedMass source

/-- The two disjoint ways for a pair of sources to contain a nonempty
observable packet: the first packet is nonempty, or the first is empty and
the second is nonempty. -/
def finePacketObservableActiveNormalizedSourcePairWeight
    (S : SlabScalePair) (observableFaceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  finePacketObservablePositiveNormalizedSourceWeight
      S observableFaceId pair.1 *
      S.fine.normalizedMass pair.2 +
    finePacketObservableEmptyNormalizedSourceWeight
      S observableFaceId pair.1 *
      finePacketObservablePositiveNormalizedSourceWeight
        S observableFaceId pair.2

def finePacketObservableActiveNormalizedSourcePairMass
    (S : SlabScalePair) (observableFaceId : Nat) : Q' :=
  listQSum
    (finePacketObservableActiveNormalizedSourcePairWeight
      S observableFaceId)
    (cartesian S.fine.physicalLabellings S.fine.physicalLabellings)

def finePacketObservablePositiveNormalizedSourceMass
    (S : SlabScalePair) (observableFaceId : Nat) : Q' :=
  normalizedSlabEventMass S.fine
    (dyadicFinePacketPositiveB S observableFaceId)

def finePacketObservableEmptyNormalizedSourceMass
    (S : SlabScalePair) (observableFaceId : Nat) : Q' :=
  normalizedSlabEventMass S.fine
    (fun source => !(dyadicFinePacketPositiveB S observableFaceId source))

private theorem finePacketObservablePositiveNormalizedSourceWeight_nonnegative
    (S : SlabScalePair) (observableFaceId : Nat) (source : EdgeLabelling) :
    (0 : Q') ≤ finePacketObservablePositiveNormalizedSourceWeight
      S observableFaceId source := by
  unfold finePacketObservablePositiveNormalizedSourceWeight
  cases dyadicFinePacketPositiveB S observableFaceId source
  · exact Q'.le_refl' 0
  · exact S.fine.normalizedMass_nonnegative source

private theorem finePacketObservableEmptyNormalizedSourceWeight_nonnegative
    (S : SlabScalePair) (observableFaceId : Nat) (source : EdgeLabelling) :
    (0 : Q') ≤ finePacketObservableEmptyNormalizedSourceWeight
      S observableFaceId source := by
  unfold finePacketObservableEmptyNormalizedSourceWeight
  cases dyadicFinePacketPositiveB S observableFaceId source
  · exact S.fine.normalizedMass_nonnegative source
  · exact Q'.le_refl' 0

private theorem finePacketObservableActiveNormalizedSourcePairWeight_nonnegative
    (S : SlabScalePair) (observableFaceId : Nat)
    (pair : EdgeLabelling × EdgeLabelling) :
    (0 : Q') ≤ finePacketObservableActiveNormalizedSourcePairWeight
      S observableFaceId pair := by
  unfold finePacketObservableActiveNormalizedSourcePairWeight
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (finePacketObservablePositiveNormalizedSourceWeight_nonnegative
        S observableFaceId pair.1)
      (S.fine.normalizedMass_nonnegative pair.2))
    (Q'.mul_nonneg _ _
      (finePacketObservableEmptyNormalizedSourceWeight_nonnegative
        S observableFaceId pair.1)
      (finePacketObservablePositiveNormalizedSourceWeight_nonnegative
        S observableFaceId pair.2))

private theorem finePacketObservablePositiveNormalizedSourceWeight_sum_eqv
    (S : SlabScalePair) (observableFaceId : Nat) :
    listQSum
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId)
        S.fine.physicalLabellings ≈
      finePacketObservablePositiveNormalizedSourceMass
        S observableFaceId := by
  unfold finePacketObservablePositiveNormalizedSourceWeight
    finePacketObservablePositiveNormalizedSourceMass
    normalizedSlabEventMass finiteEventMass
  exact Q'.eqv_refl _

private theorem finePacketObservableEmptyNormalizedSourceWeight_sum_eqv
    (S : SlabScalePair) (observableFaceId : Nat) :
    listQSum
        (finePacketObservableEmptyNormalizedSourceWeight
          S observableFaceId)
        S.fine.physicalLabellings ≈
      finePacketObservableEmptyNormalizedSourceMass
        S observableFaceId := by
  unfold finePacketObservableEmptyNormalizedSourceWeight
    finePacketObservableEmptyNormalizedSourceMass
    normalizedSlabEventMass finiteEventMass
  apply listQSum_congr_on
  intro source _
  cases hpositive : dyadicFinePacketPositiveB S observableFaceId source
  · simp only [hpositive, Bool.not_false, Bool.false_eq_true, if_false, if_true]
    exact Q'.eqv_refl _
  · simp only [hpositive, Bool.not_true, Bool.false_eq_true, if_true, if_false]
    exact Q'.eqv_refl _

private theorem positiveSourceWeightSum_mul_total_eqv_positiveMass
    (S : SlabScalePair) (observableFaceId : Nat) :
    listQSum
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId) S.fine.physicalLabellings *
      listQSum S.fine.normalizedMass S.fine.physicalLabellings ≈
        finePacketObservablePositiveNormalizedSourceMass
          S observableFaceId := by
  refine Q'.eqv_trans _
    (finePacketObservablePositiveNormalizedSourceMass S observableFaceId *
      listQSum S.fine.normalizedMass S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketObservablePositiveNormalizedSourceWeight_sum_eqv
        S observableFaceId)
  · refine Q'.eqv_trans _
      (finePacketObservablePositiveNormalizedSourceMass S observableFaceId * 1)
      _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ S.fine.normalizedMass_total
    · exact Q'.mul_one_eqv _

private theorem emptySourceWeightSum_mul_positiveSourceWeightSum_eqv
    (S : SlabScalePair) (observableFaceId : Nat) :
    listQSum
        (finePacketObservableEmptyNormalizedSourceWeight
          S observableFaceId) S.fine.physicalLabellings *
      listQSum
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId) S.fine.physicalLabellings ≈
        finePacketObservableEmptyNormalizedSourceMass S observableFaceId *
          finePacketObservablePositiveNormalizedSourceMass
            S observableFaceId := by
  refine Q'.eqv_trans _
    (finePacketObservableEmptyNormalizedSourceMass S observableFaceId *
      listQSum
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId) S.fine.physicalLabellings) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (finePacketObservableEmptyNormalizedSourceWeight_sum_eqv
        S observableFaceId)
  · exact Q'.mul_eqv_congr_left _ _ _
      (finePacketObservablePositiveNormalizedSourceWeight_sum_eqv
        S observableFaceId)

private theorem activeSourcePairWeight_eqv_zero_of_both_empty
    (S : SlabScalePair) (observableFaceId : Nat) (first second : EdgeLabelling)
    (hfirst : dyadicFinePacketPositiveB S observableFaceId first = false)
    (hsecond : dyadicFinePacketPositiveB S observableFaceId second = false) :
    finePacketObservableActiveNormalizedSourcePairWeight
      S observableFaceId (first, second) ≈ 0 := by
  unfold finePacketObservableActiveNormalizedSourcePairWeight
    finePacketObservablePositiveNormalizedSourceWeight
    finePacketObservableEmptyNormalizedSourceWeight
  simp only [hfirst, hsecond, Bool.false_eq_true, if_false]
  exact Q'.eqv_trans _ (0 + 0) _
    (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.mul_zero_eqv _))
    (Q'.eqv_of_eq (Q'.zero_add' 0))

private theorem activeSourcePairWeight_eqv_product_of_first_empty_second_positive
    (S : SlabScalePair) (observableFaceId : Nat) (first second : EdgeLabelling)
    (hfirst : dyadicFinePacketPositiveB S observableFaceId first = false)
    (hsecond : dyadicFinePacketPositiveB S observableFaceId second = true) :
    finePacketObservableActiveNormalizedSourcePairWeight
        S observableFaceId (first, second) ≈
      S.fine.normalizedMass first * S.fine.normalizedMass second := by
  unfold finePacketObservableActiveNormalizedSourcePairWeight
    finePacketObservablePositiveNormalizedSourceWeight
    finePacketObservableEmptyNormalizedSourceWeight
  simp only [hfirst, hsecond, Bool.false_eq_true, if_false, if_true]
  exact Q'.eqv_trans _
    (0 + S.fine.normalizedMass first * S.fine.normalizedMass second) _
    (Q'.add_eqv_congr' (Q'.zero_mul_eqv _) (Q'.eqv_refl _))
    (Q'.eqv_of_eq (Q'.zero_add' _))

private theorem activeSourcePairWeight_eqv_product_of_first_positive
    (S : SlabScalePair) (observableFaceId : Nat) (first second : EdgeLabelling)
    (hfirst : dyadicFinePacketPositiveB S observableFaceId first = true) :
    finePacketObservableActiveNormalizedSourcePairWeight
        S observableFaceId (first, second) ≈
      S.fine.normalizedMass first * S.fine.normalizedMass second := by
  unfold finePacketObservableActiveNormalizedSourcePairWeight
    finePacketObservablePositiveNormalizedSourceWeight
    finePacketObservableEmptyNormalizedSourceWeight
  simp only [hfirst, if_true]
  exact Q'.eqv_trans _
    (S.fine.normalizedMass first * S.fine.normalizedMass second + 0) _
    (Q'.add_eqv_congr' (Q'.eqv_refl _) (Q'.zero_mul_eqv _))
    (Q'.eqv_of_eq (Q'.add_zero' _))

private theorem finePacketFineSourceRawPairWeight_eqv_normalized_mul_partitionSquare
    (S : SlabScalePair) (first second : EdgeLabelling) :
    finePacketFineSourceRawPairWeight S first second ≈
      (S.fine.normalizedMass first * S.fine.normalizedMass second) *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let partitionPos := slabParametricKPhysicalPartition_pos
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hfirst := Q'.divPos_mul_eqv
    (S.fine.physicalTerm first) S.fine.physicalPartition partitionPos
  have hsecond := Q'.divPos_mul_eqv
    (S.fine.physicalTerm second) S.fine.physicalPartition partitionPos
  unfold finePacketFineSourceRawPairWeight
  refine Q'.eqv_symm (Q'.eqv_trans _
    ((S.fine.normalizedMass first * S.fine.physicalPartition) *
      (S.fine.normalizedMass second * S.fine.physicalPartition)) _ ?_ ?_)
  · ring_qeqv
  · exact qmul_congr_local hfirst hsecond

private theorem finePacketOrientedConnectedMass_le_active_of_product
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (first second : PositivePhysicalSource S)
    (hactive : finePacketObservableActiveNormalizedSourcePairWeight
        S observableFaceId (first.1, second.1) ≈
      S.fine.normalizedMass first.1 * S.fine.normalizedMass second.1) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≤
      finePacketObservableActiveNormalizedSourcePairWeight
          S observableFaceId (first.1, second.1) *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  have hrow :=
    finePacketOrientedNormalizedConnectedJointMass_le_sourcePairWeight
      S hfineCutoff hcoarseCoupling orientation first second observableFaceId
  exact Q'.le_trans' _ _ _ hrow
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        ((S.fine.normalizedMass first.1 *
            S.fine.normalizedMass second.1) *
          (S.fine.physicalPartition * S.fine.physicalPartition)) _
        (finePacketFineSourceRawPairWeight_eqv_normalized_mul_partitionSquare
          S first.1 second.1)
        (Q'.mul_eqv_congr_right _ _ _ (Q'.eqv_symm hactive))))

private theorem finePacketOrientedConnectedMass_le_activeSourcePairWeight
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (first second : PositivePhysicalSource S) :
    finePacketOrientedNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation first second
          observableFaceId ≤
      finePacketObservableActiveNormalizedSourcePairWeight
          S observableFaceId (first.1, second.1) *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  cases hfirst : dyadicFinePacketPositiveB S observableFaceId first.1
  · cases hsecond : dyadicFinePacketPositiveB S observableFaceId second.1
    · have hzero :=
        finePacketOrientedNormalizedConnectedJointMass_eqv_zero_of_both_empty
          S hfineCutoff hcoarseCoupling orientation first second
            observableFaceId hobservableFace hfirst hsecond
      exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hzero)
        (Q'.mul_nonneg _ _
          (finePacketObservableActiveNormalizedSourcePairWeight_nonnegative
            S observableFaceId (first.1, second.1))
          (Q'.mul_nonneg _ _
            (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))
            (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))))
    · exact finePacketOrientedConnectedMass_le_active_of_product
        S hfineCutoff hcoarseCoupling orientation observableFaceId first second
          (activeSourcePairWeight_eqv_product_of_first_empty_second_positive
            S observableFaceId first.1 second.1 hfirst hsecond)
  · exact finePacketOrientedConnectedMass_le_active_of_product
      S hfineCutoff hcoarseCoupling orientation observableFaceId first second
        (activeSourcePairWeight_eqv_product_of_first_positive
          S observableFaceId first.1 second.1 hfirst)

private theorem finePacketPositiveSourceActivePairMass_le_full
    (S : SlabScalePair) (observableFaceId : Nat) :
    listQSum
        (fun pair : PositivePhysicalSourcePair S =>
          finePacketObservableActiveNormalizedSourcePairWeight
            S observableFaceId (pair.1.1, pair.2.1))
        (positivePhysicalSourcePairs S) ≤
      finePacketObservableActiveNormalizedSourcePairMass
        S observableFaceId := by
  unfold finePacketObservableActiveNormalizedSourcePairMass
  apply listQSum_le_of_injective_nodup
    (positivePhysicalSourcePairs S)
    (cartesian S.fine.physicalLabellings S.fine.physicalLabellings)
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketObservableActiveNormalizedSourcePairWeight
        S observableFaceId (pair.1.1, pair.2.1))
    (finePacketObservableActiveNormalizedSourcePairWeight
      S observableFaceId)
    (fun pair : PositivePhysicalSourcePair S => (pair.1.1, pair.2.1))
  · exact positivePhysicalSourcePairs_nodup S
  · exact cartesian_nodup _ _
      (slabPhysicalLabellings_nodup S.fine)
      (slabPhysicalLabellings_nodup S.fine)
  · intro pair _
    exact (mem_cartesian_iff _ _ _).mpr ⟨pair.1.2.1, pair.2.2.1⟩
  · intro left _ right _ heq
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst heq
    · apply Subtype.ext
      exact congrArg Prod.snd heq
  · intro pair _
    exact Q'.le_refl' _
  · intro pair _
    exact finePacketObservableActiveNormalizedSourcePairWeight_nonnegative
      S observableFaceId pair

/-- Row normalization contracts all target labels first.  The global
connected fraction is therefore bounded by the probability that at least one
of the two independent fine-source packets is nonempty. -/
theorem finePacketGlobalNormalizedConnectedJointFraction_le_activeSourcePairMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketObservableActiveNormalizedSourcePairMass
        S observableFaceId := by
  let partitionSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hpartitionSquare : (0 : Q') < partitionSquare :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  unfold finePacketGlobalNormalizedConnectedJointFraction
  apply Q'.divPos_le_of_le_mul
  have hpoint : finePacketGlobalNormalizedConnectedJointMass
      S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
    listQSum
      (fun pair : PositivePhysicalSourcePair S =>
        finePacketObservableActiveNormalizedSourcePairWeight
            S observableFaceId (pair.1.1, pair.2.1) * partitionSquare)
      (positivePhysicalSourcePairs S) := by
    unfold finePacketGlobalNormalizedConnectedJointMass
    apply listQSum_mono_local
    intro pair _
    exact finePacketOrientedConnectedMass_le_activeSourcePairWeight
      S hfineCutoff hcoarseCoupling orientation observableFaceId
        hobservableFace pair.1 pair.2
  have hfactor := listQSum_mul_right
    (fun pair : PositivePhysicalSourcePair S =>
      finePacketObservableActiveNormalizedSourcePairWeight
        S observableFaceId (pair.1.1, pair.2.1))
    partitionSquare (positivePhysicalSourcePairs S)
  exact Q'.le_trans' _ _ _ hpoint
    (Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (finePacketPositiveSourceActivePairMass_le_full
          S observableFaceId)
        (Q'.le_of_lt hpartitionSquare)))

/-! ## 3. The explicit anchor rate -/

def finePacketAnchorVacuumPacketStrictRate : Q' :=
  Q'.mkPos 1449 1700 (by decide)

private theorem normalizedPacketMass_add_emptyMass_eqv_one
    (S : SlabScalePair) (observableFaceId : Nat) :
    finePacketObservablePositiveNormalizedSourceMass S observableFaceId +
      finePacketObservableEmptyNormalizedSourceMass S observableFaceId ≈
      (1 : Q') := by
  unfold finePacketObservablePositiveNormalizedSourceMass
    finePacketObservableEmptyNormalizedSourceMass
  exact Q'.eqv_trans _
    (listQSum S.fine.normalizedMass S.fine.physicalLabellings) _
    (finiteEventMass_add_complement_eqv_total
      S.fine.normalizedMass S.fine.physicalLabellings
        (dyadicFinePacketPositiveB S observableFaceId))
    S.fine.normalizedMass_total

private theorem bernoulli_cross_le_quarter
    {positive empty : Q'}
    (htotal : positive + empty ≈ (1 : Q')) :
    empty * positive ≤ Q'.mkPos 1 4 (by decide) := by
  let difference := positive + -empty
  have hsquare : (0 : Q') ≤ difference * difference :=
    q_mul_self_nonneg difference
  have hadd : Q'.ofNat 4 * (empty * positive) ≤
      Q'.ofNat 4 * (empty * positive) + difference * difference :=
    Q'.add_le_self_of_nonneg _ _ hsquare
  have hidentity :
      Q'.ofNat 4 * (empty * positive) + difference * difference ≈
        (1 : Q') := by
    refine Q'.eqv_trans _
      (((empty * positive + empty * positive) +
          (empty * positive + empty * positive)) +
        difference * difference) _ ?_ ?_
    · exact Q'.add_eqv_congr_right _ _ _
        (four_mul_eqv_four_add_local (empty * positive))
    · refine Q'.eqv_trans _
        (((empty * positive + -(empty * positive)) +
          ((empty * positive + -(empty * positive)) +
            (positive * positive +
              (empty * positive + empty * positive + empty * empty))))) _
        ?_ ?_
      · unfold difference
        ring_qeqv
      · refine Q'.eqv_trans _
          (0 + (0 + (positive * positive +
            (empty * positive + empty * positive + empty * empty)))) _ ?_ ?_
        · exact Q'.add_eqv_congr'
            (Q'.add_neg_self_eqv (empty * positive))
            (Q'.add_eqv_congr_right _ _ _
              (Q'.add_neg_self_eqv (empty * positive)))
        · refine Q'.eqv_trans _
            (positive * positive +
              (empty * positive + empty * positive + empty * empty)) _ ?_ ?_
          · exact Q'.eqv_trans _
              (0 + (positive * positive +
                (empty * positive + empty * positive + empty * empty))) _
              (Q'.add_eqv_congr_left 0 _ _
                (Q'.eqv_of_eq (Q'.zero_add' _)))
              (Q'.eqv_of_eq (Q'.zero_add' _))
          · refine Q'.eqv_trans _
              ((positive + empty) * (positive + empty)) _ ?_ ?_
            · ring_qeqv
            · exact Q'.eqv_trans _ (1 * 1) _
                (qmul_congr_local htotal htotal)
                (Q'.one_mul_eqv 1)
  have hfour : Q'.ofNat 4 * (empty * positive) ≤ (1 : Q') :=
    Q'.le_trans' _ _ _ hadd (Q'.le_of_eqv hidentity)
  have hquarter0 : (0 : Q') ≤ Q'.mkPos 1 4 (by decide) := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _ hfour hquarter0
  have hquarterFour :
      Q'.mkPos 1 4 (by decide) * Q'.ofNat 4 ≈ (1 : Q') := by
    decide
  exact Q'.le_trans' _
    (Q'.mkPos 1 4 (by decide) *
      (Q'.ofNat 4 * (empty * positive))) _
    (Q'.ge_of_eqv
      (Q'.eqv_trans _
        ((Q'.mkPos 1 4 (by decide) * Q'.ofNat 4) *
          (empty * positive)) _
        (Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _))
        (Q'.eqv_trans _ (1 * (empty * positive)) _
          (Q'.mul_eqv_congr_right _ _ _ hquarterFour)
          (Q'.one_mul_eqv _))))
    (Q'.le_trans' _
      (Q'.mkPos 1 4 (by decide) * (1 : Q')) _
      hscaled (Q'.le_of_eqv (Q'.mul_one_eqv _)))

theorem finePacketObservableActiveNormalizedSourcePairMass_eqv
    (S : SlabScalePair) (observableFaceId : Nat) :
    finePacketObservableActiveNormalizedSourcePairMass
        S observableFaceId ≈
      finePacketObservablePositiveNormalizedSourceMass S observableFaceId +
        finePacketObservableEmptyNormalizedSourceMass S observableFaceId *
          finePacketObservablePositiveNormalizedSourceMass
            S observableFaceId := by
  unfold finePacketObservableActiveNormalizedSourcePairMass
    finePacketObservableActiveNormalizedSourcePairWeight
  refine Q'.eqv_trans _
    (listQSum
        (fun pair =>
          finePacketObservablePositiveNormalizedSourceWeight
              S observableFaceId pair.1 *
            S.fine.normalizedMass pair.2)
        (cartesian S.fine.physicalLabellings S.fine.physicalLabellings) +
      listQSum
        (fun pair =>
          finePacketObservableEmptyNormalizedSourceWeight
              S observableFaceId pair.1 *
            finePacketObservablePositiveNormalizedSourceWeight
              S observableFaceId pair.2)
        (cartesian S.fine.physicalLabellings S.fine.physicalLabellings)) _
    (listQSum_add _ _ _) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · refine Q'.eqv_trans _
      (listQSum
          (finePacketObservablePositiveNormalizedSourceWeight
            S observableFaceId) S.fine.physicalLabellings *
        listQSum S.fine.normalizedMass S.fine.physicalLabellings) _
      (listQSum_cartesian_product
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId)
        S.fine.normalizedMass
        S.fine.physicalLabellings S.fine.physicalLabellings) ?_
    exact positiveSourceWeightSum_mul_total_eqv_positiveMass
      S observableFaceId
  · refine Q'.eqv_trans _
      (listQSum
          (finePacketObservableEmptyNormalizedSourceWeight
            S observableFaceId) S.fine.physicalLabellings *
        listQSum
          (finePacketObservablePositiveNormalizedSourceWeight
            S observableFaceId) S.fine.physicalLabellings) _
      (listQSum_cartesian_product
        (finePacketObservableEmptyNormalizedSourceWeight S observableFaceId)
        (finePacketObservablePositiveNormalizedSourceWeight
          S observableFaceId)
        S.fine.physicalLabellings S.fine.physicalLabellings) ?_
    exact emptySourceWeightSum_mul_positiveSourceWeightSum_eqv
      S observableFaceId

theorem finePacketObservableActiveNormalizedSourcePairMass_le_anchorRate
    (S : SlabScalePair) (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketObservableActiveNormalizedSourcePairMass
        S observableFaceId ≤
      finePacketAnchorVacuumPacketStrictRate := by
  let positive := finePacketObservablePositiveNormalizedSourceMass
    S observableFaceId
  let empty := finePacketObservableEmptyNormalizedSourceMass
    S observableFaceId
  have htotal : positive + empty ≈ (1 : Q') :=
    normalizedPacketMass_add_emptyMass_eqv_one
      S observableFaceId
  have hpositive : positive ≤ Q'.mkPos 256 425 (by decide) :=
    by
      unfold positive finePacketObservablePositiveNormalizedSourceMass
      exact
        normalizedAnchorSlabDyadicFinePacketPositiveMass_le_twoFiftySixFourTwentyFive
          S cutoff half observableFaceId hfine hobservableFace
  have hcross : empty * positive ≤ Q'.mkPos 1 4 (by decide) :=
    bernoulli_cross_le_quarter htotal
  have hmass := Q'.le_trans' _ (positive + empty * positive) _
    (Q'.le_of_eqv
      (finePacketObservableActiveNormalizedSourcePairMass_eqv
        S observableFaceId))
    (Q'.add_le_add hpositive hcross)
  exact Q'.le_trans' _
    (Q'.mkPos 256 425 (by decide) + Q'.mkPos 1 4 (by decide)) _
    hmass (Q'.le_of_eqv (by
      unfold finePacketAnchorVacuumPacketStrictRate
      decide))

/-- At the named SU(2) anchor, every finite-volume connected production-row
fraction is bounded by the explicit volume-independent rate `1449/1700`. -/
theorem finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketAnchorVacuumPacketStrictRate := by
  exact Q'.le_trans' _ _ _
    (finePacketGlobalNormalizedConnectedJointFraction_le_activeSourcePairMass
      S hfineCutoff hcoarseCoupling orientation observableFaceId
        hobservableFace)
    (finePacketObservableActiveNormalizedSourcePairMass_le_anchorRate
      S cutoff half observableFaceId hfine hobservableFace)

theorem finePacketAnchorVacuumPacketStrictRate_lt_one :
    finePacketAnchorVacuumPacketStrictRate < (1 : Q') := by
  unfold finePacketAnchorVacuumPacketStrictRate
  decide

theorem finePacketGlobalNormalizedConnectedJointFraction_lt_one_at_anchor
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (cutoff half observableFaceId : Nat)
    (hfine : S.fine = anchorSlabPhysicalData cutoff half)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId <
      (1 : Q') := by
  exact lt_of_le_of_lt
    (finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
      S hfineCutoff hcoarseCoupling orientation cutoff half
        observableFaceId hfine hobservableFace)
    finePacketAnchorVacuumPacketStrictRate_lt_one

#print axioms finePacketOrientedNormalizedConnectedJointMass_eqv_zero_of_both_empty
#print axioms finePacketObservablePositiveNormalizedSourceWeight
#print axioms finePacketObservableEmptyNormalizedSourceWeight
#print axioms finePacketObservableActiveNormalizedSourcePairWeight
#print axioms finePacketObservableActiveNormalizedSourcePairMass
#print axioms finePacketGlobalNormalizedConnectedJointFraction_le_activeSourcePairMass
#print axioms finePacketAnchorVacuumPacketStrictRate
#print axioms finePacketObservableActiveNormalizedSourcePairMass_eqv
#print axioms finePacketObservableActiveNormalizedSourcePairMass_le_anchorRate
#print axioms finePacketGlobalNormalizedConnectedJointFraction_le_anchorVacuumPacketRate
#print axioms finePacketAnchorVacuumPacketStrictRate_lt_one
#print axioms finePacketGlobalNormalizedConnectedJointFraction_lt_one_at_anchor

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedVacuumPacketStrictness
