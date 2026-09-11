/-
# Put the normalized production-kernel activity on the global connected carrier

The normalized connected joint summand factors exactly into its fine-source
Gibbs pair weight and the product of the two actual production-kernel rows.
The cutoff-four excitation estimate therefore replaces every supported target
pair by the explicit activity power `q(w)^K` without a source-dependent target
row prefactor.

Zero oriented rows are handled before extracting the lowering witness.  The
pointwise comparison then sums on the literal dependent connected carrier.
The resulting finite sum is the honest next entropy target; no uniform bound
on that sum is claimed here.

Constructive contract: exact rational cancellation against two proved-positive
row masses, finite list monotonicity, and the kernel-checked SU(2) activity
bound only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, enlarged heartbeat
budget, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityExcitationKernelBound
import YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier

namespace YMGap.Continuum.Z4DyadicBinaryGlobalConnectedKernelExcitationBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteSimpleWalk
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinaryGlobalConnectedDependentCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalNormalizedConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinaryJointGibbsHeatExponentFactorization
open YMGap.Continuum.Z4DyadicBinaryNormalizedConnectedUnitCongestionSum
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationFullActivityBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationKernelBound
open YMGap.Continuum.Z4DyadicBinarySourceParityExcitationTiltBound
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsLocalFactorization
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsRelativeExcitationEndpoints
open YMGap.Continuum.Z4DyadicBinaryTargetExcitationCasimirExcess
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

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

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _
      (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

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

private theorem finePacketFineSourceRawPairWeight_nonnegative
    (S : SlabScalePair) (first second : EdgeLabelling) :
    (0 : Q') ≤ finePacketFineSourceRawPairWeight S first second := by
  unfold finePacketFineSourceRawPairWeight
    CompactDualSlabPhysicalData.SlabPhysicalData.physicalTerm
  exact Q'.mul_nonneg _ _
    (slabParametricKPhysicalTerm_nonnegative
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent first)
    (slabParametricKPhysicalTerm_nonnegative
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent second)

/-! ## 1. Exact identification of the normalized target-row product -/

private theorem physicalKernel_mul_rowMass_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (source : PositivePhysicalSource S)
    (first second targetState : EdgeLabelling)
    (htarget : targetState ∈ S.coarse.physicalLabellings)
    (hlocalized :
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct S
            (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
        S.coarse.physicalTerm targetState ≈
      finePacketLocalizedTiltedGibbsRawWeight
        S source.1 first second targetState) :
    (physicalKernel S hfineCutoff hcoarseCoupling).kernel
          source.1 targetState *
        positivePhysicalSourceTiltedGibbsRowMass S source ≈
      finePacketLocalizedTiltedGibbsRawWeight
        S source.1 first second targetState := by
  let raw :=
    Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
      S.coarse.physicalTerm targetState
  let row := positivePhysicalSourceTiltedGibbsRowMass S source
  have hrow : (0 : Q') < row :=
    positivePhysicalSourceTiltedGibbsRowMass_pos
      S hfineCutoff hcoarseCoupling source
  have hkernel := physicalKernel_positivePhysicalSource_eqv_tiltedGibbs
    S hfineCutoff hcoarseCoupling source targetState htarget
  refine Q'.eqv_trans _ (Q'.divPos raw row hrow * row) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ row hkernel
  · exact Q'.eqv_trans _ raw _
      (Q'.divPos_mul_eqv raw row hrow) hlocalized

/-- Multiplying the actual oriented production-row pair by its exact two-row
normalization recovers the localized raw target pair. -/
theorem finePacketOrientedPhysicalKernelPairWeight_mul_normalization_eqv_localized
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedPhysicalKernelPairWeight
          S hfineCutoff hcoarseCoupling orientation first second pair *
        finePacketOrientedEnvelopeNormalizationMass S first second ≈
      finePacketOrientedLocalizedRawPairWeight
        S orientation first.1 second.1 pair := by
  cases orientation with
  | forward =>
      have hleftPhysical :=
        ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
      have hrightPhysical :=
        ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
      have hleft := physicalKernel_mul_rowMass_eqv_localized
        S hfineCutoff hcoarseCoupling first first.1 second.1 pair.1
          hleftPhysical
          (firstTiltedGibbsRawWeight_eqv_localized
            S first.1 second.1 pair.1)
      have hright := physicalKernel_mul_rowMass_eqv_localized
        S hfineCutoff hcoarseCoupling second first.1 second.1 pair.2
          hrightPhysical
          (secondTiltedGibbsRawWeight_eqv_localized
            S first.1 second.1 pair.2)
      unfold finePacketOrientedPhysicalKernelPairWeight
        finePacketOrientedEnvelopeNormalizationMass
        finePacketOrientedLocalizedRawPairWeight
        finePacketForwardLocalizedRawPairWeight
      refine Q'.eqv_trans _
        (((physicalKernel S hfineCutoff hcoarseCoupling).kernel
              first.1 pair.1 *
            positivePhysicalSourceTiltedGibbsRowMass S first) *
          ((physicalKernel S hfineCutoff hcoarseCoupling).kernel
              second.1 pair.2 *
            positivePhysicalSourceTiltedGibbsRowMass S second)) _ ?_ ?_
      · ring_qeqv
      · exact mul_eqv_both_local hleft hright
  | reverse =>
      have hleftPhysical :=
        ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.1).1
      have hrightPhysical :=
        ((mem_spinFourLoweringTargets_iff S _ _).mp hlowering.2).1
      have hleft := physicalKernel_mul_rowMass_eqv_localized
        S hfineCutoff hcoarseCoupling second first.1 second.1 pair.1
          hleftPhysical
          (secondTiltedGibbsRawWeight_eqv_localized
            S first.1 second.1 pair.1)
      have hright := physicalKernel_mul_rowMass_eqv_localized
        S hfineCutoff hcoarseCoupling first first.1 second.1 pair.2
          hrightPhysical
          (firstTiltedGibbsRawWeight_eqv_localized
            S first.1 second.1 pair.2)
      unfold finePacketOrientedPhysicalKernelPairWeight
        finePacketOrientedEnvelopeNormalizationMass
        finePacketOrientedLocalizedRawPairWeight
        finePacketReverseLocalizedRawPairWeight
      refine Q'.eqv_trans _
        (((physicalKernel S hfineCutoff hcoarseCoupling).kernel
              second.1 pair.1 *
            positivePhysicalSourceTiltedGibbsRowMass S second) *
          ((physicalKernel S hfineCutoff hcoarseCoupling).kernel
              first.1 pair.2 *
            positivePhysicalSourceTiltedGibbsRowMass S first)) _ ?_ ?_
      · ring_qeqv
      · exact mul_eqv_both_local hleft hright

/-- The older normalized joint summand is exactly the fine-source Gibbs pair
weight times the two actual production-kernel probabilities. -/
theorem finePacketOrientedNormalizedJointPairWeight_eqv_source_mul_kernel
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≈
      finePacketFineSourceRawPairWeight S first.1 second.1 *
        finePacketOrientedPhysicalKernelPairWeight
          S hfineCutoff hcoarseCoupling orientation first second pair := by
  let sourceWeight := finePacketFineSourceRawPairWeight S first.1 second.1
  let kernelWeight := finePacketOrientedPhysicalKernelPairWeight
    S hfineCutoff hcoarseCoupling orientation first second pair
  let row := finePacketOrientedEnvelopeNormalizationMass S first second
  have hrow : (0 : Q') < row :=
    finePacketOrientedEnvelopeNormalizationMass_pos
      S hfineCutoff hcoarseCoupling first second
  have htarget :=
    finePacketOrientedPhysicalKernelPairWeight_mul_normalization_eqv_localized
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  unfold finePacketOrientedNormalizedJointPairWeight
    finePacketOrientedJointGibbsRawPairWeight
  apply divPos_eqv_of_eqv_mul_local hrow
  refine Q'.eqv_trans _ (sourceWeight * (kernelWeight * row)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left sourceWeight _ _ (Q'.eqv_symm htarget)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv sourceWeight kernelWeight row)

/-! ## 2. Pointwise and summed connected-carrier bounds -/

/-- A supported normalized joint summand retains its exact fine-source weight
and pays only the explicit target-excitation activity in the production rows. -/
theorem finePacketOrientedNormalizedJointPairWeight_le_source_mul_excitation
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (first second : PositivePhysicalSource S)
    (pair : EdgeLabelling × EdgeLabelling)
    (hlowering : finePacketOrientedLoweringPair
      S orientation first.1 second.1 pair) :
    finePacketOrientedNormalizedJointPairWeight
        S hfineCutoff hcoarseCoupling orientation first second pair ≤
      finePacketFineSourceRawPairWeight S first.1 second.1 *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (finePacketOrientedTotalTargetExcitationActivity
            S orientation first.1 second.1 pair) := by
  have hexact :=
    finePacketOrientedNormalizedJointPairWeight_eqv_source_mul_kernel
      S hfineCutoff hcoarseCoupling orientation first second pair hlowering
  have hkernel :=
    finePacketOrientedPhysicalKernelPairWeight_le_excitationActivity
      S hfineCutoff hcoarseCoupling hcoarse1 orientation
        first second pair hlowering
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hexact)
    (Q'.mul_le_mul_of_nonneg_left _ _ _ hkernel
      (finePacketFineSourceRawPairWeight_nonnegative
        S first.1 second.1))

/-- The explicit finite entropy target left after normalized target-row
contraction on every global connected entry. -/
def finePacketGlobalConnectedKernelExcitationMass
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  listQSum
    (fun entry : FinePacketGlobalConnectedEntry S observableFaceId =>
      finePacketFineSourceRawPairWeight
          S entry.sources.1.1 entry.sources.2.1 *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (finePacketOrientedTotalTargetExcitationActivity
            S orientation entry.sources.1.1 entry.sources.2.1
              entry.targets))
    (finePacketGlobalConnectedEntries S observableFaceId)

/-- The source law is normalized only after the literal finite source-pair
sum.  This is the dimensionless observable-anchored entropy quantity that a
volume-independent contour estimate must bound. -/
def finePacketGlobalConnectedKernelExcitationFraction
    (S : SlabScalePair) (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) : Q' :=
  Q'.divPos
    (finePacketGlobalConnectedKernelExcitationMass
      S orientation observableFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

theorem finePacketGlobalConnectedEntryNormalizedWeight_le_kernelExcitation
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (entry : FinePacketGlobalConnectedEntry S observableFaceId) :
    finePacketGlobalConnectedEntryNormalizedWeight
        S hfineCutoff hcoarseCoupling orientation observableFaceId entry ≤
      finePacketFineSourceRawPairWeight
          S entry.sources.1.1 entry.sources.2.1 *
        qpow
          (spinFourParityExcitationFullActivityRate S.coarse.coupling)
          (finePacketOrientedTotalTargetExcitationActivity
            S orientation entry.sources.1.1 entry.sources.2.1
              entry.targets) := by
  by_cases hzero : finePacketGlobalConnectedEntryOrientedRawWeight
      S orientation observableFaceId entry ≈ 0
  · have hnormalized : finePacketGlobalConnectedEntryNormalizedWeight
        S hfineCutoff hcoarseCoupling orientation observableFaceId entry ≈
      0 := by
      unfold finePacketGlobalConnectedEntryNormalizedWeight
      apply finePacketOrientedNormalizedJointPairWeight_eqv_zero_of_raw_zero
      exact hzero
    have hsource0 := finePacketFineSourceRawPairWeight_nonnegative
      S entry.sources.1.1 entry.sources.2.1
    have hrate0 := spinFourParityExcitationFullActivityRate_nonnegative
      S.coarse.coupling (Q'.le_of_lt hcoarseCoupling)
    exact Q'.le_trans' _ 0 _ (Q'.le_of_eqv hnormalized)
      (Q'.mul_nonneg _ _ hsource0 (qpow_nonneg _ hrate0 _))
  · let nonzero : FinePacketGlobalOrientedNonzeroConnectedEntry
        S orientation observableFaceId := ⟨entry, hzero⟩
    have hlowering :=
      finePacketGlobalOrientedNonzeroConnectedEntryLowering
        S hfineCutoff orientation observableFaceId nonzero
    unfold finePacketGlobalConnectedEntryNormalizedWeight
    exact finePacketOrientedNormalizedJointPairWeight_le_source_mul_excitation
      S hfineCutoff hcoarseCoupling hcoarse1 orientation
        entry.sources.1 entry.sources.2 entry.targets hlowering

/-- The whole normalized connected mass is bounded on the same literal global
carrier by the source-weighted excitation fugacity sum. -/
theorem finePacketGlobalNormalizedConnectedJointMass_le_kernelExcitationMass
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointMass
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketGlobalConnectedKernelExcitationMass
        S orientation observableFaceId := by
  have hflatten := finePacketGlobalNormalizedConnectedJointMass_eqv_entrySum
    S hfineCutoff hcoarseCoupling orientation observableFaceId
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hflatten) ?_
  unfold finePacketGlobalConnectedKernelExcitationMass
  apply listQSum_mono_local
  intro entry _hentry
  exact finePacketGlobalConnectedEntryNormalizedWeight_le_kernelExcitation
    S hfineCutoff hcoarseCoupling hcoarse1 orientation
      observableFaceId entry

/-- Dividing the preceding inequality by the exact fine source partition
square exposes the normalized entropy target without changing its carrier. -/
theorem finePacketGlobalNormalizedConnectedJointFraction_le_kernelExcitationFraction
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hcoarse1 : S.coarse.coupling ≤ (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat) :
    finePacketGlobalNormalizedConnectedJointFraction
        S hfineCutoff hcoarseCoupling orientation observableFaceId ≤
      finePacketGlobalConnectedKernelExcitationFraction
        S orientation observableFaceId := by
  let sourcePartitionSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hsourcePartitionSquare : (0 : Q') < sourcePartitionSquare :=
    Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hmass :=
    finePacketGlobalNormalizedConnectedJointMass_le_kernelExcitationMass
      S hfineCutoff hcoarseCoupling hcoarse1 orientation observableFaceId
  unfold finePacketGlobalNormalizedConnectedJointFraction
    finePacketGlobalConnectedKernelExcitationFraction
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _ hmass
    (Q'.ge_of_eqv
      (Q'.divPos_mul_eqv
        (finePacketGlobalConnectedKernelExcitationMass
          S orientation observableFaceId)
        sourcePartitionSquare hsourcePartitionSquare))

#print axioms finePacketOrientedPhysicalKernelPairWeight_mul_normalization_eqv_localized
#print axioms finePacketOrientedNormalizedJointPairWeight_eqv_source_mul_kernel
#print axioms finePacketOrientedNormalizedJointPairWeight_le_source_mul_excitation
#print axioms finePacketGlobalConnectedKernelExcitationMass
#print axioms finePacketGlobalConnectedKernelExcitationFraction
#print axioms finePacketGlobalConnectedEntryNormalizedWeight_le_kernelExcitation
#print axioms finePacketGlobalNormalizedConnectedJointMass_le_kernelExcitationMass
#print axioms finePacketGlobalNormalizedConnectedJointFraction_le_kernelExcitationFraction

end YMGap.Continuum.Z4DyadicBinaryGlobalConnectedKernelExcitationBound
