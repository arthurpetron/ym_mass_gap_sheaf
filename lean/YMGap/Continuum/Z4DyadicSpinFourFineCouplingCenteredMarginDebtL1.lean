/-
# Finite L¹ envelope for the centered fine-source margin debt

The preceding pullback module identifies the normalized centered margin
numerator with a same-object average over fine source pairs.  This module
takes the first honest absolute-value step on that same source object:

  | sum_p debt(p) * contrast(p) |
      <= sum_p |debt(p)|.

The pointwise four-cell contrast bound makes this a genuine finite
certificate.  Later declarations collapse the explicit source debt envelope
using the exact finite source-pair totals.  No cutoff- or volume-uniform
sharp calibration is asserted.

Constructive contract: exact finite sums and rational inequalities only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback
import YMGap.Constructive.CRealAbs
import YMGap.Continuum.TsumDeriv
import YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtL1

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.TsumDeriv
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebt
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

local infix:50 " ≈ " => Q'.eqv

private theorem two_mul_eqv_local (a : Q') :
    (Q'.ofNat 2 * a).eqv (a + a) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 2) (1 + 1) a (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 a) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (1 * a) a (1 * a) (Q'.one_mul_eqv a)) ?_
  exact Q'.add_eqv_congr_left a (1 * a) a (Q'.one_mul_eqv a)

private theorem abs_listQSum_le_sum_abs_local {A : Type}
    (value : A → Q') : ∀ items : List A,
      Q'.abs (listQSum value items) ≤
        listQSum (fun item => Q'.abs (value item)) items
  | [] => Q'.le_refl' 0
  | head :: tail => by
      change Q'.abs (value head + listQSum value tail) ≤ _
      refine Q'.le_trans' _ _ _
        (Q'.abs_add_le' (value head) (listQSum value tail)) ?_
      exact Q'.add_le_add
        (Q'.le_refl' (Q'.abs (value head)))
        (abs_listQSum_le_sum_abs_local value tail)

private theorem listQSum_mono_local {A : Type}
    (lower upper : A → Q') : ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, h => by
      exact Q'.le_trans' _ _ _
        (Q'.add_le_add
          (h head List.mem_cons_self)
          (listQSum_mono_local lower upper tail
            (fun item hitem => h item (List.mem_cons_of_mem head hitem))))
        (Q'.le_refl' _)

private theorem fineUnitCouplingPhysicalTerm_nonnegative_local
    (S : SlabScalePair) (source : EdgeLabelling) :
    (0 : Q') ≤ fineUnitCouplingPhysicalTerm S source := by
  unfold fineUnitCouplingPhysicalTerm
  exact slabParametricKPhysicalTerm_nonnegative
    (by decide : (0 : Q') ≤ 1) S.fine.cutoff S.fine.extent source

private theorem finePhysicalTerm_nonnegative_local
    (S : SlabScalePair) (source : EdgeLabelling) :
    (0 : Q') ≤ S.fine.physicalTerm source := by
  unfold SlabPhysicalData.physicalTerm
  exact slabParametricKPhysicalTerm_nonnegative
    S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent source

private theorem fineCouplingPhysicalMarginTerm_nonnegative_local
    (S : SlabScalePair) (source : EdgeLabelling) :
    (0 : Q') ≤ fineCouplingPhysicalMarginTerm S source := by
  unfold fineCouplingPhysicalMarginTerm
  exact Q'.mul_nonneg _ _
    (geomSum_nonneg S.fine.coupling_nonnegative
      (slabPhysicalCasimirExponent S.fine.extent source))
    (fineUnitCouplingPhysicalTerm_nonnegative_local S source)

private theorem finePhysicalPartition_nonnegative_local
    (S : SlabScalePair) :
    (0 : Q') ≤ S.fine.physicalPartition := by
  unfold SlabPhysicalData.physicalPartition
  exact Q'.le_of_lt
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)

private theorem fineUnitCouplingPhysicalPartition_nonnegative_local
    (S : SlabScalePair) :
    (0 : Q') ≤ fineUnitCouplingPhysicalPartition S := by
  unfold fineUnitCouplingPhysicalPartition
  apply listQSum_nonnegative_on
  intro source _
  exact fineUnitCouplingPhysicalTerm_nonnegative_local S source

private theorem fineCouplingPhysicalPartitionMarginSum_nonnegative_local
    (S : SlabScalePair) :
    (0 : Q') ≤ fineCouplingPhysicalPartitionMarginSum S := by
  unfold fineCouplingPhysicalPartitionMarginSum
  apply listQSum_nonnegative_on
  intro source _
  exact fineCouplingPhysicalMarginTerm_nonnegative_local S source

private theorem fineCouplingPhysicalPartitionSquareMargin_nonnegative_local
    (S : SlabScalePair) :
    (0 : Q') ≤ fineCouplingPhysicalPartitionSquareMargin S := by
  unfold fineCouplingPhysicalPartitionSquareMargin
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (fineUnitCouplingPhysicalPartition_nonnegative_local S)
      (fineCouplingPhysicalPartitionMarginSum_nonnegative_local S))
    (Q'.mul_nonneg _ _
      (finePhysicalPartition_nonnegative_local S)
      (fineCouplingPhysicalPartitionMarginSum_nonnegative_local S))

private theorem sourcePairMarginRawMass_nonnegative_local
    (S : SlabScalePair) (pair : PhysicalLabellingPair) :
    (0 : Q') ≤ fineCouplingPhysicalSourcePairMarginRawMass S pair := by
  unfold fineCouplingPhysicalSourcePairMarginRawMass
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _
      (fineUnitCouplingPhysicalTerm_nonnegative_local S pair.1)
      (fineCouplingPhysicalMarginTerm_nonnegative_local S pair.2))
    (Q'.mul_nonneg _ _
      (finePhysicalTerm_nonnegative_local S pair.2)
      (fineCouplingPhysicalMarginTerm_nonnegative_local S pair.1))

private theorem sourcePairActualRawMass_nonnegative_local
    (S : SlabScalePair) (pair : PhysicalLabellingPair) :
    (0 : Q') ≤ fineCouplingPhysicalSourcePairActualRawMass S pair := by
  unfold fineCouplingPhysicalSourcePairActualRawMass
  exact Q'.mul_nonneg _ _
    (finePhysicalTerm_nonnegative_local S pair.1)
    (finePhysicalTerm_nonnegative_local S pair.2)

private theorem abs_sub_le_add_nonnegative_local
    {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    Q'.abs (a - b) ≤ a + b := by
  change Q'.abs (a + (-b)) ≤ a + b
  refine Q'.le_trans' _ _ _
    (Q'.abs_add_le' a (-b)) ?_
  refine Q'.add_le_add ?_ ?_
  · exact Q'.le_of_eqv
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg ha)
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_neg b)
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hb))

private theorem sourcePairDebt_abs_le_mass_sum_local
    (S : SlabScalePair) (pair : PhysicalLabellingPair) :
    Q'.abs (fineCouplingPhysicalSourcePairCenteredMarginRawDebt S pair) ≤
      fineCouplingPhysicalSourcePairMarginRawMass S pair *
          (S.fine.physicalPartition * S.fine.physicalPartition) +
        fineCouplingPhysicalSourcePairActualRawMass S pair *
          fineCouplingPhysicalPartitionSquareMargin S := by
  have hmargin := sourcePairMarginRawMass_nonnegative_local S pair
  have hactual := sourcePairActualRawMass_nonnegative_local S pair
  have hpartition := finePhysicalPartition_nonnegative_local S
  have hsquare : (0 : Q') ≤
      S.fine.physicalPartition * S.fine.physicalPartition :=
    Q'.mul_nonneg _ _ hpartition hpartition
  have hmarginSquare := fineCouplingPhysicalPartitionSquareMargin_nonnegative_local S
  have hleft : (0 : Q') ≤
      fineCouplingPhysicalSourcePairMarginRawMass S pair *
        (S.fine.physicalPartition * S.fine.physicalPartition) :=
    Q'.mul_nonneg _ _ hmargin hsquare
  have hright : (0 : Q') ≤
      fineCouplingPhysicalSourcePairActualRawMass S pair *
        fineCouplingPhysicalPartitionSquareMargin S :=
    Q'.mul_nonneg _ _ hactual hmarginSquare
  exact abs_sub_le_add_nonnegative_local hleft hright

private theorem sourcePairDebtCross_abs_le_sourcePairDebtL1_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    Q'.abs
        (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
          K root target) ≤
      listQSum
        (fun sourcePair =>
          Q'.abs (fineCouplingPhysicalSourcePairCenteredMarginRawDebt
            S sourcePair))
        (pushedPhysicalSourcePairs S) := by
  let sources := pushedPhysicalSourcePairs S
  let debt := fineCouplingPhysicalSourcePairCenteredMarginRawDebt S
  let contrast := fun sourcePair =>
    fineCouplingTwoReplicaFourCellOutputContrast K root target sourcePair
  have htriangle := abs_listQSum_le_sum_abs_local
    (fun sourcePair => debt sourcePair * contrast sourcePair) sources
  have hterm : ∀ sourcePair, sourcePair ∈ sources →
      Q'.abs (debt sourcePair * contrast sourcePair) ≤
        Q'.abs (debt sourcePair) := by
    intro sourcePair hsource
    have hcontrast := fineCouplingTwoReplicaFourCellOutputContrast_abs_le_one
      K root target sourcePair hsource
    have hmul := YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
      (debt sourcePair) (contrast sourcePair)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_trans' _ _ _
        (Q'.mul_le_mul_of_nonneg_left
          (Q'.abs (contrast sourcePair)) 1
          (Q'.abs (debt sourcePair)) hcontrast
          (Q'.abs_nonneg (debt sourcePair)))
        (Q'.le_of_eqv (Q'.mul_one_eqv (Q'.abs (debt sourcePair)))))
  change Q'.abs
      (listQSum
        (fun sourcePair => debt sourcePair * contrast sourcePair) sources) ≤ _
  refine Q'.le_trans' _ _ _ htriangle ?_
  exact listQSum_mono_local
    (fun sourcePair => Q'.abs (debt sourcePair * contrast sourcePair))
    (fun sourcePair => Q'.abs (debt sourcePair)) sources hterm

/-! ## The finite source-pair L¹ envelope -/

/-- The same completed source-pair object has a direct finite L¹ envelope.

The contrast is the literal four-cell output contrast from the product kernel;
the right-hand side is an explicit finite sum of absolute centered source
debts, not an existential or an opaque constant. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_sourcePairDebtL1
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    Q'.abs
        (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
          K root target) ≤
      listQSum
        (fun sourcePair =>
          Q'.abs (fineCouplingPhysicalSourcePairCenteredMarginRawDebt
            S sourcePair))
        (pushedPhysicalSourcePairs S) := by
  exact sourcePairDebtCross_abs_le_sourcePairDebtL1_local K root target

private theorem sourcePairDebtL1_le_partition_two_term_local
    (S : SlabScalePair) :
    listQSum
        (fun sourcePair =>
          Q'.abs (fineCouplingPhysicalSourcePairCenteredMarginRawDebt
            S sourcePair))
        (pushedPhysicalSourcePairs S) ≤
      fineCouplingPhysicalPartitionSquareMargin S *
          (S.fine.physicalPartition * S.fine.physicalPartition) +
        (S.fine.physicalPartition * S.fine.physicalPartition) *
          fineCouplingPhysicalPartitionSquareMargin S := by
  let sources := pushedPhysicalSourcePairs S
  let debt := fineCouplingPhysicalSourcePairCenteredMarginRawDebt S
  let marginMass := fineCouplingPhysicalSourcePairMarginRawMass S
  let actualMass := fineCouplingPhysicalSourcePairActualRawMass S
  let actualSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  have hpointwise : ∀ sourcePair, sourcePair ∈ sources →
      Q'.abs (debt sourcePair) ≤
        marginMass sourcePair * actualSquare +
          actualMass sourcePair * squareMargin := by
    intro sourcePair _
    simpa only [debt, marginMass, actualMass, actualSquare, squareMargin]
      using sourcePairDebt_abs_le_mass_sum_local S sourcePair
  have hsum := listQSum_mono_local
    (fun sourcePair => Q'.abs (debt sourcePair))
    (fun sourcePair =>
      marginMass sourcePair * actualSquare +
        actualMass sourcePair * squareMargin)
    sources hpointwise
  have hcollapse :
      listQSum
          (fun sourcePair =>
            marginMass sourcePair * actualSquare +
              actualMass sourcePair * squareMargin) sources ≈
        squareMargin * actualSquare + actualSquare * squareMargin := by
    refine Q'.eqv_trans _
      (listQSum (fun sourcePair => marginMass sourcePair * actualSquare) sources +
        listQSum (fun sourcePair => actualMass sourcePair * squareMargin) sources) _
      (listQSum_add _ _ _) ?_
    refine Q'.eqv_trans _
      (listQSum marginMass sources * actualSquare +
        listQSum actualMass sources * squareMargin) _ ?_ ?_
    · exact Q'.add_eqv_congr'
        (listQSum_mul_right marginMass actualSquare sources)
        (listQSum_mul_right actualMass squareMargin sources)
    · exact Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_right _ _ actualSquare
          (fineCouplingPhysicalSourcePairMarginRawMass_total S))
        (Q'.mul_eqv_congr_right _ _ squareMargin
          (fineCouplingPhysicalSourcePairActualRawMass_total S))
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hcollapse)

/-- The explicit finite two-term partition envelope for the centered
source-pair average.  Its displayed margin factor is not claimed uniform in
cutoff or volume. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_partition_two_term
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    Q'.abs
        (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
          K root target) ≤
      fineCouplingPhysicalPartitionSquareMargin S *
          (S.fine.physicalPartition * S.fine.physicalPartition) +
        (S.fine.physicalPartition * S.fine.physicalPartition) *
          fineCouplingPhysicalPartitionSquareMargin S := by
  exact Q'.le_trans' _ _ _
    (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_sourcePairDebtL1
      K root target)
    (sourcePairDebtL1_le_partition_two_term_local S)

/-- The same finite envelope after the exact pullback into the normalized
centered margin numerator. -/
theorem fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    Q'.abs
        (fineUnitCouplingCenteredNormalizedMarginNumerator
          K M.coarseRoot M.coarseTarget) ≤
      fineCouplingPhysicalPartitionSquareMargin S *
          (S.fine.physicalPartition * S.fine.physicalPartition) +
        (S.fine.physicalPartition * S.fine.physicalPartition) *
          fineCouplingPhysicalPartitionSquareMargin S := by
  have heq := fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_sourcePairAverage
    K M.coarseRoot M.coarseTarget
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (YMGap.Constructive.Q'.abs_eqv_congr heq)) ?_
  exact fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_partition_two_term
    K M.coarseRoot M.coarseTarget

/-! ## The finite normalized calibration ceiling -/

/-- The explicit finite ceiling obtained by dividing the two-term source-debt
envelope by the positive coupling-one partition square.  It is intentionally
parameter-dependent: this definition does not assert any cutoff- or
volume-uniform bound. -/
def finiteMarginEnvelopeCeiling (S : SlabScalePair) : Q' :=
  Q'.divPos
    (Q'.ofNat 2 * fineCouplingPhysicalPartitionSquareMargin S)
    (fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S)
    (Q'.mul_pos
      (fineUnitCouplingPhysicalPartition_pos S)
      (fineUnitCouplingPhysicalPartition_pos S))

private theorem finiteMarginEnvelopeCeiling_denominator_pos
    (S : SlabScalePair) :
    (0 : Q') <
      fineUnitCouplingPhysicalPartition S *
        fineUnitCouplingPhysicalPartition S :=
  Q'.mul_pos
    (fineUnitCouplingPhysicalPartition_pos S)
    (fineUnitCouplingPhysicalPartition_pos S)

private theorem finiteMarginEnvelopeCeiling_nonnegative
    (S : SlabScalePair) :
    (0 : Q') ≤ finiteMarginEnvelopeCeiling S := by
  unfold finiteMarginEnvelopeCeiling Q'.divPos
  apply Q'.mul_nonneg
  · exact Q'.mul_nonneg _ _
      (by decide : (0 : Q') ≤ Q'.ofNat 2)
      (fineCouplingPhysicalPartitionSquareMargin_nonnegative_local S)
  · exact Q'.le_of_lt
      (Q'.recipPos_pos _ (finiteMarginEnvelopeCeiling_denominator_pos S))

private theorem finiteMarginEnvelopeCeiling_mul_unitSquare_eqv
    (S : SlabScalePair) :
    finiteMarginEnvelopeCeiling S *
        (fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S) ≈
      Q'.ofNat 2 * fineCouplingPhysicalPartitionSquareMargin S := by
  unfold finiteMarginEnvelopeCeiling
  exact Q'.divPos_mul_eqv _ _ (finiteMarginEnvelopeCeiling_denominator_pos S)

private theorem finiteMarginEnvelopeCeiling_mul_denominator_eqv
    (S : SlabScalePair) :
    finiteMarginEnvelopeCeiling S *
        fineUnitCouplingCenteredNormalizedChangeDenominator S ≈
      (Q'.ofNat 2 * fineCouplingPhysicalPartitionSquareMargin S) *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  have hunit : finiteMarginEnvelopeCeiling S * unitSquare ≈
      Q'.ofNat 2 * fineCouplingPhysicalPartitionSquareMargin S := by
    simpa only [unitSquare] using
      finiteMarginEnvelopeCeiling_mul_unitSquare_eqv S
  refine Q'.eqv_trans _
    ((finiteMarginEnvelopeCeiling S * unitSquare) * actualSquare) _ ?_ ?_
  · exact Q'.eqv_symm
      (Q'.mul_assoc_eqv (finiteMarginEnvelopeCeiling S) unitSquare actualSquare)
  · exact Q'.mul_eqv_congr_right _ _ _ hunit

private theorem partition_two_term_eqv_regrouped
    (S : SlabScalePair) :
    fineCouplingPhysicalPartitionSquareMargin S *
          (S.fine.physicalPartition * S.fine.physicalPartition) +
        (S.fine.physicalPartition * S.fine.physicalPartition) *
          fineCouplingPhysicalPartitionSquareMargin S ≈
      (Q'.ofNat 2 * fineCouplingPhysicalPartitionSquareMargin S) *
        (S.fine.physicalPartition * S.fine.physicalPartition) := by
  let margin := fineCouplingPhysicalPartitionSquareMargin S
  let square := S.fine.physicalPartition * S.fine.physicalPartition
  have hcomm : square * margin ≈ margin * square :=
    Q'.mul_comm_eqv square margin
  have hswap : margin * square + square * margin ≈
      margin * square + margin * square :=
    Q'.add_eqv_congr_left (margin * square) (square * margin)
      (margin * square) hcomm
  refine Q'.eqv_trans _ (margin * square + margin * square) _ hswap ?_
  refine Q'.eqv_trans _ (Q'.ofNat 2 * (margin * square)) _
    (Q'.eqv_symm (two_mul_eqv_local (margin * square))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) margin square)

/-- The preceding finite L¹ envelope supplies an actual inhabitant of the
normalized margin-calibration proposition.  The ceiling is explicit and
finite, but its dependence on `S` remains visible rather than being promoted
to a uniform estimate. -/
theorem fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_partition_two_term
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) :
    FineUnitCouplingCenteredNormalizedMarginRawCalibration
      K M (finiteMarginEnvelopeCeiling S) := by
  unfold FineUnitCouplingCenteredNormalizedMarginRawCalibration
  have hnum := fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
    K M
  have hregroup := partition_two_term_eqv_regrouped S
  have hbudget := finiteMarginEnvelopeCeiling_mul_denominator_eqv S
  refine Q'.le_trans' _ _ _ hnum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) ?_
  exact Q'.le_of_eqv (Q'.eqv_symm hbudget)

/-- Compile the explicit finite margin ceiling through the matched-AF bridge.
This is still a finite, slab-dependent raw calibration; uniformity and the
independent normalized-blocking residual remain separate obligations. -/
theorem fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_partition_two_term
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    FineUnitCouplingCenteredNormalizedChangeRawCalibration
      K M g (Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) := by
  exact fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin
    K M family law g (finiteMarginEnvelopeCeiling S) hg hgle hcoupling
    (finiteMarginEnvelopeCeiling_nonnegative S)
    (fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_partition_two_term
      K M)

/-- Insert the explicit finite source-debt ceiling into the complete balanced
blocking compiler.  The only remaining producer premise here is the balanced
raw scale-defect calibration; the source-margin side is now discharged by the
same completed centered object. -/
theorem centeredCylinderRemainder_abs_le_of_balanced_and_partition_two_term
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g balancedCeiling : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hbalancedCeiling : (0 : Q') ≤ balancedCeiling)
    (hbalanced :
      FineUnitCouplingBalancedRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g balancedCeiling) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (balancedCeiling +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  have hmargin :
      FineUnitCouplingCenteredNormalizedMarginRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M (finiteMarginEnvelopeCeiling S) :=
    fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_partition_two_term
      (physicalKernel S hfineCutoff hcoarseCoupling) M
  exact centeredCylinderRemainder_abs_le_of_balanced_and_margin
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g balancedCeiling (finiteMarginEnvelopeCeiling S)
    hg hgle hcoupling hbalancedCeiling
    (finiteMarginEnvelopeCeiling_nonnegative S) hbalanced hmargin

#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_sourcePairDebtL1
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_partition_two_term
#print axioms fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
#print axioms finiteMarginEnvelopeCeiling_mul_denominator_eqv
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_partition_two_term
#print axioms fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_partition_two_term
#print axioms centeredCylinderRemainder_abs_le_of_balanced_and_partition_two_term

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtL1
