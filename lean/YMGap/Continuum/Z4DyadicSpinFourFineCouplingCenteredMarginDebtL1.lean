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
import YMGap.Continuum.LargeFieldSuppression

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
open YMGap.Continuum.RGTransport
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.BondMovingMoment
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
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

/-! ## A fixed-coupling reciprocal envelope -/

private theorem fineCouplingPhysicalPartitionMarginSum_le_reciprocal_local
    (S : SlabScalePair)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    fineCouplingPhysicalPartitionMarginSum S ≤
      Q'.divPos 1 (1 - S.fine.coupling) hgap *
        fineUnitCouplingPhysicalPartition S := by
  let reciprocal := Q'.divPos 1 (1 - S.fine.coupling) hgap
  have hpointwise : ∀ source, source ∈ S.fine.physicalLabellings →
      fineCouplingPhysicalMarginTerm S source ≤
        reciprocal * fineUnitCouplingPhysicalTerm S source := by
    intro source hsource
    unfold fineCouplingPhysicalMarginTerm
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (LargeFieldSuppression.geomSum_le_recip
        S.fine.coupling_nonnegative hgap
        (slabPhysicalCasimirExponent S.fine.extent source))
      (fineUnitCouplingPhysicalTerm_nonnegative_local S source)
  unfold fineCouplingPhysicalPartitionMarginSum
  have hsum := listQSum_mono_local
    (fineCouplingPhysicalMarginTerm S)
    (fun source => reciprocal * fineUnitCouplingPhysicalTerm S source)
    S.fine.physicalLabellings hpointwise
  refine Q'.le_trans' _ _ _ hsum ?_
  exact Q'.le_of_eqv (by
    simpa only [fineUnitCouplingPhysicalPartition] using
      (listQSum_mul_left reciprocal (fineUnitCouplingPhysicalTerm S)
        S.fine.physicalLabellings))

theorem fineCouplingPhysicalPartitionMarginSum_le_reciprocal
    (S : SlabScalePair)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    fineCouplingPhysicalPartitionMarginSum S ≤
      Q'.divPos 1 (1 - S.fine.coupling) hgap *
        fineUnitCouplingPhysicalPartition S := by
  exact fineCouplingPhysicalPartitionMarginSum_le_reciprocal_local S hgap

/-- The reciprocal ceiling is antitone in the strict coupling parameter. -/
theorem fineCouplingReciprocal_le_of_coupling_le
    {w w₀ : Q'}
    (hw₀gap : (0 : Q') < 1 - w₀)
    (hw_le : w ≤ w₀)
    (hwgap : (0 : Q') < 1 - w) :
    Q'.divPos 1 (1 - w) hwgap ≤ Q'.divPos 1 (1 - w₀) hw₀gap := by
  have hden : (1 : Q') - w₀ ≤ 1 - w := by
    exact Q'.add_le_add_left 1 (-w₀) (-w) (Q'.neg_le_neg hw_le)
  have hrecip0 : (0 : Q') ≤ Q'.divPos 1 (1 - w₀) hw₀gap :=
    Q'.le_of_lt (Q'.divPos_pos 1 (1 - w₀) hw₀gap (by decide))
  have hproduct :
      Q'.divPos 1 (1 - w₀) hw₀gap * (1 - w₀) ≤
        Q'.divPos 1 (1 - w₀) hw₀gap * (1 - w) :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hden hrecip0
  have hone :
      (1 : Q') ≤ Q'.divPos 1 (1 - w₀) hw₀gap * (1 - w₀) :=
    Q'.ge_of_eqv (Q'.divPos_mul_eqv 1 (1 - w₀) hw₀gap)
  exact Q'.divPos_le_of_le_mul 1 (1 - w) hwgap
    (Q'.le_trans' _ _ _ hone hproduct)

/-- A reciprocal envelope uniform over all slabs whose fine coupling lies below
the displayed strict corridor endpoint `w₀ < 1`. -/
theorem fineCouplingPhysicalPartitionMarginSum_le_uniform_reciprocal
    (S : SlabScalePair) (w₀ : Q')
    (hcorridor : S.fine.coupling ≤ w₀)
    (hgap₀ : (0 : Q') < 1 - w₀) :
    fineCouplingPhysicalPartitionMarginSum S ≤
      Q'.divPos 1 (1 - w₀) hgap₀ *
        fineUnitCouplingPhysicalPartition S := by
  have hden : (1 : Q') - w₀ ≤ 1 - S.fine.coupling := by
    exact Q'.add_le_add_left 1 (-w₀) (-S.fine.coupling)
      (Q'.neg_le_neg hcorridor)
  have hgap : (0 : Q') < 1 - S.fine.coupling :=
    HeatKernelRGStep.lt_of_lt_of_le hgap₀ hden
  have hbase := fineCouplingPhysicalPartitionMarginSum_le_reciprocal S hgap
  have hratio := fineCouplingReciprocal_le_of_coupling_le
    hgap₀ hcorridor hgap
  have hunit : (0 : Q') ≤ fineUnitCouplingPhysicalPartition S :=
    fineUnitCouplingPhysicalPartition_nonnegative_local S
  have hfactor :
      Q'.divPos 1 (1 - S.fine.coupling) hgap *
          fineUnitCouplingPhysicalPartition S ≤
        Q'.divPos 1 (1 - w₀) hgap₀ *
          fineUnitCouplingPhysicalPartition S :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hratio hunit
  exact Q'.le_trans' _ _ _ hbase hfactor

private theorem duplicated_nested_product_eqv_local (reciprocal unit : Q') :
    unit * (reciprocal * unit) + unit * (reciprocal * unit) ≈
      (Q'.ofNat 2 * reciprocal) * (unit * unit) := by
  refine Q'.eqv_trans _ (Q'.ofNat 2 * (unit * (reciprocal * unit))) _
    (Q'.eqv_symm (two_mul_eqv_local (unit * (reciprocal * unit)))) ?_
  refine Q'.eqv_trans _ ((Q'.ofNat 2 * unit) * (reciprocal * unit)) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) unit
      (reciprocal * unit))) ?_
  refine Q'.eqv_trans _ ((unit * Q'.ofNat 2) * (reciprocal * unit)) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv (Q'.ofNat 2) unit)) ?_
  refine Q'.eqv_trans _ (unit * (Q'.ofNat 2 * (reciprocal * unit))) _
    (Q'.mul_assoc_eqv unit (Q'.ofNat 2) (reciprocal * unit)) ?_
  refine Q'.eqv_trans _ (unit * ((Q'.ofNat 2 * reciprocal) * unit)) _
    (Q'.mul_eqv_congr_left unit _ _
      (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2) reciprocal unit))) ?_
  refine Q'.eqv_trans _ ((unit * (Q'.ofNat 2 * reciprocal)) * unit) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv unit
      (Q'.ofNat 2 * reciprocal) unit)) ?_
  refine Q'.eqv_trans _ (((Q'.ofNat 2 * reciprocal) * unit) * unit) _
    (Q'.mul_eqv_congr_right _ _ _
      (Q'.mul_comm_eqv unit (Q'.ofNat 2 * reciprocal))) ?_
  exact Q'.mul_assoc_eqv (Q'.ofNat 2 * reciprocal) unit unit

theorem fineCouplingPhysicalPartitionSquareMargin_le_reciprocal
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    fineCouplingPhysicalPartitionSquareMargin S ≤
      (Q'.ofNat 2 * Q'.divPos 1 (1 - S.fine.coupling) hgap) *
        (fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S) := by
  let reciprocal := Q'.divPos 1 (1 - S.fine.coupling) hgap
  let unitPartition := fineUnitCouplingPhysicalPartition S
  let actualPartition := S.fine.physicalPartition
  let marginSum := fineCouplingPhysicalPartitionMarginSum S
  have hunit : (0 : Q') ≤ unitPartition := by
    simpa only [unitPartition] using
      (fineUnitCouplingPhysicalPartition_nonnegative_local S)
  have hactual : (0 : Q') ≤ actualPartition := by
    simpa only [actualPartition] using finePhysicalPartition_nonnegative_local S
  have hmargin : (0 : Q') ≤ marginSum := by
    simpa only [marginSum] using
      (fineCouplingPhysicalPartitionMarginSum_nonnegative_local S)
  have hpartition : actualPartition ≤ unitPartition := by
    simpa only [actualPartition, unitPartition] using
      (finePhysicalPartition_le_unitCoupling S hfineCoupling_le_one)
  have hmarginBound : marginSum ≤ reciprocal * unitPartition := by
    simpa only [marginSum, reciprocal] using
      (fineCouplingPhysicalPartitionMarginSum_le_reciprocal S hgap)
  have hfirst : unitPartition * marginSum ≤
      unitPartition * (reciprocal * unitPartition) :=
    Q'.mul_le_mul_of_nonneg_left _ _ unitPartition hmarginBound hunit
  have hactualMargin : actualPartition * marginSum ≤
      unitPartition * marginSum :=
    Q'.mul_le_mul_of_nonneg_right _ _ marginSum hpartition hmargin
  have hsecond : actualPartition * marginSum ≤
      unitPartition * (reciprocal * unitPartition) :=
    Q'.le_trans' _ _ _ hactualMargin hfirst
  have hadd : unitPartition * marginSum + actualPartition * marginSum ≤
      unitPartition * (reciprocal * unitPartition) +
        unitPartition * (reciprocal * unitPartition) :=
    Q'.add_le_add hfirst hsecond
  unfold fineCouplingPhysicalPartitionSquareMargin
  refine Q'.le_trans' _ _ _ hadd ?_
  exact Q'.le_of_eqv
    (duplicated_nested_product_eqv_local reciprocal unitPartition)

/-- The square-margin envelope is uniform over the same displayed strict
coupling corridor. -/
theorem fineCouplingPhysicalPartitionSquareMargin_le_uniform_reciprocal
    (S : SlabScalePair) (w₀ : Q')
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hcorridor : S.fine.coupling ≤ w₀)
    (hgap₀ : (0 : Q') < 1 - w₀) :
    fineCouplingPhysicalPartitionSquareMargin S ≤
      (Q'.ofNat 2 * Q'.divPos 1 (1 - w₀) hgap₀) *
        (fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S) := by
  have hden : (1 : Q') - w₀ ≤ 1 - S.fine.coupling := by
    exact Q'.add_le_add_left 1 (-w₀) (-S.fine.coupling)
      (Q'.neg_le_neg hcorridor)
  have hgap : (0 : Q') < 1 - S.fine.coupling :=
    HeatKernelRGStep.lt_of_lt_of_le hgap₀ hden
  have hbase := fineCouplingPhysicalPartitionSquareMargin_le_reciprocal
    S hfineCoupling_le_one hgap
  have hratio := fineCouplingReciprocal_le_of_coupling_le
    hgap₀ hcorridor hgap
  have hcoef :
      Q'.ofNat 2 * Q'.divPos 1 (1 - S.fine.coupling) hgap ≤
        Q'.ofNat 2 * Q'.divPos 1 (1 - w₀) hgap₀ :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hratio
      (Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2))
  have hunitSquare : (0 : Q') ≤
      fineUnitCouplingPhysicalPartition S *
        fineUnitCouplingPhysicalPartition S :=
    Q'.mul_nonneg _ _
      (fineUnitCouplingPhysicalPartition_nonnegative_local S)
      (fineUnitCouplingPhysicalPartition_nonnegative_local S)
  have hscale :
      (Q'.ofNat 2 * Q'.divPos 1 (1 - S.fine.coupling) hgap) *
          (fineUnitCouplingPhysicalPartition S *
            fineUnitCouplingPhysicalPartition S) ≤
        (Q'.ofNat 2 * Q'.divPos 1 (1 - w₀) hgap₀) *
          (fineUnitCouplingPhysicalPartition S *
            fineUnitCouplingPhysicalPartition S) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hcoef hunitSquare
  exact Q'.le_trans' _ _ _ hbase hscale

/-! ## The reciprocal-margin normalized calibration -/

/-- A fixed-coupling ceiling for the normalized centered numerator.  It is
semantically `4 / (1 - coupling)`, but the nested `ofNat 2` form keeps the
constructive regrouping visible and avoids an opaque arithmetic normalization. -/
def fineCouplingReciprocalMarginCeiling
    (S : SlabScalePair)
    (hgap : (0 : Q') < 1 - S.fine.coupling) : Q' :=
  Q'.ofNat 2 *
    (Q'.ofNat 2 * Q'.divPos 1 (1 - S.fine.coupling) hgap)

private theorem fineCouplingReciprocalMarginCeiling_nonnegative
    (S : SlabScalePair)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    (0 : Q') ≤ fineCouplingReciprocalMarginCeiling S hgap := by
  unfold fineCouplingReciprocalMarginCeiling
  apply Q'.mul_nonneg
  · exact Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2)
  · apply Q'.mul_nonneg
    · exact Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2)
    · unfold Q'.divPos
      exact Q'.mul_nonneg
        _ _
        (by decide : (0 : Q') ≤ (1 : Q'))
        (Q'.le_of_lt
          (Q'.recipPos_pos (1 - S.fine.coupling) hgap))

private theorem reciprocal_scaled_budget_eqv_local
    (reciprocal unitSquare actualSquare : Q') :
    (Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) * unitSquare)) *
        actualSquare ≈
      (Q'.ofNat 2 * (Q'.ofNat 2 * reciprocal)) *
        (unitSquare * actualSquare) := by
  refine Q'.eqv_trans _
    (Q'.ofNat 2 * (((Q'.ofNat 2 * reciprocal) * unitSquare) *
      actualSquare)) _ ?_ ?_
  · exact Q'.mul_assoc_eqv (Q'.ofNat 2)
        ((Q'.ofNat 2 * reciprocal) * unitSquare) actualSquare
  refine Q'.eqv_trans _
    (Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) *
      (unitSquare * actualSquare))) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left (Q'.ofNat 2) _ _
      (Q'.mul_assoc_eqv (Q'.ofNat 2 * reciprocal) unitSquare actualSquare)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat 2)
      (Q'.ofNat 2 * reciprocal) (unitSquare * actualSquare))

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

/-- A fixed-coupling reciprocal envelope for the normalized centered
numerator.  The proof is finite and explicit; its ceiling is allowed to
depend on the strict gap `1 - coupling`. -/
theorem fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_reciprocal
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    FineUnitCouplingCenteredNormalizedMarginRawCalibration
      K M (fineCouplingReciprocalMarginCeiling S hgap) := by
  let reciprocal := Q'.divPos 1 (1 - S.fine.coupling) hgap
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let actualSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  have hmarginSquare : squareMargin ≤
      (Q'.ofNat 2 * reciprocal) * unitSquare := by
    simpa only [squareMargin, reciprocal, unitSquare] using
      (fineCouplingPhysicalPartitionSquareMargin_le_reciprocal
        S hfineCoupling_le_one hgap)
  have hnum := fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
    K M
  have hregroup :
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
  have hmarginScaled : (Q'.ofNat 2 * squareMargin) ≤
      Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) * unitSquare) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hmarginSquare
      (Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2))
  have hactualSquare : (0 : Q') ≤ actualSquare := by
    dsimp only [actualSquare]
    exact Q'.mul_nonneg _ _
      (finePhysicalPartition_nonnegative_local S)
      (finePhysicalPartition_nonnegative_local S)
  have hscaled : (Q'.ofNat 2 * squareMargin) * actualSquare ≤
      (Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) * unitSquare)) *
        actualSquare :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmarginScaled hactualSquare
  unfold FineUnitCouplingCenteredNormalizedMarginRawCalibration
  refine Q'.le_trans' _ _ _ hnum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) ?_
  refine Q'.le_trans' _ _ _ hscaled ?_
  exact Q'.le_of_eqv
    (reciprocal_scaled_budget_eqv_local reciprocal unitSquare actualSquare)

/-- A ceiling uniform over a prescribed strict coupling corridor `w ≤ w₀ < 1`.
Its displayed value is semantically `4/(1-w₀)`. -/
def fineCouplingUniformReciprocalMarginCeiling
    (w₀ : Q') (hgap₀ : (0 : Q') < 1 - w₀) : Q' :=
  Q'.ofNat 2 *
    (Q'.ofNat 2 * Q'.divPos 1 (1 - w₀) hgap₀)

private theorem fineCouplingUniformReciprocalMarginCeiling_nonnegative
    (w₀ : Q') (hgap₀ : (0 : Q') < 1 - w₀) :
    (0 : Q') ≤ fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀ := by
  unfold fineCouplingUniformReciprocalMarginCeiling
  apply Q'.mul_nonneg
  · exact Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2)
  · apply Q'.mul_nonneg
    · exact Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2)
    · exact Q'.le_of_lt
        (Q'.divPos_pos 1 (1 - w₀) hgap₀ (by decide))

/-- Compile the fixed-coupling reciprocal margin envelope through the matched
AF bridge.  The resulting quadratic ceiling is explicit but still depends on
the strict finite coupling gap. -/
theorem fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_reciprocal
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hgap : (0 : Q') < 1 - S.fine.coupling) :
    FineUnitCouplingCenteredNormalizedChangeRawCalibration
      K M g (Q'.ofNat 2 * fineCouplingReciprocalMarginCeiling S hgap) := by
  exact fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin
    K M family law g (fineCouplingReciprocalMarginCeiling S hgap)
      hg hgle hcoupling
      (fineCouplingReciprocalMarginCeiling_nonnegative S hgap)
      (fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_reciprocal
        K M hfineCoupling_le_one hgap)

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

/-- A normalized margin calibration uniform over every supplied slab in the
strict corridor `S.fine.coupling ≤ w₀ < 1`. -/
theorem fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_uniform_reciprocal
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (w₀ : Q')
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hcorridor : S.fine.coupling ≤ w₀)
    (hgap₀ : (0 : Q') < 1 - w₀) :
    FineUnitCouplingCenteredNormalizedMarginRawCalibration
      K M (fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀) := by
  let reciprocal := Q'.divPos 1 (1 - w₀) hgap₀
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let actualSquare := S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  have hmarginSquare : squareMargin ≤
      (Q'.ofNat 2 * reciprocal) * unitSquare := by
    simpa only [squareMargin, reciprocal, unitSquare] using
      (fineCouplingPhysicalPartitionSquareMargin_le_uniform_reciprocal
        S w₀ hfineCoupling_le_one hcorridor hgap₀)
  have hnum := fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
    K M
  have hregroup := partition_two_term_eqv_regrouped S
  have hmarginScaled : (Q'.ofNat 2 * squareMargin) ≤
      Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) * unitSquare) :=
    Q'.mul_le_mul_of_nonneg_left _ _ (Q'.ofNat 2) hmarginSquare
      (Q'.le_of_lt (by decide : (0 : Q') < Q'.ofNat 2))
  have hactualSquare : (0 : Q') ≤ actualSquare := by
    dsimp only [actualSquare]
    exact Q'.mul_nonneg _ _
      (finePhysicalPartition_nonnegative_local S)
      (finePhysicalPartition_nonnegative_local S)
  have hscaled : (Q'.ofNat 2 * squareMargin) * actualSquare ≤
      (Q'.ofNat 2 * ((Q'.ofNat 2 * reciprocal) * unitSquare)) *
        actualSquare :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmarginScaled hactualSquare
  unfold FineUnitCouplingCenteredNormalizedMarginRawCalibration
  refine Q'.le_trans' _ _ _ hnum ?_
  refine Q'.le_trans' _ _ _ (Q'.le_of_eqv hregroup) ?_
  refine Q'.le_trans' _ _ _ hscaled ?_
  exact Q'.le_of_eqv
    (reciprocal_scaled_budget_eqv_local reciprocal unitSquare actualSquare)

/-- Compile the corridor-uniform margin ceiling through the matched-AF bridge. -/
theorem fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_uniform_reciprocal
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (w₀ : Q') (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (hcorridor : S.fine.coupling ≤ w₀)
    (hgap₀ : (0 : Q') < 1 - w₀) :
    FineUnitCouplingCenteredNormalizedChangeRawCalibration
      K M g
        (Q'.ofNat 2 *
          fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀) := by
  exact fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_margin
    K M family law g
      (fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀)
      hg hgle hcoupling
      (fineCouplingUniformReciprocalMarginCeiling_nonnegative w₀ hgap₀)
      (fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_uniform_reciprocal
        K M w₀ hfineCoupling_le_one hcorridor hgap₀)

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

/-- The finite balanced carrier ceiling now supplies the balanced premise to
the complete centered-cylinder compiler.  The resulting constant remains
explicitly slab- and coupling-dependent through the carrier quotient. -/
theorem centeredCylinderRemainder_abs_le_of_finite_balanced_carrier
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierCeiling S g hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  exact centeredCylinderRemainder_abs_le_of_balanced_and_partition_two_term
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g (fineUnitCouplingBalancedCarrierCeiling S g hg)
    hg hgle hcoupling
    (fineUnitCouplingBalancedCarrierCeiling_nonnegative S g hg)
    (fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_finite_carrier
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget g hg)

/-- The relative-loss carrier compiler supplies the balanced premise to the
complete centered-cylinder estimate.  The relative loss, floor, and
floor-to-actual comparison remain explicit hypotheses; this theorem does not
promote them to cutoff-, volume-, or beta-uniform data. -/
theorem centeredCylinderRemainder_abs_le_of_relative_balanced_carrier
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (margin floor : Q')
    (hmargin : (0 : Q') ≤ margin)
    (hfloor : (0 : Q') < floor)
    (hfloor_le : floor ≤ S.fine.physicalPartition)
    (hloss : fineUnitCouplingPhysicalPartition S -
        S.fine.physicalPartition ≤ margin * floor) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierRatioCeiling
          g ((1 + margin) * (1 + margin)) hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  have hscale : (0 : Q') < 1 + margin :=
    Q'.pos_add_nonneg (by decide) hmargin
  have hratio : (0 : Q') < (1 + margin) * (1 + margin) :=
    Q'.mul_pos hscale hscale
  have hcarrierBound :
      FineUnitCouplingBalancedCarrierRatioBound S
        ((1 + margin) * (1 + margin)) :=
    fineUnitCouplingBalancedCarrierRatioBound_of_relative_loss
      S margin floor hmargin hfloor hfloor_le hloss
  have hbalanced :=
    fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_carrier_ratio
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget g
        ((1 + margin) * (1 + margin)) hg hcarrierBound
  exact centeredCylinderRemainder_abs_le_of_balanced_and_partition_two_term
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g (fineUnitCouplingBalancedCarrierRatioCeiling
      g ((1 + margin) * (1 + margin)) hg)
    hg hgle hcoupling
    (fineUnitCouplingBalancedCarrierRatioCeiling_nonnegative
      g ((1 + margin) * (1 + margin)) hg hratio)
    hbalanced

/-- The existing finite Casimir perturbation estimate supplies a concrete
relative-loss instance with floor `1`.  The resulting centered-cylinder bound
is still finite and its Casimir moment remains explicit; no uniformity is
claimed. -/
theorem centeredCylinderRemainder_abs_le_of_matched_casimir_loss
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierRatioCeiling g
          ((1 + (Q'.ofNat 2 * (g * g)) *
            fineUnitCouplingPhysicalCasimirMoment S) *
            (1 + (Q'.ofNat 2 * (g * g)) *
              fineUnitCouplingPhysicalCasimirMoment S)) hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  let margin :=
    (Q'.ofNat 2 * (g * g)) * fineUnitCouplingPhysicalCasimirMoment S
  have hmargin : (0 : Q') ≤ margin := by
    unfold margin
    exact Q'.mul_nonneg _ _
      (Q'.mul_nonneg _ _ (by decide)
        (Q'.le_of_lt (Q'.mul_pos hg hg)))
      (fineUnitCouplingPhysicalCasimirMoment_nonnegative S)
  have hfloor : (0 : Q') < 1 := by decide
  have hfloor_le : (1 : Q') ≤ S.fine.physicalPartition := by
    unfold SlabPhysicalData.physicalPartition
    exact slabParametricKPhysicalPartition_one_le
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hloss₀ :=
    fineUnitCouplingPhysicalPartition_sub_actual_le_two_square_mul_moment
      S hfineCoupling_le_one family law g hg hgle hcoupling
  have hloss : fineUnitCouplingPhysicalPartition S -
      S.fine.physicalPartition ≤ margin * (1 : Q') := by
    unfold margin at *
    exact Q'.le_trans' _ _ _ hloss₀
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv _)))
  simpa only [margin] using
      (centeredCylinderRemainder_abs_le_of_relative_balanced_carrier
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
      g hg hgle hcoupling margin (1 : Q') hmargin hfloor hfloor_le hloss)

/-- A single explicit certificate for bounding the coupling-one Casimir moment
on the same fine carrier.  A uniform instance of this proposition is the
remaining analytic input needed by the preceding finite compiler. -/
def FineUnitCouplingPhysicalCasimirMomentBound
    (S : SlabScalePair) (momentCeiling : Q') : Prop :=
  fineUnitCouplingPhysicalCasimirMoment S ≤ momentCeiling

/-! ## 6. A finite, explicit inhabitant of the moment certificate -/

private theorem list_mem_le_foldr_max_local : ∀ (xs : List Nat) (n : Nat),
    n ∈ xs → n ≤ xs.foldr Nat.max 0
  | [], _, h => False.elim (List.not_mem_nil h)
  | a :: xs, n, h => by
      rcases List.mem_cons.mp h with rfl | hn
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (list_mem_le_foldr_max_local xs n hn)
          (Nat.le_max_right _ _)

private theorem foldr_max_le_local : ∀ (xs : List Nat) (bound : Nat),
    (∀ n, n ∈ xs → n ≤ bound) → xs.foldr Nat.max 0 ≤ bound
  | [], bound, _ => Nat.zero_le _
  | head :: tail, bound, h => by
      simp only [List.foldr]
      exact (Nat.max_le).2 ⟨h head List.mem_cons_self,
        foldr_max_le_local tail bound
          (fun n hn => h n (List.mem_cons_of_mem head hn))⟩

private theorem slabPhysicalCasimirExponentOn_le_face_count_mul_c4_local
    (cutoff : Nat) (physical : EdgeLabelling) :
    ∀ faces : List Nat,
      (∀ face, face ∈ faces → physical face ≤ cutoff) →
      slabPhysicalCasimirExponentOn physical faces ≤
        faces.length * c4 cutoff
  | [], _ => by
      simp only [slabPhysicalCasimirExponentOn, List.length_nil, Nat.zero_mul]
      exact Nat.zero_le _
  | face :: rest, hfaces => by
      change c4 (physical face) +
          slabPhysicalCasimirExponentOn physical rest ≤
        (face :: rest).length * c4 cutoff
      have hface : physical face ≤ cutoff := hfaces face List.mem_cons_self
      have hc4 : c4 (physical face) ≤ c4 cutoff :=
        YMGap.Continuum.BondMovingMoment.c4_mono hface
      have hrest :=
        slabPhysicalCasimirExponentOn_le_face_count_mul_c4_local
          cutoff physical rest
          (fun id hid => hfaces id (List.mem_cons_of_mem face hid))
      have hsum := Nat.add_le_add hc4 hrest
      simpa only [List.length_cons, Nat.add_mul, Nat.one_mul,
        Nat.add_comm] using hsum

/-- The largest Casimir exponent on the displayed finite physical carrier. -/
def fineUnitCouplingPhysicalCasimirExponentCeiling
    (S : SlabScalePair) : Nat :=
  (S.fine.physicalLabellings.map
    (fun source => slabPhysicalCasimirExponent S.fine.extent source)).foldr
      Nat.max 0

theorem fineUnitCouplingPhysicalCasimirExponent_le_face_count_mul_c4
    (S : SlabScalePair) {source : EdgeLabelling}
    (hsource : source ∈ S.fine.physicalLabellings) :
    slabPhysicalCasimirExponent S.fine.extent source ≤
      S.fine.faceEdges.length * c4 S.fine.cutoff := by
  unfold slabPhysicalCasimirExponent
  apply slabPhysicalCasimirExponentOn_le_face_count_mul_c4_local
  intro face hface
  exact Nat.lt_succ_iff.mp
    ((boundedEdgeLabellings_sound S.fine.cutoff S.fine.faceEdges
      source hsource).1 face hface)

theorem fineUnitCouplingPhysicalCasimirExponentCeiling_le_face_count_mul_c4
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalCasimirExponentCeiling S ≤
      S.fine.faceEdges.length * c4 S.fine.cutoff := by
  unfold fineUnitCouplingPhysicalCasimirExponentCeiling
  apply foldr_max_le_local
  intro exponent hexponent
  rcases List.mem_map.mp hexponent with ⟨source, hsource, rfl⟩
  exact fineUnitCouplingPhysicalCasimirExponent_le_face_count_mul_c4
    S hsource

/-- A finite ceiling obtained by multiplying the largest displayed exponent
by the coupling-one partition of the same carrier. -/
def fineUnitCouplingPhysicalCasimirMomentFiniteCeiling
    (S : SlabScalePair) : Q' :=
  Q'.ofNat (fineUnitCouplingPhysicalCasimirExponentCeiling S) *
    fineUnitCouplingPhysicalPartition S

theorem fineUnitCouplingPhysicalCasimirMoment_le_finite_ceiling
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalCasimirMoment S ≤
      fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S := by
  unfold fineUnitCouplingPhysicalCasimirMoment
    fineUnitCouplingPhysicalCasimirMomentFiniteCeiling
  have hmono :
      listQSum
          (fun source =>
            Q'.ofNat (slabPhysicalCasimirExponent S.fine.extent source) *
              fineUnitCouplingPhysicalTerm S source)
          S.fine.physicalLabellings ≤
        listQSum
          (fun source =>
            Q'.ofNat (fineUnitCouplingPhysicalCasimirExponentCeiling S) *
              fineUnitCouplingPhysicalTerm S source)
          S.fine.physicalLabellings := by
    apply listQSum_mono_local
    intro source hsource
    have hmax :
        slabPhysicalCasimirExponent S.fine.extent source ≤
          fineUnitCouplingPhysicalCasimirExponentCeiling S := by
      unfold fineUnitCouplingPhysicalCasimirExponentCeiling
      exact list_mem_le_foldr_max_local _ _
        (List.mem_map.mpr ⟨source, hsource, rfl⟩)
    have hexponent :
        Q'.ofNat (slabPhysicalCasimirExponent S.fine.extent source) ≤
          Q'.ofNat (fineUnitCouplingPhysicalCasimirExponentCeiling S) :=
      Q'.ofNat_le_ofNat hmax
    have hterm : (0 : Q') ≤ fineUnitCouplingPhysicalTerm S source := by
      unfold fineUnitCouplingPhysicalTerm
      exact slabParametricKPhysicalTerm_nonnegative
        (by decide : (0 : Q') ≤ (1 : Q'))
        S.fine.cutoff S.fine.extent source
    exact Q'.mul_le_mul_of_nonneg_right _ _ _ hexponent hterm
  exact Q'.le_trans' _ _ _ hmono
    (Q'.le_of_eqv
      (listQSum_mul_left
        (Q'.ofNat (fineUnitCouplingPhysicalCasimirExponentCeiling S))
        (fineUnitCouplingPhysicalTerm S)
        S.fine.physicalLabellings))

/-! ## 7. An explicit spatial/cutoff growth envelope -/

def fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling
    (S : SlabScalePair) : Q' :=
  Q'.ofNat (S.fine.faceEdges.length * c4 S.fine.cutoff) *
    fineUnitCouplingPhysicalPartition S

theorem fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_le_spatial_cutoff
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S ≤
      fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S := by
  unfold fineUnitCouplingPhysicalCasimirMomentFiniteCeiling
    fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling
  exact Q'.mul_le_mul_of_nonneg_right _ _ _
    (Q'.ofNat_le_ofNat
      (fineUnitCouplingPhysicalCasimirExponentCeiling_le_face_count_mul_c4
        S))
    (fineUnitCouplingPhysicalPartition_nonnegative S)

theorem fineUnitCouplingPhysicalCasimirMoment_le_spatial_cutoff_ceiling
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalCasimirMoment S ≤
      fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S := by
  exact Q'.le_trans' _ _ _
    (fineUnitCouplingPhysicalCasimirMoment_le_finite_ceiling S)
    (fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_le_spatial_cutoff S)

theorem fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling_nonnegative
    (S : SlabScalePair) :
    (0 : Q') ≤ fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S := by
  unfold fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling
  exact Q'.mul_nonneg _ _
    (zero_le_ofNat _)
    (fineUnitCouplingPhysicalPartition_nonnegative S)

theorem fineUnitCouplingPhysicalCasimirMomentBound_spatial_cutoff
    (S : SlabScalePair) :
    FineUnitCouplingPhysicalCasimirMomentBound S
      (fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) := by
  unfold FineUnitCouplingPhysicalCasimirMomentBound
  exact fineUnitCouplingPhysicalCasimirMoment_le_spatial_cutoff_ceiling S

/-- The spatial/cutoff Casimir envelope supplies the carrier-ratio premise
needed by the balanced blocking compiler.  Its growth remains explicit. -/
theorem fineUnitCouplingBalancedCarrierRatioBound_of_spatial_casimir_ceiling
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    FineUnitCouplingBalancedCarrierRatioBound S
      ((1 + (Q'.ofNat 2 * (g * g)) *
        fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) *
        (1 + (Q'.ofNat 2 * (g * g)) *
          fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S)) := by
  let margin :=
    (Q'.ofNat 2 * (g * g)) *
      fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S
  have hcoef0 : (0 : Q') ≤ Q'.ofNat 2 * (g * g) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt (Q'.mul_pos hg hg))
  have hmargin : (0 : Q') ≤ margin := by
    unfold margin
    exact Q'.mul_nonneg _ _ hcoef0
      (fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling_nonnegative S)
  have hfloor : (0 : Q') < 1 := by decide
  have hfloor_le : (1 : Q') ≤ S.fine.physicalPartition := by
    unfold SlabPhysicalData.physicalPartition
    exact slabParametricKPhysicalPartition_one_le
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hloss₀ :=
    fineUnitCouplingPhysicalPartition_sub_actual_le_two_square_mul_moment
      S hfineCoupling_le_one family law g hg hgle hcoupling
  have hmoment :=
    fineUnitCouplingPhysicalCasimirMoment_le_spatial_cutoff_ceiling S
  have hlossBound : fineUnitCouplingPhysicalPartition S -
      S.fine.physicalPartition ≤ margin := by
    unfold margin
    exact Q'.le_trans' _ _ _ hloss₀
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hmoment hcoef0)
  have hloss : fineUnitCouplingPhysicalPartition S -
      S.fine.physicalPartition ≤ margin * (1 : Q') := by
    exact Q'.le_trans' _ _ _ hlossBound
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv margin)))
  simpa only [margin] using
    (fineUnitCouplingBalancedCarrierRatioBound_of_relative_loss
      S margin (1 : Q') hmargin hfloor hfloor_le hloss)

/-- Compile the spatial/cutoff carrier-ratio bound directly into the balanced
raw scale-defect calibration interface. -/
theorem fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_spatial_casimir_ceiling
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g : Q') (hg : (0 : Q') < g)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    FineUnitCouplingBalancedRawColumnScaleDefectCalibration
      S hfineCutoff hcoarseCoupling root target g
      (fineUnitCouplingBalancedCarrierRatioCeiling g
        ((1 + (Q'.ofNat 2 * (g * g)) *
          fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) *
          (1 + (Q'.ofNat 2 * (g * g)) *
            fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S)) hg) := by
  exact fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_carrier_ratio
    S hfineCutoff hcoarseCoupling root target g
    ((1 + (Q'.ofNat 2 * (g * g)) *
      fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) *
      (1 + (Q'.ofNat 2 * (g * g)) *
        fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S)) hg
    (fineUnitCouplingBalancedCarrierRatioBound_of_spatial_casimir_ceiling
      S hfineCoupling_le_one family law g hg hgle hcoupling)

theorem fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_nonnegative
    (S : SlabScalePair) :
    (0 : Q') ≤ fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S := by
  unfold fineUnitCouplingPhysicalCasimirMomentFiniteCeiling
  exact Q'.mul_nonneg _ _
    (zero_le_ofNat _)
    (fineUnitCouplingPhysicalPartition_nonnegative S)

theorem fineUnitCouplingPhysicalCasimirMomentBound_finite
    (S : SlabScalePair) :
    FineUnitCouplingPhysicalCasimirMomentBound S
      (fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S) := by
  unfold FineUnitCouplingPhysicalCasimirMomentBound
  exact fineUnitCouplingPhysicalCasimirMoment_le_finite_ceiling S

/-- Compile an explicit same-carrier Casimir-moment ceiling into the complete
finite centered-cylinder estimate.  The ceiling is parameterized by the
supplied moment certificate; no uniformity is inferred from its existence at
one slab. -/
theorem centeredCylinderRemainder_abs_le_of_casimir_moment_ceiling
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g momentCeiling : Q') (hg : (0 : Q') < g)
    (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hmomentCeiling : (0 : Q') ≤ momentCeiling)
    (hcasimir : FineUnitCouplingPhysicalCasimirMomentBound
      S momentCeiling) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierRatioCeiling g
          ((1 + (Q'.ofNat 2 * (g * g)) * momentCeiling) *
            (1 + (Q'.ofNat 2 * (g * g)) * momentCeiling)) hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  let margin :=
    (Q'.ofNat 2 * (g * g)) * momentCeiling
  have hcoef0 : (0 : Q') ≤ Q'.ofNat 2 * (g * g) := by
    exact Q'.mul_nonneg _ _ (by decide)
      (Q'.le_of_lt (Q'.mul_pos hg hg))
  have hmargin : (0 : Q') ≤ margin := by
    unfold margin
    exact Q'.mul_nonneg _ _ hcoef0 hmomentCeiling
  have hfloor : (0 : Q') < 1 := by decide
  have hfloor_le : (1 : Q') ≤ S.fine.physicalPartition := by
    unfold SlabPhysicalData.physicalPartition
    exact slabParametricKPhysicalPartition_one_le
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hcasimir' : fineUnitCouplingPhysicalCasimirMoment S ≤ momentCeiling :=
    hcasimir
  have hloss₀ :=
    fineUnitCouplingPhysicalPartition_sub_actual_le_two_square_mul_moment
      S hfineCoupling_le_one family law g hg hgle hcoupling
  have hlossBound : fineUnitCouplingPhysicalPartition S -
      S.fine.physicalPartition ≤ margin := by
    unfold margin
    exact Q'.le_trans' _ _ _ hloss₀
      (Q'.mul_le_mul_of_nonneg_left _ _ _ hcasimir' hcoef0)
  have hloss : fineUnitCouplingPhysicalPartition S -
      S.fine.physicalPartition ≤ margin * (1 : Q') := by
    exact Q'.le_trans' _ _ _ hlossBound
      (Q'.le_of_eqv (Q'.eqv_symm (Q'.mul_one_eqv margin)))
  simpa only [margin] using
    (centeredCylinderRemainder_abs_le_of_relative_balanced_carrier
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
      g hg hgle hcoupling margin (1 : Q') hmargin hfloor hfloor_le hloss)

/-- Fully explicit finite specialization of the Casimir-moment compiler.  The
ceiling is the finite maximum-exponent bound on the same physical carrier;
its dependence on the slab remains visible. -/
theorem centeredCylinderRemainder_abs_le_of_finite_casimir_ceiling
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierRatioCeiling g
          ((1 + (Q'.ofNat 2 * (g * g)) *
            fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S) *
            (1 + (Q'.ofNat 2 * (g * g)) *
              fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S)) hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  exact centeredCylinderRemainder_abs_le_of_casimir_moment_ceiling
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g (fineUnitCouplingPhysicalCasimirMomentFiniteCeiling S) hg hgle
    hcoupling
    (fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_nonnegative S)
    (fineUnitCouplingPhysicalCasimirMomentBound_finite S)

/-- Fully explicit finite centered-cylinder estimate using the spatial/cutoff
growth envelope for the same-carrier Casimir moment. -/
theorem centeredCylinderRemainder_abs_le_of_spatial_cutoff_casimir_ceiling
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (fineUnitCouplingBalancedCarrierRatioCeiling g
          ((1 + (Q'.ofNat 2 * (g * g)) *
            fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) *
            (1 + (Q'.ofNat 2 * (g * g)) *
              fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S)) hg +
        Q'.ofNat 2 * finiteMarginEnvelopeCeiling S) * (g * g) := by
  exact centeredCylinderRemainder_abs_le_of_casimir_moment_ceiling
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g (fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling S) hg hgle
    hcoupling
    (fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling_nonnegative S)
    (fineUnitCouplingPhysicalCasimirMomentBound_spatial_cutoff S)

/-- The reciprocal envelope reaches the complete finite centered-cylinder
bound once the independent balanced scale-defect calibration is supplied. -/
theorem centeredCylinderRemainder_abs_le_of_balanced_and_reciprocal
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g balancedCeiling : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hgap : (0 : Q') < 1 - S.fine.coupling)
    (hbalancedCeiling : (0 : Q') ≤ balancedCeiling)
    (hbalanced :
      FineUnitCouplingBalancedRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g balancedCeiling) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (balancedCeiling +
        Q'.ofNat 2 * fineCouplingReciprocalMarginCeiling S hgap) * (g * g) := by
  have hmargin :
      FineUnitCouplingCenteredNormalizedMarginRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M (fineCouplingReciprocalMarginCeiling S hgap) :=
    fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_reciprocal
      (physicalKernel S hfineCutoff hcoarseCoupling) M
      hfineCoupling_le_one hgap
  exact centeredCylinderRemainder_abs_le_of_balanced_and_margin
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g balancedCeiling (fineCouplingReciprocalMarginCeiling S hgap)
    hg hgle hcoupling hbalancedCeiling
    (fineCouplingReciprocalMarginCeiling_nonnegative S hgap)
    hbalanced hmargin

/-- The complete finite centered-cylinder estimate with a ceiling uniform over
the prescribed strict coupling corridor. -/
theorem centeredCylinderRemainder_abs_le_of_balanced_and_uniform_reciprocal
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (M : SlabFaceBlockMap S)
    (family : MatchedBlockFamily) (law : CubicMarginLaw family)
    (g balancedCeiling w₀ : Q')
    (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (hcorridor : S.fine.coupling ≤ w₀)
    (hgap₀ : (0 : Q') < 1 - w₀)
    (hbalancedCeiling : (0 : Q') ≤ balancedCeiling)
    (hbalanced :
      FineUnitCouplingBalancedRawColumnScaleDefectCalibration
        S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget
          g balancedCeiling) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      (balancedCeiling + Q'.ofNat 2 *
        fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀) * (g * g) := by
  have hmargin :
      FineUnitCouplingCenteredNormalizedMarginRawCalibration
        (physicalKernel S hfineCutoff hcoarseCoupling)
        M (fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀) :=
    fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_uniform_reciprocal
      (physicalKernel S hfineCutoff hcoarseCoupling) M w₀
      hfineCoupling_le_one hcorridor hgap₀
  exact centeredCylinderRemainder_abs_le_of_balanced_and_margin
    S hfineCutoff hcoarseCoupling hfineCoupling_le_one M family law
    g balancedCeiling
      (fineCouplingUniformReciprocalMarginCeiling w₀ hgap₀)
    hg hgle hcoupling hbalancedCeiling
    (fineCouplingUniformReciprocalMarginCeiling_nonnegative w₀ hgap₀)
    hbalanced hmargin

#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_sourcePairDebtL1
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_abs_le_partition_two_term
#print axioms fineUnitCouplingCenteredNormalizedMarginNumerator_abs_le_partition_two_term
#print axioms fineCouplingReciprocal_le_of_coupling_le
#print axioms fineCouplingPhysicalPartitionMarginSum_le_uniform_reciprocal
#print axioms fineCouplingPhysicalPartitionSquareMargin_le_uniform_reciprocal
#print axioms fineCouplingUniformReciprocalMarginCeiling
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_reciprocal
#print axioms fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_reciprocal
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_uniform_reciprocal
#print axioms fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_uniform_reciprocal
#print axioms finiteMarginEnvelopeCeiling_mul_denominator_eqv
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_of_partition_two_term
#print axioms fineUnitCouplingCenteredNormalizedChangeRawCalibration_of_partition_two_term
#print axioms centeredCylinderRemainder_abs_le_of_balanced_and_partition_two_term
#print axioms centeredCylinderRemainder_abs_le_of_finite_balanced_carrier
#print axioms centeredCylinderRemainder_abs_le_of_relative_balanced_carrier
#print axioms FineUnitCouplingPhysicalCasimirMomentBound
#print axioms fineUnitCouplingPhysicalCasimirExponentCeiling
#print axioms fineUnitCouplingPhysicalCasimirExponent_le_face_count_mul_c4
#print axioms fineUnitCouplingPhysicalCasimirExponentCeiling_le_face_count_mul_c4
#print axioms fineUnitCouplingPhysicalCasimirMoment_le_finite_ceiling
#print axioms fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_nonnegative
#print axioms fineUnitCouplingPhysicalCasimirMomentBound_finite
#print axioms fineUnitCouplingPhysicalCasimirMomentFiniteCeiling_le_spatial_cutoff
#print axioms fineUnitCouplingPhysicalCasimirMoment_le_spatial_cutoff_ceiling
#print axioms fineUnitCouplingPhysicalCasimirMomentSpatialCutoffCeiling_nonnegative
#print axioms fineUnitCouplingPhysicalCasimirMomentBound_spatial_cutoff
#print axioms fineUnitCouplingBalancedCarrierRatioBound_of_spatial_casimir_ceiling
#print axioms fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_spatial_casimir_ceiling
#print axioms centeredCylinderRemainder_abs_le_of_casimir_moment_ceiling
#print axioms centeredCylinderRemainder_abs_le_of_finite_casimir_ceiling
#print axioms centeredCylinderRemainder_abs_le_of_spatial_cutoff_casimir_ceiling
#print axioms centeredCylinderRemainder_abs_le_of_matched_casimir_loss
#print axioms centeredCylinderRemainder_abs_le_of_balanced_and_reciprocal
#print axioms centeredCylinderRemainder_abs_le_of_balanced_and_uniform_reciprocal

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtL1
