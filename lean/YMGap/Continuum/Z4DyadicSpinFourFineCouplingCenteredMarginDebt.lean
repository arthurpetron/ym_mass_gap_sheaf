/-
# Centered receiver-pair form of the coupling-margin quotient

The exact coupling-margin factorization leaves one signed quotient numerator.
This module rewrites that quotient as a centered receiver-pair debt.  For one
coarse target pair, the debt is

  pairMarginMass * Z_actual^2
    - actualPairMass * partitionSquareMargin.

Its sum over the complete coarse target-pair carrier is exactly zero.  The
margin numerator relevant to the two face events is exactly the source-cell
debt minus the opposite target-cell debt.  Thus the global partition response
is not an independent positive cost: it is the centering term of one signed,
mass-zero receiver-pair measure.

No absolute-value estimate is proved.  In particular, the module does not
inhabit a volume-uniform calibration, establish all-cutoff persistence,
construct a continuum measure or OS/GNS Hamiltonian, or prove the Yang--Mills
mass gap.

Constructive contract: exact finite sums and rational algebra only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedBalancedBridge

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebt

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation

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

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem listQSum_neg_local {A : Type}
    (value : A → Q') : ∀ items : List A,
    listQSum (fun item => -(value item)) items ≈
      -(listQSum value items)
  | [] => by
      change (0 : Q') ≈ -(0 : Q')
      decide
  | head :: tail => by
      refine Q'.eqv_trans _
        (-(value head) + -(listQSum value tail)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_refl _) (listQSum_neg_local value tail)
      · exact Q'.eqv_symm
          (Q'.neg_add_eqv (value head) (listQSum value tail))

private theorem listQSum_sub_local {A : Type}
    (left right : A → Q') (items : List A) :
    listQSum left items - listQSum right items ≈
      listQSum (fun item => left item - right item) items := by
  exact Q'.eqv_symm
    (Q'.eqv_trans _
      (listQSum left items +
        listQSum (fun item => -(right item)) items) _
      (listQSum_add left (fun item => -(right item)) items)
      (Q'.add_eqv_congr' (Q'.eqv_refl _)
        (listQSum_neg_local right items)))

private theorem centered_cross_regroup_local
    (sourceMargin targetMargin sourceActual targetActual
      actualSquare squareMargin : Q') :
    (sourceMargin - targetMargin) * actualSquare -
        (sourceActual - targetActual) * squareMargin ≈
      (sourceMargin * actualSquare - sourceActual * squareMargin) -
        (targetMargin * actualSquare - targetActual * squareMargin) := by
  change
    ((sourceMargin + -targetMargin) * actualSquare +
        -((sourceActual + -targetActual) * squareMargin)) ≈
      (sourceMargin * actualSquare + -(sourceActual * squareMargin)) +
        -(targetMargin * actualSquare + -(targetActual * squareMargin))
  ring_qeqv

/-! ## 1. Total mass of the geometric-quotient pushforward -/

/-- The pushed geometric-quotient column has the geometric-quotient fine
partition sum as its total mass. -/
theorem fineCouplingPushedTargetMarginRawMass_total
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    listQSum (fineCouplingPushedTargetMarginRawMass K)
        S.coarse.physicalLabellings ≈
      fineCouplingPhysicalPartitionMarginSum S := by
  unfold fineCouplingPushedTargetMarginRawMass
    fineCouplingPhysicalPartitionMarginSum
  refine Q'.eqv_trans _
    (listQSum
      (fun source =>
        listQSum
          (fun target =>
            fineCouplingPhysicalMarginTerm S source *
              K.kernel source target)
          S.coarse.physicalLabellings)
      S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_swap
      (fun source target =>
        fineCouplingPhysicalMarginTerm S source *
          K.kernel source target)
      S.fine.physicalLabellings S.coarse.physicalLabellings
  · apply listQSum_congr_on
    intro source hsource
    refine Q'.eqv_trans _
      (fineCouplingPhysicalMarginTerm S source *
        listQSum (K.kernel source) S.coarse.physicalLabellings) _ ?_ ?_
    · exact listQSum_mul_left
        (fineCouplingPhysicalMarginTerm S source)
        (K.kernel source) S.coarse.physicalLabellings
    refine Q'.eqv_trans _
      (fineCouplingPhysicalMarginTerm S source * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left
        (fineCouplingPhysicalMarginTerm S source) _ _
        (K.row_normalized source hsource)
    · exact Q'.mul_one_eqv _

/-- Complete coarse target-pair carrier. -/
def fineCouplingPushedAllTargetPairs
    (S : SlabScalePair) : List (EdgeLabelling × EdgeLabelling) :=
  cartesian S.coarse.physicalLabellings S.coarse.physicalLabellings

/-- The pair-margin mass totals to the exact quotient of the unit/actual
fine partition-square loss. -/
theorem fineCouplingPushedTargetPairMarginRawMass_total
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    listQSum (fineCouplingPushedTargetPairMarginRawMass K)
        (fineCouplingPushedAllTargetPairs S) ≈
      fineCouplingPhysicalPartitionSquareMargin S := by
  let states := S.coarse.physicalLabellings
  let unit := fineUnitCouplingPushedTargetRawMass K
  let actual := pushedPhysicalTargetRawMass K
  let margin := fineCouplingPushedTargetMarginRawMass K
  have hfirst :
      listQSum (fun pair => unit pair.1 * margin pair.2)
          (cartesian states states) ≈
        listQSum unit states * listQSum margin states :=
    listQSum_cartesian_product unit margin states states
  have hsecond :
      listQSum (fun pair => actual pair.2 * margin pair.1)
          (cartesian states states) ≈
        listQSum margin states * listQSum actual states := by
    refine Q'.eqv_trans _
      (listQSum (fun pair => margin pair.1 * actual pair.2)
        (cartesian states states)) _ ?_ ?_
    · apply listQSum_congr_on
      intro pair _
      exact Q'.mul_comm_eqv _ _
    · exact listQSum_cartesian_product margin actual states states
  unfold fineCouplingPushedAllTargetPairs
    fineCouplingPushedTargetPairMarginRawMass
  refine Q'.eqv_trans _
    (listQSum (fun pair => unit pair.1 * margin pair.2)
        (cartesian states states) +
      listQSum (fun pair => actual pair.2 * margin pair.1)
        (cartesian states states)) _ ?_ ?_
  · exact listQSum_add _ _ _
  refine Q'.eqv_trans _
    (listQSum unit states * listQSum margin states +
      listQSum margin states * listQSum actual states) _
    (Q'.add_eqv_congr' hfirst hsecond) ?_
  refine Q'.eqv_trans _
    (fineUnitCouplingPhysicalPartition S *
        fineCouplingPhysicalPartitionMarginSum S +
      fineCouplingPhysicalPartitionMarginSum S *
        S.fine.physicalPartition) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (mul_eqv_both_local
        (fineUnitCouplingPushedTargetRawMass_total K)
        (fineCouplingPushedTargetMarginRawMass_total K))
      (mul_eqv_both_local
        (fineCouplingPushedTargetMarginRawMass_total K)
        (pushedPhysicalTargetRawMass_total K))
  unfold fineCouplingPhysicalPartitionSquareMargin
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_comm_eqv
      (fineCouplingPhysicalPartitionMarginSum S)
      S.fine.physicalPartition)

/-! ## 2. The centered mass-zero receiver-pair debt -/

/-- Centered response debt on one coarse receiver pair. -/
def fineCouplingPushedTargetPairCenteredMarginRawDebt
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pair : EdgeLabelling × EdgeLabelling) : Q' :=
  fineCouplingPushedTargetPairMarginRawMass K pair *
      (S.fine.physicalPartition * S.fine.physicalPartition) -
    pushedPhysicalTargetPairRawMass K pair *
      fineCouplingPhysicalPartitionSquareMargin S

/-- Summing the pair debts over any finite carrier keeps normalization
centering inside the same signed sum. -/
theorem fineCouplingPushedTargetPairCenteredMarginRawDebt_sum_eqv
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (pairs : List (EdgeLabelling × EdgeLabelling)) :
    listQSum (fineCouplingPushedTargetPairCenteredMarginRawDebt K) pairs ≈
      listQSum (fineCouplingPushedTargetPairMarginRawMass K) pairs *
          (S.fine.physicalPartition * S.fine.physicalPartition) -
        listQSum (pushedPhysicalTargetPairRawMass K) pairs *
          fineCouplingPhysicalPartitionSquareMargin S := by
  unfold fineCouplingPushedTargetPairCenteredMarginRawDebt
  refine Q'.eqv_trans _
    (listQSum
        (fun pair =>
          fineCouplingPushedTargetPairMarginRawMass K pair *
            (S.fine.physicalPartition * S.fine.physicalPartition)) pairs -
      listQSum
        (fun pair =>
          pushedPhysicalTargetPairRawMass K pair *
            fineCouplingPhysicalPartitionSquareMargin S) pairs) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ pairs)
  · exact sub_eqv_both_local
      (listQSum_mul_right _ _ pairs)
      (listQSum_mul_right _ _ pairs)

/-- The centered receiver-pair debt has exactly zero total mass on the
complete coarse target-pair carrier. -/
theorem fineCouplingPushedTargetPairCenteredMarginRawDebt_total_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel) :
    listQSum (fineCouplingPushedTargetPairCenteredMarginRawDebt K)
        (fineCouplingPushedAllTargetPairs S) ≈ 0 := by
  let states := S.coarse.physicalLabellings
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  have hactual :
      listQSum (pushedPhysicalTargetPairRawMass K)
          (fineCouplingPushedAllTargetPairs S) ≈ actualSquare := by
    unfold fineCouplingPushedAllTargetPairs
      pushedPhysicalTargetPairRawMass
    refine Q'.eqv_trans _
      (listQSum (pushedPhysicalTargetRawMass K) states *
        listQSum (pushedPhysicalTargetRawMass K) states) _ ?_ ?_
    · exact listQSum_cartesian_product
        (pushedPhysicalTargetRawMass K)
        (pushedPhysicalTargetRawMass K) states states
    · exact mul_eqv_both_local
        (pushedPhysicalTargetRawMass_total K)
        (pushedPhysicalTargetRawMass_total K)
  refine Q'.eqv_trans _
    (listQSum (fineCouplingPushedTargetPairMarginRawMass K)
          (fineCouplingPushedAllTargetPairs S) * actualSquare -
      listQSum (pushedPhysicalTargetPairRawMass K)
          (fineCouplingPushedAllTargetPairs S) * squareMargin) _ ?_ ?_
  · simpa only [actualSquare, squareMargin] using
      (fineCouplingPushedTargetPairCenteredMarginRawDebt_sum_eqv
        K (fineCouplingPushedAllTargetPairs S))
  refine Q'.eqv_trans _
    (squareMargin * actualSquare - actualSquare * squareMargin) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_eqv_congr_right _ _ actualSquare
        (fineCouplingPushedTargetPairMarginRawMass_total K))
      (Q'.mul_eqv_congr_right _ _ squareMargin hactual)
  refine Q'.eqv_trans _
    (actualSquare * squareMargin - actualSquare * squareMargin) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv squareMargin actualSquare) (Q'.eqv_refl _)
  · exact Q'.add_neg_self_eqv _

/-! ## 3. Selected four-cell debt and the quotient calibration -/

/-- Source-cell centered margin debt. -/
def fineCouplingPushedFourCellSourceCenteredMarginRawDebt
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineCouplingPushedTargetPairCenteredMarginRawDebt K)
    (pushedFaceRawFourCellSourcePairs (S := S) root target)

/-- Opposite target-cell centered margin debt. -/
def fineCouplingPushedFourCellTargetCenteredMarginRawDebt
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum (fineCouplingPushedTargetPairCenteredMarginRawDebt K)
    (pushedFaceRawFourCellTargetPairs (S := S) root target)

/-- Signed selected receiver-pair debt. -/
def fineCouplingPushedFourCellCenteredMarginRawDebtCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  fineCouplingPushedFourCellSourceCenteredMarginRawDebt K root target -
    fineCouplingPushedFourCellTargetCenteredMarginRawDebt K root target

/-- The cancellation-preserving normalized margin numerator is exactly the
selected source-minus-target cross of the globally mass-zero pair debt. -/
theorem fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_debtCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingCenteredNormalizedMarginNumerator K root target ≈
      fineCouplingPushedFourCellCenteredMarginRawDebtCross
        K root target := by
  let sourcePairs :=
    pushedFaceRawFourCellSourcePairs (S := S) root target
  let targetPairs :=
    pushedFaceRawFourCellTargetPairs (S := S) root target
  let sourceMargin :=
    listQSum (fineCouplingPushedTargetPairMarginRawMass K) sourcePairs
  let targetMargin :=
    listQSum (fineCouplingPushedTargetPairMarginRawMass K) targetPairs
  let sourceActual :=
    listQSum (pushedPhysicalTargetPairRawMass K) sourcePairs
  let targetActual :=
    listQSum (pushedPhysicalTargetPairRawMass K) targetPairs
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  have hactual :
      pushedFaceRawFourCellCross K root target ≈
        sourceActual - targetActual := by
    simpa only [sourcePairs, targetPairs, sourceActual, targetActual] using
      (pushedFaceRawFourCellCross_eqv_pair_mass_difference
        K root target)
  have hsource :
      fineCouplingPushedFourCellSourceCenteredMarginRawDebt
          K root target ≈
        sourceMargin * actualSquare - sourceActual * squareMargin := by
    simpa only [fineCouplingPushedFourCellSourceCenteredMarginRawDebt,
      sourcePairs, sourceMargin, sourceActual, actualSquare, squareMargin] using
      (fineCouplingPushedTargetPairCenteredMarginRawDebt_sum_eqv
        K sourcePairs)
  have htarget :
      fineCouplingPushedFourCellTargetCenteredMarginRawDebt
          K root target ≈
        targetMargin * actualSquare - targetActual * squareMargin := by
    simpa only [fineCouplingPushedFourCellTargetCenteredMarginRawDebt,
      targetPairs, targetMargin, targetActual, actualSquare, squareMargin] using
      (fineCouplingPushedTargetPairCenteredMarginRawDebt_sum_eqv
        K targetPairs)
  unfold fineUnitCouplingCenteredNormalizedMarginNumerator
    fineCouplingPushedRawColumnCrossMargin
    fineCouplingPushedFourCellSourceMarginRawMass
    fineCouplingPushedFourCellTargetMarginRawMass
  change
    (sourceMargin - targetMargin) * actualSquare -
        pushedFaceRawFourCellCross K root target * squareMargin ≈ _
  refine Q'.eqv_trans _
    ((sourceMargin - targetMargin) * actualSquare -
      (sourceActual - targetActual) * squareMargin) _ ?_ ?_
  · exact sub_eqv_both_local (Q'.eqv_refl _)
      (Q'.mul_eqv_congr_right _ _ squareMargin hactual)
  refine Q'.eqv_trans _
    ((sourceMargin * actualSquare - sourceActual * squareMargin) -
      (targetMargin * actualSquare - targetActual * squareMargin)) _ ?_ ?_
  · exact centered_cross_regroup_local
      sourceMargin targetMargin sourceActual targetActual
      actualSquare squareMargin
  unfold fineCouplingPushedFourCellCenteredMarginRawDebtCross
  exact sub_eqv_both_local (Q'.eqv_symm hsource) (Q'.eqv_symm htarget)

/-- The existing signed quotient calibration stated directly on the
mass-zero receiver-pair debt cross.  This definition has no inhabitant here. -/
def FineUnitCouplingCenteredMarginDebtCrossCalibration
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (marginCeiling : Q') : Prop :=
  Q'.abs
      (fineCouplingPushedFourCellCenteredMarginRawDebtCross
        K M.coarseRoot M.coarseTarget) ≤
    marginCeiling *
      fineUnitCouplingCenteredNormalizedChangeDenominator S

/-- The margin calibration and the selected mass-zero debt-cross calibration
are exactly equivalent, with no change of constant. -/
theorem fineUnitCouplingCenteredNormalizedMarginRawCalibration_iff_debtCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (marginCeiling : Q') :
    FineUnitCouplingCenteredNormalizedMarginRawCalibration
        K M marginCeiling ↔
      FineUnitCouplingCenteredMarginDebtCrossCalibration
        K M marginCeiling := by
  let numerator :=
    fineUnitCouplingCenteredNormalizedMarginNumerator
      K M.coarseRoot M.coarseTarget
  let debt :=
    fineCouplingPushedFourCellCenteredMarginRawDebtCross
      K M.coarseRoot M.coarseTarget
  let budget := marginCeiling *
    fineUnitCouplingCenteredNormalizedChangeDenominator S
  have heq : numerator ≈ debt := by
    simpa only [numerator, debt] using
      (fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_debtCross
        K M.coarseRoot M.coarseTarget)
  unfold FineUnitCouplingCenteredNormalizedMarginRawCalibration
    FineUnitCouplingCenteredMarginDebtCrossCalibration
  change Q'.abs numerator ≤ budget ↔ Q'.abs debt ≤ budget
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm heq))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr heq)) h

#print axioms fineCouplingPushedTargetMarginRawMass_total
#print axioms fineCouplingPushedAllTargetPairs
#print axioms fineCouplingPushedTargetPairMarginRawMass_total
#print axioms fineCouplingPushedTargetPairCenteredMarginRawDebt
#print axioms fineCouplingPushedTargetPairCenteredMarginRawDebt_sum_eqv
#print axioms fineCouplingPushedTargetPairCenteredMarginRawDebt_total_eqv_zero
#print axioms fineCouplingPushedFourCellCenteredMarginRawDebtCross
#print axioms fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_debtCross
#print axioms FineUnitCouplingCenteredMarginDebtCrossCalibration
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_iff_debtCross

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebt
