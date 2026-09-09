/-
# Fine-source pullback of the centered coupling-margin debt

The centered receiver-pair debt has zero total mass, but its selected
four-cell cross is still written on the coarse output carrier.  This module
pulls that debt back through the literal two-replica product kernel.

The resulting identity writes the open signed margin numerator as a finite
sum over fine physical source pairs:

  sourcePairCenteredDebt *
    (probability of the source output cell
      - probability of the opposite target output cell).

The source-pair debt itself has total mass zero.  Thus both the coupling
response and the output selection retain their centering before any absolute
value is taken.  No estimate of this signed average is proved here.

In particular, this module does not establish a cutoff- or volume-uniform
calibration, all-cutoff persistence, a continuum measure, OS/GNS
reconstruction, a Hamiltonian gap, or the Yang--Mills mass gap.

Constructive contract: exact finite sums and rational algebra only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebt
import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPaths
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebt
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedMarginFactorization
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingNormalizedRecentering
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

private theorem margin_path_regroup_local
    (unitLeft marginRight actualRight marginLeft
      kernelLeft kernelRight : Q') :
    (unitLeft * marginRight + actualRight * marginLeft) *
        (kernelLeft * kernelRight) ≈
      (unitLeft * kernelLeft) * (marginRight * kernelRight) +
        (marginLeft * kernelLeft) * (actualRight * kernelRight) := by
  ring_qeqv

private theorem actual_path_regroup_local
    (actualLeft actualRight kernelLeft kernelRight : Q') :
    (actualLeft * actualRight) * (kernelLeft * kernelRight) ≈
      (actualLeft * kernelLeft) * (actualRight * kernelRight) := by
  ring_qeqv

private theorem centered_path_regroup_local
    (marginMass actualMass actualSquare squareMargin kernelWeight : Q') :
    (marginMass * actualSquare - actualMass * squareMargin) *
        kernelWeight ≈
      (marginMass * kernelWeight) * actualSquare -
        (actualMass * kernelWeight) * squareMargin := by
  change
    (marginMass * actualSquare + -(actualMass * squareMargin)) *
        kernelWeight ≈
      (marginMass * kernelWeight) * actualSquare +
        -((actualMass * kernelWeight) * squareMargin)
  ring_qeqv

private theorem mul_sub_factor_local (factor left right : Q') :
    factor * left - factor * right ≈ factor * (left - right) := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.eqv_symm (Q'.mul_neg_eqv factor right))
  · exact Q'.eqv_symm (Q'.mul_add_eqv factor left (-right))

private theorem listQSum_cartesian_reversed_product_local
    {A B : Type} (leftWeight : A → Q') (rightWeight : B → Q')
    (left : List A) (right : List B) :
    listQSum
        (fun pair => rightWeight pair.2 * leftWeight pair.1)
        (cartesian left right) ≈
      listQSum leftWeight left * listQSum rightWeight right := by
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => leftWeight pair.1 * rightWeight pair.2)
      (cartesian left right)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _
    exact Q'.mul_comm_eqv _ _
  · exact listQSum_cartesian_product
      leftWeight rightWeight left right

private theorem listQSum_filter_le_on_local {A : Type}
    (weight : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → (0 : Q') ≤ weight item) →
      listQSum weight (items.filter test) ≤ listQSum weight items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hweight => by
      have hhead : (0 : Q') ≤ weight head :=
        hweight head List.mem_cons_self
      have htail : ∀ item, item ∈ tail → (0 : Q') ≤ weight item :=
        fun item hitem => hweight item (List.mem_cons_of_mem head hitem)
      have ih := listQSum_filter_le_on_local weight test tail htail
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            ↓reduceIte, listQSum]
          have htailLe : listQSum weight tail ≤
              weight head + listQSum weight tail := by
            have h := Q'.add_le_add_right
              (0 : Q') (weight head) (listQSum weight tail) hhead
            rwa [Q'.zero_add'] at h
          exact Q'.le_trans' _ _ _ ih htailLe
      | true =>
          simp only [List.filter_cons, htest, ↓reduceIte, listQSum]
          exact Q'.add_le_add_left _ _ _ ih

/-! ## 1. Fine source-pair response and centering -/

/-- Product-rule coupling quotient before the two fine sources are pushed
through the block kernel. -/
def fineCouplingPhysicalSourcePairMarginRawMass
    (S : SlabScalePair) (pair : PhysicalLabellingPair) : Q' :=
  fineUnitCouplingPhysicalTerm S pair.1 *
      fineCouplingPhysicalMarginTerm S pair.2 +
    S.fine.physicalTerm pair.2 *
      fineCouplingPhysicalMarginTerm S pair.1

/-- Actual unnormalized two-replica mass on a fine physical source pair. -/
def fineCouplingPhysicalSourcePairActualRawMass
    (S : SlabScalePair) (pair : PhysicalLabellingPair) : Q' :=
  S.fine.physicalTerm pair.1 * S.fine.physicalTerm pair.2

/-- The fine source-pair quotient totals to the partition-square quotient. -/
theorem fineCouplingPhysicalSourcePairMarginRawMass_total
    (S : SlabScalePair) :
    listQSum (fineCouplingPhysicalSourcePairMarginRawMass S)
        (pushedPhysicalSourcePairs S) ≈
      fineCouplingPhysicalPartitionSquareMargin S := by
  let states := S.fine.physicalLabellings
  let unit := fineUnitCouplingPhysicalTerm S
  let actual := S.fine.physicalTerm
  let margin := fineCouplingPhysicalMarginTerm S
  unfold pushedPhysicalSourcePairs
    fineCouplingPhysicalSourcePairMarginRawMass
  refine Q'.eqv_trans _
    (listQSum (fun pair => unit pair.1 * margin pair.2)
        (cartesian states states) +
      listQSum (fun pair => actual pair.2 * margin pair.1)
        (cartesian states states)) _ ?_ ?_
  · exact listQSum_add _ _ _
  refine Q'.eqv_trans _
    (listQSum unit states * listQSum margin states +
      listQSum margin states * listQSum actual states) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (listQSum_cartesian_product unit margin states states)
      (listQSum_cartesian_reversed_product_local
        margin actual states states)
  change
    fineUnitCouplingPhysicalPartition S *
        fineCouplingPhysicalPartitionMarginSum S +
      fineCouplingPhysicalPartitionMarginSum S *
        S.fine.physicalPartition ≈
      fineCouplingPhysicalPartitionSquareMargin S
  unfold fineCouplingPhysicalPartitionSquareMargin
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_comm_eqv
      (fineCouplingPhysicalPartitionMarginSum S)
      S.fine.physicalPartition)

/-- The actual fine source-pair mass totals to the actual partition square. -/
theorem fineCouplingPhysicalSourcePairActualRawMass_total
    (S : SlabScalePair) :
    listQSum (fineCouplingPhysicalSourcePairActualRawMass S)
        (pushedPhysicalSourcePairs S) ≈
      S.fine.physicalPartition * S.fine.physicalPartition := by
  unfold pushedPhysicalSourcePairs
    fineCouplingPhysicalSourcePairActualRawMass
  refine Q'.eqv_trans _
    (listQSum S.fine.physicalTerm S.fine.physicalLabellings *
      listQSum S.fine.physicalTerm S.fine.physicalLabellings) _ ?_ ?_
  · exact listQSum_cartesian_product _ _ _ _
  unfold SlabPhysicalData.physicalPartition
  exact Q'.eqv_refl _

/-- Centered coupling response on a fine physical source pair. -/
def fineCouplingPhysicalSourcePairCenteredMarginRawDebt
    (S : SlabScalePair) (pair : PhysicalLabellingPair) : Q' :=
  fineCouplingPhysicalSourcePairMarginRawMass S pair *
      (S.fine.physicalPartition * S.fine.physicalPartition) -
    fineCouplingPhysicalSourcePairActualRawMass S pair *
      fineCouplingPhysicalPartitionSquareMargin S

theorem fineCouplingPhysicalSourcePairCenteredMarginRawDebt_sum_eqv
    (S : SlabScalePair) (pairs : List PhysicalLabellingPair) :
    listQSum (fineCouplingPhysicalSourcePairCenteredMarginRawDebt S) pairs ≈
      listQSum (fineCouplingPhysicalSourcePairMarginRawMass S) pairs *
          (S.fine.physicalPartition * S.fine.physicalPartition) -
        listQSum (fineCouplingPhysicalSourcePairActualRawMass S) pairs *
          fineCouplingPhysicalPartitionSquareMargin S := by
  unfold fineCouplingPhysicalSourcePairCenteredMarginRawDebt
  refine Q'.eqv_trans _
    (listQSum
        (fun pair =>
          fineCouplingPhysicalSourcePairMarginRawMass S pair *
            (S.fine.physicalPartition * S.fine.physicalPartition)) pairs -
      listQSum
        (fun pair =>
          fineCouplingPhysicalSourcePairActualRawMass S pair *
            fineCouplingPhysicalPartitionSquareMargin S) pairs) _ ?_ ?_
  · exact Q'.eqv_symm (listQSum_sub_local _ _ pairs)
  · exact sub_eqv_both_local
      (listQSum_mul_right _ _ pairs)
      (listQSum_mul_right _ _ pairs)

/-- The fine source-pair debt is itself exactly mass zero. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginRawDebt_total_eqv_zero
    (S : SlabScalePair) :
    listQSum (fineCouplingPhysicalSourcePairCenteredMarginRawDebt S)
        (pushedPhysicalSourcePairs S) ≈ 0 := by
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  refine Q'.eqv_trans _
    (listQSum (fineCouplingPhysicalSourcePairMarginRawMass S)
          (pushedPhysicalSourcePairs S) * actualSquare -
      listQSum (fineCouplingPhysicalSourcePairActualRawMass S)
          (pushedPhysicalSourcePairs S) * squareMargin) _ ?_ ?_
  · simpa only [actualSquare, squareMargin] using
      (fineCouplingPhysicalSourcePairCenteredMarginRawDebt_sum_eqv
        S (pushedPhysicalSourcePairs S))
  refine Q'.eqv_trans _
    (squareMargin * actualSquare - actualSquare * squareMargin) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_eqv_congr_right _ _ actualSquare
        (fineCouplingPhysicalSourcePairMarginRawMass_total S))
      (Q'.mul_eqv_congr_right _ _ squareMargin
        (fineCouplingPhysicalSourcePairActualRawMass_total S))
  refine Q'.eqv_trans _
    (actualSquare * squareMargin - actualSquare * squareMargin) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv squareMargin actualSquare) (Q'.eqv_refl _)
  · exact Q'.add_neg_self_eqv _

/-! ## 2. Product-kernel pushforward of the source debt -/

/-- The literal independent two-replica product of one block-kernel row. -/
def fineCouplingTwoReplicaKernelWeight
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair targetPair : PhysicalLabellingPair) : Q' :=
  K.kernel sourcePair.1 targetPair.1 *
    K.kernel sourcePair.2 targetPair.2

theorem fineCouplingTwoReplicaKernelWeight_nonnegative
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair targetPair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S)
    (htarget : targetPair ∈ fineCouplingPushedAllTargetPairs S) :
    (0 : Q') ≤
      fineCouplingTwoReplicaKernelWeight K sourcePair targetPair := by
  have hs := mem_cartesian_iff
    S.fine.physicalLabellings S.fine.physicalLabellings sourcePair
  have ht := mem_cartesian_iff
    S.coarse.physicalLabellings S.coarse.physicalLabellings targetPair
  unfold pushedPhysicalSourcePairs at hsource
  unfold fineCouplingPushedAllTargetPairs at htarget
  exact Q'.mul_nonneg _ _
    (K.nonnegative sourcePair.1 targetPair.1
      ((hs.mp hsource).1) ((ht.mp htarget).1))
    (K.nonnegative sourcePair.2 targetPair.2
      ((hs.mp hsource).2) ((ht.mp htarget).2))

/-- The independent two-replica row has total mass one on the complete
coarse output-pair carrier. -/
theorem fineCouplingTwoReplicaKernelWeight_total
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S) :
    listQSum (fineCouplingTwoReplicaKernelWeight K sourcePair)
        (fineCouplingPushedAllTargetPairs S) ≈ 1 := by
  have hs := mem_cartesian_iff
    S.fine.physicalLabellings S.fine.physicalLabellings sourcePair
  unfold pushedPhysicalSourcePairs at hsource
  unfold fineCouplingPushedAllTargetPairs
    fineCouplingTwoReplicaKernelWeight
  refine Q'.eqv_trans _
    (listQSum (K.kernel sourcePair.1) S.coarse.physicalLabellings *
      listQSum (K.kernel sourcePair.2) S.coarse.physicalLabellings) _ ?_ ?_
  · exact listQSum_cartesian_product _ _ _ _
  refine Q'.eqv_trans _ (1 * 1) _ ?_ ?_
  · exact mul_eqv_both_local
      (K.row_normalized sourcePair.1 (hs.mp hsource).1)
      (K.row_normalized sourcePair.2 (hs.mp hsource).2)
  · exact Q'.one_mul_eqv 1

/-- Pushing the fine source-pair quotient through the product kernel gives
the previously defined coarse target-pair quotient. -/
theorem fineCouplingPushedTargetPairMarginRawMass_eqv_sourcePairPushforward
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          fineCouplingPhysicalSourcePairMarginRawMass S sourcePair *
            fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
        (pushedPhysicalSourcePairs S) ≈
      fineCouplingPushedTargetPairMarginRawMass K targetPair := by
  let states := S.fine.physicalLabellings
  let unitLeft := fun source =>
    fineUnitCouplingPhysicalTerm S source *
      K.kernel source targetPair.1
  let marginRight := fun source =>
    fineCouplingPhysicalMarginTerm S source *
      K.kernel source targetPair.2
  let marginLeft := fun source =>
    fineCouplingPhysicalMarginTerm S source *
      K.kernel source targetPair.1
  let actualRight := fun source =>
    S.fine.physicalTerm source * K.kernel source targetPair.2
  unfold pushedPhysicalSourcePairs
    fineCouplingPhysicalSourcePairMarginRawMass
    fineCouplingTwoReplicaKernelWeight
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        unitLeft sourcePair.1 * marginRight sourcePair.2 +
          marginLeft sourcePair.1 * actualRight sourcePair.2)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr_on
    intro sourcePair _
    exact margin_path_regroup_local _ _ _ _ _ _
  refine Q'.eqv_trans _
    (listQSum
        (fun sourcePair => unitLeft sourcePair.1 * marginRight sourcePair.2)
        (cartesian states states) +
      listQSum
        (fun sourcePair => marginLeft sourcePair.1 * actualRight sourcePair.2)
        (cartesian states states)) _ ?_ ?_
  · exact listQSum_add _ _ _
  refine Q'.eqv_trans _
    (listQSum unitLeft states * listQSum marginRight states +
      listQSum marginLeft states * listQSum actualRight states) _ ?_ ?_
  · exact Q'.add_eqv_congr'
      (listQSum_cartesian_product unitLeft marginRight states states)
      (listQSum_cartesian_product marginLeft actualRight states states)
  unfold fineCouplingPushedTargetPairMarginRawMass
    fineUnitCouplingPushedTargetRawMass
    fineCouplingPushedTargetMarginRawMass
    pushedPhysicalTargetRawMass
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_comm_eqv
      (listQSum marginLeft states)
      (listQSum actualRight states))

/-- The analogous product-kernel pushforward identity for the actual
fine source-pair mass. -/
theorem pushedPhysicalTargetPairRawMass_eqv_sourcePairPushforward
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          fineCouplingPhysicalSourcePairActualRawMass S sourcePair *
            fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
        (pushedPhysicalSourcePairs S) ≈
      pushedPhysicalTargetPairRawMass K targetPair := by
  let states := S.fine.physicalLabellings
  let actualLeft := fun source =>
    S.fine.physicalTerm source * K.kernel source targetPair.1
  let actualRight := fun source =>
    S.fine.physicalTerm source * K.kernel source targetPair.2
  unfold pushedPhysicalSourcePairs
    fineCouplingPhysicalSourcePairActualRawMass
    fineCouplingTwoReplicaKernelWeight
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        actualLeft sourcePair.1 * actualRight sourcePair.2)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr_on
    intro sourcePair _
    exact actual_path_regroup_local _ _ _ _
  refine Q'.eqv_trans _
    (listQSum actualLeft states * listQSum actualRight states) _ ?_ ?_
  · exact listQSum_cartesian_product
      actualLeft actualRight states states
  unfold pushedPhysicalTargetPairRawMass pushedPhysicalTargetRawMass
  exact Q'.eqv_refl _

/-- The coarse centered receiver-pair debt is exactly the product-kernel
pushforward of the centered fine source-pair debt. -/
theorem fineCouplingPushedTargetPairCenteredMarginRawDebt_eqv_sourcePairPushforward
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (targetPair : PhysicalLabellingPair) :
    listQSum
        (fun sourcePair =>
          fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
            fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
        (pushedPhysicalSourcePairs S) ≈
      fineCouplingPushedTargetPairCenteredMarginRawDebt K targetPair := by
  let sourceMargin := fineCouplingPhysicalSourcePairMarginRawMass S
  let sourceActual := fineCouplingPhysicalSourcePairActualRawMass S
  let kernelWeight := fun sourcePair =>
    fineCouplingTwoReplicaKernelWeight K sourcePair targetPair
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let squareMargin := fineCouplingPhysicalPartitionSquareMargin S
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        (sourceMargin sourcePair * kernelWeight sourcePair) * actualSquare -
          (sourceActual sourcePair * kernelWeight sourcePair) * squareMargin)
      (pushedPhysicalSourcePairs S)) _ ?_ ?_
  · unfold fineCouplingPhysicalSourcePairCenteredMarginRawDebt
    apply listQSum_congr_on
    intro sourcePair _
    exact centered_path_regroup_local _ _ _ _ _
  refine Q'.eqv_trans _
    (listQSum (fun sourcePair =>
          sourceMargin sourcePair * kernelWeight sourcePair)
          (pushedPhysicalSourcePairs S) * actualSquare -
      listQSum (fun sourcePair =>
          sourceActual sourcePair * kernelWeight sourcePair)
          (pushedPhysicalSourcePairs S) * squareMargin) _ ?_ ?_
  · exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm (listQSum_sub_local _ _ _))
      (sub_eqv_both_local
        (listQSum_mul_right _ _ _)
        (listQSum_mul_right _ _ _))
  unfold fineCouplingPushedTargetPairCenteredMarginRawDebt
  exact sub_eqv_both_local
    (Q'.mul_eqv_congr_right _ _ actualSquare
      (by simpa only [sourceMargin, kernelWeight] using
        (fineCouplingPushedTargetPairMarginRawMass_eqv_sourcePairPushforward
          K targetPair)))
    (Q'.mul_eqv_congr_right _ _ squareMargin
      (by simpa only [sourceActual, kernelWeight] using
        (pushedPhysicalTargetPairRawMass_eqv_sourcePairPushforward
          K targetPair)))

/-! ## 3. Selected output-cell contrast on each fine source pair -/

/-- Product-kernel mass delivered from one fine source pair to an arbitrary
finite carrier of coarse output pairs. -/
def fineCouplingTwoReplicaOutputPairMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair : PhysicalLabellingPair)
    (targetPairs : List PhysicalLabellingPair) : Q' :=
  listQSum (fineCouplingTwoReplicaKernelWeight K sourcePair) targetPairs

/-- Every Cartesian pair of coarse Boolean events has product-kernel mass in
the unit interval for a physical fine source pair. -/
theorem fineCouplingTwoReplicaFilteredOutputPairMass_nonnegative_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S)
    (leftEvent rightEvent : EdgeLabelling → Bool) :
    let targetPairs := cartesian
      (S.coarse.physicalLabellings.filter leftEvent)
      (S.coarse.physicalLabellings.filter rightEvent)
    (0 : Q') ≤ fineCouplingTwoReplicaOutputPairMass
        K sourcePair targetPairs ∧
      fineCouplingTwoReplicaOutputPairMass K sourcePair targetPairs ≤ 1 := by
  let leftTargets := S.coarse.physicalLabellings.filter leftEvent
  let rightTargets := S.coarse.physicalLabellings.filter rightEvent
  let leftMass := listQSum (K.kernel sourcePair.1) leftTargets
  let rightMass := listQSum (K.kernel sourcePair.2) rightTargets
  have hs := mem_cartesian_iff
    S.fine.physicalLabellings S.fine.physicalLabellings sourcePair
  have hsourceParts := hs.mp (by
    simpa only [pushedPhysicalSourcePairs] using hsource)
  have hleft0 : (0 : Q') ≤ leftMass := by
    unfold leftMass leftTargets
    apply listQSum_nonnegative_on
    intro coarse hcoarse
    exact K.nonnegative sourcePair.1 coarse hsourceParts.1
      (List.mem_filter.mp hcoarse).1
  have hright0 : (0 : Q') ≤ rightMass := by
    unfold rightMass rightTargets
    apply listQSum_nonnegative_on
    intro coarse hcoarse
    exact K.nonnegative sourcePair.2 coarse hsourceParts.2
      (List.mem_filter.mp hcoarse).1
  have hleft1 : leftMass ≤ 1 := by
    refine Q'.le_trans' _ _ _
      (listQSum_filter_le_on_local
        (K.kernel sourcePair.1) leftEvent S.coarse.physicalLabellings
        (fun coarse hcoarse =>
          K.nonnegative sourcePair.1 coarse hsourceParts.1 hcoarse)) ?_
    exact Q'.le_of_eqv
      (K.row_normalized sourcePair.1 hsourceParts.1)
  have hright1 : rightMass ≤ 1 := by
    refine Q'.le_trans' _ _ _
      (listQSum_filter_le_on_local
        (K.kernel sourcePair.2) rightEvent S.coarse.physicalLabellings
        (fun coarse hcoarse =>
          K.nonnegative sourcePair.2 coarse hsourceParts.2 hcoarse)) ?_
    exact Q'.le_of_eqv
      (K.row_normalized sourcePair.2 hsourceParts.2)
  have hmass :
      fineCouplingTwoReplicaOutputPairMass K sourcePair
          (cartesian leftTargets rightTargets) ≈
        leftMass * rightMass := by
    unfold fineCouplingTwoReplicaOutputPairMass
      fineCouplingTwoReplicaKernelWeight leftMass rightMass
    exact listQSum_cartesian_product _ _ _ _
  have hproduct0 : (0 : Q') ≤ leftMass * rightMass :=
    Q'.mul_nonneg _ _ hleft0 hright0
  have hproduct1 : leftMass * rightMass ≤ 1 := by
    refine Q'.le_trans' _ _ _
      (Q'.mul_le_mul_of_nonneg_right
        leftMass 1 rightMass hleft1 hright0) ?_
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.one_mul_eqv rightMass)) hright1
  change
    (0 : Q') ≤
        fineCouplingTwoReplicaOutputPairMass K sourcePair
          (cartesian leftTargets rightTargets) ∧
      fineCouplingTwoReplicaOutputPairMass K sourcePair
          (cartesian leftTargets rightTargets) ≤ 1
  exact ⟨Q'.le_trans' _ _ _ hproduct0
      (Q'.le_of_eqv (Q'.eqv_symm hmass)),
    Q'.le_trans' _ _ _ (Q'.le_of_eqv hmass) hproduct1⟩

/-- The source-cell minus opposite-target-cell output contrast of one fine
source pair. -/
def fineCouplingTwoReplicaFourCellOutputContrast
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (sourcePair : PhysicalLabellingPair) : Q' :=
  fineCouplingTwoReplicaOutputPairMass K sourcePair
      (pushedFaceRawFourCellSourcePairs (S := S) root target) -
    fineCouplingTwoReplicaOutputPairMass K sourcePair
      (pushedFaceRawFourCellTargetPairs (S := S) root target)

theorem fineCouplingTwoReplicaFourCellSourceOutputMass_nonnegative_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (sourcePair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S) :
    (0 : Q') ≤
        fineCouplingTwoReplicaOutputPairMass K sourcePair
          (pushedFaceRawFourCellSourcePairs (S := S) root target) ∧
      fineCouplingTwoReplicaOutputPairMass K sourcePair
          (pushedFaceRawFourCellSourcePairs (S := S) root target) ≤ 1 := by
  simpa only [pushedFaceRawFourCellSourcePairs] using
    (fineCouplingTwoReplicaFilteredOutputPairMass_nonnegative_le_one
      K sourcePair hsource
      (fun state =>
        slabPhysicalFacePositiveB root state &&
          slabPhysicalFacePositiveB target state)
      (fun state =>
        !(slabPhysicalFacePositiveB root state) &&
          !(slabPhysicalFacePositiveB target state)))

theorem fineCouplingTwoReplicaFourCellTargetOutputMass_nonnegative_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (sourcePair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S) :
    (0 : Q') ≤
        fineCouplingTwoReplicaOutputPairMass K sourcePair
          (pushedFaceRawFourCellTargetPairs (S := S) root target) ∧
      fineCouplingTwoReplicaOutputPairMass K sourcePair
          (pushedFaceRawFourCellTargetPairs (S := S) root target) ≤ 1 := by
  simpa only [pushedFaceRawFourCellTargetPairs] using
    (fineCouplingTwoReplicaFilteredOutputPairMass_nonnegative_le_one
      K sourcePair hsource
      (fun state =>
        !(slabPhysicalFacePositiveB root state) &&
          slabPhysicalFacePositiveB target state)
      (fun state =>
        slabPhysicalFacePositiveB root state &&
          !(slabPhysicalFacePositiveB target state)))

/-- The literal source-cell versus opposite-target-cell output contrast is
pointwise bounded by one on every physical fine source pair. -/
theorem fineCouplingTwoReplicaFourCellOutputContrast_abs_le_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (sourcePair : PhysicalLabellingPair)
    (hsource : sourcePair ∈ pushedPhysicalSourcePairs S) :
    Q'.abs
        (fineCouplingTwoReplicaFourCellOutputContrast
          K root target sourcePair) ≤ 1 := by
  let sourceMass :=
    fineCouplingTwoReplicaOutputPairMass K sourcePair
      (pushedFaceRawFourCellSourcePairs (S := S) root target)
  let targetMass :=
    fineCouplingTwoReplicaOutputPairMass K sourcePair
      (pushedFaceRawFourCellTargetPairs (S := S) root target)
  have hsourceMass : (0 : Q') ≤ sourceMass ∧ sourceMass ≤ 1 := by
    simpa only [sourceMass] using
      (fineCouplingTwoReplicaFourCellSourceOutputMass_nonnegative_le_one
        K root target sourcePair hsource)
  have htargetMass : (0 : Q') ≤ targetMass ∧ targetMass ≤ 1 := by
    simpa only [targetMass] using
      (fineCouplingTwoReplicaFourCellTargetOutputMass_nonnegative_le_one
        K root target sourcePair hsource)
  have hone_le_target_add : (1 : Q') ≤ targetMass + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') targetMass 1 htargetMass.1
    rwa [Q'.zero_add'] at h
  have hone_le_source_add : (1 : Q') ≤ sourceMass + 1 := by
    have h := Q'.add_le_add_right
      (0 : Q') sourceMass 1 hsourceMass.1
    rwa [Q'.zero_add'] at h
  unfold fineCouplingTwoReplicaFourCellOutputContrast
  change Q'.abs (sourceMass - targetMass) ≤ 1
  exact CReal.abs_sub_le_of_bounds
    (Q'.le_trans' _ _ _ hsourceMass.2 hone_le_target_add)
    (Q'.le_trans' _ _ _ htargetMass.2 hone_le_source_add)

/-- Fine-source form of the selected centered debt cross. -/
def fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  listQSum
    (fun sourcePair =>
      fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
        fineCouplingTwoReplicaFourCellOutputContrast
          K root target sourcePair)
    (pushedPhysicalSourcePairs S)

private theorem targetPairDebt_sum_eqv_sourcePairOutputMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (targetPairs : List PhysicalLabellingPair) :
    listQSum (fineCouplingPushedTargetPairCenteredMarginRawDebt K)
        targetPairs ≈
      listQSum
        (fun sourcePair =>
          fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
            fineCouplingTwoReplicaOutputPairMass
              K sourcePair targetPairs)
        (pushedPhysicalSourcePairs S) := by
  refine Q'.eqv_trans _
    (listQSum
      (fun targetPair =>
        listQSum
          (fun sourcePair =>
            fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
              fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
          (pushedPhysicalSourcePairs S))
      targetPairs) _ ?_ ?_
  · apply listQSum_congr_on
    intro targetPair _
    exact Q'.eqv_symm
      (fineCouplingPushedTargetPairCenteredMarginRawDebt_eqv_sourcePairPushforward
        K targetPair)
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        listQSum
          (fun targetPair =>
            fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
              fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
          targetPairs)
      (pushedPhysicalSourcePairs S)) _ ?_ ?_
  · exact listQSum_swap
      (fun sourcePair targetPair =>
        fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair *
          fineCouplingTwoReplicaKernelWeight K sourcePair targetPair)
      (pushedPhysicalSourcePairs S) targetPairs
  · unfold fineCouplingTwoReplicaOutputPairMass
    apply listQSum_congr_on
    intro sourcePair _
    exact listQSum_mul_left _ _ _

/-- The selected coarse receiver-pair debt cross is exactly a signed average
over fine source pairs of the mass-zero source debt times the literal
four-cell output contrast of the product kernel. -/
theorem fineCouplingPushedFourCellCenteredMarginRawDebtCross_eqv_sourcePairAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineCouplingPushedFourCellCenteredMarginRawDebtCross K root target ≈
      fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
        K root target := by
  let sources := pushedPhysicalSourcePairs S
  let debt := fineCouplingPhysicalSourcePairCenteredMarginRawDebt S
  let sourcePairs :=
    pushedFaceRawFourCellSourcePairs (S := S) root target
  let targetPairs :=
    pushedFaceRawFourCellTargetPairs (S := S) root target
  let sourceOutput := fun sourcePair =>
    fineCouplingTwoReplicaOutputPairMass K sourcePair sourcePairs
  let targetOutput := fun sourcePair =>
    fineCouplingTwoReplicaOutputPairMass K sourcePair targetPairs
  unfold fineCouplingPushedFourCellCenteredMarginRawDebtCross
    fineCouplingPushedFourCellSourceCenteredMarginRawDebt
    fineCouplingPushedFourCellTargetCenteredMarginRawDebt
  refine Q'.eqv_trans _
    (listQSum (fun sourcePair => debt sourcePair * sourceOutput sourcePair)
        sources -
      listQSum (fun sourcePair => debt sourcePair * targetOutput sourcePair)
        sources) _ ?_ ?_
  · exact sub_eqv_both_local
      (by simpa only [sources, debt, sourcePairs, sourceOutput] using
        (targetPairDebt_sum_eqv_sourcePairOutputMass K sourcePairs))
      (by simpa only [sources, debt, targetPairs, targetOutput] using
        (targetPairDebt_sum_eqv_sourcePairOutputMass K targetPairs))
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        debt sourcePair * sourceOutput sourcePair -
          debt sourcePair * targetOutput sourcePair)
      sources) _ ?_ ?_
  · exact listQSum_sub_local _ _ sources
  unfold fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
    fineCouplingTwoReplicaFourCellOutputContrast
  apply listQSum_congr_on
  intro sourcePair _
  simpa only [sources, debt, sourcePairs, targetPairs,
    sourceOutput, targetOutput] using
    (mul_sub_factor_local
      (debt sourcePair) (sourceOutput sourcePair) (targetOutput sourcePair))

/-- Direct fine-source identity for the cancellation-preserving normalized
margin numerator. -/
theorem fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_sourcePairAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingCenteredNormalizedMarginNumerator K root target ≈
      fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
        K root target := by
  exact Q'.eqv_trans _ _ _
    (fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_debtCross
      K root target)
    (fineCouplingPushedFourCellCenteredMarginRawDebtCross_eqv_sourcePairAverage
      K root target)

/-! ## 4. No-loss calibration interface at the fine-source level -/

/-- The open volume-uniform margin estimate stated directly on the signed
fine-source average.  This definition has no inhabitant here. -/
def FineUnitCouplingCenteredMarginSourcePairAverageCalibration
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (marginCeiling : Q') : Prop :=
  Q'.abs
      (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
        K M.coarseRoot M.coarseTarget) ≤
    marginCeiling *
      fineUnitCouplingCenteredNormalizedChangeDenominator S

/-- The prior normalized margin calibration and the fine-source signed
average calibration are exactly equivalent, with no change of constant. -/
theorem fineUnitCouplingCenteredNormalizedMarginRawCalibration_iff_sourcePairAverage
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (M : SlabFaceBlockMap S) (marginCeiling : Q') :
    FineUnitCouplingCenteredNormalizedMarginRawCalibration
        K M marginCeiling ↔
      FineUnitCouplingCenteredMarginSourcePairAverageCalibration
        K M marginCeiling := by
  let numerator :=
    fineUnitCouplingCenteredNormalizedMarginNumerator
      K M.coarseRoot M.coarseTarget
  let sourceAverage :=
    fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
      K M.coarseRoot M.coarseTarget
  let budget := marginCeiling *
    fineUnitCouplingCenteredNormalizedChangeDenominator S
  have heq : numerator ≈ sourceAverage := by
    simpa only [numerator, sourceAverage] using
      (fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_sourcePairAverage
        K M.coarseRoot M.coarseTarget)
  unfold FineUnitCouplingCenteredNormalizedMarginRawCalibration
    FineUnitCouplingCenteredMarginSourcePairAverageCalibration
  change Q'.abs numerator ≤ budget ↔ Q'.abs sourceAverage ≤ budget
  constructor
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr (Q'.eqv_symm heq))) h
  · intro h
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr heq)) h

#print axioms fineCouplingPhysicalSourcePairMarginRawMass_total
#print axioms fineCouplingPhysicalSourcePairActualRawMass_total
#print axioms fineCouplingPhysicalSourcePairCenteredMarginRawDebt
#print axioms fineCouplingPhysicalSourcePairCenteredMarginRawDebt_total_eqv_zero
#print axioms fineCouplingTwoReplicaKernelWeight
#print axioms fineCouplingTwoReplicaKernelWeight_nonnegative
#print axioms fineCouplingTwoReplicaKernelWeight_total
#print axioms fineCouplingPushedTargetPairMarginRawMass_eqv_sourcePairPushforward
#print axioms pushedPhysicalTargetPairRawMass_eqv_sourcePairPushforward
#print axioms fineCouplingPushedTargetPairCenteredMarginRawDebt_eqv_sourcePairPushforward
#print axioms fineCouplingTwoReplicaFourCellOutputContrast
#print axioms fineCouplingTwoReplicaFourCellOutputContrast_abs_le_one
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
#print axioms fineCouplingPushedFourCellCenteredMarginRawDebtCross_eqv_sourcePairAverage
#print axioms fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_sourcePairAverage
#print axioms FineUnitCouplingCenteredMarginSourcePairAverageCalibration
#print axioms fineUnitCouplingCenteredNormalizedMarginRawCalibration_iff_sourcePairAverage

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback
