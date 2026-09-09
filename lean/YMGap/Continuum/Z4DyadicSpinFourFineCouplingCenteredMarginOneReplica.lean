/-
# One-replica reduction of the centered coupling-margin debt

The fine-source pullback writes the open coupling-margin numerator as a
signed sum over two independent fine sources.  This module proves that the
pair debt is not an irreducible two-replica object.

For one fine source `x`, define the centered margin score

  d(x) = m(x) * Z_actual - a(x) * M,

where `a` is the actual fine mass, `m` is the exact geometric coupling
quotient, and `M` is its total mass.  The score has total mass zero.  The
two-source centered debt factors exactly through `d`, and the product-kernel
four-cell contrast is a two-by-two determinant of one-row event masses.
Finite Fubini therefore contracts the open pair average to four products of
one-replica moments.

This is an exact algebraic reduction.  It proves no cutoff- or volume-uniform
estimate.  In particular, it does not establish all-cutoff persistence, a
continuum measure, OS/GNS reconstruction, a Hamiltonian gap, or the
Yang--Mills mass gap.

Constructive contract: finite sums and rational algebra only; no
`Classical`, choice, `native_decide`, proof hole, noncomputable declaration,
or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica

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
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginDebtPullback
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

private theorem sub_self_eqv_zero_local (value : Q') :
    value - value ≈ 0 := by
  refine Q'.eqv_trans _ (-value + value) _
    (Q'.add_comm_eqv value (-value)) ?_
  exact Q'.neg_add_self_eqv value

private theorem mul_sub_expand_local (factor left right : Q') :
    factor * (left - right) ≈
      factor * left - factor * right := by
  refine Q'.eqv_trans _
    (factor * left + factor * (-right)) _
    (Q'.mul_add_eqv factor left (-right)) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.mul_neg_eqv factor right)

private theorem add_sub_cancel_middle_local (x y z : Q') :
    (x - y) + (y - z) ≈ x - z := by
  change (x + -y) + (y + -z) ≈ x + -z
  refine Q'.eqv_trans _ (x + (-y + (y + -z))) _ ?_ ?_
  · exact Q'.add_assoc_eqv x (-y) (y + -z)
  refine Q'.eqv_trans _ (x + ((-y + y) + -z)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-y) y (-z)))
  refine Q'.eqv_trans _ (x + (0 + -z)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.add_eqv_congr_right (-y + y) 0 (-z)
        (Q'.neg_add_self_eqv y))
  · exact Q'.add_eqv_congr_left x _ _
      (Q'.eqv_of_eq (Q'.zero_add' (-z)))

private theorem cross_shift_local (x y z w : Q')
    (h : x - y ≈ z - w) :
    y - w ≈ x - z := by
  have hadded :
      (x - y) + (y - z) ≈ (z - w) + (y - z) :=
    Q'.add_eqv_congr_right _ _ (y - z) h
  have hleft : (x - y) + (y - z) ≈ x - z :=
    add_sub_cancel_middle_local x y z
  have hright : (z - w) + (y - z) ≈ y - w :=
    Q'.eqv_trans _ ((y - z) + (z - w)) _
      (Q'.add_comm_eqv (z - w) (y - z))
      (add_sub_cancel_middle_local y z w)
  exact Q'.eqv_trans _ _ _
    (Q'.eqv_symm hright)
    (Q'.eqv_trans _ _ _ (Q'.eqv_symm hadded) hleft)

private theorem add_mul_sub_expand_local (left right positive negative : Q') :
    (left + right) * (positive - negative) ≈
      (left * positive - left * negative) +
        (right * positive - right * negative) := by
  refine Q'.eqv_trans _
    (left * (positive - negative) +
      right * (positive - negative)) _ ?_ ?_
  · exact Q'.add_mul_eqv left right (positive - negative)
  apply Q'.add_eqv_congr'
  · exact mul_sub_expand_local left positive negative
  · exact mul_sub_expand_local right positive negative

private theorem filter_and_eq_filter_filter_local {A : Type}
    (first second : A → Bool) (ambient : List A) :
    ambient.filter (fun item => first item && second item) =
      (ambient.filter first).filter second := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (first item) (second item)

/-! ## 1. The centered one-source margin score -/

/-- Centered geometric-quotient score on one fine physical source. -/
def fineCouplingPhysicalSourceCenteredMarginRawDebt
    (S : SlabScalePair) (source : EdgeLabelling) : Q' :=
  fineCouplingPhysicalMarginTerm S source * S.fine.physicalPartition -
    S.fine.physicalTerm source *
      fineCouplingPhysicalPartitionMarginSum S

/-- The one-source centered margin score has exactly zero total mass. -/
theorem fineCouplingPhysicalSourceCenteredMarginRawDebt_total_eqv_zero
    (S : SlabScalePair) :
    listQSum (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
        S.fine.physicalLabellings ≈ 0 := by
  refine Q'.eqv_trans _
    (listQSum (fineCouplingPhysicalMarginTerm S)
          S.fine.physicalLabellings * S.fine.physicalPartition -
      listQSum S.fine.physicalTerm S.fine.physicalLabellings *
          fineCouplingPhysicalPartitionMarginSum S) _ ?_ ?_
  · unfold fineCouplingPhysicalSourceCenteredMarginRawDebt
    exact Q'.eqv_trans _ _ _
      (Q'.eqv_symm
        (listQSum_sub_local
          (fun source =>
            fineCouplingPhysicalMarginTerm S source *
              S.fine.physicalPartition)
          (fun source =>
            S.fine.physicalTerm source *
              fineCouplingPhysicalPartitionMarginSum S)
          S.fine.physicalLabellings))
      (sub_eqv_both_local
        (listQSum_mul_right _ _ _)
        (listQSum_mul_right _ _ _))
  change
    fineCouplingPhysicalPartitionMarginSum S *
        S.fine.physicalPartition -
      S.fine.physicalPartition *
        fineCouplingPhysicalPartitionMarginSum S ≈ 0
  refine Q'.eqv_trans _
    (S.fine.physicalPartition *
        fineCouplingPhysicalPartitionMarginSum S -
      S.fine.physicalPartition *
        fineCouplingPhysicalPartitionMarginSum S) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv _ _) (Q'.eqv_refl _)
  · exact sub_self_eqv_zero_local _

private theorem centered_pair_debt_factor_local
    (unitX actualX marginX actualY marginY
      actualPartition unitPartition marginPartition couplingMargin : Q')
    (hsource : unitX - actualX ≈ couplingMargin * marginX)
    (hpartition : unitPartition - actualPartition ≈
      couplingMargin * marginPartition) :
    (unitX * marginY + actualY * marginX) *
          (actualPartition * actualPartition) -
        (actualX * actualY) *
          (unitPartition * marginPartition +
            actualPartition * marginPartition) ≈
      (unitX * actualPartition) *
          (marginY * actualPartition - actualY * marginPartition) +
        (actualY * unitPartition) *
          (marginX * actualPartition - actualX * marginPartition) := by
  have hleftMargin :
      marginPartition * (unitX - actualX) ≈
        marginPartition * (couplingMargin * marginX) :=
    Q'.mul_eqv_congr_left marginPartition _ _ hsource
  have hrightMargin :
      marginX * (unitPartition - actualPartition) ≈
        marginX * (couplingMargin * marginPartition) :=
    Q'.mul_eqv_congr_left marginX _ _ hpartition
  have hmarginSame :
      marginPartition * (couplingMargin * marginX) ≈
        marginX * (couplingMargin * marginPartition) := by
    ring_qeqv
  have hscaledDifference :
      marginX * (unitPartition - actualPartition) ≈
        marginPartition * (unitX - actualX) := by
    exact Q'.eqv_trans _ _ _ hrightMargin
      (Q'.eqv_trans _ _ _ (Q'.eqv_symm hmarginSame)
        (Q'.eqv_symm hleftMargin))
  have hexpandedDifference :
      marginX * unitPartition - marginX * actualPartition ≈
        unitX * marginPartition - actualX * marginPartition := by
    refine Q'.eqv_trans _
      (marginX * (unitPartition - actualPartition)) _ ?_ ?_
    · exact Q'.eqv_symm
        (mul_sub_expand_local marginX unitPartition actualPartition)
    refine Q'.eqv_trans _
      (marginPartition * (unitX - actualX)) _
      hscaledDifference ?_
    refine Q'.eqv_trans _
      (marginPartition * unitX - marginPartition * actualX) _ ?_ ?_
    · exact mul_sub_expand_local marginPartition unitX actualX
    · exact sub_eqv_both_local
        (Q'.mul_comm_eqv marginPartition unitX)
        (Q'.mul_comm_eqv marginPartition actualX)
  have hcenterShift :
      marginX * actualPartition - actualX * marginPartition ≈
        marginX * unitPartition - unitX * marginPartition :=
    cross_shift_local
      (marginX * unitPartition) (marginX * actualPartition)
      (unitX * marginPartition) (actualX * marginPartition)
      hexpandedDifference
  let commonLeft := (unitX * marginY) *
    (actualPartition * actualPartition)
  let commonRight := (actualX * actualY) *
    (unitPartition * marginPartition)
  let leftCenter :=
    marginX * actualPartition - actualX * marginPartition
  let rightCenter :=
    marginX * unitPartition - unitX * marginPartition
  refine Q'.eqv_trans _
    (commonLeft +
      (actualY * actualPartition) * leftCenter - commonRight) _ ?_ ?_
  · simp only [commonLeft, commonRight, leftCenter]
    change
      ((unitX * marginY + actualY * marginX) *
            (actualPartition * actualPartition) +
          -((actualX * actualY) *
            (unitPartition * marginPartition +
              actualPartition * marginPartition))) ≈
        (unitX * marginY) *
              (actualPartition * actualPartition) +
            (actualY * actualPartition) *
              (marginX * actualPartition +
                -(actualX * marginPartition)) +
          -((actualX * actualY) *
            (unitPartition * marginPartition))
    ring_qeqv
  refine Q'.eqv_trans _
    (commonLeft +
      (actualY * actualPartition) * rightCenter - commonRight) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.add_eqv_congr_left commonLeft _ _
        (Q'.mul_eqv_congr_left (actualY * actualPartition)
          leftCenter rightCenter hcenterShift))
      (Q'.eqv_refl _)
  · simp only [commonLeft, commonRight, rightCenter]
    change
      (unitX * marginY) *
            (actualPartition * actualPartition) +
          (actualY * actualPartition) *
            (marginX * unitPartition +
              -(unitX * marginPartition)) +
        -((actualX * actualY) *
          (unitPartition * marginPartition)) ≈
        (unitX * actualPartition) *
              (marginY * actualPartition +
                -(actualY * marginPartition)) +
          (actualY * unitPartition) *
            (marginX * actualPartition +
              -(actualX * marginPartition))
    ring_qeqv

/-- The centered two-source debt factors exactly through one-source centered
scores.  Only the first source needs the termwise coupling identity; the
partition identity supplies its global counterpart. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginRawDebt_eqv_oneSource
    (S : SlabScalePair) (sourcePair : PhysicalLabellingPair)
    (hsourcePair : sourcePair ∈ pushedPhysicalSourcePairs S) :
    fineCouplingPhysicalSourcePairCenteredMarginRawDebt S sourcePair ≈
      (fineUnitCouplingPhysicalTerm S sourcePair.1 *
          S.fine.physicalPartition) *
        fineCouplingPhysicalSourceCenteredMarginRawDebt S sourcePair.2 +
      (S.fine.physicalTerm sourcePair.2 *
          fineUnitCouplingPhysicalPartition S) *
        fineCouplingPhysicalSourceCenteredMarginRawDebt S sourcePair.1 := by
  have hs := mem_cartesian_iff
    S.fine.physicalLabellings S.fine.physicalLabellings sourcePair
  have hparts : sourcePair.1 ∈ S.fine.physicalLabellings ∧
      sourcePair.2 ∈ S.fine.physicalLabellings := by
    exact hs.mp (by
      simpa only [pushedPhysicalSourcePairs] using hsourcePair)
  simpa only [fineCouplingPhysicalSourcePairCenteredMarginRawDebt,
      fineCouplingPhysicalSourcePairMarginRawMass,
      fineCouplingPhysicalSourcePairActualRawMass,
      fineCouplingPhysicalPartitionSquareMargin,
      fineCouplingPhysicalSourceCenteredMarginRawDebt] using
    (centered_pair_debt_factor_local
      (fineUnitCouplingPhysicalTerm S sourcePair.1)
      (S.fine.physicalTerm sourcePair.1)
      (fineCouplingPhysicalMarginTerm S sourcePair.1)
      (S.fine.physicalTerm sourcePair.2)
      (fineCouplingPhysicalMarginTerm S sourcePair.2)
      S.fine.physicalPartition
      (fineUnitCouplingPhysicalPartition S)
      (fineCouplingPhysicalPartitionMarginSum S)
      (1 + -S.fine.coupling)
      (fineUnitCouplingPhysicalTerm_sub_actual_eqv_margin_mul
        S sourcePair.1 hparts.1)
      (fineUnitCouplingPhysicalPartition_sub_actual_eqv_margin_mul S))

/-! ## 2. One-row face-event masses -/

def fineCouplingFaceTTEvent
    (root target : Nat) (state : EdgeLabelling) : Bool :=
  slabPhysicalFacePositiveB root state &&
    slabPhysicalFacePositiveB target state

def fineCouplingFaceFFEvent
    (root target : Nat) (state : EdgeLabelling) : Bool :=
  !(slabPhysicalFacePositiveB root state) &&
    !(slabPhysicalFacePositiveB target state)

def fineCouplingFaceFTEvent
    (root target : Nat) (state : EdgeLabelling) : Bool :=
  !(slabPhysicalFacePositiveB root state) &&
    slabPhysicalFacePositiveB target state

def fineCouplingFaceTFEvent
    (root target : Nat) (state : EdgeLabelling) : Bool :=
  slabPhysicalFacePositiveB root state &&
    !(slabPhysicalFacePositiveB target state)

/-- Mass sent by one kernel row to one Boolean output event. -/
def fineCouplingKernelOutputEventMass
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (source : EdgeLabelling) (event : EdgeLabelling → Bool) : Q' :=
  listQSum (K.kernel source)
    (S.coarse.physicalLabellings.filter event)

/-- Product-kernel mass of a Cartesian pair of output events factors into
the product of the two one-row event masses. -/
theorem fineCouplingTwoReplicaOutputPairMass_cartesian_eqv_oneRowProduct
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourcePair : PhysicalLabellingPair)
    (leftEvent rightEvent : EdgeLabelling → Bool) :
    fineCouplingTwoReplicaOutputPairMass K sourcePair
        (cartesian
          (S.coarse.physicalLabellings.filter leftEvent)
          (S.coarse.physicalLabellings.filter rightEvent)) ≈
      fineCouplingKernelOutputEventMass K sourcePair.1 leftEvent *
        fineCouplingKernelOutputEventMass K sourcePair.2 rightEvent := by
  unfold fineCouplingTwoReplicaOutputPairMass
    fineCouplingTwoReplicaKernelWeight
    fineCouplingKernelOutputEventMass
  exact listQSum_cartesian_product _ _ _ _

/-- The literal four-cell output contrast is the determinant of four
one-row event masses. -/
theorem fineCouplingTwoReplicaFourCellOutputContrast_eqv_oneRowDeterminant
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (sourcePair : PhysicalLabellingPair) :
    fineCouplingTwoReplicaFourCellOutputContrast
        K root target sourcePair ≈
      fineCouplingKernelOutputEventMass K sourcePair.1
          (fineCouplingFaceTTEvent root target) *
        fineCouplingKernelOutputEventMass K sourcePair.2
          (fineCouplingFaceFFEvent root target) -
      fineCouplingKernelOutputEventMass K sourcePair.1
          (fineCouplingFaceFTEvent root target) *
        fineCouplingKernelOutputEventMass K sourcePair.2
          (fineCouplingFaceTFEvent root target) := by
  unfold fineCouplingTwoReplicaFourCellOutputContrast
    pushedFaceRawFourCellSourcePairs pushedFaceRawFourCellTargetPairs
    fineCouplingFaceTTEvent fineCouplingFaceFFEvent
    fineCouplingFaceFTEvent fineCouplingFaceTFEvent
  exact sub_eqv_both_local
    (fineCouplingTwoReplicaOutputPairMass_cartesian_eqv_oneRowProduct
      K sourcePair _ _)
    (fineCouplingTwoReplicaOutputPairMass_cartesian_eqv_oneRowProduct
      K sourcePair _ _)

/-- The four Boolean output cells partition every physical kernel row. -/
theorem fineCouplingKernelFaceFourCellMass_eqv_one
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) (source : EdgeLabelling)
    (hsource : source ∈ S.fine.physicalLabellings) :
    (fineCouplingKernelOutputEventMass K source
          (fineCouplingFaceTTEvent root target) +
        fineCouplingKernelOutputEventMass K source
          (fineCouplingFaceTFEvent root target)) +
      (fineCouplingKernelOutputEventMass K source
          (fineCouplingFaceFTEvent root target) +
        fineCouplingKernelOutputEventMass K source
          (fineCouplingFaceFFEvent root target)) ≈ 1 := by
  let first := slabPhysicalFacePositiveB root
  let second := slabPhysicalFacePositiveB target
  let states := S.coarse.physicalLabellings
  let weight := K.kernel source
  have hsplit := listQSum_filter_partition weight first states
  have htrue := listQSum_filter_partition weight second
    (states.filter first)
  have hfalse := listQSum_filter_partition weight second
    (states.filter (fun state => !(first state)))
  rw [← filter_and_eq_filter_filter_local first second states,
    ← filter_and_eq_filter_filter_local first
      (fun state => !(second state)) states] at htrue
  rw [← filter_and_eq_filter_filter_local
      (fun state => !(first state)) second states,
    ← filter_and_eq_filter_filter_local
      (fun state => !(first state))
      (fun state => !(second state)) states] at hfalse
  have hfour :
      listQSum weight states ≈
        (listQSum weight
              (states.filter (fun state => first state && second state)) +
            listQSum weight
              (states.filter
                (fun state => first state && !(second state)))) +
          (listQSum weight
              (states.filter
                (fun state => !(first state) && second state)) +
            listQSum weight
              (states.filter
                (fun state => !(first state) && !(second state)))) := by
    exact Q'.eqv_trans _ _ _ hsplit
      (Q'.add_eqv_congr' htrue hfalse)
  refine Q'.eqv_trans _ (listQSum weight states) _ ?_ ?_
  · exact Q'.eqv_symm (by
      simpa only [fineCouplingKernelOutputEventMass,
        fineCouplingFaceTTEvent, fineCouplingFaceTFEvent,
        fineCouplingFaceFTEvent, fineCouplingFaceFFEvent,
        first, second, states, weight] using hfour)
  · exact K.row_normalized source hsource

/-! ## 3. Finite Fubini to one-replica moments -/

/-- One-replica moment of a fine source weight against one coarse-output
event probability. -/
def fineCouplingPhysicalSourceKernelEventMoment
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (sourceWeight : EdgeLabelling → Q')
    (event : EdgeLabelling → Bool) : Q' :=
  listQSum
    (fun source => sourceWeight source *
      fineCouplingKernelOutputEventMass K source event)
    S.fine.physicalLabellings

/-- The explicit one-replica expression obtained after factoring the source
debt and the product-kernel determinant. -/
def fineCouplingPhysicalCenteredMarginOneReplicaCross
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) : Q' :=
  S.fine.physicalPartition *
      (fineCouplingPhysicalSourceKernelEventMoment K
          (fineUnitCouplingPhysicalTerm S)
          (fineCouplingFaceTTEvent root target) *
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceFFEvent root target) -
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineUnitCouplingPhysicalTerm S)
          (fineCouplingFaceFTEvent root target) *
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceTFEvent root target)) +
    fineUnitCouplingPhysicalPartition S *
      (fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceTTEvent root target) *
        fineCouplingPhysicalSourceKernelEventMoment K
          S.fine.physicalTerm
          (fineCouplingFaceFFEvent root target) -
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceFTEvent root target) *
        fineCouplingPhysicalSourceKernelEventMoment K
          S.fine.physicalTerm
          (fineCouplingFaceTFEvent root target))

/-- The four one-replica moments of the centered score sum to zero.  This is
the conservation law that permits complement recodings without paying an
`L1` norm. -/
theorem fineCouplingPhysicalCenteredMarginFourCellMoments_eqv_zero
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    (fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceTTEvent root target) +
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceTFEvent root target)) +
      (fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceFTEvent root target) +
        fineCouplingPhysicalSourceKernelEventMoment K
          (fineCouplingPhysicalSourceCenteredMarginRawDebt S)
          (fineCouplingFaceFFEvent root target)) ≈ 0 := by
  let states := S.fine.physicalLabellings
  let debt := fineCouplingPhysicalSourceCenteredMarginRawDebt S
  let tt := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceTTEvent root target)
  let tf := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceTFEvent root target)
  let ft := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceFTEvent root target)
  let ff := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceFFEvent root target)
  let combined := fun source =>
    (debt source * tt source + debt source * tf source) +
      (debt source * ft source + debt source * ff source)
  have hcombine :
      listQSum combined states ≈
        (listQSum (fun source => debt source * tt source) states +
          listQSum (fun source => debt source * tf source) states) +
        (listQSum (fun source => debt source * ft source) states +
          listQSum (fun source => debt source * ff source) states) := by
    refine Q'.eqv_trans _
      (listQSum
          (fun source => debt source * tt source + debt source * tf source)
          states +
        listQSum
          (fun source => debt source * ft source + debt source * ff source)
          states) _ ?_ ?_
    · unfold combined
      exact listQSum_add _ _ _
    · exact Q'.add_eqv_congr'
        (listQSum_add _ _ _)
        (listQSum_add _ _ _)
  refine Q'.eqv_trans _ (listQSum combined states) _ ?_ ?_
  · exact Q'.eqv_symm (by
      simpa only [fineCouplingPhysicalSourceKernelEventMoment,
        states, debt, tt, tf, ft, ff] using hcombine)
  refine Q'.eqv_trans _ (listQSum debt states) _ ?_ ?_
  · apply listQSum_congr_on
    intro source hsource
    refine Q'.eqv_trans _
      (debt source *
        ((tt source + tf source) + (ft source + ff source))) _ ?_ ?_
    · unfold combined
      refine Q'.eqv_trans _
        (debt source * (tt source + tf source) +
          debt source * (ft source + ff source)) _ ?_ ?_
      · exact Q'.add_eqv_congr'
          (Q'.eqv_symm
            (Q'.mul_add_eqv (debt source) (tt source) (tf source)))
          (Q'.eqv_symm
            (Q'.mul_add_eqv (debt source) (ft source) (ff source)))
      · exact Q'.eqv_symm
          (Q'.mul_add_eqv (debt source)
            (tt source + tf source) (ft source + ff source))
    refine Q'.eqv_trans _ (debt source * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (debt source) _ _ (by
        simpa only [tt, tf, ft, ff] using
          (fineCouplingKernelFaceFourCellMass_eqv_one
            K root target source hsource))
    · exact Q'.mul_one_eqv _
  · simpa only [states, debt] using
      (fineCouplingPhysicalSourceCenteredMarginRawDebt_total_eqv_zero S)

private theorem listQSum_cartesian_weighted_determinant_local
    {X : Type} (states : List X)
    (scaleLeft scaleRight : Q')
    (unit actual debt tt ff ft tf : X → Q') :
    listQSum
        (fun pair =>
          (((unit pair.1 * scaleLeft) * debt pair.2 +
              (actual pair.2 * scaleRight) * debt pair.1) *
            (tt pair.1 * ff pair.2 - ft pair.1 * tf pair.2)))
        (cartesian states states) ≈
      scaleLeft *
          (listQSum (fun x => unit x * tt x) states *
              listQSum (fun x => debt x * ff x) states -
            listQSum (fun x => unit x * ft x) states *
              listQSum (fun x => debt x * tf x) states) +
        scaleRight *
          (listQSum (fun x => debt x * tt x) states *
              listQSum (fun x => actual x * ff x) states -
            listQSum (fun x => debt x * ft x) states *
              listQSum (fun x => actual x * tf x) states) := by
  let leftTerm := fun pair : X × X =>
    scaleLeft *
      ((unit pair.1 * tt pair.1) * (debt pair.2 * ff pair.2) -
        (unit pair.1 * ft pair.1) * (debt pair.2 * tf pair.2))
  let rightTerm := fun pair : X × X =>
    scaleRight *
      ((debt pair.1 * tt pair.1) * (actual pair.2 * ff pair.2) -
        (debt pair.1 * ft pair.1) * (actual pair.2 * tf pair.2))
  refine Q'.eqv_trans _
    (listQSum (fun pair => leftTerm pair + rightTerm pair)
      (cartesian states states)) _ ?_ ?_
  · apply listQSum_congr_on
    intro pair _
    simp only [leftTerm, rightTerm]
    let left := (unit pair.1 * scaleLeft) * debt pair.2
    let right := (actual pair.2 * scaleRight) * debt pair.1
    let positive := tt pair.1 * ff pair.2
    let negative := ft pair.1 * tf pair.2
    refine Q'.eqv_trans _
      ((left * positive - left * negative) +
        (right * positive - right * negative)) _ ?_ ?_
    · simpa only [left, right, positive, negative] using
        (add_mul_sub_expand_local left right positive negative)
    apply Q'.add_eqv_congr'
    · refine Q'.eqv_trans _
        (scaleLeft *
            ((unit pair.1 * tt pair.1) *
              (debt pair.2 * ff pair.2)) -
          scaleLeft *
            ((unit pair.1 * ft pair.1) *
              (debt pair.2 * tf pair.2))) _ ?_ ?_
      · apply sub_eqv_both_local
        · simp only [left, positive]
          ring_qeqv
        · simp only [left, negative]
          ring_qeqv
      · exact Q'.eqv_symm
          (mul_sub_expand_local scaleLeft _ _)
    · refine Q'.eqv_trans _
        (scaleRight *
            ((debt pair.1 * tt pair.1) *
              (actual pair.2 * ff pair.2)) -
          scaleRight *
            ((debt pair.1 * ft pair.1) *
              (actual pair.2 * tf pair.2))) _ ?_ ?_
      · apply sub_eqv_both_local
        · simp only [right, positive]
          ring_qeqv
        · simp only [right, negative]
          ring_qeqv
      · exact Q'.eqv_symm
          (mul_sub_expand_local scaleRight _ _)
  refine Q'.eqv_trans _
    (listQSum leftTerm (cartesian states states) +
      listQSum rightTerm (cartesian states states)) _ ?_ ?_
  · exact listQSum_add _ _ _
  apply Q'.add_eqv_congr'
  · refine Q'.eqv_trans _
      (scaleLeft *
        listQSum
          (fun pair =>
            (unit pair.1 * tt pair.1) * (debt pair.2 * ff pair.2) -
              (unit pair.1 * ft pair.1) * (debt pair.2 * tf pair.2))
          (cartesian states states)) _ ?_ ?_
    · unfold leftTerm
      exact listQSum_mul_left _ _ _
    apply Q'.mul_eqv_congr_left
    refine Q'.eqv_trans _
      (listQSum
          (fun pair =>
            (unit pair.1 * tt pair.1) * (debt pair.2 * ff pair.2))
          (cartesian states states) -
        listQSum
          (fun pair =>
            (unit pair.1 * ft pair.1) * (debt pair.2 * tf pair.2))
          (cartesian states states)) _ ?_ ?_
    · exact Q'.eqv_symm (listQSum_sub_local _ _ _)
    · exact sub_eqv_both_local
        (listQSum_cartesian_product
          (fun x => unit x * tt x) (fun x => debt x * ff x)
          states states)
        (listQSum_cartesian_product
          (fun x => unit x * ft x) (fun x => debt x * tf x)
          states states)
  · refine Q'.eqv_trans _
      (scaleRight *
        listQSum
          (fun pair =>
            (debt pair.1 * tt pair.1) * (actual pair.2 * ff pair.2) -
              (debt pair.1 * ft pair.1) * (actual pair.2 * tf pair.2))
          (cartesian states states)) _ ?_ ?_
    · unfold rightTerm
      exact listQSum_mul_left _ _ _
    apply Q'.mul_eqv_congr_left
    refine Q'.eqv_trans _
      (listQSum
          (fun pair =>
            (debt pair.1 * tt pair.1) * (actual pair.2 * ff pair.2))
          (cartesian states states) -
        listQSum
          (fun pair =>
            (debt pair.1 * ft pair.1) * (actual pair.2 * tf pair.2))
          (cartesian states states)) _ ?_ ?_
    · exact Q'.eqv_symm (listQSum_sub_local _ _ _)
    · exact sub_eqv_both_local
        (listQSum_cartesian_product
          (fun x => debt x * tt x) (fun x => actual x * ff x)
          states states)
        (listQSum_cartesian_product
          (fun x => debt x * ft x) (fun x => actual x * tf x)
          states states)

/-- The signed two-source debt average contracts exactly to four products of
one-replica centered event moments.  No absolute value or triangle
inequality occurs in this reduction. -/
theorem fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_eqv_oneReplica
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
        K root target ≈
      fineCouplingPhysicalCenteredMarginOneReplicaCross K root target := by
  let states := S.fine.physicalLabellings
  let unit := fineUnitCouplingPhysicalTerm S
  let actual := S.fine.physicalTerm
  let debt := fineCouplingPhysicalSourceCenteredMarginRawDebt S
  let tt := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceTTEvent root target)
  let ff := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceFFEvent root target)
  let ft := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceFTEvent root target)
  let tf := fun source => fineCouplingKernelOutputEventMass K source
    (fineCouplingFaceTFEvent root target)
  refine Q'.eqv_trans _
    (listQSum
      (fun sourcePair =>
        (((unit sourcePair.1 * S.fine.physicalPartition) *
              debt sourcePair.2 +
            (actual sourcePair.2 *
              fineUnitCouplingPhysicalPartition S) * debt sourcePair.1) *
          (tt sourcePair.1 * ff sourcePair.2 -
            ft sourcePair.1 * tf sourcePair.2)))
      (cartesian states states)) _ ?_ ?_
  · unfold fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage
      pushedPhysicalSourcePairs
    apply listQSum_congr_on
    intro sourcePair hsourcePair
    exact mul_eqv_both_local
      (by simpa only [states, unit, actual, debt] using
        (fineCouplingPhysicalSourcePairCenteredMarginRawDebt_eqv_oneSource
          S sourcePair (by
            simpa only [states, pushedPhysicalSourcePairs] using hsourcePair)))
      (by simpa only [tt, ff, ft, tf] using
        (fineCouplingTwoReplicaFourCellOutputContrast_eqv_oneRowDeterminant
          K root target sourcePair))
  · simpa only [fineCouplingPhysicalCenteredMarginOneReplicaCross,
      fineCouplingPhysicalSourceKernelEventMoment,
      states, unit, actual, debt, tt, ff, ft, tf] using
      (listQSum_cartesian_weighted_determinant_local
        states S.fine.physicalPartition
        (fineUnitCouplingPhysicalPartition S)
        unit actual debt tt ff ft tf)

/-- Direct normalized-margin identity in one-replica form. -/
theorem fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_oneReplica
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingCenteredNormalizedMarginNumerator K root target ≈
      fineCouplingPhysicalCenteredMarginOneReplicaCross K root target := by
  exact Q'.eqv_trans _ _ _
    (fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_sourcePairAverage
      K root target)
    (fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_eqv_oneReplica
      K root target)

#print axioms fineCouplingPhysicalSourceCenteredMarginRawDebt
#print axioms fineCouplingPhysicalSourceCenteredMarginRawDebt_total_eqv_zero
#print axioms fineCouplingPhysicalSourcePairCenteredMarginRawDebt_eqv_oneSource
#print axioms fineCouplingKernelOutputEventMass
#print axioms fineCouplingTwoReplicaOutputPairMass_cartesian_eqv_oneRowProduct
#print axioms fineCouplingTwoReplicaFourCellOutputContrast_eqv_oneRowDeterminant
#print axioms fineCouplingKernelFaceFourCellMass_eqv_one
#print axioms fineCouplingPhysicalSourceKernelEventMoment
#print axioms fineCouplingPhysicalCenteredMarginOneReplicaCross
#print axioms fineCouplingPhysicalCenteredMarginFourCellMoments_eqv_zero
#print axioms fineCouplingPhysicalSourcePairCenteredMarginDebtCrossAverage_eqv_oneReplica
#print axioms fineUnitCouplingCenteredNormalizedMarginNumerator_eqv_oneReplica

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOneReplica
