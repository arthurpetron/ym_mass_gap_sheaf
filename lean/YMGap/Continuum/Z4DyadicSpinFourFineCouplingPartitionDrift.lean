/-
# Partition drift inside the coupling-one reference scale defect

The coupling-one reference from the preceding module changes two logically
different objects at once: the pushed receiver cross is evaluated with the
fine coupling-one mass, while its coarse comparison is still multiplied by
the *actual* fine partition square.  This module separates those effects.

It introduces the balanced coupling-one blocking defect, in which both the
fine cross and the fine partition are evaluated at coupling one, and proves
the exact identity

  referenceScaleDefect
    = balancedBlockingDefect
        - (unitPartition^2 - actualPartition^2) * coarseCross.

The partition-square loss is nonnegative below coupling one and is bounded
by the already proved global Casimir moment times the explicit matched-AF
factor `2*g^2`.  Thus the previous reference-calibration hypothesis splits
into an honest blocking-law comparison and an explicit global-normalization
term.  This exposes, rather than conceals, the possible growing-volume cost
of a global coupling-one interpolation.

Nothing here proves that either residual has a volume-uniform ceiling, takes
a cutoff or continuum limit, constructs the OS/GNS theory, or proves the
Yang--Mills mass gap.

Constructive contract: finite rational sums, monotonicity, and exact rational
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

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
    (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle =>
      Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_mono_local left right tail
          (fun item hitem => hle item
            (List.mem_cons_of_mem head hitem)))

private theorem diffSquares_local (u v : Q') :
    (u + -v) * (u + v) ≈ u * u + -(v * v) := by
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.QPoly.q_add_mul u (-v) (u + v)) ?_
  refine Q'.eqv_trans _ _ _
    (YMGap.Constructive.QPoly.q_add_congr
      (Q'.mul_add_eqv u u v)
      (Q'.mul_add_eqv (-v) u v)) ?_
  have hleft : (-v) * u ≈ -(u * v) :=
    Q'.eqv_trans _ _ _ (Q'.neg_mul_eqv v u)
      (Q'.neg_eqv_congr _ _ (Q'.mul_comm_eqv v u))
  have hright : (-v) * v ≈ -(v * v) := Q'.neg_mul_eqv v v
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left _ _ _
      (YMGap.Constructive.QPoly.q_add_congr hleft hright)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + u * v)
      (-(u * v) + -(v * v)) (-(v * v) + -(u * v))
      (Q'.add_comm_eqv (-(u * v)) (-(v * v)))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_swap_inner (u * u) (u * v) (-(v * v)) (-(u * v))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_left (u * u + -(v * v))
      (u * v + -(u * v)) 0 (Q'.add_neg_self_eqv (u * v))) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' (u * u + -(v * v)))

private theorem neg_sub_local (left right : Q') :
    -(left + -right) ≈ right + -left := by
  refine Q'.eqv_trans _ (-left + -(-right)) _
    (Q'.neg_add_eqv left (-right)) ?_
  refine Q'.eqv_trans _ (-left + right) _
    (Q'.add_eqv_congr_left (-left) _ _ (Q'.neg_neg_eqv right)) ?_
  exact Q'.add_comm_eqv (-left) right

private theorem sub_split_local (A B C : Q') :
    A + -B ≈ (A + -C) + (C + -B) := by
  apply Q'.eqv_symm
  refine Q'.eqv_trans _ (A + (-C + (C + -B))) _
    (Q'.add_assoc_eqv A (-C) (C + -B)) ?_
  refine Q'.eqv_trans _ (A + ((-C + C) + -B)) _
    (Q'.add_eqv_congr_left A _ _
      (Q'.eqv_symm (Q'.add_assoc_eqv (-C) C (-B)))) ?_
  refine Q'.eqv_trans _ (A + ((0 : Q') + -B)) _
    (Q'.add_eqv_congr_left A _ _
      (Q'.add_eqv_congr_right _ _ (-B) (Q'.neg_add_self_eqv C))) ?_
  exact Q'.add_eqv_congr_left A _ _
    (Q'.eqv_of_eq (Q'.zero_add' (-B)))

private theorem scaleReferenceRecenter_local
    (actualSquare unitSquare cross common : Q') :
    actualSquare * cross + -common ≈
      (unitSquare * cross + -common) +
        -((unitSquare + -actualSquare) * cross) := by
  let actualCross := actualSquare * cross
  let unitCross := unitSquare * cross
  have hdelta :
      (unitSquare + -actualSquare) * cross ≈
        unitCross + -actualCross := by
    refine Q'.eqv_trans _
      (unitSquare * cross + (-actualSquare) * cross) _
      (Q'.add_mul_eqv unitSquare (-actualSquare) cross) ?_
    exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_mul_eqv actualSquare cross)
  have hreverse :
      actualCross + -unitCross ≈
        -((unitSquare + -actualSquare) * cross) := by
    refine Q'.eqv_trans _ (-(unitCross + -actualCross)) _
      (Q'.eqv_symm (neg_sub_local unitCross actualCross)) ?_
    exact Q'.neg_eqv_congr _ _ (Q'.eqv_symm hdelta)
  refine Q'.eqv_trans _
    ((actualCross + -unitCross) + (unitCross + -common)) _
    (by
      simpa only [actualCross, unitCross] using
        (sub_split_local actualCross common unitCross)) ?_
  refine Q'.eqv_trans _
    (-((unitSquare + -actualSquare) * cross) +
      (unitCross + -common)) _
    (Q'.add_eqv_congr_right _ _ _ hreverse) ?_
  exact Q'.add_comm_eqv
    (-((unitSquare + -actualSquare) * cross))
    (unitCross + -common)

private theorem physicalPartition_nonnegative (D : SlabPhysicalData) :
    (0 : Q') ≤ D.physicalPartition :=
  Q'.le_of_lt
    (slabParametricKPhysicalPartition_pos
      D.coupling_nonnegative D.cutoff D.extent)

/-! ## 1. Monotone partition loss -/

/-- Below coupling one, the actual fine partition is bounded by the literal
coupling-one partition on the same finite carrier. -/
theorem finePhysicalPartition_le_unitCoupling
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1) :
    S.fine.physicalPartition ≤ fineUnitCouplingPhysicalPartition S := by
  unfold fineUnitCouplingPhysicalPartition
    SlabPhysicalData.physicalPartition
    YMGap.Continuum.Z4HalfTimeReflectionPartition.slabParametricKPhysicalPartition
    SlabPhysicalData.physicalLabellings
    SlabPhysicalData.faceEdges
  apply listQSum_mono_local
  intro source hsource
  simpa only [fineUnitCouplingPhysicalTerm] using
    (slabParametricKPhysicalTerm_le_atOne
      S.fine.coupling_nonnegative hfineCoupling_le_one
      S.fine.cutoff S.fine.extent source hsource)

/-- The coupling-one fine partition is nonnegative. -/
theorem fineUnitCouplingPhysicalPartition_nonnegative
    (S : SlabScalePair) :
    (0 : Q') ≤ fineUnitCouplingPhysicalPartition S := by
  unfold fineUnitCouplingPhysicalPartition
  apply listQSum_nonnegative_on
  intro source _
  exact slabParametricKPhysicalTerm_nonnegative
    (by decide : (0 : Q') ≤ (1 : Q'))
    S.fine.cutoff S.fine.extent source

/-- Loss of fine partition square caused by globally replacing the actual
coupling by one. -/
def fineUnitCouplingPhysicalPartitionSquareLoss
    (S : SlabScalePair) : Q' :=
  fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S -
    S.fine.physicalPartition * S.fine.physicalPartition

/-- The partition-square loss factors into the partition loss times the
partition sum. -/
theorem fineUnitCouplingPhysicalPartitionSquareLoss_eqv_factorized
    (S : SlabScalePair) :
    fineUnitCouplingPhysicalPartitionSquareLoss S ≈
      (fineUnitCouplingPhysicalPartition S - S.fine.physicalPartition) *
        (fineUnitCouplingPhysicalPartition S + S.fine.physicalPartition) := by
  unfold fineUnitCouplingPhysicalPartitionSquareLoss
  change
    fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S +
        -(S.fine.physicalPartition * S.fine.physicalPartition) ≈
      (fineUnitCouplingPhysicalPartition S +
          -S.fine.physicalPartition) *
        (fineUnitCouplingPhysicalPartition S + S.fine.physicalPartition)
  exact Q'.eqv_symm
    (diffSquares_local
      (fineUnitCouplingPhysicalPartition S) S.fine.physicalPartition)

/-- The partition-square loss is nonnegative below coupling one. -/
theorem fineUnitCouplingPhysicalPartitionSquareLoss_nonnegative
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1) :
    (0 : Q') ≤ fineUnitCouplingPhysicalPartitionSquareLoss S := by
  apply Q'.sub_nonneg_of_le
  have hpartition :=
    finePhysicalPartition_le_unitCoupling S hfineCoupling_le_one
  have hactual0 := physicalPartition_nonnegative S.fine
  have hunit0 := fineUnitCouplingPhysicalPartition_nonnegative S
  exact Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _
      S.fine.physicalPartition hpartition hactual0)
    (Q'.mul_le_mul_of_nonneg_left _ _
      (fineUnitCouplingPhysicalPartition S) hpartition hunit0)

/-- The matched-AF partition-square loss has the explicit `2*g^2`
prefactor.  The remaining multiplier contains the total, hence potentially
volume-dependent, coupling-one Casimir moment. -/
theorem fineUnitCouplingPhysicalPartitionSquareLoss_le_two_square_mul_globalMoment
    (S : SlabScalePair)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g) :
    fineUnitCouplingPhysicalPartitionSquareLoss S ≤
      (Q'.ofNat 2 * (g * g)) *
        (fineUnitCouplingPhysicalCasimirMoment S *
          (fineUnitCouplingPhysicalPartition S +
            S.fine.physicalPartition)) := by
  have hloss :=
    fineUnitCouplingPhysicalPartition_sub_actual_le_two_square_mul_moment
      S hfineCoupling_le_one family law g hg hgle hcoupling
  have hsum0 :
      (0 : Q') ≤ fineUnitCouplingPhysicalPartition S +
        S.fine.physicalPartition :=
    Q'.zero_le_add _ _
      (fineUnitCouplingPhysicalPartition_nonnegative S)
      (physicalPartition_nonnegative S.fine)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (fineUnitCouplingPhysicalPartitionSquareLoss_eqv_factorized S)) ?_
  refine Q'.le_trans' _ _ _
    (Q'.mul_le_mul_of_nonneg_right _ _
      (fineUnitCouplingPhysicalPartition S + S.fine.physicalPartition)
      hloss hsum0) ?_
  exact Q'.le_of_eqv (by ring_qeqv)

/-! ## 2. Balanced blocking defect and exact second recentering -/

/-- Coupling-one blocking defect with both the pushed fine cross and its fine
normalization evaluated at coupling one. -/
def fineUnitCouplingBalancedRawColumnScaleDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  (fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S) *
      coarseObservableFourCellRawColumnCross S root target -
    (S.coarse.physicalPartition * S.coarse.physicalPartition) *
      fineUnitCouplingPushedRawColumnCross
        (physicalKernel S hfineCutoff hcoarseCoupling) root target

/-- Exact separation of the coupling-one reference defect into a balanced
blocking-law residual and the global fine-partition drift. -/
theorem fineUnitCouplingReferenceRawColumnScaleDefect_eqv_balanced_sub_partitionDrift
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    fineUnitCouplingReferenceRawColumnScaleDefect
        S hfineCutoff hcoarseCoupling root target ≈
      fineUnitCouplingBalancedRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target -
        fineUnitCouplingPhysicalPartitionSquareLoss S *
          coarseObservableFourCellRawColumnCross S root target := by
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let coarseCross := coarseObservableFourCellRawColumnCross S root target
  let unitCross := fineUnitCouplingPushedRawColumnCross
    (physicalKernel S hfineCutoff hcoarseCoupling) root target
  unfold fineUnitCouplingReferenceRawColumnScaleDefect
    fineUnitCouplingBalancedRawColumnScaleDefect
    fineUnitCouplingPhysicalPartitionSquareLoss
  change
    actualSquare * coarseCross + -(coarseSquare * unitCross) ≈
      (unitSquare * coarseCross + -(coarseSquare * unitCross)) +
        -((unitSquare + -actualSquare) * coarseCross)
  exact scaleReferenceRecenter_local
    actualSquare unitSquare coarseCross (coarseSquare * unitCross)

/-- Absolute reference defect bounded by the balanced blocking residual plus
the explicit partition-drift payment. -/
theorem fineUnitCouplingReferenceRawColumnScaleDefect_abs_le_balanced_add_partitionDrift
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingReferenceRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs
          (fineUnitCouplingBalancedRawColumnScaleDefect
            S hfineCutoff hcoarseCoupling root target) +
        fineUnitCouplingPhysicalPartitionSquareLoss S *
          Q'.abs (coarseObservableFourCellRawColumnCross S root target) := by
  let balanced := fineUnitCouplingBalancedRawColumnScaleDefect
    S hfineCutoff hcoarseCoupling root target
  let loss := fineUnitCouplingPhysicalPartitionSquareLoss S
  let cross := coarseObservableFourCellRawColumnCross S root target
  have hrecenter :
      fineUnitCouplingReferenceRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target ≈
        balanced + -(loss * cross) := by
    simpa only [balanced, loss, cross] using
      (fineUnitCouplingReferenceRawColumnScaleDefect_eqv_balanced_sub_partitionDrift
        S hfineCutoff hcoarseCoupling root target)
  have hloss0 : (0 : Q') ≤ loss := by
    simpa only [loss] using
      (fineUnitCouplingPhysicalPartitionSquareLoss_nonnegative
        S hfineCoupling_le_one)
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hrecenter))
    (Q'.le_trans' _ _ _
      (Q'.abs_add_le' balanced (-(loss * cross))) ?_)
  apply Q'.add_le_add_left
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_neg' (loss * cross)))
    (Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le loss cross) ?_)
  exact Q'.le_of_eqv
    (Q'.mul_eqv_congr_right _ _ (Q'.abs cross)
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hloss0))

/-- Matched-AF form of the second recentering.  It isolates the total
coupling-one Casimir moment as the sole normalization payment introduced by
the global reference. -/
theorem fineUnitCouplingReferenceRawColumnScaleDefect_abs_le_balanced_add_two_square_mul_globalMoment
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (hfineCoupling_le_one : S.fine.coupling ≤ 1)
    (family : MatchedBlockFamily)
    (law : CubicMarginLaw family)
    (g : Q') (hg : (0 : Q') < g) (hgle : g ≤ law.g₁)
    (hcoupling : S.fine.coupling = blockedWeight family g)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingReferenceRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.abs
          (fineUnitCouplingBalancedRawColumnScaleDefect
            S hfineCutoff hcoarseCoupling root target) +
        ((Q'.ofNat 2 * (g * g)) *
          (fineUnitCouplingPhysicalCasimirMoment S *
            (fineUnitCouplingPhysicalPartition S +
              S.fine.physicalPartition))) *
          Q'.abs (coarseObservableFourCellRawColumnCross S root target) := by
  have hbase :=
    fineUnitCouplingReferenceRawColumnScaleDefect_abs_le_balanced_add_partitionDrift
      S hfineCutoff hcoarseCoupling hfineCoupling_le_one root target
  have hloss :=
    fineUnitCouplingPhysicalPartitionSquareLoss_le_two_square_mul_globalMoment
      S hfineCoupling_le_one family law g hg hgle hcoupling
  exact Q'.le_trans' _ _ _ hbase
    (Q'.add_le_add_left _ _ _
      (Q'.mul_le_mul_of_nonneg_right _ _
        (Q'.abs (coarseObservableFourCellRawColumnCross S root target))
        hloss
        (Q'.abs_nonneg _)))

/-! ## 3. Honest calibration interfaces -/

/-- The genuinely scale-matching part of the coupling-one reference: the
unit-normalized pushed fine law versus the explicitly decimated coarse law. -/
def FineUnitCouplingBalancedRawColumnScaleDefectCalibration
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g balancedCeiling : Q') : Prop :=
  Q'.abs
      (fineUnitCouplingBalancedRawColumnScaleDefect
        S hfineCutoff hcoarseCoupling root target) ≤
    (balancedCeiling * (g * g)) *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

/-- Explicit normalized global-moment input needed by the global
coupling-one interpolation.  Unlike the receiver-local moment, this contains
the Casimir exponent summed over the entire fine slab. -/
def FineUnitCouplingGlobalPartitionCasimirNormalization
    (S : SlabScalePair) (root target : Nat)
    (globalCeiling : Q') : Prop :=
  (fineUnitCouplingPhysicalCasimirMoment S *
      (fineUnitCouplingPhysicalPartition S +
        S.fine.physicalPartition)) *
      Q'.abs (coarseObservableFourCellRawColumnCross S root target) ≤
    globalCeiling *
      ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
        (S.fine.physicalPartition * S.fine.physicalPartition))

#print axioms finePhysicalPartition_le_unitCoupling
#print axioms fineUnitCouplingPhysicalPartition_nonnegative
#print axioms fineUnitCouplingPhysicalPartitionSquareLoss
#print axioms fineUnitCouplingPhysicalPartitionSquareLoss_eqv_factorized
#print axioms fineUnitCouplingPhysicalPartitionSquareLoss_nonnegative
#print axioms fineUnitCouplingPhysicalPartitionSquareLoss_le_two_square_mul_globalMoment
#print axioms fineUnitCouplingBalancedRawColumnScaleDefect
#print axioms fineUnitCouplingReferenceRawColumnScaleDefect_eqv_balanced_sub_partitionDrift
#print axioms fineUnitCouplingReferenceRawColumnScaleDefect_abs_le_balanced_add_partitionDrift
#print axioms fineUnitCouplingReferenceRawColumnScaleDefect_abs_le_balanced_add_two_square_mul_globalMoment
#print axioms FineUnitCouplingBalancedRawColumnScaleDefectCalibration
#print axioms FineUnitCouplingGlobalPartitionCasimirNormalization

end YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift
