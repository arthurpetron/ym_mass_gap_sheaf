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

The finite carrier layer is now made explicit: each coarse and coupling-one
four-cell cross is bounded by twice the corresponding positive partition
square, and the balanced coupling-one scale defect is bounded by
`4 * Z_coarse^2 * Z_unit^2`.  This is a finite carrier envelope only.  The
unit partition is not the actual-fine normalized partition, so the
cutoff/volume-uniform balanced calibration remains open.  The explicit
`fineUnitCouplingBalancedCarrierCeiling` divides this finite envelope by
`g^2 * actualPartition^2` and compiles it into
`FineUnitCouplingBalancedRawColumnScaleDefectCalibration`; its dependence on
the displayed finite parameters is part of the statement.

Constructive contract: finite rational sums, monotonicity, and exact rational
algebra only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
import YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction

namespace YMGap.Continuum.Z4DyadicSpinFourFineCouplingPartitionDrift

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFiniteCoreReduction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableFiniteVolumeVacuumStrictness
open YMGap.Continuum.CompactDualSlabObservableHighSpinCoreCarrier
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceCross
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferencePerturbation
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingReferenceScaleDefect
open YMGap.Continuum.Z4DyadicSpinFourReceiverRawColumnCrossCalibration

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

private theorem two_mul_eqv_local (a : Q') :
    (Q'.ofNat 2 * a).eqv (a + a) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 2) (1 + 1) a (by decide)) ?_
  refine Q'.eqv_trans _ _ _ (Q'.add_mul_eqv 1 1 a) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr_right (1 * a) a (1 * a) (Q'.one_mul_eqv a)) ?_
  exact Q'.add_eqv_congr_left a (1 * a) a (Q'.one_mul_eqv a)

private theorem four_mul_eqv_local (a : Q') :
    (Q'.ofNat 4 * a).eqv ((a + a) + (a + a)) := by
  have hfour : (Q'.ofNat 4).eqv (Q'.ofNat 2 + Q'.ofNat 2) := by
    decide
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right (Q'.ofNat 4)
      (Q'.ofNat 2 + Q'.ofNat 2) a hfour) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.add_mul_eqv (Q'.ofNat 2) (Q'.ofNat 2) a) ?_
  exact Q'.add_eqv_congr'
    (two_mul_eqv_local a) (two_mul_eqv_local a)

private theorem abs_nonnegative_factor_eqv_local
    (a b : Q') (ha : (0 : Q') ≤ a) :
    Q'.abs a * b ≈ a * b :=
  Q'.mul_eqv_congr_right _ _ _
    (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg ha)

private theorem abs_sub_le_abs_add_local (a b : Q') :
    Q'.abs (a - b) ≤ Q'.abs a + Q'.abs b := by
  change Q'.abs (a + (-b)) ≤ Q'.abs a + Q'.abs b
  exact Q'.le_trans' _ _ _ (Q'.abs_add_le' a (-b))
    (Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.eqv_refl (Q'.abs a))
        (YMGap.Continuum.TsumDeriv.Q'.abs_neg b)))

private theorem two_cross_regroup_local (a b : Q') :
    a * (Q'.ofNat 2 * b) + b * (Q'.ofNat 2 * a) ≈
      ((b * a) + (b * a)) + ((b * a) + (b * a)) := by
  refine Q'.eqv_trans _ _ _
    (Q'.add_eqv_congr'
      (Q'.mul_eqv_congr_left _ _ _ (two_mul_eqv_local b))
      (Q'.mul_eqv_congr_left _ _ _ (two_mul_eqv_local a))) ?_
  ring_qeqv

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

private theorem abs_sub_nonnegative_le_add_local
    {a b : Q'} (ha : (0 : Q') ≤ a) (hb : (0 : Q') ≤ b) :
    Q'.abs (a - b) ≤ a + b := by
  change Q'.abs (a + (-b)) ≤ a + b
  refine Q'.le_trans' _ _ _ (Q'.abs_add_le' a (-b)) ?_
  refine Q'.add_le_add ?_ ?_
  · exact Q'.le_of_eqv
      (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg ha)
  · exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _
        (YMGap.Continuum.TsumDeriv.Q'.abs_neg b)
        (YMGap.Continuum.TsumDeriv.Q'.abs_of_nonneg hb))

private theorem pushedSourcePair_components_mem_local
    {S : SlabScalePair} {root target : Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hpair : pair ∈ pushedFaceRawFourCellSourcePairs
      (S := S) root target) :
    pair.1 ∈ S.coarse.physicalLabellings ∧
      pair.2 ∈ S.coarse.physicalLabellings := by
  unfold pushedFaceRawFourCellSourcePairs at hpair
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact ⟨(List.mem_filter.mp hmembers.1).1,
    (List.mem_filter.mp hmembers.2).1⟩

private theorem pushedTargetPair_components_mem_local
    {S : SlabScalePair} {root target : Nat}
    {pair : EdgeLabelling × EdgeLabelling}
    (hpair : pair ∈ pushedFaceRawFourCellTargetPairs
      (S := S) root target) :
    pair.1 ∈ S.coarse.physicalLabellings ∧
      pair.2 ∈ S.coarse.physicalLabellings := by
  unfold pushedFaceRawFourCellTargetPairs at hpair
  have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
  exact ⟨(List.mem_filter.mp hmembers.1).1,
    (List.mem_filter.mp hmembers.2).1⟩

private theorem pushedFaceRawFourCellSourcePairs_nodup_local
    (S : SlabScalePair) (root target : Nat) :
    (pushedFaceRawFourCellSourcePairs (S := S) root target).Nodup := by
  unfold pushedFaceRawFourCellSourcePairs
  apply cartesian_nodup
  · exact (List.filter_sublist.nodup
      (slabPhysicalLabellings_nodup S.coarse))
  · exact (List.filter_sublist.nodup
      (slabPhysicalLabellings_nodup S.coarse))

private theorem pushedFaceRawFourCellTargetPairs_nodup_local
    (S : SlabScalePair) (root target : Nat) :
    (pushedFaceRawFourCellTargetPairs (S := S) root target).Nodup := by
  unfold pushedFaceRawFourCellTargetPairs
  apply cartesian_nodup
  · exact (List.filter_sublist.nodup
      (slabPhysicalLabellings_nodup S.coarse))
  · exact (List.filter_sublist.nodup
      (slabPhysicalLabellings_nodup S.coarse))

private theorem pushedTargetPairRawMass_nonnegative_local
    {S : SlabScalePair} (K : S.FiniteSlabKernel)
    {pair : EdgeLabelling × EdgeLabelling}
    (hleft : pair.1 ∈ S.coarse.physicalLabellings)
    (hright : pair.2 ∈ S.coarse.physicalLabellings) :
    (0 : Q') ≤ fineUnitCouplingPushedTargetPairRawMass K pair := by
  unfold fineUnitCouplingPushedTargetPairRawMass
  exact Q'.mul_nonneg _ _
    (fineUnitCouplingPushedTargetRawMass_nonnegative K hleft)
    (fineUnitCouplingPushedTargetRawMass_nonnegative K hright)

private theorem coarsePairRawMass_nonnegative_local
    {D : SlabPhysicalData} {root : Nat}
    (pair : SlabObservableTwoReplicaPair D root) :
    (0 : Q') ≤ slabObservableTwoReplicaPairWeight D pair :=
  slabObservableTwoReplicaPairWeight_nonnegative D root pair

private theorem coarseSourcePair_mem_positiveTimesAll_local
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellSourcePairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have hsource :=
    (mem_cartesian_iff
      (slabObservableRootTargetEntries D root target)
      (slabObservableRootComplementTargetComplementEntries D root target)
      pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp hsource.1).1,
    (List.mem_filter.mp hsource.2).1⟩

private theorem coarseTargetPair_mem_positiveTimesAll_local
    (D : SlabPhysicalData) (root target : Nat)
    (pair : SlabObservableTwoReplicaPair D root)
    (hpair : pair ∈ slabObservableFourCellTargetPairs D root target) :
    pair ∈ slabObservablePositiveTimesAllPairs D root := by
  have htarget :=
    (mem_cartesian_iff
      (slabObservableRootTargetComplementEntries D root target)
      (slabObservableRootComplementTargetEntries D root target)
      pair).mp hpair
  apply (mem_cartesian_iff
    (slabObservablePositiveSourceEntries D root)
    (slabExpandedFineSourceEntries D) pair).mpr
  exact ⟨(List.mem_filter.mp htarget.1).1,
    (List.mem_filter.mp htarget.2).1⟩

private theorem coarsePositiveTimesAllPairs_nodup_local
    (D : SlabPhysicalData) (root : Nat) :
    (slabObservablePositiveTimesAllPairs D root).Nodup := by
  unfold slabObservablePositiveTimesAllPairs
  apply cartesian_nodup
  · unfold slabObservablePositiveSourceEntries
    exact attach_nodup_of_nodup _
      (slabObservablePositiveExpandedSources_nodup D root)
  · exact slabExpandedFineSourceEntries_nodup D

private theorem coarsePositiveSourceWeight_le_partition_local
    (D : SlabPhysicalData) (root : Nat) :
    slabObservablePositiveSourceWeight D root ≤ D.physicalPartition := by
  have hpositiveAdd :=
    slabObservablePositiveSourceWeight_add_one_le_partition D root
  exact Q'.le_trans' _ _ _
    (Q'.add_le_self_of_nonneg
      (slabObservablePositiveSourceWeight D root) 1 (by decide))
    hpositiveAdd

private theorem coarsePositiveTimesAllPairs_weight_le_partitionSquare_local
    (D : SlabPhysicalData) (root : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePositiveTimesAllPairs D root) ≤
      D.physicalPartition * D.physicalPartition := by
  have hpositive := coarsePositiveSourceWeight_le_partition_local D root
  have hpartition0 : (0 : Q') ≤ D.physicalPartition :=
    physicalPartition_nonnegative D
  have hscaled := Q'.mul_le_mul_of_nonneg_right
    (slabObservablePositiveSourceWeight D root)
    D.physicalPartition D.physicalPartition hpositive hpartition0
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (slabObservablePositiveTimesAllPairs_weight_eqv D root))
    hscaled

/-! ## 1a. Finite carrier ceilings for the coarse and pushed crosses -/

/- The two four-cell carriers are literal sublists of the complete positive
   two-replica carrier.  This gives a finite `Z^2` ceiling without supplying
   the still-open blocking law. -/
theorem coarseObservableFourCellSourceRawMass_le_partitionSquare
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellSourcePairs S.coarse root target) ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellSourcePairs S.coarse root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservablePositiveTimesAllPairs S.coarse root) := by
    apply listQSum_le_of_injective_nodup
      (slabObservableFourCellSourcePairs S.coarse root target)
      (slabObservablePositiveTimesAllPairs S.coarse root)
      (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableTwoReplicaPairWeight S.coarse)
      (fun pair => pair)
      (slabObservableFourCellSourcePairs_nodup
        S.coarse root target)
      (coarsePositiveTimesAllPairs_nodup_local S.coarse root)
    · intro pair hpair
      exact coarseSourcePair_mem_positiveTimesAll_local
        S.coarse root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact coarsePairRawMass_nonnegative_local pair
  exact Q'.le_trans' _ _ _ hsub
    (coarsePositiveTimesAllPairs_weight_le_partitionSquare_local
      S.coarse root)

theorem coarseObservableFourCellTargetRawMass_le_partitionSquare
    (S : SlabScalePair) (root target : Nat) :
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
        (slabObservableFourCellTargetPairs S.coarse root target) ≤
      S.coarse.physicalPartition * S.coarse.physicalPartition := by
  have hsub :
      listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservableFourCellTargetPairs S.coarse root target) ≤
        listQSum (slabObservableTwoReplicaPairWeight S.coarse)
          (slabObservablePositiveTimesAllPairs S.coarse root) := by
    apply listQSum_le_of_injective_nodup
      (slabObservableFourCellTargetPairs S.coarse root target)
      (slabObservablePositiveTimesAllPairs S.coarse root)
      (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableTwoReplicaPairWeight S.coarse)
      (fun pair => pair)
      (slabObservableFourCellTargetPairs_nodup
        S.coarse root target)
      (coarsePositiveTimesAllPairs_nodup_local S.coarse root)
    · intro pair hpair
      exact coarseTargetPair_mem_positiveTimesAll_local
        S.coarse root target pair hpair
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact coarsePairRawMass_nonnegative_local pair
  exact Q'.le_trans' _ _ _ hsub
    (coarsePositiveTimesAllPairs_weight_le_partitionSquare_local
      S.coarse root)

theorem fineUnitCouplingPushedFourCellSourceRawMass_le_partitionSquare
    (S : SlabScalePair) (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellSourceRawMass K root target ≤
      fineUnitCouplingPhysicalPartition S *
        fineUnitCouplingPhysicalPartition S := by
  have hsub :
      listQSum (fineUnitCouplingPushedTargetPairRawMass K)
          (pushedFaceRawFourCellSourcePairs (S := S) root target) ≤
        listQSum (fineUnitCouplingPushedTargetPairRawMass K)
          (cartesian S.coarse.physicalLabellings
            S.coarse.physicalLabellings) := by
    apply listQSum_le_of_injective_nodup
      (pushedFaceRawFourCellSourcePairs (S := S) root target)
      (cartesian S.coarse.physicalLabellings
        S.coarse.physicalLabellings)
      (fineUnitCouplingPushedTargetPairRawMass K)
      (fineUnitCouplingPushedTargetPairRawMass K)
      (fun pair => pair)
      (pushedFaceRawFourCellSourcePairs_nodup_local S root target)
      (cartesian_nodup _ _
        (slabPhysicalLabellings_nodup S.coarse)
        (slabPhysicalLabellings_nodup S.coarse))
    · intro pair hpair
      exact (mem_cartesian_iff _ _ pair).mpr
        (pushedSourcePair_components_mem_local hpair)
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair hpair
      have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
      exact pushedTargetPairRawMass_nonnegative_local K
        hmembers.1 hmembers.2
  have hcart := listQSum_cartesian_product
    (fineUnitCouplingPushedTargetRawMass K)
    (fineUnitCouplingPushedTargetRawMass K)
    S.coarse.physicalLabellings S.coarse.physicalLabellings
  have htotal := fineUnitCouplingPushedTargetRawMass_total K
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hcart
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ htotal)
          (Q'.mul_eqv_congr_left _ _ _ htotal))))

theorem fineUnitCouplingPushedFourCellTargetRawMass_le_partitionSquare
    (S : SlabScalePair) (K : S.FiniteSlabKernel)
    (root target : Nat) :
    fineUnitCouplingPushedFourCellTargetRawMass K root target ≤
      fineUnitCouplingPhysicalPartition S *
        fineUnitCouplingPhysicalPartition S := by
  have hsub :
      listQSum (fineUnitCouplingPushedTargetPairRawMass K)
          (pushedFaceRawFourCellTargetPairs (S := S) root target) ≤
        listQSum (fineUnitCouplingPushedTargetPairRawMass K)
          (cartesian S.coarse.physicalLabellings
            S.coarse.physicalLabellings) := by
    apply listQSum_le_of_injective_nodup
      (pushedFaceRawFourCellTargetPairs (S := S) root target)
      (cartesian S.coarse.physicalLabellings
        S.coarse.physicalLabellings)
      (fineUnitCouplingPushedTargetPairRawMass K)
      (fineUnitCouplingPushedTargetPairRawMass K)
      (fun pair => pair)
      (pushedFaceRawFourCellTargetPairs_nodup_local S root target)
      (cartesian_nodup _ _
        (slabPhysicalLabellings_nodup S.coarse)
        (slabPhysicalLabellings_nodup S.coarse))
    · intro pair hpair
      exact (mem_cartesian_iff _ _ pair).mpr
        (pushedTargetPair_components_mem_local hpair)
    · intro first _ second _ heq
      exact heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair hpair
      have hmembers := (mem_cartesian_iff _ _ pair).mp hpair
      exact pushedTargetPairRawMass_nonnegative_local K
        hmembers.1 hmembers.2
  have hcart := listQSum_cartesian_product
    (fineUnitCouplingPushedTargetRawMass K)
    (fineUnitCouplingPushedTargetRawMass K)
    S.coarse.physicalLabellings S.coarse.physicalLabellings
  have htotal := fineUnitCouplingPushedTargetRawMass_total K
  exact Q'.le_trans' _ _ _ hsub
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hcart
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_right _ _ _ htotal)
          (Q'.mul_eqv_congr_left _ _ _ htotal))))

theorem coarseObservableFourCellRawColumnCross_abs_le_two_partitionSquare
    (S : SlabScalePair) (root target : Nat) :
    Q'.abs (coarseObservableFourCellRawColumnCross S root target) ≤
      Q'.ofNat 2 *
        (S.coarse.physicalPartition * S.coarse.physicalPartition) := by
  let source :=
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellSourcePairs S.coarse root target)
  let opposite :=
    listQSum (slabObservableTwoReplicaPairWeight S.coarse)
      (slabObservableFourCellTargetPairs S.coarse root target)
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  have hsource0 : (0 : Q') ≤ source := by
    unfold source
    apply listQSum_nonnegative_on
    intro pair _
    exact coarsePairRawMass_nonnegative_local pair
  have hopposite0 : (0 : Q') ≤ opposite := by
    unfold opposite
    apply listQSum_nonnegative_on
    intro pair _
    exact coarsePairRawMass_nonnegative_local pair
  have hsource :=
    coarseObservableFourCellSourceRawMass_le_partitionSquare S root target
  have hopposite :=
    coarseObservableFourCellTargetRawMass_le_partitionSquare S root target
  have habs : Q'.abs (source - opposite) ≤ source + opposite :=
    abs_sub_nonnegative_le_add_local hsource0 hopposite0
  have hsum : source + opposite ≤ coarseSquare + coarseSquare := by
    exact Q'.add_le_add
      (by simpa only [source, coarseSquare] using hsource)
      (by simpa only [opposite, coarseSquare] using hopposite)
  have hfinal : source + opposite ≤ Q'.ofNat 2 * coarseSquare :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (two_mul_eqv_local coarseSquare)))
  simpa only [coarseObservableFourCellRawColumnCross,
    source, opposite, coarseSquare] using
    (Q'.le_trans' _ _ _ habs hfinal)

theorem fineUnitCouplingPushedRawColumnCross_abs_le_two_partitionSquare
    (S : SlabScalePair) (K : S.FiniteSlabKernel)
    (root target : Nat) :
    Q'.abs (fineUnitCouplingPushedRawColumnCross K root target) ≤
      Q'.ofNat 2 *
        (fineUnitCouplingPhysicalPartition S *
          fineUnitCouplingPhysicalPartition S) := by
  let source := fineUnitCouplingPushedFourCellSourceRawMass K root target
  let opposite := fineUnitCouplingPushedFourCellTargetRawMass K root target
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  have hsource0 : (0 : Q') ≤ source := by
    unfold source fineUnitCouplingPushedFourCellSourceRawMass
    apply listQSum_nonnegative_on
    intro pair hpair
    have hmembers := pushedSourcePair_components_mem_local hpair
    exact pushedTargetPairRawMass_nonnegative_local K
      hmembers.1 hmembers.2
  have hopposite0 : (0 : Q') ≤ opposite := by
    unfold opposite fineUnitCouplingPushedFourCellTargetRawMass
    apply listQSum_nonnegative_on
    intro pair hpair
    have hmembers := pushedTargetPair_components_mem_local hpair
    exact pushedTargetPairRawMass_nonnegative_local K
      hmembers.1 hmembers.2
  have hsource :=
    fineUnitCouplingPushedFourCellSourceRawMass_le_partitionSquare
      S K root target
  have hopposite :=
    fineUnitCouplingPushedFourCellTargetRawMass_le_partitionSquare
      S K root target
  have habs : Q'.abs (source - opposite) ≤ source + opposite :=
    abs_sub_nonnegative_le_add_local hsource0 hopposite0
  have hsum : source + opposite ≤ unitSquare + unitSquare := by
    exact Q'.add_le_add
      (by simpa only [source, unitSquare] using hsource)
      (by simpa only [opposite, unitSquare] using hopposite)
  have hfinal : source + opposite ≤ Q'.ofNat 2 * unitSquare :=
    Q'.le_trans' _ _ _ hsum
      (Q'.le_of_eqv (Q'.eqv_symm (two_mul_eqv_local unitSquare)))
  simpa only [fineUnitCouplingPushedRawColumnCross,
    source, opposite, unitSquare] using
    (Q'.le_trans' _ _ _ habs hfinal)

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

/-! The finite carrier ceiling now discharges both signed four-cell payments.
   Its right side still uses the coupling-one fine partition, so it is not a
   uniform balanced calibration in the actual fine partition. -/
theorem fineUnitCouplingBalancedRawColumnScaleDefect_abs_le_four_partitionSquares
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    Q'.abs
        (fineUnitCouplingBalancedRawColumnScaleDefect
          S hfineCutoff hcoarseCoupling root target) ≤
      Q'.ofNat 4 *
        ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (fineUnitCouplingPhysicalPartition S *
            fineUnitCouplingPhysicalPartition S)) := by
  let K := physicalKernel S hfineCutoff hcoarseCoupling
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let coarseCross := coarseObservableFourCellRawColumnCross S root target
  let pushedCross := fineUnitCouplingPushedRawColumnCross K root target
  have hcoarseSquare0 : (0 : Q') ≤ coarseSquare := by
    unfold coarseSquare
    exact Q'.mul_nonneg _ _
      (physicalPartition_nonnegative S.coarse)
      (physicalPartition_nonnegative S.coarse)
  have hunitSquare0 : (0 : Q') ≤ unitSquare := by
    unfold unitSquare
    exact Q'.mul_nonneg _ _
      (fineUnitCouplingPhysicalPartition_nonnegative S)
      (fineUnitCouplingPhysicalPartition_nonnegative S)
  have hcoarse :=
    coarseObservableFourCellRawColumnCross_abs_le_two_partitionSquare
      S root target
  have hpushed :=
    fineUnitCouplingPushedRawColumnCross_abs_le_two_partitionSquare
      S K root target
  have hfirst :
      Q'.abs (unitSquare * coarseCross) ≤
        unitSquare * (Q'.ofNat 2 * coarseSquare) := by
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        unitSquare coarseCross) ?_
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hcoarse
      (Q'.abs_nonneg unitSquare)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (abs_nonnegative_factor_eqv_local
          unitSquare (Q'.ofNat 2 * coarseSquare) hunitSquare0))
  have hsecond :
      Q'.abs (coarseSquare * pushedCross) ≤
        coarseSquare * (Q'.ofNat 2 * unitSquare) := by
    refine Q'.le_trans' _ _ _
      (YMGap.Continuum.TsumDeriv.Q'.abs_mul_le
        coarseSquare pushedCross) ?_
    have hmul := Q'.mul_le_mul_of_nonneg_left _ _ _ hpushed
      (Q'.abs_nonneg coarseSquare)
    exact Q'.le_trans' _ _ _ hmul
      (Q'.le_of_eqv
        (abs_nonnegative_factor_eqv_local
          coarseSquare (Q'.ofNat 2 * unitSquare) hcoarseSquare0))
  have hsplit :
      Q'.abs (unitSquare * coarseCross - coarseSquare * pushedCross) ≤
        Q'.abs (unitSquare * coarseCross) +
          Q'.abs (coarseSquare * pushedCross) := by
    exact abs_sub_le_abs_add_local
      (unitSquare * coarseCross) (coarseSquare * pushedCross)
  have hsum := Q'.add_le_add hfirst hsecond
  have hcollapse :
      unitSquare * (Q'.ofNat 2 * coarseSquare) +
          coarseSquare * (Q'.ofNat 2 * unitSquare) ≈
        ((coarseSquare * unitSquare) +
          (coarseSquare * unitSquare)) +
          ((coarseSquare * unitSquare) +
            (coarseSquare * unitSquare)) := by
    exact two_cross_regroup_local unitSquare coarseSquare
  have hfinal :
      Q'.abs (unitSquare * coarseCross - coarseSquare * pushedCross) ≤
        Q'.ofNat 4 * (coarseSquare * unitSquare) := by
    refine Q'.le_trans' _ _ _ hsplit
      (Q'.le_trans' _ _ _ hsum ?_)
    exact Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hcollapse
        (Q'.eqv_symm (four_mul_eqv_local (coarseSquare * unitSquare))))
  unfold fineUnitCouplingBalancedRawColumnScaleDefect
  simpa only [K, coarseSquare, unitSquare, coarseCross, pushedCross]
    using hfinal

/-- Explicit finite calibration ceiling obtained by dividing the carrier
ceiling by the displayed positive factor `g^2 * actualPartition^2`.  The
quotient is intentionally parameter-dependent: it is a compiler for the
finite carrier estimate, not a cutoff- or volume-uniform blocking constant. -/
def fineUnitCouplingBalancedCarrierCeiling
    (S : SlabScalePair) (g : Q') (hg : (0 : Q') < g) : Q' :=
  Q'.divPos
    (Q'.ofNat 4 *
      (fineUnitCouplingPhysicalPartition S *
        fineUnitCouplingPhysicalPartition S))
    ((g * g) *
      (S.fine.physicalPartition * S.fine.physicalPartition))
    (Q'.mul_pos
      (Q'.mul_pos hg hg)
      (Q'.mul_pos
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
        (slabParametricKPhysicalPartition_pos
          S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)))

private theorem nested_product_swap_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * (b * d)) * c := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv a b (c * d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
      (Q'.eqv_symm (Q'.mul_assoc_eqv b c d))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
      (Q'.mul_eqv_congr_right (b * c) (c * b) d
        (Q'.mul_comm_eqv b c))) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
      (Q'.mul_assoc_eqv c b d)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left a (c * (b * d)) ((b * d) * c)
      (Q'.mul_comm_eqv c (b * d))) ?_
  exact Q'.eqv_symm (Q'.mul_assoc_eqv a (b * d) c)

private theorem four_unit_coarse_regroup_local (unit coarse : Q') :
    (Q'.ofNat 4 * unit) * coarse ≈
      Q'.ofNat 4 * (coarse * unit) := by
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv (Q'.ofNat 4) unit coarse) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left (Q'.ofNat 4)
      (unit * coarse) (coarse * unit)
      (Q'.mul_comm_eqv unit coarse)) ?_
  exact Q'.eqv_refl _

private theorem fineUnitCouplingBalancedCarrierCeiling_budget_mul_actualSquare_eqv
    (S : SlabScalePair) (g : Q') (hg : (0 : Q') < g) :
    (fineUnitCouplingBalancedCarrierCeiling S g hg * (g * g)) *
        ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (S.fine.physicalPartition * S.fine.physicalPartition)) ≈
      Q'.ofNat 4 *
        ((S.coarse.physicalPartition * S.coarse.physicalPartition) *
          (fineUnitCouplingPhysicalPartition S *
            fineUnitCouplingPhysicalPartition S)) := by
  let unitSquare :=
    fineUnitCouplingPhysicalPartition S *
      fineUnitCouplingPhysicalPartition S
  let actualSquare :=
    S.fine.physicalPartition * S.fine.physicalPartition
  let coarseSquare :=
    S.coarse.physicalPartition * S.coarse.physicalPartition
  let gSquare := g * g
  let numerator := Q'.ofNat 4 * unitSquare
  let denominator := gSquare * actualSquare
  have hactual : (0 : Q') < S.fine.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent
  have hdenominator : (0 : Q') < denominator := by
    unfold denominator gSquare actualSquare
    exact Q'.mul_pos
      (Q'.mul_pos hg hg)
      (Q'.mul_pos hactual hactual)
  have hdivision :
      Q'.divPos numerator denominator hdenominator * denominator ≈
        numerator :=
    Q'.divPos_mul_eqv numerator denominator hdenominator
  unfold fineUnitCouplingBalancedCarrierCeiling
  change
    (Q'.divPos numerator denominator hdenominator * gSquare) *
          (coarseSquare * actualSquare) ≈
      Q'.ofNat 4 * (coarseSquare * unitSquare)
  refine Q'.eqv_trans _ _ _
    (nested_product_swap_local
      (Q'.divPos numerator denominator hdenominator)
      gSquare coarseSquare actualSquare) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right
      (Q'.divPos numerator denominator hdenominator * denominator)
      numerator coarseSquare hdivision) ?_
  exact four_unit_coarse_regroup_local unitSquare coarseSquare

/-- The finite carrier ceiling inhabits the existing balanced-calibration
interface after an explicit actual-partition normalization.  Its dependence
on `S` and `g` is exposed by `fineUnitCouplingBalancedCarrierCeiling`. -/
theorem fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_finite_carrier
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) (g : Q') (hg : (0 : Q') < g) :
    FineUnitCouplingBalancedRawColumnScaleDefectCalibration
      S hfineCutoff hcoarseCoupling root target g
      (fineUnitCouplingBalancedCarrierCeiling S g hg) := by
  unfold FineUnitCouplingBalancedRawColumnScaleDefectCalibration
  have hbase :=
    fineUnitCouplingBalancedRawColumnScaleDefect_abs_le_four_partitionSquares
      S hfineCutoff hcoarseCoupling root target
  have hbudget :=
    fineUnitCouplingBalancedCarrierCeiling_budget_mul_actualSquare_eqv
      S g hg
  exact Q'.le_trans' _ _ _ hbase
    (Q'.le_of_eqv (Q'.eqv_symm hbudget))

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
#print axioms coarseObservableFourCellSourceRawMass_le_partitionSquare
#print axioms coarseObservableFourCellTargetRawMass_le_partitionSquare
#print axioms fineUnitCouplingPushedFourCellSourceRawMass_le_partitionSquare
#print axioms fineUnitCouplingPushedFourCellTargetRawMass_le_partitionSquare
#print axioms coarseObservableFourCellRawColumnCross_abs_le_two_partitionSquare
#print axioms fineUnitCouplingPushedRawColumnCross_abs_le_two_partitionSquare
#print axioms fineUnitCouplingBalancedRawColumnScaleDefect_abs_le_four_partitionSquares
#print axioms fineUnitCouplingBalancedCarrierCeiling
#print axioms fineUnitCouplingBalancedRawColumnScaleDefectCalibration_of_finite_carrier
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
