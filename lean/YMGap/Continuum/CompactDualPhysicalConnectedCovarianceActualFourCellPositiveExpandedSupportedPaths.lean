/-
# Delete zero-raw accepted-fiber covariance paths

The accepted-fiber covariance carrier contains paths whose fine source is
strictly Gibbs-positive but whose selected whole-slab raw transition can
still vanish.  Such paths cannot yet be oriented by the receiver bridge,
whose coarse accepted witness is extracted from strict raw positivity.

This module constructively filters both paired four-cell path cells to the
strict raw support.  If either replica has nonpositive raw transition weight,
nonnegativity makes that raw weight exactly zero; hence its conditional
kernel factor and the entire paired path contribution are exactly zero.
Attaching the surviving positivity proofs therefore preserves both cell
masses, their determinant, and the complete connected raw-cross defect.
Every survivor is now an input to the receiver-orientation module.

This is an exact finite support reduction.  It does not compare a surviving
cross-scale conditional weight with a same-datum receiver weight and proves
no `O(a)` estimate, continuum measure, OS/GNS reconstruction, or physical
mass gap.

Constructive contract: dependent finite attachment and exact rational
identities only; no choice, `Classical`, `native_decide`, `sorry`,
noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation

namespace YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths

set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 4000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualCutoffOnePhysicalPushforward
open YMGap.Continuum.CompactDualCutoffOneTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCell
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedPaths
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedReceiverOrientation
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualRawKernel
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceRawCross
open YMGap.Continuum.CompactDualSlabObservablePhysicalBlockingDefect
open YMGap.Continuum.CompactDualSlabObservablePhysicalCenteredRemainderExpansion
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualWholeSlabRecouplingRawKernel
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem q_nonpositive_of_not_positive_local
    {q : Q'} (hnot : ¬ (0 : Q') < q) :
    q ≤ 0 := by
  show q.num * (1 : Int) ≤
    (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_not_positive_local
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnot : ¬ (0 : Q') < q) :
    q ≈ 0 := by
  have hnonpositive : q ≤ 0 :=
    q_nonpositive_of_not_positive_local hnot
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

private theorem listQSum_eq_filter_of_zero_local
    {A : Type} (value : A → Q') (test : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → test item = false →
        value item ≈ 0) →
      listQSum value items ≈
        listQSum value (items.filter test)
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      have htail :
          ∀ item, item ∈ tail → test item = false →
            value item ≈ 0 := by
        intro item hitem htest
        exact hzero item (List.mem_cons_of_mem head hitem) htest
      cases htest : test head with
      | false =>
          simp only [List.filter_cons, htest, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _
            (0 + listQSum value (tail.filter test)) _
            (Q'.add_eqv_congr'
              (hzero head List.mem_cons_self htest)
              (listQSum_eq_filter_of_zero_local
                value test tail htail))
            (Q'.eqv_of_eq (Q'.zero_add' _))
      | true =>
          simp only [List.filter_cons, htest, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_eq_filter_of_zero_local
              value test tail htail)

/-! ## 1. Vanishing of a nonpositive raw transition -/

/-- A nonpositive whole-slab raw entry is exactly zero because every raw
entry is nonnegative. -/
theorem wholeSlabRecouplingRawWeight_eqv_zero_of_not_positive
    (S : SlabScalePair) (fineState target : EdgeLabelling)
    (hnot : ¬ (0 : Q') <
      wholeSlabRecouplingRawWeight S fineState target) :
    wholeSlabRecouplingRawWeight S fineState target ≈ 0 :=
  q_eqv_zero_of_nonnegative_of_not_positive_local
    (wholeSlabRecouplingRawWeight_nonnegative
      S fineState target) hnot

/-- Dividing a zero raw entry by its positive complete row partition leaves
the corresponding conditional-kernel entry exactly zero. -/
theorem wholeSlabRecouplingConditionalKernel_eqv_zero_of_raw_not_positive
    {S : SlabScalePair} (source : CoherentSlabRecouplingSource S)
    (target : EdgeLabelling)
    (hnot : ¬ (0 : Q') <
      wholeSlabRecouplingRawWeight S source.fineState target) :
    wholeSlabRecouplingConditionalKernel source target ≈ 0 := by
  unfold wholeSlabRecouplingConditionalKernel Q'.divPos
  refine Q'.eqv_trans _
    (0 * Q'.recipPos (wholeSlabRecouplingPartition source)
      (wholeSlabRecouplingPartition_pos source)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_right _ _ _
      (wholeSlabRecouplingRawWeight_eqv_zero_of_not_positive
        S source.fineState target hnot)
  · exact Q'.zero_mul_eqv _

theorem positiveExpandedSourceKernelPathRawMass_eqv_zero_of_raw_not_positive
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (target : EdgeLabelling)
    (source : PositiveExpandedPhysicalSource S)
    (hnot : ¬ (0 : Q') <
      wholeSlabRecouplingRawWeight S source.1.1 target) :
    positiveExpandedSourceKernelPathRawMass S hfineCutoff
        hcoarseCoupling target source ≈ 0 := by
  unfold positiveExpandedSourceKernelPathRawMass
  exact Q'.eqv_trans _
    (positiveExpandedPhysicalSourceWeight S source * 0) _
    (Q'.mul_eqv_congr_left _ _ _
      (wholeSlabRecouplingConditionalKernel_eqv_zero_of_raw_not_positive
        (positiveCoherentSource S hfineCutoff hcoarseCoupling
          source.1.1 source.1.2.1 source.1.2.2)
        target hnot))
    (Q'.mul_zero_eqv _)

theorem positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_left
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (path : PositiveExpandedPushedPhysicalTwoReplicaPath S)
    (hnot : ¬ (0 : Q') <
      wholeSlabRecouplingRawWeight S path.2.1.1.1 path.1.1) :
    positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling path ≈ 0 := by
  unfold positiveExpandedPushedPhysicalTwoReplicaPathRawMass
  exact Q'.eqv_trans _
    (0 * positiveExpandedSourceKernelPathRawMass
      S hfineCutoff hcoarseCoupling path.1.2 path.2.2) _
    (Q'.mul_eqv_congr_right _ _ _
      (positiveExpandedSourceKernelPathRawMass_eqv_zero_of_raw_not_positive
        S hfineCutoff hcoarseCoupling path.1.1 path.2.1 hnot))
    (Q'.zero_mul_eqv _)

theorem positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_right
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (path : PositiveExpandedPushedPhysicalTwoReplicaPath S)
    (hnot : ¬ (0 : Q') <
      wholeSlabRecouplingRawWeight S path.2.2.1.1 path.1.2) :
    positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling path ≈ 0 := by
  unfold positiveExpandedPushedPhysicalTwoReplicaPathRawMass
  exact Q'.eqv_trans _
    (positiveExpandedSourceKernelPathRawMass
        S hfineCutoff hcoarseCoupling path.1.1 path.2.1 * 0) _
    (Q'.mul_eqv_congr_left _ _ _
      (positiveExpandedSourceKernelPathRawMass_eqv_zero_of_raw_not_positive
        S hfineCutoff hcoarseCoupling path.1.2 path.2.2 hnot))
    (Q'.mul_zero_eqv _)

/-! ## 2. Proof-carrying strict-support enumerations -/

/-- Boolean strict-support predicate for both replicas of an expanded path. -/
def positiveExpandedPathRawSupportedB
    (S : SlabScalePair)
    (path : PositiveExpandedPushedPhysicalTwoReplicaPath S) : Bool :=
  decide ((0 : Q') <
      wholeSlabRecouplingRawWeight S path.2.1.1.1 path.1.1) &&
    decide ((0 : Q') <
      wholeSlabRecouplingRawWeight S path.2.2.1.1 path.1.2)

def positiveExpandedFourCellSourceSupportedPathOfAttached
    (S : SlabScalePair) (root target : Nat)
    (item : {path // path ∈
      (positiveExpandedPushedFaceRawFourCellSourcePaths
        S root target).filter (positiveExpandedPathRawSupportedB S)}) :
    PositiveExpandedFourCellSourceSupportedPath S root target := by
  have hparts := List.mem_filter.mp item.2
  have hsupport := (Bool.and_eq_true _ _).mp hparts.2
  exact
    { path := item.1
      path_mem := hparts.1
      leftRawWeight_pos := of_decide_eq_true hsupport.1
      rightRawWeight_pos := of_decide_eq_true hsupport.2 }

def positiveExpandedFourCellTargetSupportedPathOfAttached
    (S : SlabScalePair) (root target : Nat)
    (item : {path // path ∈
      (positiveExpandedPushedFaceRawFourCellTargetPaths
        S root target).filter (positiveExpandedPathRawSupportedB S)}) :
    PositiveExpandedFourCellTargetSupportedPath S root target := by
  have hparts := List.mem_filter.mp item.2
  have hsupport := (Bool.and_eq_true _ _).mp hparts.2
  exact
    { path := item.1
      path_mem := hparts.1
      leftRawWeight_pos := of_decide_eq_true hsupport.1
      rightRawWeight_pos := of_decide_eq_true hsupport.2 }

/-- Every source-cell path with two strictly positive raw transitions,
carrying the proofs needed by receiver orientation. -/
def positiveExpandedFourCellSourceSupportedPaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedFourCellSourceSupportedPath S root target) :=
  ((positiveExpandedPushedFaceRawFourCellSourcePaths S root target).filter
      (positiveExpandedPathRawSupportedB S)).attach.map
    (positiveExpandedFourCellSourceSupportedPathOfAttached S root target)

/-- Every opposite-cell path with two strictly positive raw transitions,
carrying the proofs needed by the swapped receiver orientation. -/
def positiveExpandedFourCellTargetSupportedPaths
    (S : SlabScalePair) (root target : Nat) :
    List (PositiveExpandedFourCellTargetSupportedPath S root target) :=
  ((positiveExpandedPushedFaceRawFourCellTargetPaths S root target).filter
      (positiveExpandedPathRawSupportedB S)).attach.map
    (positiveExpandedFourCellTargetSupportedPathOfAttached S root target)

def positiveExpandedFourCellSourceSupportedPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellSourceSupportedPath
      S root target) : Q' :=
  positiveExpandedPushedPhysicalTwoReplicaPathRawMass
    S hfineCutoff hcoarseCoupling supported.path

def positiveExpandedFourCellTargetSupportedPathRawMass
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    {root target : Nat}
    (supported : PositiveExpandedFourCellTargetSupportedPath
      S root target) : Q' :=
  positiveExpandedPushedPhysicalTwoReplicaPathRawMass
    S hfineCutoff hcoarseCoupling supported.path

/-! ## 3. Exact deletion from both four-cell path sums -/

private theorem expandedPathRawMass_eqv_zero_of_not_supported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (path : PositiveExpandedPushedPhysicalTwoReplicaPath S)
    (hnot : positiveExpandedPathRawSupportedB S path = false) :
    positiveExpandedPushedPhysicalTwoReplicaPathRawMass
        S hfineCutoff hcoarseCoupling path ≈ 0 := by
  by_cases hleft : (0 : Q') <
      wholeSlabRecouplingRawWeight S path.2.1.1.1 path.1.1
  · by_cases hright : (0 : Q') <
        wholeSlabRecouplingRawWeight S path.2.2.1.1 path.1.2
    · have htrue : positiveExpandedPathRawSupportedB S path = true := by
        unfold positiveExpandedPathRawSupportedB
        rw [decide_eq_true hleft, decide_eq_true hright]
        rfl
      rw [htrue] at hnot
      cases hnot
    · exact
        positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_right
          S hfineCutoff hcoarseCoupling path hright
  · exact
      positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_left
        S hfineCutoff hcoarseCoupling path hleft

theorem positiveExpandedFourCellSourcePaths_mass_eqv_supported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedPushedFaceRawFourCellSourcePaths
          S root target) ≈
      listQSum
        (positiveExpandedFourCellSourceSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellSourceSupportedPaths
          S root target) := by
  let paths :=
    positiveExpandedPushedFaceRawFourCellSourcePaths S root target
  let value := positiveExpandedPushedPhysicalTwoReplicaPathRawMass
    S hfineCutoff hcoarseCoupling
  let test := positiveExpandedPathRawSupportedB S
  refine Q'.eqv_trans _
    (listQSum value (paths.filter test)) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro path _ htest
    exact expandedPathRawMass_eqv_zero_of_not_supported
      S hfineCutoff hcoarseCoupling path htest
  · unfold positiveExpandedFourCellSourceSupportedPaths
      positiveExpandedFourCellSourceSupportedPathRawMass
    rw [listQSum_map]
    exact Q'.eqv_symm
      (Q'.eqv_of_eq
        (listQSum_attach value (paths.filter test)))

theorem positiveExpandedFourCellTargetPaths_mass_eqv_supported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    listQSum
        (positiveExpandedPushedPhysicalTwoReplicaPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedPushedFaceRawFourCellTargetPaths
          S root target) ≈
      listQSum
        (positiveExpandedFourCellTargetSupportedPathRawMass
          S hfineCutoff hcoarseCoupling)
        (positiveExpandedFourCellTargetSupportedPaths
          S root target) := by
  let paths :=
    positiveExpandedPushedFaceRawFourCellTargetPaths S root target
  let value := positiveExpandedPushedPhysicalTwoReplicaPathRawMass
    S hfineCutoff hcoarseCoupling
  let test := positiveExpandedPathRawSupportedB S
  refine Q'.eqv_trans _
    (listQSum value (paths.filter test)) _ ?_ ?_
  · apply listQSum_eq_filter_of_zero_local
    intro path _ htest
    exact expandedPathRawMass_eqv_zero_of_not_supported
      S hfineCutoff hcoarseCoupling path htest
  · unfold positiveExpandedFourCellTargetSupportedPaths
      positiveExpandedFourCellTargetSupportedPathRawMass
    rw [listQSum_map]
    exact Q'.eqv_symm
      (Q'.eqv_of_eq
        (listQSum_attach value (paths.filter test)))

/-! ## 4. Supported covariance cross and final exact consumer -/

def actualPositiveExpandedSupportedFaceRawFourCellPathCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) : Q' :=
  listQSum
      (positiveExpandedFourCellSourceSupportedPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellSourceSupportedPaths S root target) -
    listQSum
      (positiveExpandedFourCellTargetSupportedPathRawMass
        S hfineCutoff hcoarseCoupling)
      (positiveExpandedFourCellTargetSupportedPaths S root target)

theorem actualPositiveExpandedPushedFaceRawFourCellPathCross_eqv_supported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (root target : Nat) :
    actualPositiveExpandedPushedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target ≈
      actualPositiveExpandedSupportedFaceRawFourCellPathCross
        S hfineCutoff hcoarseCoupling root target := by
  unfold actualPositiveExpandedPushedFaceRawFourCellPathCross
    actualPositiveExpandedSupportedFaceRawFourCellPathCross
  exact sub_eqv_both_local
    (positiveExpandedFourCellSourcePaths_mass_eqv_supported
      S hfineCutoff hcoarseCoupling root target)
    (positiveExpandedFourCellTargetPaths_mass_eqv_supported
      S hfineCutoff hcoarseCoupling root target)

def physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) : Q' :=
  (physicalFaceRawFourCellCross
      S.coarse M.coarseRoot M.coarseTarget *
      S.coarse.physicalPartition) *
      rawCovarianceDenominator S.fine.physicalPartition -
    (actualPositiveExpandedSupportedFaceRawFourCellPathCross
      S hfineCutoff hcoarseCoupling M.coarseRoot M.coarseTarget *
      S.fine.physicalPartition) *
      rawCovarianceDenominator S.coarse.physicalPartition

theorem physicalConnectedCovariancePositiveExpandedPathRawCrossDefect_eqv_supported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M := by
  unfold physicalConnectedCovariancePositiveExpandedPathRawCrossDefect
    physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
  exact sub_eqv_both_local (Q'.eqv_refl _)
    (Q'.mul_eqv_congr_right _ _
      (rawCovarianceDenominator S.coarse.physicalPartition)
      (Q'.mul_eqv_congr_right _ _ S.fine.physicalPartition
        (actualPositiveExpandedPushedFaceRawFourCellPathCross_eqv_supported
          S hfineCutoff hcoarseCoupling
          M.coarseRoot M.coarseTarget)))

theorem physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedSupported
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) :
    physicalConnectedCovarianceRawCrossDefect S hfineCutoff
        hcoarseCoupling M ≈
      physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
        S hfineCutoff hcoarseCoupling M :=
  Q'.eqv_trans _ _ _
    (physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedPathRawCross
      S hfineCutoff hcoarseCoupling M)
    (physicalConnectedCovariancePositiveExpandedPathRawCrossDefect_eqv_supported
      S hfineCutoff hcoarseCoupling M)

/-- A relative bound on the strict-support receiver-orientable path cross is
enough for the exact connected pushed-law remainder estimate. -/
theorem centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedSupportedPathRawCross
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (hcoarseCoupling : (0 : Q') < S.coarse.coupling)
    (M : SlabFaceBlockMap S) (budget : Q')
    (hcross :
      Q'.abs
          (physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
            S hfineCutoff hcoarseCoupling M) ≤
        budget * connectedCovarianceRawCrossDenominator S) :
    Q'.abs
        (centeredCylinderRemainder
          (physicalKernel S hfineCutoff hcoarseCoupling) M) ≤
      budget := by
  apply centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedPathRawCross
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.abs_eqv_congr
        (physicalConnectedCovariancePositiveExpandedPathRawCrossDefect_eqv_supported
          S hfineCutoff hcoarseCoupling M)))
    hcross

#print axioms wholeSlabRecouplingRawWeight_eqv_zero_of_not_positive
#print axioms wholeSlabRecouplingConditionalKernel_eqv_zero_of_raw_not_positive
#print axioms positiveExpandedSourceKernelPathRawMass_eqv_zero_of_raw_not_positive
#print axioms positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_left
#print axioms positiveExpandedPushedPhysicalTwoReplicaPathRawMass_eqv_zero_of_right
#print axioms positiveExpandedPathRawSupportedB
#print axioms positiveExpandedFourCellSourceSupportedPathOfAttached
#print axioms positiveExpandedFourCellTargetSupportedPathOfAttached
#print axioms positiveExpandedFourCellSourceSupportedPaths
#print axioms positiveExpandedFourCellTargetSupportedPaths
#print axioms positiveExpandedFourCellSourceSupportedPathRawMass
#print axioms positiveExpandedFourCellTargetSupportedPathRawMass
#print axioms positiveExpandedFourCellSourcePaths_mass_eqv_supported
#print axioms positiveExpandedFourCellTargetPaths_mass_eqv_supported
#print axioms actualPositiveExpandedSupportedFaceRawFourCellPathCross
#print axioms actualPositiveExpandedPushedFaceRawFourCellPathCross_eqv_supported
#print axioms physicalConnectedCovariancePositiveExpandedSupportedPathRawCrossDefect
#print axioms physicalConnectedCovariancePositiveExpandedPathRawCrossDefect_eqv_supported
#print axioms physicalConnectedCovarianceRawCrossDefect_eqv_positiveExpandedSupported
#print axioms centeredCylinderRemainder_physicalKernel_abs_le_of_positiveExpandedSupportedPathRawCross

end YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositiveExpandedSupportedPaths
