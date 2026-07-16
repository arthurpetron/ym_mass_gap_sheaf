/-
# Same-volume cylinder ratios for the arbitrary-cutoff spin-summed gas

The spin-summed marked switch lives entirely in one target box.  Accordingly,
the first comparison after switching is not yet a cross-volume theorem: it is
the comparison between the full target gas and the literal embedded target
subensemble, both evaluated with the target-box activity.  This module makes
that distinction explicit, proves all finite numerator/denominator
decompositions, and reduces the target-versus-embedded cross numerator to the
connected cylinder residue.

No invariance of spin-summed activities under box transport is used here.
-/

import YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation

namespace YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalConnectedSurfaceGas
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerBoundaryTail
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedCylinderSwitchSummation
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Literal target-box embedded and boundary cells -/

def parametricKEmbeddedTargetPartition
    (cutoff small n : Nat) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    (embeddedTargetFamilies small n)

def parametricKBoundaryTargetPartition
    (cutoff small n : Nat) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    (boundaryTargetFamilies small n)

def parametricKEmbeddedTargetEventNumerator
    (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    ((embeddedTargetFamilies small n).filter event)

def parametricKBoundaryTargetEventNumerator
    (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    ((boundaryTargetFamilies small n).filter event)

def parametricKEmbeddedTargetEventComplementNumerator
    (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    ((embeddedTargetFamilies small n).filter
      (fun family => !(event family)))

def parametricKBoundaryTargetEventComplementNumerator
    (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum (parametricKSupportFamilyActivity cutoff n)
    ((boundaryTargetFamilies small n).filter
      (fun family => !(event family)))

theorem parametricKEmbeddedTargetPartition_nonnegative
    (cutoff small n : Nat) :
    (0 : Q') ≤ parametricKEmbeddedTargetPartition cutoff small n := by
  unfold parametricKEmbeddedTargetPartition
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

theorem parametricKBoundaryTargetPartition_nonnegative
    (cutoff small n : Nat) :
    (0 : Q') ≤ parametricKBoundaryTargetPartition cutoff small n := by
  unfold parametricKBoundaryTargetPartition
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

private theorem filter_decide_mem_nil {A : Type} [DecidableEq A] :
    ∀ xs : List A,
      xs.filter (fun item => decide (item ∈ ([] : List A))) = []
  | [] => rfl
  | head :: tail => by
      change (if decide (head ∈ ([] : List A)) then
          head :: tail.filter
            (fun item => decide (item ∈ ([] : List A)))
        else tail.filter
          (fun item => decide (item ∈ ([] : List A)))) = []
      rw [show decide (head ∈ ([] : List A)) = false from
        decide_eq_false (fun h => absurd h List.not_mem_nil)]
      exact filter_decide_mem_nil tail

theorem nil_mem_embeddedCompatibleFamilies
    (small n : Nat) :
    [] ∈ embeddedCompatibleFamilies small n := by
  unfold embeddedCompatibleFamilies
  apply List.mem_map.mpr
  refine ⟨[], nil_mem_canonicalCompatibleAmbientFamilies small, ?_⟩
  unfold embeddedTransportFamily transportFamily ambientOrderedFamily
  exact filter_decide_mem_nil (canonicalSurfacePolymers n)

theorem parametricKEmbeddedTargetPartition_one_le
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n) :
    (1 : Q') ≤ parametricKEmbeddedTargetPartition cutoff small n := by
  have hmember := listQSum_member_le
    (parametricKSupportFamilyActivity cutoff n)
    (parametricKSupportFamilyActivity_nonnegative cutoff n)
    (embeddedCompatibleFamilies small n)
    (x := []) (nil_mem_embeddedCompatibleFamilies small n)
  have hperm := listQSum_perm
    (parametricKSupportFamilyActivity cutoff n)
    (embeddedCompatibleFamilies_perm_target hsmall)
  change (1 : Q') ≤ listQSum
    (parametricKSupportFamilyActivity cutoff n)
      (embeddedCompatibleFamilies small n) at hmember
  unfold parametricKEmbeddedTargetPartition
  exact Q'.le_trans' _ _ _ hmember (Q'.le_of_eqv hperm)

theorem parametricKEmbeddedTargetPartition_pos
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n) :
    (0 : Q') < parametricKEmbeddedTargetPartition cutoff small n :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide)
    (parametricKEmbeddedTargetPartition_one_le cutoff hsmall)

theorem parametricKEmbeddedTargetEventNumerator_nonnegative
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      parametricKEmbeddedTargetEventNumerator cutoff small n event := by
  unfold parametricKEmbeddedTargetEventNumerator
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

theorem parametricKBoundaryTargetEventNumerator_nonnegative
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      parametricKBoundaryTargetEventNumerator cutoff small n event := by
  unfold parametricKBoundaryTargetEventNumerator
  exact listQSum_nonnegative _
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

theorem parametricKEmbeddedTargetEventNumerator_le_partition
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKEmbeddedTargetEventNumerator cutoff small n event ≤
      parametricKEmbeddedTargetPartition cutoff small n := by
  unfold parametricKEmbeddedTargetEventNumerator
    parametricKEmbeddedTargetPartition
  exact listQSum_filter_le _ event
    (parametricKSupportFamilyActivity_nonnegative cutoff n) _

def parametricKEmbeddedTargetEventProbability
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) : Q' :=
  Q'.divPos
    (parametricKEmbeddedTargetEventNumerator cutoff small n event)
    (parametricKEmbeddedTargetPartition cutoff small n)
    (parametricKEmbeddedTargetPartition_pos cutoff hsmall)

theorem parametricKEmbeddedTargetEventProbability_nonnegative
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) :
    (0 : Q') ≤
      parametricKEmbeddedTargetEventProbability cutoff hsmall event := by
  unfold parametricKEmbeddedTargetEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (parametricKEmbeddedTargetEventNumerator_nonnegative
      cutoff small n event)
    (Q'.le_of_lt
      (Q'.recipPos_pos
        (parametricKEmbeddedTargetPartition cutoff small n)
        (parametricKEmbeddedTargetPartition_pos cutoff hsmall)))

theorem parametricKEmbeddedTargetEventProbability_le_one
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (event : List (List Nat) → Bool) :
    parametricKEmbeddedTargetEventProbability cutoff hsmall event ≤
      (1 : Q') := by
  unfold parametricKEmbeddedTargetEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (parametricKEmbeddedTargetEventNumerator_le_partition
      cutoff small n event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKEmbeddedTargetPartition cutoff small n)))

private theorem filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

/-! ## 2. Exact target-box decompositions -/

theorem parametricKCompatiblePartition_eqv_embedded_add_boundary
    (cutoff small n : Nat) :
    parametricKCompatibleSupportGasPartition cutoff n ≈
      parametricKEmbeddedTargetPartition cutoff small n +
        parametricKBoundaryTargetPartition cutoff small n := by
  unfold parametricKCompatibleSupportGasPartition
    parametricKEmbeddedTargetPartition
    parametricKBoundaryTargetPartition embeddedTargetFamilies
    boundaryTargetFamilies embeddedFamilyB
  exact listQSum_filter_partition
    (parametricKSupportFamilyActivity cutoff n)
    (fun family => decide
      (family ∈ embeddedCompatibleFamilies small n))
    (canonicalCompatibleAmbientFamilies n)

theorem parametricKCompatibleEventNumerator_eqv_embedded_add_boundary
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventNumerator cutoff n event ≈
      parametricKEmbeddedTargetEventNumerator cutoff small n event +
        parametricKBoundaryTargetEventNumerator cutoff small n event := by
  unfold parametricKCompatibleSupportEventNumerator
    parametricKEmbeddedTargetEventNumerator
    parametricKBoundaryTargetEventNumerator embeddedTargetFamilies
    boundaryTargetFamilies embeddedFamilyB
  rw [filters_commute
      (fun family : List (List Nat) => decide
        (family ∈ embeddedCompatibleFamilies small n)) event,
    filters_commute
      (fun family : List (List Nat) =>
        !(decide (family ∈ embeddedCompatibleFamilies small n))) event]
  exact listQSum_filter_partition
    (parametricKSupportFamilyActivity cutoff n)
    (fun family => decide
      (family ∈ embeddedCompatibleFamilies small n))
    ((canonicalCompatibleAmbientFamilies n).filter event)

theorem parametricKEmbeddedPartition_eqv_event_add_complement
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKEmbeddedTargetPartition cutoff small n ≈
      parametricKEmbeddedTargetEventNumerator cutoff small n event +
        parametricKEmbeddedTargetEventComplementNumerator
          cutoff small n event := by
  unfold parametricKEmbeddedTargetPartition
    parametricKEmbeddedTargetEventNumerator
    parametricKEmbeddedTargetEventComplementNumerator
  exact listQSum_filter_partition
    (parametricKSupportFamilyActivity cutoff n) event
    (embeddedTargetFamilies small n)

theorem parametricKBoundaryPartition_eqv_event_add_complement
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKBoundaryTargetPartition cutoff small n ≈
      parametricKBoundaryTargetEventNumerator cutoff small n event +
        parametricKBoundaryTargetEventComplementNumerator
          cutoff small n event := by
  unfold parametricKBoundaryTargetPartition
    parametricKBoundaryTargetEventNumerator
    parametricKBoundaryTargetEventComplementNumerator
  exact listQSum_filter_partition
    (parametricKSupportFamilyActivity cutoff n) event
    (boundaryTargetFamilies small n)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-- The exact cross numerator between the full target measure and its literal
embedded target subensemble.  This is a same-volume identity. -/
theorem parametricKTargetCrossDifference_eqv_boundary
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKCompatibleSupportEventNumerator cutoff n event *
          parametricKEmbeddedTargetPartition cutoff small n -
        parametricKEmbeddedTargetEventNumerator cutoff small n event *
          parametricKCompatibleSupportGasPartition cutoff n ≈
      parametricKBoundaryTargetEventNumerator cutoff small n event *
          parametricKEmbeddedTargetPartition cutoff small n -
        parametricKEmbeddedTargetEventNumerator cutoff small n event *
          parametricKBoundaryTargetPartition cutoff small n := by
  have hnum :=
    parametricKCompatibleEventNumerator_eqv_embedded_add_boundary
      cutoff small n event
  have hden :=
    parametricKCompatiblePartition_eqv_embedded_add_boundary cutoff small n
  refine Q'.eqv_trans _
    ((parametricKEmbeddedTargetEventNumerator cutoff small n event +
          parametricKBoundaryTargetEventNumerator cutoff small n event) *
        parametricKEmbeddedTargetPartition cutoff small n -
      parametricKEmbeddedTargetEventNumerator cutoff small n event *
        (parametricKEmbeddedTargetPartition cutoff small n +
          parametricKBoundaryTargetPartition cutoff small n)) _ ?_ ?_
  · exact sub_eqv_both
      (mul_eqv_both hnum (Q'.eqv_refl _))
      (mul_eqv_both (Q'.eqv_refl _) hden)
  · exact crossDifference_split
      (parametricKEmbeddedTargetEventNumerator cutoff small n event)
      (parametricKBoundaryTargetEventNumerator cutoff small n event)
      (parametricKEmbeddedTargetPartition cutoff small n)
      (parametricKBoundaryTargetPartition cutoff small n)

/-! ## 3. Identification of the four switching cells -/

theorem spinSummedBoundaryCylinderEventFamilySum_eqv_numerator
    (cutoff small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (parametricKSupportFamilyActivity cutoff n)
        (boundaryCylinderEventFamilyList small n roots predicate) ≈
      parametricKBoundaryTargetEventNumerator cutoff small n
        (markedCylinderEvent roots predicate) := by
  exact Q'.eqv_refl _

theorem spinSummedBoundaryCylinderComplementFamilySum_eqv_numerator
    (cutoff small n : Nat) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum (parametricKSupportFamilyActivity cutoff n)
        (boundaryCylinderComplementFamilyList small n roots predicate) ≈
      parametricKBoundaryTargetEventComplementNumerator cutoff small n
        (markedCylinderEvent roots predicate) := by
  exact Q'.eqv_refl _

theorem spinSummedEmbeddedCylinderEventFamilySum_eqv_numerator
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (parametricKSupportFamilyActivity cutoff n)
        (embeddedCylinderEventFamilyList small n roots predicate) ≈
      parametricKEmbeddedTargetEventNumerator cutoff small n
        (markedCylinderEvent roots predicate) := by
  have hperm := listQSum_perm
    (parametricKSupportFamilyActivity cutoff n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (markedCylinderEvent roots predicate))
  unfold embeddedCylinderEventFamilyList
    parametricKEmbeddedTargetEventNumerator
  exact hperm

theorem spinSummedEmbeddedCylinderComplementFamilySum_eqv_numerator
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum (parametricKSupportFamilyActivity cutoff n)
        (embeddedCylinderComplementFamilyList small n roots predicate) ≈
      parametricKEmbeddedTargetEventComplementNumerator cutoff small n
        (markedCylinderEvent roots predicate) := by
  have hperm := listQSum_perm
    (parametricKSupportFamilyActivity cutoff n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (fun family => !(markedCylinderEvent roots predicate family)))
  unfold embeddedCylinderComplementFamilyList
    parametricKEmbeddedTargetEventComplementNumerator
  exact hperm

/-- The division-free numerator comparing a target event ratio with the same
event conditioned on the embedded target subensemble. -/
def parametricKTargetEventCrossDifference
    (cutoff small n : Nat) (event : List (List Nat) → Bool) : Q' :=
  parametricKCompatibleSupportEventNumerator cutoff n event *
      parametricKEmbeddedTargetPartition cutoff small n -
    parametricKEmbeddedTargetEventNumerator cutoff small n event *
      parametricKCompatibleSupportGasPartition cutoff n

/-- The target/embedded determinant after splitting the full target ensemble
into its embedded and boundary pieces. -/
def parametricKBoundaryCrossDifference
    (cutoff small n : Nat) (event : List (List Nat) → Bool) : Q' :=
  parametricKBoundaryTargetEventNumerator cutoff small n event *
      parametricKEmbeddedTargetPartition cutoff small n -
    parametricKEmbeddedTargetEventNumerator cutoff small n event *
      parametricKBoundaryTargetPartition cutoff small n

/-- The opposite-cell form of the boundary determinant to which the marked
component switch applies. -/
def parametricKBoundaryCellCrossDifference
    (cutoff small n : Nat) (event : List (List Nat) → Bool) : Q' :=
  parametricKBoundaryTargetEventNumerator cutoff small n event *
      parametricKEmbeddedTargetEventComplementNumerator cutoff small n event -
    parametricKEmbeddedTargetEventNumerator cutoff small n event *
      parametricKBoundaryTargetEventComplementNumerator cutoff small n event

/-- The connected source-pair remainder left by the finite marked switch. -/
def spinSummedConnectedCylinderResidue
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) : Q' :=
  listQSum (spinSummedCylinderSourcePairWeight cutoff)
    (connectedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)

theorem spinSummedBoundaryCylinderCellCrossDifference_le_connected
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    parametricKBoundaryCellCrossDifference cutoff small n
        (markedCylinderEvent roots predicate) ≤
      spinSummedConnectedCylinderResidue cutoff hsmall roots predicate := by
  unfold parametricKBoundaryCellCrossDifference
    spinSummedConnectedCylinderResidue
  have hraw :=
    spinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
      cutoff hsmall roots predicate
  have hboundaryEvent :=
    spinSummedBoundaryCylinderEventFamilySum_eqv_numerator
      cutoff small n roots predicate
  have hembeddedComplement :=
    spinSummedEmbeddedCylinderComplementFamilySum_eqv_numerator
      cutoff hsmall roots predicate
  have hboundaryComplement :=
    spinSummedBoundaryCylinderComplementFamilySum_eqv_numerator
      cutoff small n roots predicate
  have hembeddedEvent :=
    spinSummedEmbeddedCylinderEventFamilySum_eqv_numerator
      cutoff hsmall roots predicate
  have hcells :
      parametricKBoundaryTargetEventNumerator cutoff small n
            (markedCylinderEvent roots predicate) *
          parametricKEmbeddedTargetEventComplementNumerator cutoff small n
            (markedCylinderEvent roots predicate) ≤
        parametricKBoundaryTargetEventComplementNumerator cutoff small n
              (markedCylinderEvent roots predicate) *
            parametricKEmbeddedTargetEventNumerator cutoff small n
              (markedCylinderEvent roots predicate) +
          listQSum (spinSummedCylinderSourcePairWeight cutoff)
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (mul_eqv_both (Q'.eqv_symm hboundaryEvent)
          (Q'.eqv_symm hembeddedComplement)))
      (Q'.le_trans' _ _ _ hraw
        (Q'.le_of_eqv
          (Q'.add_eqv_congr'
            (mul_eqv_both hboundaryComplement hembeddedEvent)
            (Q'.eqv_refl _))))
  have hreordered :
      parametricKBoundaryTargetEventNumerator cutoff small n
            (markedCylinderEvent roots predicate) *
          parametricKEmbeddedTargetEventComplementNumerator cutoff small n
            (markedCylinderEvent roots predicate) ≤
        parametricKEmbeddedTargetEventNumerator cutoff small n
              (markedCylinderEvent roots predicate) *
            parametricKBoundaryTargetEventComplementNumerator cutoff small n
              (markedCylinderEvent roots predicate) +
          listQSum (spinSummedCylinderSourcePairWeight cutoff)
            (connectedCylinderSourcePairs
              (roots := roots) (predicate := predicate) hsmall) :=
    Q'.le_trans' _ _ _ hcells
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (Q'.mul_comm_eqv
            (parametricKBoundaryTargetEventComplementNumerator
              cutoff small n (markedCylinderEvent roots predicate))
            (parametricKEmbeddedTargetEventNumerator
              cutoff small n (markedCylinderEvent roots predicate)))
          (Q'.eqv_refl _)))
  exact Q'.sub_le_of_le_add hreordered

theorem parametricKTargetEventCrossDifference_eqv_boundary
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKTargetEventCrossDifference cutoff small n event ≈
      parametricKBoundaryCrossDifference cutoff small n event := by
  unfold parametricKTargetEventCrossDifference
    parametricKBoundaryCrossDifference
  exact parametricKTargetCrossDifference_eqv_boundary
    cutoff small n event

/-- Splitting both boundary-cross partitions into event and complement cells
leaves exactly the opposite-cell determinant used by switching. -/
theorem parametricKBoundaryCrossDifference_eqv_cells
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKBoundaryCrossDifference cutoff small n event ≈
      parametricKBoundaryCellCrossDifference cutoff small n event := by
  have hembedded :=
    parametricKEmbeddedPartition_eqv_event_add_complement
      cutoff small n event
  have hboundary :=
    parametricKBoundaryPartition_eqv_event_add_complement
      cutoff small n event
  unfold parametricKBoundaryCrossDifference
    parametricKBoundaryCellCrossDifference
  refine Q'.eqv_trans _ _ _
    (sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hembedded)
      (mul_eqv_both (Q'.eqv_refl _) hboundary)) ?_
  exact eventBoundaryCrossDifference_cells
    (parametricKEmbeddedTargetEventNumerator cutoff small n event)
    (parametricKBoundaryTargetEventNumerator cutoff small n event)
    (parametricKEmbeddedTargetEventComplementNumerator cutoff small n event)
    (parametricKBoundaryTargetEventComplementNumerator cutoff small n event)

theorem parametricKTargetEventCrossDifference_eqv_cells
    (cutoff small n : Nat) (event : List (List Nat) → Bool) :
    parametricKTargetEventCrossDifference cutoff small n event ≈
      parametricKBoundaryCellCrossDifference cutoff small n event := by
  exact Q'.eqv_trans _ _ _
    (parametricKTargetEventCrossDifference_eqv_boundary
      cutoff small n event)
    (parametricKBoundaryCrossDifference_eqv_cells
      cutoff small n event)

/-- Compact proposition wrapper for the same-volume cylinder comparison. -/
def ParametricKTargetCylinderConnectedBound
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) : Prop :=
  parametricKTargetEventCrossDifference cutoff small n
      (markedCylinderEvent roots predicate) ≤
    spinSummedConnectedCylinderResidue cutoff hsmall roots predicate

/-- The full-target versus embedded-target cylinder cross numerator is bounded
by precisely the connected source-pair residue. -/
theorem parametricKTargetCylinderCrossDifference_le_connected
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    ParametricKTargetCylinderConnectedBound
      cutoff hsmall roots predicate := by
  unfold ParametricKTargetCylinderConnectedBound
  have hcross := parametricKTargetEventCrossDifference_eqv_cells
    cutoff small n (markedCylinderEvent roots predicate)
  have hboundary :=
    spinSummedBoundaryCylinderCellCrossDifference_le_connected
      cutoff hsmall roots predicate
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcross) hboundary

end YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKCompatiblePartition_eqv_embedded_add_boundary
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.nil_mem_embeddedCompatibleFamilies
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKEmbeddedTargetPartition_pos
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKTargetCrossDifference_eqv_boundary
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKTargetEventCrossDifference_eqv_boundary
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKBoundaryCrossDifference_eqv_cells
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKTargetEventCrossDifference_eqv_cells
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.spinSummedBoundaryCylinderCellCrossDifference_le_connected
#print axioms YMGap.Continuum.Z4SpinSummedTargetCylinderRatio.parametricKTargetCylinderCrossDifference_le_connected
