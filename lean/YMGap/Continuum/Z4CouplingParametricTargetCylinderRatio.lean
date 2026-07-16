/-
# Same-volume cylinder ratios below the anchor coupling

This module repeats the finite four-cell marked-switch calculation with the
exact coupling-`w` family activity.  The geometric switch is coupling blind;
only nonnegativity of `w` is needed here.  The result reduces the division-free
target-versus-embedded determinant to the coupling-parametric connected
cylinder residue.
-/

import YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail

namespace YMGap.Continuum.Z4CouplingParametricTargetCylinderRatio

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPolymerBoundaryCovariance
open YMGap.Continuum.Z4CanonicalPolymerFiniteMeasure
open YMGap.Continuum.Z4CanonicalPolymerPartitionRatio
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedEventBridge
open YMGap.Continuum.Z4CouplingParametricSpinSummedPinnedLayer
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Coupling-parametric boundary cells -/

def couplingParametricKBoundaryTargetPartition
    (coupling : Q') (cutoff small n : Nat) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (boundaryTargetFamilies small n)

def couplingParametricKBoundaryTargetEventNumerator
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((boundaryTargetFamilies small n).filter event)

def couplingParametricKEmbeddedTargetEventComplementNumerator
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((embeddedTargetFamilies small n).filter
      (fun family => !(event family)))

def couplingParametricKBoundaryTargetEventComplementNumerator
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  listQSum
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((boundaryTargetFamilies small n).filter
      (fun family => !(event family)))

private theorem filters_commute {A : Type}
    (first second : A → Bool) (xs : List A) :
    (xs.filter first).filter second =
      (xs.filter second).filter first := by
  rw [List.filter_filter, List.filter_filter]
  apply List.filter_congr
  intro item _
  exact Bool.and_comm (second item) (first item)

theorem couplingParametricKCompatiblePartition_eqv_embedded_add_boundary
    (coupling : Q') (cutoff small n : Nat) :
    couplingParametricKCompatibleSupportGasPartition coupling cutoff n ≈
      couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n +
        couplingParametricKBoundaryTargetPartition
          coupling cutoff small n := by
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKEmbeddedTargetPartition
    couplingParametricKBoundaryTargetPartition embeddedTargetFamilies
    boundaryTargetFamilies embeddedFamilyB
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (fun family => decide
      (family ∈ embeddedCompatibleFamilies small n))
    (canonicalCompatibleAmbientFamilies n)

theorem couplingParametricKCompatibleEventNumerator_eqv_embedded_add_boundary
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event ≈
      couplingParametricKEmbeddedTargetEventNumerator
          coupling cutoff small n event +
        couplingParametricKBoundaryTargetEventNumerator
          coupling cutoff small n event := by
  unfold couplingParametricKCompatibleSupportEventNumerator
    couplingParametricKEmbeddedTargetEventNumerator
    couplingParametricKBoundaryTargetEventNumerator embeddedTargetFamilies
    boundaryTargetFamilies embeddedFamilyB
  rw [filters_commute
      (fun family : List (List Nat) => decide
        (family ∈ embeddedCompatibleFamilies small n)) event,
    filters_commute
      (fun family : List (List Nat) =>
        !(decide (family ∈ embeddedCompatibleFamilies small n))) event]
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (fun family => decide
      (family ∈ embeddedCompatibleFamilies small n))
    ((canonicalCompatibleAmbientFamilies n).filter event)

theorem couplingParametricKEmbeddedPartition_eqv_event_add_complement
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKEmbeddedTargetPartition coupling cutoff small n ≈
      couplingParametricKEmbeddedTargetEventNumerator
          coupling cutoff small n event +
        couplingParametricKEmbeddedTargetEventComplementNumerator
          coupling cutoff small n event := by
  unfold couplingParametricKEmbeddedTargetPartition
    couplingParametricKEmbeddedTargetEventNumerator
    couplingParametricKEmbeddedTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n) event
    (embeddedTargetFamilies small n)

theorem couplingParametricKBoundaryPartition_eqv_event_add_complement
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKBoundaryTargetPartition coupling cutoff small n ≈
      couplingParametricKBoundaryTargetEventNumerator
          coupling cutoff small n event +
        couplingParametricKBoundaryTargetEventComplementNumerator
          coupling cutoff small n event := by
  unfold couplingParametricKBoundaryTargetPartition
    couplingParametricKBoundaryTargetEventNumerator
    couplingParametricKBoundaryTargetEventComplementNumerator
  exact listQSum_filter_partition
    (couplingParametricKSupportFamilyActivity coupling cutoff n) event
    (boundaryTargetFamilies small n)

private theorem mul_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _ (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem sub_eqv_both {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a - b ≈ a' - b' :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

/-! ## 2. Division-free cross differences -/

def couplingParametricKTargetEventCrossDifference
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKCompatibleSupportEventNumerator
        coupling cutoff n event *
      couplingParametricKEmbeddedTargetPartition coupling cutoff small n -
    couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n event *
      couplingParametricKCompatibleSupportGasPartition coupling cutoff n

def couplingParametricKBoundaryCrossDifference
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKBoundaryTargetEventNumerator
        coupling cutoff small n event *
      couplingParametricKEmbeddedTargetPartition coupling cutoff small n -
    couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n event *
      couplingParametricKBoundaryTargetPartition coupling cutoff small n

def couplingParametricKBoundaryCellCrossDifference
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) : Q' :=
  couplingParametricKBoundaryTargetEventNumerator
        coupling cutoff small n event *
      couplingParametricKEmbeddedTargetEventComplementNumerator
        coupling cutoff small n event -
    couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n event *
      couplingParametricKBoundaryTargetEventComplementNumerator
        coupling cutoff small n event

def couplingSpinSummedConnectedCylinderResidue
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) : Q' :=
  listQSum (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
    (connectedCylinderSourcePairs
      (roots := roots) (predicate := predicate) hsmall)

theorem couplingParametricKTargetEventCrossDifference_eqv_boundary
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTargetEventCrossDifference
        coupling cutoff small n event ≈
      couplingParametricKBoundaryCrossDifference
        coupling cutoff small n event := by
  have hnum :=
    couplingParametricKCompatibleEventNumerator_eqv_embedded_add_boundary
      coupling cutoff small n event
  have hden :=
    couplingParametricKCompatiblePartition_eqv_embedded_add_boundary
      coupling cutoff small n
  unfold couplingParametricKTargetEventCrossDifference
    couplingParametricKBoundaryCrossDifference
  refine Q'.eqv_trans _
    ((couplingParametricKEmbeddedTargetEventNumerator
            coupling cutoff small n event +
          couplingParametricKBoundaryTargetEventNumerator
            coupling cutoff small n event) *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n -
      couplingParametricKEmbeddedTargetEventNumerator
          coupling cutoff small n event *
        (couplingParametricKEmbeddedTargetPartition
            coupling cutoff small n +
          couplingParametricKBoundaryTargetPartition
            coupling cutoff small n)) _ ?_ ?_
  · exact sub_eqv_both
      (mul_eqv_both hnum (Q'.eqv_refl _))
      (mul_eqv_both (Q'.eqv_refl _) hden)
  · exact crossDifference_split
      (couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n event)
      (couplingParametricKBoundaryTargetEventNumerator
        coupling cutoff small n event)
      (couplingParametricKEmbeddedTargetPartition
        coupling cutoff small n)
      (couplingParametricKBoundaryTargetPartition
        coupling cutoff small n)

theorem couplingParametricKBoundaryCrossDifference_eqv_cells
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKBoundaryCrossDifference
        coupling cutoff small n event ≈
      couplingParametricKBoundaryCellCrossDifference
        coupling cutoff small n event := by
  have hembedded :=
    couplingParametricKEmbeddedPartition_eqv_event_add_complement
      coupling cutoff small n event
  have hboundary :=
    couplingParametricKBoundaryPartition_eqv_event_add_complement
      coupling cutoff small n event
  unfold couplingParametricKBoundaryCrossDifference
    couplingParametricKBoundaryCellCrossDifference
  refine Q'.eqv_trans _ _ _
    (sub_eqv_both
      (mul_eqv_both (Q'.eqv_refl _) hembedded)
      (mul_eqv_both (Q'.eqv_refl _) hboundary)) ?_
  exact eventBoundaryCrossDifference_cells
    (couplingParametricKEmbeddedTargetEventNumerator
      coupling cutoff small n event)
    (couplingParametricKBoundaryTargetEventNumerator
      coupling cutoff small n event)
    (couplingParametricKEmbeddedTargetEventComplementNumerator
      coupling cutoff small n event)
    (couplingParametricKBoundaryTargetEventComplementNumerator
      coupling cutoff small n event)

theorem couplingParametricKTargetEventCrossDifference_eqv_cells
    (coupling : Q') (cutoff small n : Nat)
    (event : List (List Nat) → Bool) :
    couplingParametricKTargetEventCrossDifference
        coupling cutoff small n event ≈
      couplingParametricKBoundaryCellCrossDifference
        coupling cutoff small n event := by
  exact Q'.eqv_trans _ _ _
    (couplingParametricKTargetEventCrossDifference_eqv_boundary
      coupling cutoff small n event)
    (couplingParametricKBoundaryCrossDifference_eqv_cells
      coupling cutoff small n event)

/-! ## 3. Identification and switching of the four cells -/

private theorem boundary_event_sum_eqv
    (coupling : Q') (cutoff small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum
        (couplingParametricKSupportFamilyActivity coupling cutoff n)
        (boundaryCylinderEventFamilyList small n roots predicate) ≈
      couplingParametricKBoundaryTargetEventNumerator
        coupling cutoff small n (markedCylinderEvent roots predicate) :=
  Q'.eqv_refl _

private theorem boundary_complement_sum_eqv
    (coupling : Q') (cutoff small n : Nat)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    listQSum
        (couplingParametricKSupportFamilyActivity coupling cutoff n)
        (boundaryCylinderComplementFamilyList small n roots predicate) ≈
      couplingParametricKBoundaryTargetEventComplementNumerator
        coupling cutoff small n (markedCylinderEvent roots predicate) :=
  Q'.eqv_refl _

private theorem embedded_event_sum_eqv
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingParametricKSupportFamilyActivity coupling cutoff n)
        (embeddedCylinderEventFamilyList small n roots predicate) ≈
      couplingParametricKEmbeddedTargetEventNumerator
        coupling cutoff small n (markedCylinderEvent roots predicate) := by
  unfold embeddedCylinderEventFamilyList
    couplingParametricKEmbeddedTargetEventNumerator
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (markedCylinderEvent roots predicate))

private theorem embedded_complement_sum_eqv
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) :
    listQSum
        (couplingParametricKSupportFamilyActivity coupling cutoff n)
        (embeddedCylinderComplementFamilyList small n roots predicate) ≈
      couplingParametricKEmbeddedTargetEventComplementNumerator
        coupling cutoff small n (markedCylinderEvent roots predicate) := by
  unfold embeddedCylinderComplementFamilyList
    couplingParametricKEmbeddedTargetEventComplementNumerator
  exact listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    ((embeddedCompatibleFamilies_perm_target hsmall).filter
      (fun family => !(markedCylinderEvent roots predicate family)))

theorem couplingSpinSummedBoundaryCylinderCellCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    couplingParametricKBoundaryCellCrossDifference coupling cutoff small n
        (markedCylinderEvent roots predicate) ≤
      couplingSpinSummedConnectedCylinderResidue
        coupling cutoff hsmall roots predicate := by
  unfold couplingParametricKBoundaryCellCrossDifference
    couplingSpinSummedConnectedCylinderResidue
  have hraw :=
    couplingSpinSummedBoundaryCylinderEvent_embeddedComplement_le_opposite_add_connected
      hcoupling cutoff hsmall roots predicate
  have hcells := Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (mul_eqv_both
        (Q'.eqv_symm
          (boundary_event_sum_eqv
            coupling cutoff small n roots predicate))
        (Q'.eqv_symm
          (embedded_complement_sum_eqv
            coupling cutoff hsmall roots predicate))))
    (Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.add_eqv_congr'
          (mul_eqv_both
            (boundary_complement_sum_eqv
              coupling cutoff small n roots predicate)
            (embedded_event_sum_eqv
              coupling cutoff hsmall roots predicate))
          (Q'.eqv_refl _))))
  have hreordered := Q'.le_trans' _ _ _ hcells
    (Q'.le_of_eqv
      (Q'.add_eqv_congr'
        (Q'.mul_comm_eqv
          (couplingParametricKBoundaryTargetEventComplementNumerator
            coupling cutoff small n (markedCylinderEvent roots predicate))
          (couplingParametricKEmbeddedTargetEventNumerator
            coupling cutoff small n (markedCylinderEvent roots predicate)))
        (Q'.eqv_refl _)))
  exact Q'.sub_le_of_le_add hreordered

def CouplingParametricKTargetCylinderConnectedBound
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (roots : List (CanonicalAtom n))
    (predicate : List Bool → Bool) : Prop :=
  couplingParametricKTargetEventCrossDifference coupling cutoff small n
      (markedCylinderEvent roots predicate) ≤
    couplingSpinSummedConnectedCylinderResidue
      coupling cutoff hsmall roots predicate

theorem couplingParametricKTargetCylinderCrossDifference_le_connected
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool) :
    CouplingParametricKTargetCylinderConnectedBound
      coupling cutoff hsmall roots predicate := by
  unfold CouplingParametricKTargetCylinderConnectedBound
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingParametricKTargetEventCrossDifference_eqv_cells
        coupling cutoff small n (markedCylinderEvent roots predicate)))
    (couplingSpinSummedBoundaryCylinderCellCrossDifference_le_connected
      hcoupling cutoff hsmall roots predicate)

#print axioms couplingParametricKCompatiblePartition_eqv_embedded_add_boundary
#print axioms couplingParametricKCompatibleEventNumerator_eqv_embedded_add_boundary
#print axioms couplingParametricKTargetEventCrossDifference_eqv_boundary
#print axioms couplingParametricKBoundaryCrossDifference_eqv_cells
#print axioms couplingSpinSummedBoundaryCylinderCellCrossDifference_le_connected
#print axioms couplingParametricKTargetCylinderCrossDifference_le_connected

end YMGap.Continuum.Z4CouplingParametricTargetCylinderRatio
