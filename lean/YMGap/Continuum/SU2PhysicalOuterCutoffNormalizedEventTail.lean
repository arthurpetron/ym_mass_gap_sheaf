/-
# Fixed-anchor normalized SU(2) outer-cutoff event tails

For a fixed finite four-dimensional box and the strong-coupling anchor
`w = 1/400`, the physical cutoff carriers are exactly nested.  Both the full
partition and every Boolean-event numerator split into their retained part
plus the literal new-label sector.

The generic constructive rational normalization lemma then gives the sharp
bound

  |P_M(event) - P_K(event)| <= new total mass.

Combining this with the degree-thirteen incidence/Fubini estimate and its
executable schedule makes the right-hand side independent of the later
Peter--Weyl cutoff `K`.

This is a fixed-anchor, fixed-finite-box statement.  It contains no spacing
limit, continuum-trajectory comparison, or infinite-volume assertion.

## Axiom gate

Finite `List`, `Nat`, and `Q'` algebra only.  No `Classical.*`, `Real`,
`native_decide`, `sorry`, custom axiom, choice, or noncomputable declaration.
-/

import YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
import YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule
import YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal

namespace YMGap.Continuum.SU2PhysicalOuterCutoffNormalizedEventTail

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4U1OuterCutoffNormalizedEventTail
open YMGap.Continuum.BondMovingScaledNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2PhysicalOuterCutoffAnchorSchedule
open YMGap.Continuum.SU2PhysicalOuterCutoffFiniteFubiniTail
open YMGap.Continuum.SU2PhysicalOuterCutoffTensorTail
open YMGap.Continuum.Z4CouplingParametricCutoffEventCofinal
open YMGap.Continuum.Z4CouplingParametricFiniteCylinderLaw
open YMGap.Continuum.Z4FiniteBoxTrivalentResolution
open YMGap.Continuum.Z4ParametricCutoffEventCofinal
open YMGap.Continuum.Z4ParametricPhysicalCutoffPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem positive_of_one_le_local
    {q : Q'} (hq : (1 : Q') ≤ q) :
    (0 : Q') < q :=
  YMGap.Continuum.HeatKernelRGStep.lt_of_lt_of_le
    (by decide) hq

private theorem one_le_add_nonnegative_local
    {d n : Q'} (hd : (1 : Q') ≤ d)
    (hn : (0 : Q') ≤ n) :
    (1 : Q') ≤ d + n :=
  Q'.le_trans' _ _ _ hd
    (Q'.add_le_self_of_nonneg d n hn)

/-! ## 1. Arbitrary-cutoff anchor event law -/

/-- Exact normalized probability of an arbitrary Boolean predicate of the
physical face labelling at a finite cutoff. -/
def anchorPhysicalCutoffEventProbability
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) : Q' :=
  Q'.divPos
    (parametricKEventNumerator anchorCoupling
      cutoff volume event)
    (parametricKPhysicalPartition anchorCoupling
      cutoff volume)
    (couplingKPhysicalPartition_pos
      (coupling := anchorCoupling)
      (by decide) cutoff volume)

theorem anchorEventNumerator_nonnegative
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      parametricKEventNumerator anchorCoupling
        cutoff volume event :=
  parametricKEventNumerator_nonnegative
    (w := anchorCoupling) (by decide)
    cutoff volume event

theorem anchorEventNumerator_le_partition
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator anchorCoupling
        cutoff volume event ≤
      parametricKPhysicalPartition anchorCoupling
        cutoff volume :=
  parametricKEventNumerator_le_partition
    (w := anchorCoupling) (by decide)
    cutoff volume event

theorem anchorPhysicalCutoffEventProbability_nonnegative
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      anchorPhysicalCutoffEventProbability
        cutoff volume event := by
  unfold anchorPhysicalCutoffEventProbability Q'.divPos
  exact Q'.mul_nonneg _ _
    (anchorEventNumerator_nonnegative
      cutoff volume event)
    (Q'.le_of_lt
      (Q'.recipPos_pos _
        (couplingKPhysicalPartition_pos
          (coupling := anchorCoupling)
          (by decide) cutoff volume)))

theorem anchorPhysicalCutoffEventProbability_le_one
    (cutoff volume : Nat)
    (event : EdgeLabelling → Bool) :
    anchorPhysicalCutoffEventProbability
        cutoff volume event ≤
      (1 : Q') := by
  unfold anchorPhysicalCutoffEventProbability
  apply Q'.divPos_le_of_le_mul
  exact Q'.le_trans' _ _ _
    (anchorEventNumerator_le_partition
      cutoff volume event)
    (Q'.ge_of_eqv
      (Q'.one_mul_eqv
        (parametricKPhysicalPartition
          anchorCoupling cutoff volume)))

/-! ## 2. Exact retained-plus-new decomposition -/

theorem anchorEventNumerator_eq_old_add_new
    {M K volume : Nat} (hMK : M ≤ K)
    (event : EdgeLabelling → Bool) :
    parametricKEventNumerator anchorCoupling
        K volume event ≈
      parametricKEventNumerator anchorCoupling
          M volume event +
        parametricKEventCutoffIncrement anchorCoupling
          M K volume event :=
  parametricKEventNumerator_eq_base_add_increment
    (w := anchorCoupling) hMK

theorem anchorPartition_eq_old_add_new
    {M K volume : Nat} (hMK : M ≤ K) :
    parametricKPhysicalPartition anchorCoupling
        K volume ≈
      parametricKPhysicalPartition anchorCoupling
          M volume +
        parametricKCutoffIncrement anchorCoupling
          M K volume :=
  parametricKPhysicalPartition_eq_base_add_increment
    (w := anchorCoupling) hMK

theorem anchorNewEventMass_nonnegative
    (M K volume : Nat)
    (event : EdgeLabelling → Bool) :
    (0 : Q') ≤
      parametricKEventCutoffIncrement anchorCoupling
        M K volume event :=
  parametricKEventCutoffIncrement_nonnegative
    (w := anchorCoupling) (by decide)
    M K volume event

theorem anchorNewEventMass_le_newTotalMass
    (M K volume : Nat)
    (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement anchorCoupling
        M K volume event ≤
      parametricKCutoffIncrement anchorCoupling
        M K volume :=
  parametricKEventCutoffIncrement_le_partitionIncrement
    (w := anchorCoupling) (by decide)
    M K volume event

/-! ## 3. Sharp normalized arbitrary-event stability -/

/-- For every nested pair of physical cutoffs, the normalized probability of
any Boolean event changes by at most the complete mass of the new sector.
There is no carrier-cardinality factor. -/
theorem anchorPhysicalCutoffEventProbability_abs_le_increment
    {M K volume : Nat} (hMK : M ≤ K)
    (event : EdgeLabelling → Bool) :
    absQ
        (anchorPhysicalCutoffEventProbability
            M volume event +
          -anchorPhysicalCutoffEventProbability
            K volume event) ≤
      parametricKCutoffIncrement anchorCoupling
        M K volume := by
  let a :=
    parametricKEventNumerator anchorCoupling
      M volume event
  let b :=
    parametricKEventCutoffIncrement anchorCoupling
      M K volume event
  let d :=
    parametricKPhysicalPartition anchorCoupling
      M volume
  let n :=
    parametricKCutoffIncrement anchorCoupling
      M K volume
  let A :=
    parametricKEventNumerator anchorCoupling
      K volume event
  let D :=
    parametricKPhysicalPartition anchorCoupling
      K volume
  have ha : (0 : Q') ≤ a := by
    dsimp only [a]
    exact anchorEventNumerator_nonnegative
      M volume event
  have hb : (0 : Q') ≤ b := by
    dsimp only [b]
    exact anchorNewEventMass_nonnegative
      M K volume event
  have hn : (0 : Q') ≤ n := by
    dsimp only [n]
    exact parametricKCutoffIncrement_nonnegative
      (w := anchorCoupling) (by decide)
      M K volume
  have hd1 : (1 : Q') ≤ d := by
    dsimp only [d]
    exact couplingKPhysicalPartition_one_le
      (coupling := anchorCoupling)
      (by decide) M volume
  have had : a ≤ d := by
    dsimp only [a, d]
    exact anchorEventNumerator_le_partition
      M volume event
  have hbn : b ≤ n := by
    dsimp only [b, n]
    exact anchorNewEventMass_le_newTotalMass
      M K volume event
  have hbase :=
    nested_normalized_event_abs_le_newMass
      ha hb hn hd1 had hbn
  have hd :
      (0 : Q') < d :=
    positive_of_one_le_local hd1
  have hdn :
      (0 : Q') < d + n :=
    positive_of_one_le_local
      (one_le_add_nonnegative_local hd1 hn)
  have hbaseExplicit :
      absQ
          (Q'.divPos a d hd +
            -(Q'.divPos (a + b) (d + n) hdn)) ≤
        n := by
    simpa only using hbase
  have hA : A ≈ a + b := by
    dsimp only [A, a, b]
    exact anchorEventNumerator_eq_old_add_new
      hMK event
  have hD : D ≈ d + n := by
    dsimp only [D, d, n]
    exact anchorPartition_eq_old_add_new hMK
  have hDactual :
      (0 : Q') < D := by
    dsimp only [D]
    exact couplingKPhysicalPartition_pos
      (coupling := anchorCoupling)
      (by decide) K volume
  have hlarge :
      Q'.divPos A D hDactual ≈
        Q'.divPos (a + b) (d + n) hdn := by
    apply Q'.eqv_of_le_le
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos A D hDactual)
            (d + n) D (Q'.eqv_symm hD))
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv A D hDactual)
            hA))
    · apply Q'.le_divPos_of_mul_le
      exact Q'.le_of_eqv
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left
            (Q'.divPos (a + b) (d + n) hdn)
            D (d + n) hD)
          (Q'.eqv_trans _ _ _
            (Q'.divPos_mul_eqv
              (a + b) (d + n) hdn)
            (Q'.eqv_symm hA)))
  unfold anchorPhysicalCutoffEventProbability
  dsimp only [a, b, d, n, A, D] at hbaseExplicit hlarge
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (YMGap.Continuum.ContinuumYMStack.absQ_eqv_congr
        (Q'.add_eqv_congr_left
          (Q'.divPos
            (parametricKEventNumerator anchorCoupling
              M volume event)
            (parametricKPhysicalPartition anchorCoupling
              M volume)
            (couplingKPhysicalPartition_pos
              (coupling := anchorCoupling)
              (by decide) M volume))
          _
          (-(Q'.divPos
            (parametricKEventNumerator anchorCoupling
                M volume event +
              parametricKEventCutoffIncrement
                anchorCoupling M K volume event)
            (parametricKPhysicalPartition anchorCoupling
                M volume +
              parametricKCutoffIncrement
                anchorCoupling M K volume)
            hdn))
          (Q'.neg_eqv_congr _ _ hlarge))))
    hbaseExplicit

/-! ## 4. Scheduled outer-cutoff-uniform normalized tail -/

theorem anchorScheduledEventIncrement_le_tensorEnvelope
    (precision : Nat) {K volume : Nat}
    (hretained :
      anchorPhysicalRetainedCutoff precision ≤ K)
    (event : EdgeLabelling → Bool) :
    parametricKEventCutoffIncrement anchorCoupling
        (anchorPhysicalRetainedCutoff precision)
        K volume event ≤
      su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalRetainedCutoff precision)
        precision
        (plaquetteEdgeCount volume) := by
  exact Q'.le_trans' _ _ _
    (anchorNewEventMass_le_newTotalMass
      (anchorPhysicalRetainedCutoff precision)
      K volume event)
    (anchorScheduledCutoffIncrement_le_tensorEnvelope
      precision hretained)

/-- Main normalized-event tail theorem.  For fixed precision and finite box,
the right-hand side is independent of every later cutoff containing the
retained window. -/
theorem anchorScheduledEventProbability_abs_le_tensorEnvelope
    (precision : Nat) {K volume : Nat}
    (hretained :
      anchorPhysicalRetainedCutoff precision ≤ K)
    (event : EdgeLabelling → Bool) :
    absQ
        (anchorPhysicalCutoffEventProbability
            (anchorPhysicalRetainedCutoff precision)
            volume event +
          -anchorPhysicalCutoffEventProbability
            K volume event) ≤
      su2PhysicalTensorTailEnvelope
        anchorCoupling
        anchorPhysicalBaseCutoff
        (anchorPhysicalRetainedCutoff precision)
        precision
        (plaquetteEdgeCount volume) := by
  exact Q'.le_trans' _ _ _
    (anchorPhysicalCutoffEventProbability_abs_le_increment
      hretained event)
    (anchorScheduledCutoffIncrement_le_tensorEnvelope
      precision hretained)

#print axioms anchorEventNumerator_eq_old_add_new
#print axioms anchorPartition_eq_old_add_new
#print axioms anchorNewEventMass_le_newTotalMass
#print axioms anchorPhysicalCutoffEventProbability_nonnegative
#print axioms anchorPhysicalCutoffEventProbability_le_one
#print axioms anchorPhysicalCutoffEventProbability_abs_le_increment
#print axioms anchorScheduledEventIncrement_le_tensorEnvelope
#print axioms anchorScheduledEventProbability_abs_le_tensorEnvelope

end YMGap.Continuum.SU2PhysicalOuterCutoffNormalizedEventTail
