/-
# The guarded literal observable row has residual rate at most three quarters

The literal pivot cylinder now contributes at least one quarter of the
normalized successful recoupling row at every positive cutoff.  This module
places that row on the actual support-connected source carrier and records
the resulting unthinned residual rate.

The conclusion is deliberately row-local.  Canonical first-source thinning
can erase a row when several sources spend the same receiver column, so the
three-quarter bound is not yet a shared-column posterior contraction or a
face-covariance estimate.  The next proof obligation is exactly to retain an
aggregate fraction through receiver allocation, or to provide a different
joint column-capacity certificate.

Constructive contract: exact finite `Q'` order, the checked quarter-mass
injection, and literal support connectivity only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccessfulMass
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedFirstSourceThinning
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRealization
open YMGap.Continuum.CompactDualSlabObservablePairedStrandRecouplingRow
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBistochasticQKernelProduct
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableSuccessfulMass

local infix:50 " ≈ " => Q'.eqv

private theorem q_lt_of_lt_of_le_local {a b c : Q'}
    (hab : a < b) (hbc : b ≤ c) : a < c := by
  have habCross :
      a.num * (b.den : Int) < b.num * (a.den : Int) := hab
  have hbcCross :
      b.num * (c.den : Int) ≤ c.num * (b.den : Int) := hbc
  show a.num * (c.den : Int) < c.num * (a.den : Int)
  have hfirst :
      (a.num * (c.den : Int)) * (b.den : Int) <
        (b.num * (a.den : Int)) * (c.den : Int) := by
    have hscaled := Int.mul_lt_mul_of_pos_right habCross
      (by exact_mod_cast c.den_pos : (0 : Int) < (c.den : Int))
    have hreorder :
        (a.num * (b.den : Int)) * (c.den : Int) =
          (a.num * (c.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (c.den : Int)]
    rwa [hreorder] at hscaled
  have hsecond :
      (b.num * (a.den : Int)) * (c.den : Int) ≤
        (c.num * (a.den : Int)) * (b.den : Int) := by
    have hscaled := Int.mul_le_mul_of_nonneg_right hbcCross
      (by exact_mod_cast Nat.zero_le a.den : (0 : Int) ≤ (a.den : Int))
    have hleft :
        (b.num * (c.den : Int)) * (a.den : Int) =
          (b.num * (a.den : Int)) * (c.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (c.den : Int) (a.den : Int)]
    have hright :
        (c.num * (b.den : Int)) * (a.den : Int) =
          (c.num * (a.den : Int)) * (b.den : Int) := by
      rw [Int.mul_assoc, Int.mul_assoc,
        Int.mul_comm (b.den : Int) (a.den : Int)]
    rwa [hleft, hright] at hscaled
  have hcombined := Int.lt_of_lt_of_le hfirst hsecond
  exact Int.lt_of_mul_lt_mul_right hcombined
    (by exact_mod_cast Nat.zero_le b.den)

private theorem q_nonpositive_of_not_positive_local
    {q : Q'} (hnot : ¬ (0 : Q') < q) : q ≤ 0 := by
  show q.num * (1 : Int) ≤ (0 : Int) * (q.den : Int)
  rw [Int.mul_one, Int.zero_mul]
  exact Int.not_lt.mp (fun hnum =>
    hnot (CReal.pos_of_num_pos hnum))

private theorem q_eqv_zero_of_nonnegative_of_not_positive_local
    {q : Q'} (hnonnegative : (0 : Q') ≤ q)
    (hnot : ¬ (0 : Q') < q) : q ≈ 0 := by
  have hnonpositive : q ≤ 0 :=
    q_nonpositive_of_not_positive_local hnot
  show q.num * ((0 : Q').den : Int) =
    (0 : Q').num * (q.den : Int)
  exact Int.le_antisymm hnonpositive hnonnegative

private theorem listQSum_filter_eq_of_zero_local
    {A : Type} (value : A → Q') (predicate : A → Bool) :
    ∀ items : List A,
      (∀ item, item ∈ items → predicate item = false →
        value item ≈ 0) →
      listQSum value (items.filter predicate) ≈
        listQSum value items
  | [], _ => Q'.eqv_refl 0
  | head :: tail, hzero => by
      cases hp : predicate head with
      | false =>
          simp only [List.filter_cons, hp, Bool.false_eq_true,
            if_false, listQSum]
          exact Q'.eqv_trans _ _ _
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))
            (Q'.eqv_symm
              (Q'.eqv_trans _ _ _
                (Q'.add_eqv_congr'
                  (hzero head List.mem_cons_self hp)
                  (Q'.eqv_refl _))
                (Q'.eqv_of_eq (Q'.zero_add' _))))
      | true =>
          simp only [List.filter_cons, hp, if_true, listQSum]
          exact Q'.add_eqv_congr'
            (Q'.eqv_refl _)
            (listQSum_filter_eq_of_zero_local
              value predicate tail
              (fun item hitem =>
                hzero item
                  (List.mem_cons_of_mem head hitem)))

/-! ## 1. The arbitrary-cutoff guarded source is support-connected -/

theorem reflectedBentGuardGraftObservableSourcePairAtCutoff_connected
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    slabObservableTwoReplicaPairPairedSupportConnectedB
      D reflectedBentRootFaceId reflectedBentTargetFaceId
      (reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff hextent state) = true := by
  unfold slabObservableTwoReplicaPairPairedSupportConnectedB
    slabObservableTwoReplicaPairPairedSupportSwapMask
    slabTwoReplicaSupportSwapMask
    reflectedBentGuardGraftObservableSourcePairAtCutoff
  rw [reflectedBentGuardGraftLeftPositiveEntryAtCutoff_physical,
    reflectedBentGuardGraftRightExpandedEntryAtCutoff_physical]
  rw [hextent]
  exact decide_eq_true
    (reflectedBentGuardGraft_root_mem_targetSupportComponent
      D hextent state)

theorem reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_connected
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff hextent state ∈
      slabObservablePairedSupportConnectedFourCellSourcePairs
        D reflectedBentRootFaceId reflectedBentTargetFaceId := by
  apply List.mem_filter.mpr
  exact ⟨
    reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_fourCell
      D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePairAtCutoff_connected
      D hcutoff hextent state⟩

def reflectedBentGuardGraftConnectedStrandSourceAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    SlabObservablePairedConnectedStrandSource
      D reflectedBentRootFaceId reflectedBentTargetFaceId :=
  ⟨reflectedBentGuardGraftObservableSourcePairAtCutoff
      D hcutoff hextent state,
    reflectedBentGuardGraftObservableSourcePairAtCutoff_mem_connected
      D hcutoff hextent state⟩

theorem reflectedBentGuardGraftConnectedStrandSourceAtCutoff_toRecouplingSource
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
        D hcutoff hextent state).toRecouplingSource =
      reflectedBentGuardGraftObservableRecouplingSourceAtCutoff
        D hcutoff hextent state := by
  apply Subtype.ext
  exact (reflectedBentGuardGraftObservableSourcePackageAtCutoff
    D hcutoff hextent state).sourcePair_eq.symm

/-! ## 2. Exact successful fraction -/

def reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Q' :=
  slabObservablePairedStrandDisconnectionMass D
    reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      D hcutoff hextent state).toRecouplingSource

theorem reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_quarter
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    oneQuarter ≤
      reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
        D hcutoff hextent state := by
  unfold reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
  rw [reflectedBentGuardGraftConnectedStrandSourceAtCutoff_toRecouplingSource]
  exact reflectedBentGuardGraftLiteralObservableDisconnectionMass_quarter
    D hcutoff hextent state

theorem reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_pos
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (0 : Q') <
      reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
        D hcutoff hextent state :=
  q_lt_of_lt_of_le_local (by decide)
    (reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_quarter
      D hcutoff hextent state)

theorem reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_le_one
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
        D hcutoff hextent state ≤ (1 : Q') := by
  unfold reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
  exact slabObservablePairedStrandDisconnectionMass_le_one
    D reflectedBentRootFaceId reflectedBentTargetFaceId
    (reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      D hcutoff hextent state).toRecouplingSource

/-! ## 3. The receiver-facing unthinned connected row -/

/-- Removing zero-weight successful choices does not change the guarded
connected row mass.  This is the exact row consumed by first-source thinning;
the later thinning itself is intentionally absent from this equality. -/
theorem reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_eqv_successfulFraction
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      D hcutoff hextent state
    listQSum
        (slabObservablePairedConnectedStrandWeight D
          reflectedBentRootFaceId reflectedBentTargetFaceId source)
        (slabObservablePairedConnectedStrandChoices D
          reflectedBentRootFaceId reflectedBentTargetFaceId source) ≈
      reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
        D hcutoff hextent state := by
  let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
    D hcutoff hextent state
  let successfulWeight :=
    slabObservablePairedStrandSuccessfulWeight D
      reflectedBentRootFaceId reflectedBentTargetFaceId
      source.toRecouplingSource
  let positiveB := fun choice => decide ((0 : Q') < successfulWeight choice)
  have hfilter :
      listQSum successfulWeight
          ((slabObservablePairedStrandSuccessfulChoices D
            reflectedBentRootFaceId reflectedBentTargetFaceId
            source.toRecouplingSource).filter positiveB) ≈
        listQSum successfulWeight
          (slabObservablePairedStrandSuccessfulChoices D
            reflectedBentRootFaceId reflectedBentTargetFaceId
            source.toRecouplingSource) := by
    apply listQSum_filter_eq_of_zero_local
    intro choice _ hfalse
    apply q_eqv_zero_of_nonnegative_of_not_positive_local
    · exact slabObservablePairedStrandSuccessfulWeight_nonnegative D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        source.toRecouplingSource choice
    · simpa only [positiveB, decide_eq_false_iff_not] using hfalse
  exact Q'.eqv_trans _ _ _
    (by simpa only [source, successfulWeight, positiveB,
        slabObservablePairedConnectedStrandWeight,
        slabObservablePairedConnectedStrandChoices] using hfilter)
    (by
      unfold reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
      exact slabObservablePairedStrandSuccessfulWeight_row_mass D
        reflectedBentRootFaceId reflectedBentTargetFaceId
        source.toRecouplingSource)

/-- The complete positive successful-choice row, before collision-aware
first-source thinning, retains at least one quarter. -/
theorem reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_quarter
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
      D hcutoff hextent state
    oneQuarter ≤
      listQSum
        (slabObservablePairedConnectedStrandWeight D
          reflectedBentRootFaceId reflectedBentTargetFaceId source)
        (slabObservablePairedConnectedStrandChoices D
          reflectedBentRootFaceId reflectedBentTargetFaceId source) := by
  let source := reflectedBentGuardGraftConnectedStrandSourceAtCutoff
    D hcutoff hextent state
  exact Q'.le_trans' _ _ _
    (reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_quarter
      D hcutoff hextent state)
    (Q'.ge_of_eqv
      (reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_eqv_successfulFraction
        D hcutoff hextent state))

/-! ## 4. The exact residual rate -/

/-- The exact untransported portion of the normalized guarded row. -/
def reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) : Q' :=
  (1 : Q') +
    -reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff
      D hcutoff hextent state

/-- The displayed numerical ceiling for the guarded row residue. -/
def reflectedBentGuardGraftLiteralObservableThreeQuarterRate : Q' :=
  Q'.mkPos 3 4 (by decide)

theorem reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff_nonnegative
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    (0 : Q') ≤
      reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
        D hcutoff hextent state := by
  unfold reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
  exact Q'.sub_nonneg_of_le
    (reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_le_one
      D hcutoff hextent state)

theorem reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff_le_threeQuarter
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
        D hcutoff hextent state ≤
      reflectedBentGuardGraftLiteralObservableThreeQuarterRate := by
  unfold reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
    reflectedBentGuardGraftLiteralObservableThreeQuarterRate
  exact Q'.le_trans' _ _ _
    (Q'.add_le_add_left (1 : Q') _ _
      (Q'.neg_le_neg
        (reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_quarter
          D hcutoff hextent state)))
    (Q'.le_of_eqv (by decide))

/-- **Strict connected-row contraction.**  The unthinned guarded recoupling
row leaves residual rate at most `3/4`, hence strictly below one. -/
theorem reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff_lt_one
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff
        D hcutoff hextent state < (1 : Q') := by
  exact Q'.lt_of_le_of_lt
    (reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff_le_threeQuarter
      D hcutoff hextent state)
    (by decide)

#print axioms reflectedBentGuardGraftObservableSourcePairAtCutoff_connected
#print axioms reflectedBentGuardGraftConnectedStrandSourceAtCutoff_toRecouplingSource
#print axioms reflectedBentGuardGraftLiteralObservableSuccessfulFractionAtCutoff_quarter
#print axioms reflectedBentGuardGraftConnectedStrandRowMassAtCutoff_quarter
#print axioms reflectedBentGuardGraftLiteralObservableResidualRateAtCutoff_lt_one

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableConnectedRowContraction
