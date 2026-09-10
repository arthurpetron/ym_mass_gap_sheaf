/-
# Ground-plus-excitation decomposition of every tilted production row

The geometric parity state is the unique target whose face labels are the
minimal parity-compatible values below a cutoff-one packet total.  This file
uses a Boolean equality test on the finite coarse face carrier, rather than a
decidable equality on function-valued labellings, to isolate that target.

The complete source-dependent tilted-Gibbs denominator then splits exactly
into its positive parity-ground summand plus the remaining excitation mass.
Every remaining target carries a witnessed face whose parity excitation
level is positive, and each local target is reconstructed exactly as

  source % 2 + 2 * excitationLevel.

This is the exact polymerization coordinate for the next analytic bound.  No
volume-uniform estimate on the excitation mass is asserted here.

Constructive contract: finite Boolean filtering and exact rational algebra
only; no `Classical`, choice, `native_decide`, proof hole, noncomputable
declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
import YMGap.Continuum.FiniteWeightedCartesianInjection

namespace YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualCutoffOneParitySlabTarget
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceLoweringConditionalLaw
open YMGap.Continuum.Z4DyadicBinarySourceParityGroundState
open YMGap.Continuum.Z4DyadicSpinFourLoweringDownset
open YMGap.Continuum.Z4DyadicSpinFourLoweringGibbsTilt
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Exact local excitation coordinates -/

/-- Number of two-spin raising steps above the minimal parity-compatible
target. -/
def spinFourParityExcitationLevel
    (sourceSpin targetSpin : Nat) : Nat :=
  (targetSpin - sourceSpin % 2) / 2

/-- Every supported local target is reconstructed from its parity ground
spin and its excitation level. -/
theorem spinFourLoweringTarget_eq_ground_add_twice_excitationLevel
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    targetSpin = sourceSpin % 2 +
      2 * spinFourParityExcitationLevel sourceSpin targetSpin := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourParityExcitationLevel] at *

/-- On the local lowering carrier, positive excitation level is equivalent
to not being the parity ground spin. -/
theorem spinFourParityExcitationLevel_pos_iff_ne_ground
    {sourceSpin targetSpin : Nat}
    (hsource : sourceSpin ≤ 4) (htarget : targetSpin ≤ 4)
    (hlowering : targetSpin ≤ sourceSpin ∧
      targetSpin % 2 = sourceSpin % 2) :
    0 < spinFourParityExcitationLevel sourceSpin targetSpin ↔
      targetSpin ≠ sourceSpin % 2 := by
  have hs : sourceSpin = 0 ∨ sourceSpin = 1 ∨ sourceSpin = 2 ∨
      sourceSpin = 3 ∨ sourceSpin = 4 := by
    omega
  have ht : targetSpin = 0 ∨ targetSpin = 1 ∨ targetSpin = 2 ∨
      targetSpin = 3 ∨ targetSpin = 4 := by
    omega
  rcases hs with rfl | rfl | rfl | rfl | rfl <;>
    rcases ht with rfl | rfl | rfl | rfl | rfl <;>
    simp [spinFourParityExcitationLevel] at *

/-! ## 2. A finite-carrier ground-state discriminator -/

/-- Boolean test that a target equals the source's parity ground label on
every physical coarse face. -/
def spinFourParityGroundTargetB
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) : Bool :=
  S.coarse.faceEdges.all fun faceId =>
    decide (targetState faceId = sourceState faceId % 2)

theorem spinFourParityGroundTargetB_true_iff
    (S : SlabScalePair) (sourceState targetState : EdgeLabelling) :
    spinFourParityGroundTargetB S sourceState targetState = true ↔
      ∀ faceId, faceId ∈ S.coarse.faceEdges →
        targetState faceId = sourceState faceId % 2 := by
  unfold spinFourParityGroundTargetB
  rw [List.all_eq_true]
  simp only [decide_eq_true_eq]

/-- On the physical coarse carrier, the finite face test identifies exactly
the geometric parity state. -/
theorem spinFourParityGroundTargetB_true_iff_eq_parityState
    (S : SlabScalePair) {fineState targetState : EdgeLabelling}
    (hfineCutoff : S.fine.cutoff = 1)
    (hfineMem : fineState ∈ S.fine.physicalLabellings)
    (htargetMem : targetState ∈ S.coarse.physicalLabellings) :
    spinFourParityGroundTargetB S
        (wholeSlabFinePacketTotalLabelling S fineState) targetState = true ↔
      targetState = cutoffOneCoarseParityState S fineState := by
  constructor
  · intro htest
    have hpoint := (spinFourParityGroundTargetB_true_iff S _ _).mp htest
    have htargetSound := boundedEdgeLabellings_sound
      S.coarse.cutoff S.coarse.faceEdges targetState htargetMem
    have hgroundMem := cutoffOneCoarseParityState_mem hfineCutoff fineState
    have hgroundSound := boundedEdgeLabellings_sound
      S.coarse.cutoff S.coarse.faceEdges
        (cutoffOneCoarseParityState S fineState) hgroundMem
    funext faceId
    by_cases hface : faceId ∈ S.coarse.faceEdges
    · exact (hpoint faceId hface).trans
        (cutoffOneCoarseParityState_face_eq_total_mod_two
          S hfineCutoff hfineMem hface).symm
    · rw [htargetSound.2 faceId hface,
        hgroundSound.2 faceId hface]
  · intro heq
    subst targetState
    apply (spinFourParityGroundTargetB_true_iff S _ _).mpr
    intro faceId hface
    exact cutoffOneCoarseParityState_face_eq_total_mod_two
      S hfineCutoff hfineMem hface

/-- The exact lowering carrier is duplicate-free. -/
theorem spinFourLoweringTargets_nodup
    (S : SlabScalePair) (sourceState : EdgeLabelling) :
    (spinFourLoweringTargets S sourceState).Nodup := by
  unfold spinFourLoweringTargets
  exact (slabPhysicalLabellings_nodup S.coarse).filter _

private theorem filter_eq_nil_of_all_false_local {A : Type}
    (test : A → Bool) : ∀ items : List A,
    (∀ item, item ∈ items → test item = false) →
      items.filter test = []
  | [], _ => rfl
  | head :: tail, hfalse => by
      have hhead := hfalse head List.mem_cons_self
      have htail := filter_eq_nil_of_all_false_local test tail
        (fun item hmem =>
          hfalse item (List.mem_cons_of_mem head hmem))
      simp [hhead, htail]

private theorem filter_eq_singleton_of_unique_true_local {A : Type}
    (test : A → Bool) (selected : A) : ∀ items : List A,
    items.Nodup → selected ∈ items → test selected = true →
    (∀ item, item ∈ items → test item = true → item = selected) →
      items.filter test = [selected]
  | [], _, hmem, _, _ => False.elim (List.not_mem_nil hmem)
  | head :: tail, hnodup, hselected, hselectedTrue, hunique => by
      have hparts := List.nodup_cons.mp hnodup
      cases hhead : test head with
      | false =>
          have hselectedTail : selected ∈ tail := by
            rcases List.mem_cons.mp hselected with heq | htail
            · subst head
              rw [hselectedTrue] at hhead
              cases hhead
            · exact htail
          have htailFilter :=
            filter_eq_singleton_of_unique_true_local
              test selected tail hparts.2 hselectedTail hselectedTrue
              (fun item hmem htrue =>
                hunique item (List.mem_cons_of_mem head hmem) htrue)
          simp [hhead, htailFilter]
      | true =>
          have hheadEq := hunique head List.mem_cons_self hhead
          subst head
          have htailFalse : ∀ item, item ∈ tail → test item = false := by
            intro item hmem
            cases hitem : test item with
            | false => rfl
            | true =>
                have hitemEq := hunique item
                  (List.mem_cons_of_mem selected hmem) hitem
                subst item
                exact False.elim (hparts.1 hmem)
          have htailFilter :=
            filter_eq_nil_of_all_false_local test tail htailFalse
          simp [hhead, htailFilter]

/-! ## 3. Exact singleton-plus-excitation split -/

/-- The non-ground targets in one positive source's exact lowering row. -/
def positivePhysicalSourceParityExcitationTargets
    (S : SlabScalePair) (source : PositivePhysicalSource S) :
    List EdgeLabelling :=
  (spinFourLoweringTargets S
      (wholeSlabFinePacketTotalLabelling S source.1)).filter
    (fun targetState =>
      !(spinFourParityGroundTargetB S
        (wholeSlabFinePacketTotalLabelling S source.1) targetState))

/-- The exact tilted-Gibbs mass carried by all non-ground targets. -/
def positivePhysicalSourceParityExcitationMass
    (S : SlabScalePair) (source : PositivePhysicalSource S) : Q' :=
  listQSum
    (fun targetState =>
      Q'.ofNat
          (spinFourLoweringMultiplicityProduct S
            (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
        S.coarse.physicalTerm targetState)
    (positivePhysicalSourceParityExcitationTargets S source)

/-- The ground-state test filters the exact lowering carrier to the single
geometric parity target. -/
theorem positivePhysicalSourceParityGround_filter_eq_singleton
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    (spinFourLoweringTargets S
        (wholeSlabFinePacketTotalLabelling S source.1)).filter
      (spinFourParityGroundTargetB S
        (wholeSlabFinePacketTotalLabelling S source.1)) =
      [cutoffOneCoarseParityState S source.1] := by
  let targets := spinFourLoweringTargets S
    (wholeSlabFinePacketTotalLabelling S source.1)
  let test := spinFourParityGroundTargetB S
    (wholeSlabFinePacketTotalLabelling S source.1)
  apply filter_eq_singleton_of_unique_true_local
  · exact spinFourLoweringTargets_nodup S _
  · exact cutoffOneCoarseParityState_mem_totalLoweringTargets
      S hfineCutoff source.2.1
  · exact (spinFourParityGroundTargetB_true_iff_eq_parityState
      S hfineCutoff source.2.1
        (cutoffOneCoarseParityState_mem hfineCutoff source.1)).mpr rfl
  · intro targetState htarget htest
    exact (spinFourParityGroundTargetB_true_iff_eq_parityState
      S hfineCutoff source.2.1
        ((mem_spinFourLoweringTargets_iff S _ _).mp htarget).1).mp htest

/-- Every source-dependent tilted denominator is exactly its positive ground
summand plus the complete non-ground excitation mass. -/
theorem positivePhysicalSourceTiltedGibbsRowMass_eqv_ground_add_excitation
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S) :
    positivePhysicalSourceTiltedGibbsRowMass S source ≈
      positivePhysicalSourceParityGroundMass S source +
        positivePhysicalSourceParityExcitationMass S source := by
  let weight := fun targetState =>
    Q'.ofNat
        (spinFourLoweringMultiplicityProduct S
          (wholeSlabFinePacketTotalLabelling S source.1) targetState) *
      S.coarse.physicalTerm targetState
  let targets := spinFourLoweringTargets S
    (wholeSlabFinePacketTotalLabelling S source.1)
  let test := spinFourParityGroundTargetB S
    (wholeSlabFinePacketTotalLabelling S source.1)
  have hpartition := listQSum_filter_partition weight test targets
  rw [positivePhysicalSourceParityGround_filter_eq_singleton
    S hfineCutoff source] at hpartition
  simpa only [positivePhysicalSourceTiltedGibbsRowMass,
    positivePhysicalSourceParityGroundMass,
    positivePhysicalSourceParityExcitationMass,
    positivePhysicalSourceParityExcitationTargets,
    listQSum, Q'.add_zero'] using hpartition

/-- The excitation mass is nonnegative at nonnegative coarse coupling. -/
theorem positivePhysicalSourceParityExcitationMass_nonnegative
    (S : SlabScalePair)
    (hcoarseCoupling : (0 : Q') ≤ S.coarse.coupling)
    (source : PositivePhysicalSource S) :
    (0 : Q') ≤ positivePhysicalSourceParityExcitationMass S source := by
  unfold positivePhysicalSourceParityExcitationMass
  exact listQSum_nonnegative_on _ _
    (fun targetState _ =>
      Q'.mul_nonneg _ _
        (YMGap.Continuum.HeatKernelRGStep.zero_le_ofNat _)
        (slabParametricKPhysicalTerm_nonnegative hcoarseCoupling
          S.coarse.cutoff S.coarse.extent targetState))

private theorem exists_false_of_all_false_local {A : Type}
    (test : A → Bool) : ∀ items : List A,
    items.all test = false →
      ∃ item, item ∈ items ∧ test item = false
  | [], hfalse => by cases hfalse
  | head :: tail, hfalse => by
      cases hhead : test head with
      | false => exact ⟨head, List.mem_cons_self, hhead⟩
      | true =>
          have htail : tail.all test = false := by
            simp only [List.all_cons, hhead, Bool.true_and] at hfalse
            exact hfalse
          obtain ⟨item, hitem, htest⟩ :=
            exists_false_of_all_false_local test tail htail
          exact ⟨item, List.mem_cons_of_mem head hitem, htest⟩

private theorem coarse_target_spin_le_four_local
    (S : SlabScalePair) (hfineCutoff : S.fine.cutoff = 1)
    {targetState : EdgeLabelling}
    (htargetMem : targetState ∈ S.coarse.physicalLabellings)
    (faceId : Nat) (hface : faceId ∈ S.coarse.faceEdges) :
    targetState faceId ≤ 4 := by
  have htargetSound := boundedEdgeLabellings_sound
    S.coarse.cutoff S.coarse.faceEdges targetState htargetMem
  have hbound := Nat.le_of_lt_succ (htargetSound.1 faceId hface)
  rw [S.coarse_cutoff, hfineCutoff] at hbound
  omega

/-- Every non-ground target has a concrete coarse face carrying at least one
positive two-spin excitation above its parity background. -/
theorem mem_positivePhysicalSourceParityExcitationTargets_exists_positive_level
    (S : SlabScalePair)
    (hfineCutoff : S.fine.cutoff = 1)
    (source : PositivePhysicalSource S)
    {targetState : EdgeLabelling}
    (htarget : targetState ∈
      positivePhysicalSourceParityExcitationTargets S source) :
    ∃ faceId, faceId ∈ S.coarse.faceEdges ∧
      0 < spinFourParityExcitationLevel
        (wholeSlabFinePacketTotalLabelling S source.1 faceId)
        (targetState faceId) := by
  have hparts := List.mem_filter.mp htarget
  have hlowering :=
    (mem_spinFourLoweringTargets_iff S _ _).mp hparts.1
  have htestFalse :
      spinFourParityGroundTargetB S
          (wholeSlabFinePacketTotalLabelling S source.1) targetState =
        false := by
    cases htest : spinFourParityGroundTargetB S
        (wholeSlabFinePacketTotalLabelling S source.1) targetState with
    | false => rfl
    | true =>
        simp only [htest, Bool.not_true, Bool.false_eq_true] at hparts
        exact False.elim hparts.2
  unfold spinFourParityGroundTargetB at htestFalse
  obtain ⟨faceId, hface, hfaceFalse⟩ :=
    exists_false_of_all_false_local
      (fun id => decide
        (targetState id =
          wholeSlabFinePacketTotalLabelling S source.1 id % 2))
      S.coarse.faceEdges htestFalse
  refine ⟨faceId, hface, ?_⟩
  apply (spinFourParityExcitationLevel_pos_iff_ne_ground
    (wholeSlabFinePacketTotalLabelling_le_four
      S hfineCutoff source.2.1 faceId hface)
    (coarse_target_spin_le_four_local
      S hfineCutoff hlowering.1 faceId hface)
    (hlowering.2 faceId hface)).2
  exact of_decide_eq_false hfaceFalse

/-! ## 4. Axiom audit -/

#print axioms spinFourLoweringTarget_eq_ground_add_twice_excitationLevel
#print axioms spinFourParityExcitationLevel_pos_iff_ne_ground
#print axioms spinFourParityGroundTargetB_true_iff_eq_parityState
#print axioms spinFourLoweringTargets_nodup
#print axioms positivePhysicalSourceParityGround_filter_eq_singleton
#print axioms positivePhysicalSourceTiltedGibbsRowMass_eqv_ground_add_excitation
#print axioms positivePhysicalSourceParityExcitationMass_nonnegative
#print axioms mem_positivePhysicalSourceParityExcitationTargets_exists_positive_level

end YMGap.Continuum.Z4DyadicBinarySourceParityExcitationSplit
