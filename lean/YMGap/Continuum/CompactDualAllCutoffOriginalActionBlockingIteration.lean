/-
# Two-step accumulation for the all-cutoff original-action block comparison

One exact all-cutoff block step compares the fine original action with the
coarse Wilson action by the literal pushed-law `L1` remainder.  This module
proves that those costs accumulate additively through a second actual
all-cutoff stochastic kernel.

When the first coarse physical datum is the second fine physical datum, push
the first blocked law through the second physical kernel.  Markov `L1`
nonexpansiveness transports the first defect without amplification, and the
second blocked-versus-Wilson defect adds by the triangle inequality.  Hence

  twoStepDefectL1 <= first.remainderL1 + second.remainderL1.

The same bound controls every pointwise-unit-bounded final observable.  This
is the finite recurrence needed for an iterative error budget; it does not
prove that the displayed remainder sequence is summable.  Each transition
still uses the explicit enriched law and forgetting kernel certified by the
one-step module, but the repeatable carrier here is the projected physical
carrier.  A lossless repeated enriched carrier remains open.

Constructive contract: finite exact-rational sums, triangle inequalities, and
stochastic-kernel nonexpansiveness only; no choice, `Classical`,
`native_decide`, `sorry`, noncomputable declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingComparison
import YMGap.Continuum.FiniteSignedKernelL1

namespace YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingComparison
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.ConstructiveRefreshContraction
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteSignedKernelL1
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Generic finite `L1` and observable lemmas -/

private theorem listQSum_mono_local {A : Type} (lower upper : A → Q') :
    ∀ items : List A,
      (∀ item, item ∈ items → lower item ≤ upper item) →
      listQSum lower items ≤ listQSum upper items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hbound =>
      Q'.add_le_add
        (hbound head List.mem_cons_self)
        (listQSum_mono_local lower upper tail
          (fun item hitem =>
            hbound item (List.mem_cons_of_mem head hitem)))

private theorem finiteL1Distance_triangle_local
    {State : Type} (states : List State)
    (left middle right : State → Q') :
    finiteL1Distance states left right ≤
      finiteL1Distance states left middle +
        finiteL1Distance states middle right := by
  unfold finiteL1Distance
  refine Q'.le_trans' _
    (listQSum
      (fun state =>
        Q'.abs (left state + (-middle state)) +
          Q'.abs (middle state + (-right state)))
      states) _ ?_ ?_
  · apply listQSum_mono_local
    intro state _
    have hdecompose :
        left state + (-right state) ≈
          (left state + (-middle state)) +
            (middle state + (-right state)) := by
      have hinner :
          (-middle state) + (middle state + (-right state)) ≈
            -right state := by
        refine Q'.eqv_trans _
          (((-middle state) + middle state) + (-right state)) _ ?_ ?_
        · exact Q'.eqv_symm
            (Q'.add_assoc_eqv
              (-middle state) (middle state) (-right state))
        refine Q'.eqv_trans _ (0 + (-right state)) _ ?_ ?_
        · exact Q'.add_eqv_congr_right _ _ (-right state)
            (Q'.neg_add_self_eqv (middle state))
        · exact Q'.eqv_of_eq (Q'.zero_add' (-right state))
      exact Q'.eqv_symm
        (Q'.eqv_trans _ _ _
          (Q'.add_assoc_eqv
            (left state) (-middle state)
            (middle state + (-right state)))
          (Q'.add_eqv_congr_left
            (left state) _ _ hinner))
    refine Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.abs_eqv_congr hdecompose)) ?_
    exact Q'.abs_add_le' _ _
  · exact Q'.le_of_eqv
      (listQSum_add
        (fun state => Q'.abs (left state + (-middle state)))
        (fun state => Q'.abs (middle state + (-right state)))
        states)

private theorem listQSum_neg_local {A : Type} (value : A → Q') :
    ∀ items : List A,
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
    listQSum (fun item => left item + -(right item)) items ≈
      listQSum left items + -(listQSum right items) := by
  refine Q'.eqv_trans _
    (listQSum left items +
      listQSum (fun item => -(right item)) items) _ ?_ ?_
  · exact listQSum_add left (fun item => -(right item)) items
  · exact Q'.add_eqv_congr'
      (Q'.eqv_refl _) (listQSum_neg_local right items)

private theorem sub_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') :
    a + (-b) ≈ a' + (-b') :=
  Q'.add_eqv_congr' ha (Q'.neg_eqv_congr _ _ hb)

private theorem mul_sub_distribute_left_local (a b c : Q') :
    a * b + -(a * c) ≈ a * (b + (-c)) := by
  refine Q'.eqv_trans _ (a * b + a * (-c)) _ ?_ ?_
  · exact Q'.add_eqv_congr' (Q'.eqv_refl _)
      (Q'.eqv_symm (Q'.mul_neg_eqv a c))
  · exact Q'.eqv_symm (Q'.mul_add_eqv a b (-c))

private theorem mul_sub_distribute_right_local (a b c : Q') :
    a * c + -(b * c) ≈ (a + (-b)) * c := by
  refine Q'.eqv_trans _
    (c * a + -(c * b)) _ ?_ ?_
  · exact sub_eqv_both_local
      (Q'.mul_comm_eqv a c) (Q'.mul_comm_eqv b c)
  refine Q'.eqv_trans _ (c * (a + (-b))) _
    (mul_sub_distribute_left_local c a b) ?_
  exact Q'.mul_comm_eqv c (a + (-b))

private theorem finiteObservableDifferenceList_abs_le_l1
    {State : Type} (left right observable : State → Q') :
    ∀ states : List State,
      (∀ state, state ∈ states →
        Q'.abs (observable state) ≤ (1 : Q')) →
      Q'.abs
          (listQSum
            (fun state =>
              (left state + (-right state)) * observable state)
            states) ≤
        finiteL1Distance states left right
  | [], _ => by
      change Q'.abs (0 : Q') ≤ (0 : Q')
      decide
  | head :: tail, hbound => by
      simp only [listQSum]
      have hhead :
          Q'.abs
              ((left head + (-right head)) * observable head) ≤
            Q'.abs (left head + (-right head)) := by
        refine Q'.le_trans' _ _ _
          (abs_mul_le
            (left head + (-right head)) (observable head)) ?_
        refine Q'.le_trans' _
          (Q'.abs (left head + (-right head)) * 1) _ ?_ ?_
        · exact Q'.mul_le_mul_of_nonneg_left
            (Q'.abs (observable head)) 1
            (Q'.abs (left head + (-right head)))
            (hbound head List.mem_cons_self)
            (Q'.abs_nonneg (left head + (-right head)))
        · exact Q'.le_of_eqv
            (Q'.mul_one_eqv
              (Q'.abs (left head + (-right head))))
      have htail :=
        finiteObservableDifferenceList_abs_le_l1
          left right observable tail
          (fun state hstate =>
            hbound state (List.mem_cons_of_mem head hstate))
      exact Q'.le_trans' _ _ _
        (Q'.abs_add_le'
          ((left head + (-right head)) * observable head)
          (listQSum
            (fun state =>
              (left state + (-right state)) * observable state)
            tail))
        (Q'.add_le_add hhead htail)

private theorem finiteObservableExpectation_difference_abs_le_l1
    {State : Type} (states : List State)
    (left right observable : State → Q')
    (hbound : ∀ state, state ∈ states →
      Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (listQSum (fun state => left state * observable state) states +
          -(listQSum
            (fun state => right state * observable state) states)) ≤
      finiteL1Distance states left right := by
  have hrewrite :
      listQSum (fun state => left state * observable state) states +
          -(listQSum
            (fun state => right state * observable state) states) ≈
        listQSum
          (fun state =>
            (left state + (-right state)) * observable state)
          states := by
    refine Q'.eqv_trans _
      (listQSum
        (fun state =>
          left state * observable state +
            -(right state * observable state))
        states) _ ?_ ?_
    · exact Q'.eqv_symm
        (listQSum_sub_local
          (fun state => left state * observable state)
          (fun state => right state * observable state) states)
    · apply listQSum_congr_on
      intro state _
      exact mul_sub_distribute_right_local
        (left state) (right state) (observable state)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.abs_eqv_congr hrewrite))
    (finiteObservableDifferenceList_abs_le_l1
      left right observable states hbound)

/-! ## 2. The actual two-step physical pushforward -/

/-- Push the first actual blocked law through the second actual all-cutoff
physical kernel. -/
def allCutoffTwoStepBlockedMass
    (first : SlabScalePair) (hfirstCutoff : 1 ≤ first.fine.cutoff)
    (second : SlabScalePair) (hsecondCutoff : 1 ≤ second.fine.cutoff)
    (target : EdgeLabelling) : Q' :=
  finiteKernelPushforward second.fine.physicalLabellings
    (allCutoffPhysicalKernel first hfirstCutoff).blockedMass
    (allCutoffPhysicalKernel second hsecondCutoff).kernel target

/-- Total variation between the two-step pushed law and the normalized final
coarse Wilson action. -/
def allCutoffTwoStepDefectL1
    (first : SlabScalePair) (hfirstCutoff : 1 ≤ first.fine.cutoff)
    (second : SlabScalePair) (hsecondCutoff : 1 ≤ second.fine.cutoff) : Q' :=
  finiteL1Distance second.coarse.physicalLabellings
    (allCutoffTwoStepBlockedMass
      first hfirstCutoff second hsecondCutoff)
    second.coarse.normalizedMass

/-- Markov nonexpansiveness makes the first physical remainder survive a
second step without amplification; the second remainder then adds. -/
theorem allCutoffTwoStepDefectL1_le_add_remainderL1
    (first : SlabScalePair) (hfirstCutoff : 1 ≤ first.fine.cutoff)
    (second : SlabScalePair) (hsecondCutoff : 1 ≤ second.fine.cutoff)
    (hmatch : first.coarse = second.fine) :
    allCutoffTwoStepDefectL1
        first hfirstCutoff second hsecondCutoff ≤
      (allCutoffPhysicalKernel first hfirstCutoff).remainderL1 +
        (allCutoffPhysicalKernel second hsecondCutoff).remainderL1 := by
  let firstKernel := allCutoffPhysicalKernel first hfirstCutoff
  let secondKernel := allCutoffPhysicalKernel second hsecondCutoff
  have hnonexpansive :
      finiteL1Distance second.coarse.physicalLabellings
          (finiteKernelPushforward second.fine.physicalLabellings
            firstKernel.blockedMass secondKernel.kernel)
          secondKernel.blockedMass ≤
        finiteL1Distance second.fine.physicalLabellings
          firstKernel.blockedMass second.fine.normalizedMass := by
    change finiteL1Distance second.coarse.physicalLabellings
        (finiteKernelPushforward second.fine.physicalLabellings
          firstKernel.blockedMass secondKernel.kernel)
        (finiteKernelPushforward second.fine.physicalLabellings
          second.fine.normalizedMass secondKernel.kernel) ≤
      finiteL1Distance second.fine.physicalLabellings
        firstKernel.blockedMass second.fine.normalizedMass
    exact finiteMarkov_l1_nonexpansive
      second.fine.physicalLabellings
      second.coarse.physicalLabellings
      secondKernel.kernel
      (fun source hsource target htarget =>
        secondKernel.nonnegative source target hsource htarget)
      (fun source hsource =>
        secondKernel.row_normalized source hsource)
      firstKernel.blockedMass second.fine.normalizedMass
  have hfirstDefect :
      finiteL1Distance second.fine.physicalLabellings
          firstKernel.blockedMass second.fine.normalizedMass ≈
        firstKernel.remainderL1 := by
    rw [← hmatch]
    unfold finiteL1Distance
      SlabScalePair.FiniteSlabKernel.remainderL1
      SlabScalePair.FiniteSlabKernel.remainder
    exact Q'.eqv_refl _
  have hsecondDefect :
      finiteL1Distance second.coarse.physicalLabellings
          secondKernel.blockedMass second.coarse.normalizedMass ≈
        secondKernel.remainderL1 := by
    unfold finiteL1Distance
      SlabScalePair.FiniteSlabKernel.remainderL1
      SlabScalePair.FiniteSlabKernel.remainder
    exact Q'.eqv_refl _
  have htriangle := finiteL1Distance_triangle_local
    second.coarse.physicalLabellings
    (finiteKernelPushforward second.fine.physicalLabellings
      firstKernel.blockedMass secondKernel.kernel)
    secondKernel.blockedMass second.coarse.normalizedMass
  unfold allCutoffTwoStepDefectL1 allCutoffTwoStepBlockedMass
  change finiteL1Distance second.coarse.physicalLabellings
      (finiteKernelPushforward second.fine.physicalLabellings
        firstKernel.blockedMass secondKernel.kernel)
      second.coarse.normalizedMass ≤
    firstKernel.remainderL1 + secondKernel.remainderL1
  exact Q'.le_trans' _ _ _ htriangle
    (Q'.add_le_add
      (Q'.le_trans' _ _ _ hnonexpansive
        (Q'.le_of_eqv hfirstDefect))
      (Q'.le_of_eqv hsecondDefect))

/-! ## 3. Final-observable consequence -/

def allCutoffTwoStepBlockedExpectation
    (first : SlabScalePair) (hfirstCutoff : 1 ≤ first.fine.cutoff)
    (second : SlabScalePair) (hsecondCutoff : 1 ≤ second.fine.cutoff)
    (observable : EdgeLabelling → Q') : Q' :=
  observableExpectation
    (allCutoffTwoStepBlockedMass
      first hfirstCutoff second hsecondCutoff)
    second.coarse.physicalLabellings observable

/-- Every unit-bounded final observable inherits the additive two-step error
budget.  This is the expectation-level form consumed by a future summable
trajectory modulus. -/
theorem allCutoffTwoStepExpectation_defect_le_add_remainderL1
    (first : SlabScalePair) (hfirstCutoff : 1 ≤ first.fine.cutoff)
    (second : SlabScalePair) (hsecondCutoff : 1 ≤ second.fine.cutoff)
    (hmatch : first.coarse = second.fine)
    (observable : EdgeLabelling → Q')
    (hbound : ∀ state, state ∈ second.coarse.physicalLabellings →
      Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (allCutoffTwoStepBlockedExpectation
            first hfirstCutoff second hsecondCutoff observable +
          -(allCutoffCoarseWilsonExpectation second observable)) ≤
      (allCutoffPhysicalKernel first hfirstCutoff).remainderL1 +
        (allCutoffPhysicalKernel second hsecondCutoff).remainderL1 := by
  refine Q'.le_trans' _
    (allCutoffTwoStepDefectL1
      first hfirstCutoff second hsecondCutoff) _ ?_ ?_
  · unfold allCutoffTwoStepBlockedExpectation
      allCutoffCoarseWilsonExpectation
      BF4ObservableMatchedOneStep.observableExpectation
      allCutoffTwoStepDefectL1
    exact finiteObservableExpectation_difference_abs_le_l1
      second.coarse.physicalLabellings
      (allCutoffTwoStepBlockedMass
        first hfirstCutoff second hsecondCutoff)
      second.coarse.normalizedMass observable hbound
  · exact allCutoffTwoStepDefectL1_le_add_remainderL1
      first hfirstCutoff second hsecondCutoff hmatch

/-! ## 4. Arbitrary finite matched trajectories -/

/-- One concrete all-cutoff physical block step, including the cutoff witness
needed to construct its kernel. -/
structure AllCutoffOriginalActionStep where
  pair : SlabScalePair
  fineCutoff : 1 ≤ pair.fine.cutoff

/-- A nonempty sequence of concrete all-cutoff physical block steps.  Carrier
matching is kept as a separate proposition so the pushed mass remains an
explicit computable recursion. -/
inductive AllCutoffOriginalActionTrajectory where
  | single (step : AllCutoffOriginalActionStep)
  | append
      (prior : AllCutoffOriginalActionTrajectory)
      (next : AllCutoffOriginalActionStep)

namespace AllCutoffOriginalActionTrajectory

def lastStep : AllCutoffOriginalActionTrajectory →
    AllCutoffOriginalActionStep
  | .single step => step
  | .append _ next => next

/-- Every adjacent coarse/fine physical datum agrees exactly. -/
def Matched : AllCutoffOriginalActionTrajectory → Prop
  | .single _ => True
  | .append prior next =>
      Matched prior ∧
        (lastStep prior).pair.coarse = next.pair.fine

/-- The actual physical law after every step in the trajectory. -/
def blockedMass : AllCutoffOriginalActionTrajectory →
    EdgeLabelling → Q'
  | .single step =>
      (allCutoffPhysicalKernel step.pair step.fineCutoff).blockedMass
  | .append prior next =>
      finiteKernelPushforward next.pair.fine.physicalLabellings
        (blockedMass prior)
        (allCutoffPhysicalKernel
          next.pair next.fineCutoff).kernel

/-- The literal additive error budget accumulated along the trajectory. -/
def remainderBudget : AllCutoffOriginalActionTrajectory → Q'
  | .single step =>
      (allCutoffPhysicalKernel step.pair step.fineCutoff).remainderL1
  | .append prior next =>
      remainderBudget prior +
        (allCutoffPhysicalKernel next.pair next.fineCutoff).remainderL1

/-- Final total variation from the normalized final coarse Wilson law. -/
def defectL1 (trajectory : AllCutoffOriginalActionTrajectory) : Q' :=
  finiteL1Distance
    (lastStep trajectory).pair.coarse.physicalLabellings
    (blockedMass trajectory)
    (lastStep trajectory).pair.coarse.normalizedMass

/-- Along every finite matched trajectory, the final physical-law defect is
at most the sum of the literal one-step remainders. -/
theorem defectL1_le_remainderBudget
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory) :
    defectL1 trajectory ≤ remainderBudget trajectory := by
  induction trajectory with
  | single step =>
      unfold defectL1 lastStep blockedMass remainderBudget
        SlabScalePair.FiniteSlabKernel.remainderL1
        SlabScalePair.FiniteSlabKernel.remainder
        finiteL1Distance
      exact Q'.le_refl' _
  | append prior next ih =>
      change Matched prior ∧
        (lastStep prior).pair.coarse = next.pair.fine at hmatched
      rcases hmatched with ⟨hpriorMatched, hmatch⟩
      let nextKernel :=
        allCutoffPhysicalKernel next.pair next.fineCutoff
      have hnonexpansive :
          finiteL1Distance next.pair.coarse.physicalLabellings
              (finiteKernelPushforward
                next.pair.fine.physicalLabellings
                (blockedMass prior) nextKernel.kernel)
              nextKernel.blockedMass ≤
            finiteL1Distance next.pair.fine.physicalLabellings
              (blockedMass prior) next.pair.fine.normalizedMass := by
        change finiteL1Distance next.pair.coarse.physicalLabellings
            (finiteKernelPushforward
              next.pair.fine.physicalLabellings
              (blockedMass prior) nextKernel.kernel)
            (finiteKernelPushforward
              next.pair.fine.physicalLabellings
              next.pair.fine.normalizedMass nextKernel.kernel) ≤
          finiteL1Distance next.pair.fine.physicalLabellings
            (blockedMass prior) next.pair.fine.normalizedMass
        exact finiteMarkov_l1_nonexpansive
          next.pair.fine.physicalLabellings
          next.pair.coarse.physicalLabellings nextKernel.kernel
          (fun source hsource target htarget =>
            nextKernel.nonnegative source target hsource htarget)
          (fun source hsource =>
            nextKernel.row_normalized source hsource)
          (blockedMass prior) next.pair.fine.normalizedMass
      have hpriorDefect :
          finiteL1Distance next.pair.fine.physicalLabellings
              (blockedMass prior) next.pair.fine.normalizedMass ≤
            remainderBudget prior := by
        rw [← hmatch]
        change defectL1 prior ≤ remainderBudget prior
        exact ih hpriorMatched
      have hnextDefect :
          finiteL1Distance next.pair.coarse.physicalLabellings
              nextKernel.blockedMass next.pair.coarse.normalizedMass ≈
            nextKernel.remainderL1 := by
        unfold finiteL1Distance
          SlabScalePair.FiniteSlabKernel.remainderL1
          SlabScalePair.FiniteSlabKernel.remainder
        exact Q'.eqv_refl _
      have htriangle := finiteL1Distance_triangle_local
        next.pair.coarse.physicalLabellings
        (finiteKernelPushforward
          next.pair.fine.physicalLabellings
          (blockedMass prior) nextKernel.kernel)
        nextKernel.blockedMass next.pair.coarse.normalizedMass
      unfold defectL1 lastStep blockedMass remainderBudget
      change finiteL1Distance next.pair.coarse.physicalLabellings
          (finiteKernelPushforward
            next.pair.fine.physicalLabellings
            (blockedMass prior) nextKernel.kernel)
          next.pair.coarse.normalizedMass ≤
        remainderBudget prior + nextKernel.remainderL1
      exact Q'.le_trans' _ _ _ htriangle
        (Q'.add_le_add
          (Q'.le_trans' _ _ _ hnonexpansive hpriorDefect)
          (Q'.le_of_eqv hnextDefect))

def blockedExpectation
    (trajectory : AllCutoffOriginalActionTrajectory)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun state => blockedMass trajectory state * observable state)
    (lastStep trajectory).pair.coarse.physicalLabellings

def coarseWilsonExpectation
    (trajectory : AllCutoffOriginalActionTrajectory)
    (observable : EdgeLabelling → Q') : Q' :=
  listQSum
    (fun state =>
      (lastStep trajectory).pair.coarse.normalizedMass state *
        observable state)
    (lastStep trajectory).pair.coarse.physicalLabellings

/-- Every unit-bounded final observable is controlled by the same finite
trajectory remainder budget. -/
theorem expectation_defect_le_remainderBudget
    (trajectory : AllCutoffOriginalActionTrajectory)
    (hmatched : Matched trajectory)
    (observable : EdgeLabelling → Q')
    (hbound : ∀ state,
      state ∈ (lastStep trajectory).pair.coarse.physicalLabellings →
        Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (blockedExpectation trajectory observable +
          -(coarseWilsonExpectation trajectory observable)) ≤
      remainderBudget trajectory := by
  refine Q'.le_trans' _ (defectL1 trajectory) _ ?_ ?_
  · unfold blockedExpectation coarseWilsonExpectation defectL1
    exact finiteObservableExpectation_difference_abs_le_l1
      (lastStep trajectory).pair.coarse.physicalLabellings
      (blockedMass trajectory)
      (lastStep trajectory).pair.coarse.normalizedMass observable hbound
  · exact defectL1_le_remainderBudget trajectory hmatched

end AllCutoffOriginalActionTrajectory

/-! ## Axiom audit -/

#print axioms allCutoffTwoStepBlockedMass
#print axioms allCutoffTwoStepDefectL1
#print axioms allCutoffTwoStepDefectL1_le_add_remainderL1
#print axioms allCutoffTwoStepBlockedExpectation
#print axioms allCutoffTwoStepExpectation_defect_le_add_remainderL1
#print axioms AllCutoffOriginalActionStep
#print axioms AllCutoffOriginalActionTrajectory.lastStep
#print axioms AllCutoffOriginalActionTrajectory.Matched
#print axioms AllCutoffOriginalActionTrajectory.blockedMass
#print axioms AllCutoffOriginalActionTrajectory.remainderBudget
#print axioms AllCutoffOriginalActionTrajectory.defectL1
#print axioms AllCutoffOriginalActionTrajectory.defectL1_le_remainderBudget
#print axioms AllCutoffOriginalActionTrajectory.blockedExpectation
#print axioms AllCutoffOriginalActionTrajectory.coarseWilsonExpectation
#print axioms AllCutoffOriginalActionTrajectory.expectation_defect_le_remainderBudget

end YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
