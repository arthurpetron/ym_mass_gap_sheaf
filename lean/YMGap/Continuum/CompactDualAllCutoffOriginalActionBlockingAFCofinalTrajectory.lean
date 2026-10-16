/-
# Cofinal finite matched block trajectories on the AF nome schedule

One fixed finite slab cannot support infinitely many dyadic block steps.  This
module constructs the correct replacement: for every requested depth, a
finite matched trajectory whose initial slab is a sufficiently deep dyadic
preimage of a supplied terminal half-size.

The construction uses the repository `NomeSchedule` directly as the coupling
parameter of `SlabPhysicalData`.  Every step keeps the preceding coarse datum
as the next fine datum, multiplies the character cutoff by four, shrinks the
half-size by the exact dyadic law, and advances one schedule index.  The
specialization to `afNomeSchedule`, initial cutoff one, terminal half-size
zero, and start stage zero supplies arbitrarily long finite AF-calibrated
chains.

This is geometric and algebraic cofinality only.  It does not prove
compatibility of local observable transports between different outer-volume
members, decay of either split remainder producer, a lattice-spacing law, or
a continuum limit.

Constructive contract: explicit finite recursion and exact natural/rational
data only; no choice, `Classical`, `native_decide`, `sorry`, noncomputable
declaration, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingTrajectoryFiniteVolume
import YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory

namespace YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4WilsonAllNomeAFPaddedTrajectory
open YMGap.Continuum.BF4WilsonAllNomeDyadicSmoothedTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingIteration.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingRemainderSplit
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingRemainderSplit.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingTrajectoryFiniteVolume
open YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingTrajectoryFiniteVolume.AllCutoffOriginalActionTrajectory
open YMGap.Continuum.CompactDualAllCutoffPhysicalPushforward
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicSlabReflectionParityKernel
open YMGap.Continuum.Z4HalfTimeReflectionGeometry

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Scheduled physical data and one exact dyadic step -/

def scheduledPhysicalData
    (schedule : NomeSchedule) (stage cutoff half : Nat) :
    SlabPhysicalData where
  coupling := schedule.nome stage
  coupling_nonnegative := Q'.le_of_lt (schedule.nome_pos stage)
  cutoff := cutoff
  half := half

/-- One scheduled step built from an already fixed fine datum.  Its constant
flow records exactly the next scheduled coupling and nothing stronger. -/
def scheduledScalePairFromFine
    (schedule : NomeSchedule) (coarseStage : Nat)
    (fine : SlabPhysicalData) (coarseHalf : Nat)
    (hfineHalf : fine.half = 2 * coarseHalf + 1) :
    SlabScalePair where
  fine := fine
  coarse := scheduledPhysicalData schedule coarseStage
    (4 * fine.cutoff) coarseHalf
  couplingFlow := fun _ => schedule.nome coarseStage
  fine_extent := by
    change centralExtent fine.half =
      dyadicSlabFineExtent (centralExtent coarseHalf)
    rw [hfineHalf]
    unfold centralExtent dyadicSlabFineExtent
    omega
  coarse_cutoff := rfl
  coarse_coupling := Q'.eqv_refl _

/-! ## 2. A finite trajectory ending at a prescribed half-size -/

/-- A checked matched trajectory together with its prescribed terminal
coarse half-size. -/
structure MatchedTrajectoryEndingAt (terminalHalf : Nat) : Type where
  trajectory : AllCutoffOriginalActionTrajectory
  matched : Matched trajectory
  lastCoarseHalf :
    (lastStep trajectory).pair.coarse.half = terminalHalf

/-- Iterated dyadic preimage half-size.  The recursion order matches the
cofinal trajectory constructor below. -/
def expandedHalf : Nat → Nat → Nat
  | 0, terminalHalf => terminalHalf
  | depth + 1, terminalHalf =>
      expandedHalf depth (2 * terminalHalf + 1)

/-- `extraDepth = 0` produces one step.  Every successor first builds the
earlier part ending at the fine half-size required by the new terminal step,
then appends that step using the previous coarse datum literally as its fine
datum. -/
def scheduledTrajectoryEndingAt
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf : Nat) :
    (extraDepth : Nat) → MatchedTrajectoryEndingAt terminalHalf
  | 0 =>
      let fine := scheduledPhysicalData schedule startStage initialCutoff
        (2 * terminalHalf + 1)
      let pair := scheduledScalePairFromFine schedule (startStage + 1)
        fine terminalHalf rfl
      let step : AllCutoffOriginalActionStep :=
        { pair := pair
          fineCutoff := hinitialCutoff }
      { trajectory := .single step
        matched := True.intro
        lastCoarseHalf := rfl }
  | extraDepth + 1 =>
      let prior := scheduledTrajectoryEndingAt schedule startStage
        initialCutoff hinitialCutoff (2 * terminalHalf + 1) extraDepth
      let priorLast := lastStep prior.trajectory
      let nextPair := scheduledScalePairFromFine schedule
        (startStage + (extraDepth + 2)) priorLast.pair.coarse
        terminalHalf prior.lastCoarseHalf
      have hnextFineCutoff : 1 ≤ nextPair.fine.cutoff := by
        change 1 ≤ priorLast.pair.coarse.cutoff
        rw [priorLast.pair.coarse_cutoff]
        have hpositive := priorLast.fineCutoff
        omega
      let nextStep : AllCutoffOriginalActionStep :=
        { pair := nextPair
          fineCutoff := hnextFineCutoff }
      { trajectory := .append prior.trajectory nextStep
        matched := by
          change Matched prior.trajectory ∧
            (lastStep prior.trajectory).pair.coarse = nextPair.fine
          exact ⟨prior.matched, rfl⟩
        lastCoarseHalf := rfl }

/-! ## 3. Exact schedule and geometry of the constructed family -/

theorem scheduledTrajectoryEndingAt_stepCount
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    stepCount
        (scheduledTrajectoryEndingAt schedule startStage initialCutoff
          hinitialCutoff terminalHalf extraDepth).trajectory =
      extraDepth + 1 := by
  induction extraDepth generalizing terminalHalf with
  | zero => rfl
  | succ extraDepth ih =>
      change stepCount
          (scheduledTrajectoryEndingAt schedule startStage initialCutoff
            hinitialCutoff (2 * terminalHalf + 1) extraDepth).trajectory + 1 =
        extraDepth + 1 + 1
      rw [ih]

theorem scheduledTrajectoryEndingAt_firstFineHalf
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (firstStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.fine.half =
      expandedHalf (extraDepth + 1) terminalHalf := by
  induction extraDepth generalizing terminalHalf with
  | zero => rfl
  | succ extraDepth ih =>
      change
        (firstStep
          (scheduledTrajectoryEndingAt schedule startStage initialCutoff
            hinitialCutoff (2 * terminalHalf + 1) extraDepth).trajectory).pair.fine.half =
          expandedHalf (extraDepth + 1) (2 * terminalHalf + 1)
      exact ih (2 * terminalHalf + 1)

theorem scheduledTrajectoryEndingAt_firstFineCutoff
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (firstStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.fine.cutoff =
      initialCutoff := by
  induction extraDepth generalizing terminalHalf with
  | zero => rfl
  | succ extraDepth ih =>
      change
        (firstStep
          (scheduledTrajectoryEndingAt schedule startStage initialCutoff
            hinitialCutoff (2 * terminalHalf + 1) extraDepth).trajectory).pair.fine.cutoff =
          initialCutoff
      exact ih (2 * terminalHalf + 1)

theorem scheduledTrajectoryEndingAt_firstFineCoupling
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (firstStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.fine.coupling =
      schedule.nome startStage := by
  induction extraDepth generalizing terminalHalf with
  | zero => rfl
  | succ extraDepth ih =>
      change
        (firstStep
          (scheduledTrajectoryEndingAt schedule startStage initialCutoff
            hinitialCutoff (2 * terminalHalf + 1) extraDepth).trajectory).pair.fine.coupling =
          schedule.nome startStage
      exact ih (2 * terminalHalf + 1)

theorem scheduledTrajectoryEndingAt_firstCoarseCoupling
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (firstStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.coarse.coupling =
      schedule.nome (startStage + 1) := by
  induction extraDepth generalizing terminalHalf with
  | zero => rfl
  | succ extraDepth ih =>
      change
        (firstStep
          (scheduledTrajectoryEndingAt schedule startStage initialCutoff
            hinitialCutoff (2 * terminalHalf + 1) extraDepth).trajectory).pair.coarse.coupling =
          schedule.nome (startStage + 1)
      exact ih (2 * terminalHalf + 1)

theorem scheduledTrajectoryEndingAt_lastCoarseCoupling
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (lastStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.coarse.coupling =
      schedule.nome (startStage + (extraDepth + 1)) := by
  cases extraDepth with
  | zero => rfl
  | succ extraDepth => rfl

theorem scheduledTrajectoryEndingAt_lastCoarseCutoff
    (schedule : NomeSchedule) (startStage initialCutoff : Nat)
    (hinitialCutoff : 1 ≤ initialCutoff) (terminalHalf extraDepth : Nat) :
    (lastStep
      (scheduledTrajectoryEndingAt schedule startStage initialCutoff
        hinitialCutoff terminalHalf extraDepth).trajectory).pair.coarse.cutoff =
      4 ^ (extraDepth + 1) * initialCutoff := by
  induction extraDepth generalizing terminalHalf with
  | zero =>
      change 4 * initialCutoff = 4 ^ 1 * initialCutoff
      rfl
  | succ extraDepth ih =>
      change 4 *
          (lastStep
            (scheduledTrajectoryEndingAt schedule startStage initialCutoff
              hinitialCutoff (2 * terminalHalf + 1)
              extraDepth).trajectory).pair.coarse.cutoff =
        4 ^ (extraDepth + 1 + 1) * initialCutoff
      rw [ih]
      simp only [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-! ## 4. The concrete AF cofinal family -/

/-- A trajectory with `depth + 1` actual block steps, beginning at cutoff one
and ending at half-size zero on the AF-calibrated nome schedule. -/
def afCofinalTrajectory (depth : Nat) :
    AllCutoffOriginalActionTrajectory :=
  (scheduledTrajectoryEndingAt afNomeSchedule 0 1 (by decide) 0 depth).trajectory

theorem afCofinalTrajectory_matched (depth : Nat) :
    Matched (afCofinalTrajectory depth) :=
  (scheduledTrajectoryEndingAt afNomeSchedule 0 1
    (by decide) 0 depth).matched

theorem afCofinalTrajectory_stepCount (depth : Nat) :
    stepCount (afCofinalTrajectory depth) = depth + 1 := by
  exact scheduledTrajectoryEndingAt_stepCount
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afCofinalTrajectory_firstFineHalf (depth : Nat) :
    (firstStep (afCofinalTrajectory depth)).pair.fine.half =
      expandedHalf (depth + 1) 0 := by
  exact scheduledTrajectoryEndingAt_firstFineHalf
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afCofinalTrajectory_depth_le_firstFineHalf (depth : Nat) :
    depth + 1 ≤
      (firstStep (afCofinalTrajectory depth)).pair.fine.half := by
  rw [← afCofinalTrajectory_stepCount depth]
  exact stepCount_le_firstFineHalf
    (afCofinalTrajectory depth) (afCofinalTrajectory_matched depth)

theorem afCofinalTrajectory_firstFineCutoff (depth : Nat) :
    (firstStep (afCofinalTrajectory depth)).pair.fine.cutoff = 1 := by
  exact scheduledTrajectoryEndingAt_firstFineCutoff
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afCofinalTrajectory_firstFineCoupling (depth : Nat) :
    (firstStep (afCofinalTrajectory depth)).pair.fine.coupling =
      afNomeSchedule.nome 0 := by
  exact scheduledTrajectoryEndingAt_firstFineCoupling
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afCofinalTrajectory_firstCoarseCoupling (depth : Nat) :
    (firstStep (afCofinalTrajectory depth)).pair.coarse.coupling =
      afNomeSchedule.nome 1 := by
  exact scheduledTrajectoryEndingAt_firstCoarseCoupling
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afScheduledTrajectory_lastCoarseCoupling (depth : Nat) :
    (lastStep
      (scheduledTrajectoryEndingAt afNomeSchedule 0 1
        (by decide) 0 depth).trajectory).pair.coarse.coupling =
      afNomeSchedule.nome (0 + (depth + 1)) :=
  scheduledTrajectoryEndingAt_lastCoarseCoupling
    afNomeSchedule 0 1 (by decide) 0 depth

theorem afCofinalTrajectory_lastCoarseCutoff (depth : Nat) :
    (lastStep (afCofinalTrajectory depth)).pair.coarse.cutoff =
      4 ^ (depth + 1) := by
  have hcutoff := scheduledTrajectoryEndingAt_lastCoarseCutoff
    afNomeSchedule 0 1 (by decide) 0 depth
  change
    (lastStep
      (scheduledTrajectoryEndingAt afNomeSchedule 0 1
        (by decide) 0 depth).trajectory).pair.coarse.cutoff =
      4 ^ (depth + 1)
  simpa only [Nat.mul_one] using hcutoff

theorem afCofinalTrajectory_lastCoarseHalf (depth : Nat) :
    (lastStep (afCofinalTrajectory depth)).pair.coarse.half = 0 :=
  (scheduledTrajectoryEndingAt afNomeSchedule 0 1
    (by decide) 0 depth).lastCoarseHalf

/-! ## 5. Concrete split-budget consequences on the AF family -/

theorem afCofinalTrajectory_defectL1_le_splitBudget (depth : Nat) :
    defectL1 (afCofinalTrajectory depth) ≤
      splitBudget (afCofinalTrajectory depth) := by
  exact defectL1_le_splitBudget
    (afCofinalTrajectory depth) (afCofinalTrajectory_matched depth)

theorem afCofinalTrajectory_expectation_defect_le_splitBudget
    (depth : Nat) (observable : EdgeLabelling → Q')
    (hbound : ∀ state,
      state ∈
          (lastStep
            (afCofinalTrajectory depth)).pair.coarse.physicalLabellings →
        Q'.abs (observable state) ≤ (1 : Q')) :
    Q'.abs
        (blockedExpectation (afCofinalTrajectory depth) observable +
          -(coarseWilsonExpectation
            (afCofinalTrajectory depth) observable)) ≤
      splitBudget (afCofinalTrajectory depth) := by
  exact expectation_defect_le_splitBudget
    (afCofinalTrajectory depth) (afCofinalTrajectory_matched depth)
    observable hbound

/-- The first AF step starts at cutoff one, so its positive-incoherent source
probability vanishes exactly.  Later all-cutoff steps still require control. -/
theorem afCofinalTrajectory_firstIncoherentMass_eqv_zero (depth : Nat) :
    positiveIncoherentRecouplingMass
        (firstStep (afCofinalTrajectory depth)).pair ≈
      0 := by
  apply positiveIncoherentRecouplingMass_eqv_zero_at_cutoffOne
  · exact afCofinalTrajectory_firstFineCutoff depth
  · rw [afCofinalTrajectory_firstCoarseCoupling depth]
    exact afNomeSchedule.nome_pos 1

/-- The explicit fallback column itself vanishes targetwise on the first
cutoff-one AF step. -/
theorem afCofinalTrajectory_firstFallbackBlockedMass_eqv_zero
    (depth : Nat) (target : EdgeLabelling) :
    positiveIncoherentFallbackBlockedMass
        (firstStep (afCofinalTrajectory depth)).pair target ≈
      0 := by
  apply positiveIncoherentFallbackBlockedMass_eqv_zero_at_cutoffOne
  · exact afCofinalTrajectory_firstFineCutoff depth
  · rw [afCofinalTrajectory_firstCoarseCoupling depth]
    exact afNomeSchedule.nome_pos 1

/-- Hence the complete first-step signed remainder is exactly the coherent
recoupling-to-Wilson mismatch. -/
theorem afCofinalTrajectory_firstRemainder_eqv_coherentWilson
    (depth : Nat) (target : EdgeLabelling) :
    (allCutoffPhysicalKernel
        (firstStep (afCofinalTrajectory depth)).pair
        (firstStep (afCofinalTrajectory depth)).fineCutoff).remainder target ≈
      coherentWilsonRemainder
        (firstStep (afCofinalTrajectory depth)).pair target := by
  let step := firstStep (afCofinalTrajectory depth)
  refine Q'.eqv_trans _
    (coherentWilsonRemainder step.pair target +
      positiveIncoherentFallbackBlockedMass step.pair target) _
    (allCutoffPhysicalRemainder_eqv_coherentWilson_add_fallback
      step.pair step.fineCutoff target) ?_
  refine Q'.eqv_trans _
    (coherentWilsonRemainder step.pair target + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (afCofinalTrajectory_firstFallbackBlockedMass_eqv_zero
        depth target)) ?_
  exact Q'.eqv_of_eq
    (Q'.add_zero' (coherentWilsonRemainder step.pair target))

/-- Accordingly, the first one-step total-variation remainder is exactly,
not merely bounded by, the coherent-to-Wilson mismatch. -/
theorem afCofinalTrajectory_firstRemainderL1_eqv_coherentWilson
    (depth : Nat) :
    (allCutoffPhysicalKernel
        (firstStep (afCofinalTrajectory depth)).pair
        (firstStep (afCofinalTrajectory depth)).fineCutoff).remainderL1 ≈
      coherentWilsonRemainderL1
        (firstStep (afCofinalTrajectory depth)).pair := by
  let step := firstStep (afCofinalTrajectory depth)
  unfold SlabScalePair.FiniteSlabKernel.remainderL1
    coherentWilsonRemainderL1
  apply listQSum_congr_on
  intro target _htarget
  exact Q'.abs_eqv_congr
    (afCofinalTrajectory_firstRemainder_eqv_coherentWilson
      depth target)

/-! ## Axiom audit -/

#print axioms scheduledPhysicalData
#print axioms scheduledScalePairFromFine
#print axioms MatchedTrajectoryEndingAt
#print axioms expandedHalf
#print axioms scheduledTrajectoryEndingAt
#print axioms scheduledTrajectoryEndingAt_stepCount
#print axioms scheduledTrajectoryEndingAt_firstFineHalf
#print axioms scheduledTrajectoryEndingAt_firstFineCutoff
#print axioms scheduledTrajectoryEndingAt_firstFineCoupling
#print axioms scheduledTrajectoryEndingAt_firstCoarseCoupling
#print axioms scheduledTrajectoryEndingAt_lastCoarseCoupling
#print axioms scheduledTrajectoryEndingAt_lastCoarseCutoff
#print axioms afCofinalTrajectory
#print axioms afCofinalTrajectory_matched
#print axioms afCofinalTrajectory_stepCount
#print axioms afCofinalTrajectory_firstFineHalf
#print axioms afCofinalTrajectory_depth_le_firstFineHalf
#print axioms afCofinalTrajectory_firstFineCutoff
#print axioms afCofinalTrajectory_firstFineCoupling
#print axioms afCofinalTrajectory_firstCoarseCoupling
#print axioms afScheduledTrajectory_lastCoarseCoupling
#print axioms afCofinalTrajectory_lastCoarseCutoff
#print axioms afCofinalTrajectory_lastCoarseHalf
#print axioms afCofinalTrajectory_defectL1_le_splitBudget
#print axioms afCofinalTrajectory_expectation_defect_le_splitBudget
#print axioms afCofinalTrajectory_firstIncoherentMass_eqv_zero
#print axioms afCofinalTrajectory_firstFallbackBlockedMass_eqv_zero
#print axioms afCofinalTrajectory_firstRemainder_eqv_coherentWilson
#print axioms afCofinalTrajectory_firstRemainderL1_eqv_coherentWilson

end YMGap.Continuum.CompactDualAllCutoffOriginalActionBlockingAFCofinalTrajectory
