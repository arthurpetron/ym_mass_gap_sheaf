/-
# Iterating the observable-matched BF4 step

`BF4ObservableMatchedOneStep` removes the free-flow ambiguity at one exact
cutoff-one block: the coarse coupling is a finite observable-matching argmin.
This module iterates that constructor over a supplied schedule of geometries,
positive candidate atlases, and observables.

The output trajectory is data.  Every successor coupling carries:

* strict positivity;
* membership in the atlas used at that step;
* global minimality of the exact pushed-vs-coarse observable defect;
* a computable comparison certificate against the two-dimensional reference
  `s ↦ s^4`.

The module also proves the exact finite-atlas facts needed before taking an
atlas limit:

* adding candidates cannot increase the selected physical matching defect;
* a supplied candidate error bound transfers automatically to the selected
  coupling;
* a refinement certificate saying the old minimizer remains minimal in the
  enlarged atlas gives semantic equality of the two optimal defects.

Honest boundary: none of these order statements implies convergence of the
selected couplings.  That requires a Yang--Mills-specific identifiability or
coercivity estimate for the chosen separator observable.  No such estimate,
DP separator observable, U(1) mirror kernel, marginal AF envelope, or physical
continuum trajectory is asserted here.

## Constructive contract

Finite recursion and exact `Q'` arithmetic only.  No `Classical.*`,
`native_decide`, custom axiom, `noncomputable` declaration, or placeholder.
-/

import YMGap.Continuum.BF4ObservableMatchedOneStep

namespace YMGap.Continuum.BF4ObservableMatchedTrajectory

open YMGap.Constructive
open YMGap.Continuum.BF4ObservableMatchedOneStep

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Positive coupling states and schedules -/

/-- A coupling carried together with the strict positivity needed by the next
physical matching step. -/
structure PositiveCoupling : Type where
  value : Q'
  value_pos : (0 : Q') < value

theorem PositiveCoupling.value_nonnegative (state : PositiveCoupling) :
    (0 : Q') ≤ state.value :=
  Q'.le_of_lt state.value_pos

/-- All data that may vary from one exact BF4 matching step to the next. -/
structure ObservableMatchedSchedule : Type where
  geometry : Nat → CutoffOneGeometry
  atlas : Nat → PositiveCouplingAtlas
  observable : Nat → SlabLabelling → Q'

namespace ObservableMatchedSchedule

/-- One derived successor state.  Its coupling is computed by exact physical
observable matching; no externally supplied flow value enters. -/
def nextState
    (schedule : ObservableMatchedSchedule)
    (step : Nat)
    (current : PositiveCoupling) :
    PositiveCoupling where
  value :=
    observableMatchedCoupling
      (schedule.geometry step)
      current.value current.value_nonnegative
      (schedule.atlas step)
      (schedule.observable step)
  value_pos :=
    observableMatchedCoupling_pos
      (schedule.geometry step)
      current.value current.value_nonnegative
      (schedule.atlas step)
      (schedule.observable step)

/-- The recursively derived observable-matched trajectory. -/
def trajectory
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling) :
    Nat → PositiveCoupling
  | 0 => initial
  | step + 1 =>
      schedule.nextState step (schedule.trajectory initial step)

@[simp] theorem trajectory_zero
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling) :
    schedule.trajectory initial 0 = initial :=
  rfl

@[simp] theorem trajectory_succ
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    schedule.trajectory initial (step + 1) =
      schedule.nextState step (schedule.trajectory initial step) :=
  rfl

/-- Scalar view of the derived trajectory. -/
def couplingAt
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) : Q' :=
  (schedule.trajectory initial step).value

theorem couplingAt_pos
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (0 : Q') < schedule.couplingAt initial step :=
  (schedule.trajectory initial step).value_pos

theorem couplingAt_nonnegative
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (0 : Q') ≤ schedule.couplingAt initial step :=
  Q'.le_of_lt (schedule.couplingAt_pos initial step)

@[simp] theorem couplingAt_zero
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling) :
    schedule.couplingAt initial 0 = initial.value :=
  rfl

@[simp] theorem couplingAt_succ
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    schedule.couplingAt initial (step + 1) =
      observableMatchedCoupling
        (schedule.geometry step)
        (schedule.couplingAt initial step)
        (schedule.couplingAt_nonnegative initial step)
        (schedule.atlas step)
        (schedule.observable step) :=
  rfl

/-! ## 2. Per-step exact certificates -/

/-- Every derived successor belongs to the candidate atlas used at that
step. -/
theorem couplingAt_succ_mem
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    schedule.couplingAt initial (step + 1) ∈
      (schedule.atlas step).candidates := by
  exact observableMatchedCoupling_mem
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.atlas step)
    (schedule.observable step)

/-- The exact physical matching defect selected at a trajectory step. -/
def selectedStepDefect
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) : Q' :=
  observableMatchDefect
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.couplingAt initial (step + 1))
    (schedule.couplingAt_pos initial (step + 1))
    (schedule.observable step)

theorem selectedStepDefect_nonnegative
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (0 : Q') ≤ schedule.selectedStepDefect initial step := by
  unfold selectedStepDefect observableMatchDefect
  exact Q'.abs_nonneg _

/-- At every step, the recursively selected coupling minimizes the exact
physical observable-matching defect over the complete supplied atlas. -/
theorem couplingAt_succ_minimizes
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat)
    (candidate : Q')
    (hcandidate :
      candidate ∈ (schedule.atlas step).candidates) :
    schedule.selectedStepDefect initial step ≤
      observableMatchDefect
        (schedule.geometry step)
        (schedule.couplingAt initial step)
        (schedule.couplingAt_nonnegative initial step)
        candidate
        ((schedule.atlas step).candidate_pos hcandidate)
        (schedule.observable step) := by
  unfold selectedStepDefect
  exact observableMatchedCoupling_minimizes
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.atlas step)
    (schedule.observable step)
    candidate hcandidate

/-- The `Type`-valued exact discriminator at one point of the recursively
derived trajectory. -/
def stepReferenceComparison
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    ReferenceComparison
      (schedule.couplingAt initial (step + 1))
      (twoDimensionalReference (schedule.couplingAt initial step)) :=
  observableMatchedReferenceComparison
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.atlas step)
    (schedule.observable step)

/-- Propositional view of the exact per-step comparison certificate. -/
theorem couplingAt_succ_vs_twoDimensional
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    schedule.couplingAt initial (step + 1) <
        twoDimensionalReference (schedule.couplingAt initial step) ∨
      schedule.couplingAt initial (step + 1) ≈
        twoDimensionalReference (schedule.couplingAt initial step) ∨
      twoDimensionalReference (schedule.couplingAt initial step) <
        schedule.couplingAt initial (step + 1) := by
  exact observableMatched_vs_twoDimensional
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.atlas step)
    (schedule.observable step)

/-! ## 3. Quantitative candidate certificates -/

/-- A concrete atlas candidate whose exact physical matching defect is at most
`epsilon`.  This is `Type`-valued because the candidate is computational data
that downstream selection consumes. -/
structure StepDefectWitness
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat)
    (epsilon : Q') : Type where
  candidate : Q'
  candidate_mem :
    candidate ∈ (schedule.atlas step).candidates
  defect_le :
    observableMatchDefect
        (schedule.geometry step)
        (schedule.couplingAt initial step)
        (schedule.couplingAt_nonnegative initial step)
        candidate
        ((schedule.atlas step).candidate_pos candidate_mem)
        (schedule.observable step) ≤
      epsilon

/-- Any certified candidate error bound transfers to the exact selected
coupling. -/
theorem selectedStepDefect_le_of_witness
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat)
    (epsilon : Q')
    (witness :
      StepDefectWitness schedule initial step epsilon) :
    schedule.selectedStepDefect initial step ≤ epsilon :=
  Q'.le_trans' _ _ _
    (schedule.couplingAt_succ_minimizes
      initial step witness.candidate witness.candidate_mem)
    witness.defect_le

/-- Quantitative handoff from observable-defect control to coupling control.

The substantive input `identifies` is deliberately explicit: it is the
Yang--Mills-specific coercivity estimate saying that coupling distance from a
target is bounded by `constant` times the physical observable-matching
defect.  Given it, any finite candidate-error certificate immediately yields
the corresponding coupling-distance bound for the recursively selected
successor. -/
theorem couplingAt_succ_distance_le_of_identifiability
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat)
    (epsilon target constant : Q')
    (constant_nonnegative : (0 : Q') ≤ constant)
    (identifies :
      ∀ candidate : Q',
        ∀ hcandidate :
          candidate ∈ (schedule.atlas step).candidates,
        Q'.abs (candidate + -target) ≤
          constant *
            observableMatchDefect
              (schedule.geometry step)
              (schedule.couplingAt initial step)
              (schedule.couplingAt_nonnegative initial step)
              candidate
              ((schedule.atlas step).candidate_pos hcandidate)
              (schedule.observable step))
    (witness :
      StepDefectWitness schedule initial step epsilon) :
    Q'.abs
        (schedule.couplingAt initial (step + 1) + -target) ≤
      constant * epsilon := by
  have hmember :=
    schedule.couplingAt_succ_mem initial step
  have hidentify :=
    identifies
      (schedule.couplingAt initial (step + 1))
      hmember
  have hdefect :
      schedule.selectedStepDefect initial step ≤ epsilon :=
    schedule.selectedStepDefect_le_of_witness
      initial step epsilon witness
  have hscaled :
      constant * schedule.selectedStepDefect initial step ≤
        constant * epsilon :=
    Q'.mul_le_mul_of_nonneg_left _ _ constant
      hdefect constant_nonnegative
  exact Q'.le_trans' _ _ _ hidentify hscaled

end ObservableMatchedSchedule

/-! ## 4. Atlas refinement order -/

/-- `fine` refines `coarse` when it retains every old candidate.  The witness
is `Type`-valued so it can be composed and consumed computationally. -/
structure AtlasRefinement
    (coarse fine : PositiveCouplingAtlas) : Type where
  preserves :
    ∀ candidate : Q',
      candidate ∈ coarse.candidates →
        candidate ∈ fine.candidates

def AtlasRefinement.refl
    (atlas : PositiveCouplingAtlas) :
    AtlasRefinement atlas atlas where
  preserves := fun _ hcandidate => hcandidate

def AtlasRefinement.trans
    {first second third : PositiveCouplingAtlas}
    (left : AtlasRefinement first second)
    (right : AtlasRefinement second third) :
    AtlasRefinement first third where
  preserves := fun candidate hcandidate =>
    right.preserves candidate
      (left.preserves candidate hcandidate)

/-- Exact selected defect for one fixed coupling, geometry, atlas, and
observable. -/
def selectedDefect
    (geometry : CutoffOneGeometry)
    (coupling : Q') (coupling_nonnegative : (0 : Q') ≤ coupling)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') : Q' :=
  observableMatchDefect geometry coupling coupling_nonnegative
    (observableMatchedCoupling geometry coupling coupling_nonnegative
      atlas observable)
    (observableMatchedCoupling_pos geometry coupling coupling_nonnegative
      atlas observable)
    observable

theorem selectedDefect_nonnegative
    (geometry : CutoffOneGeometry)
    (coupling : Q') (coupling_nonnegative : (0 : Q') ≤ coupling)
    (atlas : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') :
    (0 : Q') ≤
      selectedDefect geometry coupling coupling_nonnegative
        atlas observable := by
  unfold selectedDefect observableMatchDefect
  exact Q'.abs_nonneg _

/-- Enlarging a candidate atlas cannot worsen the exact selected physical
matching defect. -/
theorem selectedDefect_antitone_of_refinement
    (geometry : CutoffOneGeometry)
    (coupling : Q') (coupling_nonnegative : (0 : Q') ≤ coupling)
    (coarse fine : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (refinement : AtlasRefinement coarse fine) :
    selectedDefect geometry coupling coupling_nonnegative fine observable ≤
      selectedDefect geometry coupling coupling_nonnegative coarse observable := by
  let coarseChoice :=
    observableMatchedCoupling geometry coupling coupling_nonnegative
      coarse observable
  have hcoarse :
      coarseChoice ∈ coarse.candidates :=
    observableMatchedCoupling_mem geometry coupling coupling_nonnegative
      coarse observable
  have hfine :
      coarseChoice ∈ fine.candidates :=
    refinement.preserves coarseChoice hcoarse
  unfold selectedDefect
  exact observableMatchedCoupling_minimizes
    geometry coupling coupling_nonnegative fine observable
    coarseChoice hfine

/-- A refinement is defect-safe when the old selected coupling remains a
global minimizer even after all new candidates are admitted. -/
structure DefectSafeRefinement
    (geometry : CutoffOneGeometry)
    (coupling : Q') (coupling_nonnegative : (0 : Q') ≤ coupling)
    (coarse fine : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q') : Type where
  refinement : AtlasRefinement coarse fine
  old_remains_minimal :
    ∀ candidate : Q', ∀ hcandidate : candidate ∈ fine.candidates,
      selectedDefect geometry coupling coupling_nonnegative coarse observable ≤
        observableMatchDefect geometry coupling coupling_nonnegative
          candidate (fine.candidate_pos hcandidate) observable

private theorem q_eqv_of_le_antisymm {left right : Q'}
    (hleft : left ≤ right) (hright : right ≤ left) :
    left ≈ right := by
  show
    left.num * (right.den : Int) =
      right.num * (left.den : Int)
  exact Int.le_antisymm hleft hright

/-- A defect-safe refinement preserves the optimal defect exactly, up to the
semantic rational equivalence `Q'.eqv`.  This is the finite stability theorem
available without assuming coupling identifiability. -/
theorem selectedDefect_eqv_of_safe_refinement
    (geometry : CutoffOneGeometry)
    (coupling : Q') (coupling_nonnegative : (0 : Q') ≤ coupling)
    (coarse fine : PositiveCouplingAtlas)
    (observable : SlabLabelling → Q')
    (safe :
      DefectSafeRefinement geometry coupling coupling_nonnegative
        coarse fine observable) :
    selectedDefect geometry coupling coupling_nonnegative fine observable ≈
      selectedDefect geometry coupling coupling_nonnegative coarse observable := by
  have hfine_le_coarse :
      selectedDefect geometry coupling coupling_nonnegative fine observable ≤
        selectedDefect geometry coupling coupling_nonnegative coarse observable :=
    selectedDefect_antitone_of_refinement
      geometry coupling coupling_nonnegative coarse fine observable
      safe.refinement
  have hfineChoice :
      observableMatchedCoupling geometry coupling coupling_nonnegative
          fine observable ∈ fine.candidates :=
    observableMatchedCoupling_mem
      geometry coupling coupling_nonnegative fine observable
  have hcoarse_le_fine :
      selectedDefect geometry coupling coupling_nonnegative coarse observable ≤
        selectedDefect geometry coupling coupling_nonnegative fine observable := by
    unfold selectedDefect
    exact safe.old_remains_minimal
      (observableMatchedCoupling geometry coupling coupling_nonnegative
        fine observable)
      hfineChoice
  exact q_eqv_of_le_antisymm hfine_le_coarse hcoarse_le_fine

end YMGap.Continuum.BF4ObservableMatchedTrajectory

/-! ## Axiom-dependency gates -/

#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.trajectory
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.couplingAt_succ_mem
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.couplingAt_succ_minimizes
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.stepReferenceComparison
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.couplingAt_succ_vs_twoDimensional
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.selectedStepDefect_le_of_witness
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.ObservableMatchedSchedule.couplingAt_succ_distance_le_of_identifiability
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.selectedDefect_antitone_of_refinement
#print axioms YMGap.Continuum.BF4ObservableMatchedTrajectory.selectedDefect_eqv_of_safe_refinement
