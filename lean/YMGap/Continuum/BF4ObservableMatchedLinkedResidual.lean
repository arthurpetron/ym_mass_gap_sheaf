/-
# The observable-matched BF4 trajectory as a linked scalar residual path

`BF4ObservableMatchedTrajectory` recursively chooses each successor coupling
by minimizing an exact observable discrepancy for the globally link-glued
cutoff-one BF4 pushforward.  This module gives that already-constructed scalar
trajectory the fail-closed residual interface of
`BF4PhysicalTrajectoryFence`.

At step `k` the local residual is not assumed or hidden.  It is the literal
finite rational

    delta k = |w(k+1) - w(k)^4|.

The scale-four exponent is the exact two-dimensional heat-semigroup reference
already used by the observable-matched trajectory.  With physical spacing
`a(k) > 0`, the residual record uses the explicit reciprocal curvature cutoff
`Lambda(k) = 1/a(k)`, so `delta <= delta * a * Lambda` is an equality.  This is
bookkeeping, not a small-error estimate.  Observable identifiability plus a
candidate defect witness supplies the substantive upper bound on `delta`.

The module also records the present carrier obstruction.  Each matched step
starts at cutoff one and lands at cutoff four, while the next constructor again
starts at cutoff one.  Thus the recursively linked scalar couplings are not yet
a literally reproduced full-state trajectory.  A general-cutoff block step or
an explicit cutoff-four-to-next-input recoding remains necessary.

## Axiom gate

Finite recursion and exact `Q'` arithmetic only.  No classical choice,
placeholder, or hidden physical estimate.
-/

import YMGap.Continuum.BF4ObservableMatchedTrajectory
import YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability

namespace YMGap.Continuum.BF4ObservableMatchedLinkedResidual

open YMGap.Constructive
open YMGap.Constructive.QPoly
open YMGap.Continuum.BF4ObservableMatchedOneStep
open YMGap.Continuum.BF4ObservableMatchedTrajectory
open YMGap.Continuum.BF4PhysicalTrajectoryFence
open YMGap.Continuum.BF4LinkedBondMovingTrajectoryStability
open YMGap.Continuum.HeatKernelRGStep
open YMGap.Continuum.RGTransport

/-! ## 1. The literal scalar residual of the exact matched step -/

/-- Exact distance from the selected four-dimensional matched coupling to the
scale-four heat-semigroup reference. -/
def observableMatchedStepDelta
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) : Q' :=
  Q'.abs
    (schedule.couplingAt initial (step + 1) -
      mkDecimate 4 (schedule.couplingAt initial step))

theorem observableMatchedStepDelta_nonnegative
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (0 : Q') ≤ observableMatchedStepDelta schedule initial step :=
  Q'.abs_nonneg _

/-- The coupled residual record for one exact observable-matched BF4 step.

`resC = delta` and `cutoff = 1/a`; consequently the legacy dimensional bound
is exactly saturated.  The useful content is the separate literal
`deviation_control`, also saturated by definition. -/
def observableMatchedCoupledResidual
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step)
    (step : Nat) :
    CoupledBondMovingResidual 4 (spacing step)
      (schedule.couplingAt initial step) where
  base :=
    { delta := observableMatchedStepDelta schedule initial step
      delta_nonneg :=
        observableMatchedStepDelta_nonnegative schedule initial step
      resC := observableMatchedStepDelta schedule initial step
      resC_nonneg :=
        observableMatchedStepDelta_nonnegative schedule initial step
      cutoff := Q'.recipPos (spacing step) (spacing_pos step)
      cutoff_nonneg :=
        Q'.le_of_lt (Q'.recipPos_pos (spacing step) (spacing_pos step))
      fullStepWeight := schedule.couplingAt initial (step + 1)
      decimatedWeight := mkDecimate 4 (schedule.couplingAt initial step)
      decimated_eq := rfl
      residual_bound := by
        constructor
        · exact observableMatchedStepDelta_nonnegative schedule initial step
        · apply Q'.ge_of_eqv
          refine Q'.eqv_trans _ _ _
            (Q'.mul_assoc_eqv
              (observableMatchedStepDelta schedule initial step)
              (spacing step)
              (Q'.recipPos (spacing step) (spacing_pos step))) ?_
          refine Q'.eqv_trans _ _ _
            (Q'.mul_eqv_congr_left
              (observableMatchedStepDelta schedule initial step) _ _
              (Q'.mul_recipPos_eqv
                (spacing step) (spacing_pos step))) ?_
          exact Q'.mul_one_eqv
            (observableMatchedStepDelta schedule initial step) }
  deviation_control := Q'.le_refl' _

/-- The recursively selected observable-matched couplings therefore inhabit
the repaired linked scalar interface, with their exact mismatch from heat
decimation exposed as data. -/
def observableMatchedLinkedTrajectory
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step) :
    LinkedBondMovingTrajectory 4 where
  spacing := spacing
  spacing_pos := spacing_pos
  weight := schedule.couplingAt initial
  step := observableMatchedCoupledResidual
    schedule initial spacing spacing_pos
  next_identification := fun _step => Q'.eqv_refl _

@[simp] theorem observableMatchedLinkedTrajectory_weight
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step)
    (step : Nat) :
    (observableMatchedLinkedTrajectory
      schedule initial spacing spacing_pos).weight step =
        schedule.couplingAt initial step :=
  rfl

@[simp] theorem observableMatchedLinkedTrajectory_delta
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step)
    (step : Nat) :
    ((observableMatchedLinkedTrajectory
      schedule initial spacing spacing_pos).step step).base.delta =
        observableMatchedStepDelta schedule initial step :=
  rfl

/-! ## 2. The finite identifiability estimate is exactly the residual target -/

/-- A candidate defect witness and observable identifiability against the
heat-semigroup target bound the literal linked residual.  This is the precise
place where non-abelian BF4 mathematics must control the selected coupling. -/
theorem observableMatchedStepDelta_le_of_identifiability
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat)
    (epsilon constant : Q')
    (constant_nonnegative : (0 : Q') ≤ constant)
    (identifies :
      ∀ candidate : Q',
        ∀ hcandidate :
          candidate ∈ (schedule.atlas step).candidates,
        Q'.abs
            (candidate +
              -mkDecimate 4 (schedule.couplingAt initial step)) ≤
          constant *
            observableMatchDefect
              (schedule.geometry step)
              (schedule.couplingAt initial step)
              (schedule.couplingAt_nonnegative initial step)
              candidate
              ((schedule.atlas step).candidate_pos hcandidate)
              (schedule.observable step))
    (witness :
      ObservableMatchedSchedule.StepDefectWitness
        schedule initial step epsilon) :
    observableMatchedStepDelta schedule initial step ≤
      constant * epsilon := by
  exact schedule.couplingAt_succ_distance_le_of_identifiability
    initial step epsilon
    (mkDecimate 4 (schedule.couplingAt initial step))
    constant constant_nonnegative identifies witness

/-! ## 3. Unit-interval transport and the stability handoff -/

/-- If the initial coupling and every atlas candidate are below one, then the
entire recursively selected matched trajectory is below one. -/
theorem couplingAt_lt_one_of_atlas
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (initial_lt_one : initial.value < (1 : Q'))
    (atlas_lt_one :
      ∀ step candidate,
        candidate ∈ (schedule.atlas step).candidates →
          candidate < (1 : Q')) :
    ∀ step, schedule.couplingAt initial step < (1 : Q')
  | 0 => initial_lt_one
  | step + 1 =>
      atlas_lt_one step
        (schedule.couplingAt initial (step + 1))
        (schedule.couplingAt_succ_mem initial step)

/-- The general linked-trajectory stability theorem specialized to the exact
observable-matched BF4 scalar orbit. -/
theorem observableMatchedCoupling_close_to_heatDecimationOrbit
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step)
    (initial_lt_one : initial.value < (1 : Q'))
    (atlas_lt_one :
      ∀ step candidate,
        candidate ∈ (schedule.atlas step).candidates →
          candidate < (1 : Q'))
    (step : Nat) :
    Q'.abs
        (schedule.couplingAt initial step -
          idealDecimationOrbit 4 initial.value step) ≤
      trajectoryAccumulatedDefect
        (observableMatchedLinkedTrajectory
          schedule initial spacing spacing_pos) step := by
  let linked := observableMatchedLinkedTrajectory
    schedule initial spacing spacing_pos
  apply linked_weight_close_to_idealDecimationOrbit linked
  · intro index
    exact schedule.couplingAt_nonnegative initial index
  · intro index
    exact Q'.le_of_lt
      (couplingAt_lt_one_of_atlas
        schedule initial initial_lt_one atlas_lt_one index)

/-- **Observable-to-corridor compiler.**  A uniform finite candidate-defect
witness and a uniform identifiability constant bound every literal RG
residual by `constant * epsilon`.  The closed stability criterion then places
the recursively selected BF4 coupling in the strong corridor.

Every quantified parameter is visible.  In particular, no beta- or
scale-uniform estimate is asserted by this theorem; such uniformity has to be
supplied by `identifies` and `witness`. -/
theorem observableMatchedCoupling_le_anchorCoupling_of_uniform_control
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (spacing : Nat → Q')
    (spacing_pos : ∀ step, (0 : Q') < spacing step)
    (initial_lt_one : initial.value < (1 : Q'))
    (atlas_lt_one :
      ∀ step candidate,
        candidate ∈ (schedule.atlas step).candidates →
          candidate < (1 : Q'))
    (epsilon constant : Q')
    (constant_nonnegative : (0 : Q') ≤ constant)
    (identifies :
      ∀ step candidate,
        ∀ hcandidate :
          candidate ∈ (schedule.atlas step).candidates,
        Q'.abs
            (candidate +
              -mkDecimate 4 (schedule.couplingAt initial step)) ≤
          constant *
            observableMatchDefect
              (schedule.geometry step)
              (schedule.couplingAt initial step)
              (schedule.couplingAt_nonnegative initial step)
              candidate
              ((schedule.atlas step).candidate_pos hcandidate)
              (schedule.observable step))
    (witness :
      ∀ step,
        ObservableMatchedSchedule.StepDefectWitness
          schedule initial step epsilon)
    (step : Nat)
    (hbudget :
      qpow initial.value (4 ^ step) +
          (constant * epsilon) * geomSum (Q'.ofNat 4) step ≤
        YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling) :
    schedule.couplingAt initial step ≤
      YMGap.Continuum.Z4StrongCouplingParametricAnchor.anchorCoupling := by
  let linked := observableMatchedLinkedTrajectory
    schedule initial spacing spacing_pos
  apply linked_weight_le_anchorCoupling_of_uniform_residual
    linked
  · intro index
    exact schedule.couplingAt_nonnegative initial index
  · intro index
    exact Q'.le_of_lt
      (couplingAt_lt_one_of_atlas
        schedule initial initial_lt_one atlas_lt_one index)
  · intro index
    change observableMatchedStepDelta schedule initial index ≤
      constant * epsilon
    exact observableMatchedStepDelta_le_of_identifiability
      schedule initial index epsilon constant constant_nonnegative
      (identifies index) (witness index)
  · exact hbudget

/-! ## 4. The present full-carrier reproduction obstruction -/

/-- The exact matched physical scale pair used at one recursive scalar step. -/
def observableMatchedScalePairAt
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :=
  observableMatchedScalePair
    (schedule.geometry step)
    (schedule.couplingAt initial step)
    (schedule.couplingAt_nonnegative initial step)
    (schedule.atlas step)
    (schedule.observable step)

@[simp] theorem observableMatchedScalePairAt_fine_cutoff
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (observableMatchedScalePairAt schedule initial step).fine.cutoff = 1 :=
  rfl

@[simp] theorem observableMatchedScalePairAt_coarse_cutoff
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    (observableMatchedScalePairAt schedule initial step).coarse.cutoff = 4 :=
  rfl

/-- **Kernel-checked carrier fence.**  The present cutoff-one matched-step
constructor cannot reproduce its full coarse carrier as the next fine carrier:
the former has cutoff four and the latter cutoff one.  Only the scalar coupling
is currently iterated. -/
theorem observableMatchedScalePairAt_not_cutoff_reproduced
    (schedule : ObservableMatchedSchedule)
    (initial : PositiveCoupling)
    (step : Nat) :
    ¬ (observableMatchedScalePairAt schedule initial step).coarse.cutoff =
        (observableMatchedScalePairAt schedule initial (step + 1)).fine.cutoff := by
  simp only [observableMatchedScalePairAt_coarse_cutoff,
    observableMatchedScalePairAt_fine_cutoff]
  decide

end YMGap.Continuum.BF4ObservableMatchedLinkedResidual

#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedCoupledResidual
#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedLinkedTrajectory
#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedStepDelta_le_of_identifiability
#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedCoupling_close_to_heatDecimationOrbit
#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedCoupling_le_anchorCoupling_of_uniform_control
#print axioms YMGap.Continuum.BF4ObservableMatchedLinkedResidual.observableMatchedScalePairAt_not_cutoff_reproduced
