/- Generated finite-prefix data.  The generator is untrusted; Lean checks this file. -/
import YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

namespace YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarterExample

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageRelativeRankOneQuarter
open YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarter

local infix:50 " ≈ " => Q'.eqv

-- Generator-side threshold: 2
-- Generator-side maximum prefix error: 1/16
def boundaryMessagePrefixPilotBudget
    (error : Nat -> Q')
    (boundaryMessagePrefixPilotStage0_exact :
      error 0 ≈ Q'.mkPos 1 32 (by decide))
    (boundaryMessagePrefixPilotStage1_exact :
      error 1 ≈ Q'.mkPos 1 20 (by decide))
    (boundaryMessagePrefixPilotStage2_exact :
      error 2 ≈ Q'.mkPos 1 16 (by decide))
    (tail_step : forall stage : Nat,
      2 <= stage -> error (stage + 1) <= error stage) :
    QuarterErrorPrefixTail error where
  threshold := 2
  prefix_bound := by
    intro stage hstage
    have hcases : stage = 0 ∨ stage = 1 := by omega
    rcases hcases with rfl | rfl
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv boundaryMessagePrefixPilotStage0_exact) (by decide)
    · exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv boundaryMessagePrefixPilotStage1_exact) (by decide)
  threshold_bound := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv boundaryMessagePrefixPilotStage2_exact) (by decide)
  tail_step := tail_step

theorem boundaryMessagePrefixPilotAllStages_le
    (error : Nat -> Q')
    (boundaryMessagePrefixPilotStage0_exact :
      error 0 ≈ Q'.mkPos 1 32 (by decide))
    (boundaryMessagePrefixPilotStage1_exact :
      error 1 ≈ Q'.mkPos 1 20 (by decide))
    (boundaryMessagePrefixPilotStage2_exact :
      error 2 ≈ Q'.mkPos 1 16 (by decide))
    (tail_step : forall stage : Nat,
      2 <= stage -> error (stage + 1) <= error stage) :
    forall stage : Nat, error stage <= relativeRankOneTolerance := by
  intro stage
  exact (boundaryMessagePrefixPilotBudget error
    boundaryMessagePrefixPilotStage0_exact
    boundaryMessagePrefixPilotStage1_exact
    boundaryMessagePrefixPilotStage2_exact tail_step).bound_all stage

end YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarterExample

#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarterExample.boundaryMessagePrefixPilotBudget
#print axioms YMGap.Continuum.BF4BoundaryMessagePrefixTailQuarterExample.boundaryMessagePrefixPilotAllStages_le
