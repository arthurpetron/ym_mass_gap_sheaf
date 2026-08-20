/- Generated computed-floor prefix data.  The generator is untrusted; Lean checks this file. -/
import YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail

namespace YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTailExample

open YMGap.Constructive
open YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTail
open YMGap.Continuum.BF4PhysicalHalfAmplitudeRelativeTerminalPerturbation

local infix:50 " ≈ " => Q'.eqv

-- Generator-side threshold: 2
-- Generator-side maximum error/floor ratio: 1/2048
def computedFloorPrefixDemoBudget
    (error floor : Nat -> Q')
    (computedFloorPrefixDemoErrorStage0_exact : error 0 ≈ Q'.mkPos 1 8192 (by decide))
    (computedFloorPrefixDemoFloorStage0_exact : floor 0 ≈ Q'.mkPos 1 2 (by decide))
    (computedFloorPrefixDemoErrorStage1_exact : error 1 ≈ Q'.mkPos 3 16384 (by decide))
    (computedFloorPrefixDemoFloorStage1_exact : floor 1 ≈ Q'.mkPos 3 4 (by decide))
    (computedFloorPrefixDemoErrorStage2_exact : error 2 ≈ Q'.mkPos 1 2048 (by decide))
    (computedFloorPrefixDemoFloorStage2_exact : floor 2 ≈ Q'.mkPos 1 1 (by decide))
    (floor_pos : forall stage, (0 : Q') < floor stage)
    (tail_cross : forall stage : Nat,
      2 <= stage ->
        error (stage + 1) * floor stage <=
          error stage * floor (stage + 1))
    : PositiveFloorErrorCrossTail
        error floor physicalRelativeErrorTolerance where
  threshold := 2
  floor_pos := floor_pos
  prefix_bound := by
    intro stage hstage
    have hcases : stage = 0 ∨ stage = 1 := by omega
    rcases hcases with rfl | rfl
    ·
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv computedFloorPrefixDemoErrorStage0_exact)
        (Q'.le_trans' _ _ _
          (by decide)
          (Q'.ge_of_eqv
            (Q'.mul_eqv_congr_left
              physicalRelativeErrorTolerance _ _
              computedFloorPrefixDemoFloorStage0_exact)))
    ·
      exact Q'.le_trans' _ _ _
        (Q'.le_of_eqv computedFloorPrefixDemoErrorStage1_exact)
        (Q'.le_trans' _ _ _
          (by decide)
          (Q'.ge_of_eqv
            (Q'.mul_eqv_congr_left
              physicalRelativeErrorTolerance _ _
              computedFloorPrefixDemoFloorStage1_exact)))
  threshold_bound := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv computedFloorPrefixDemoErrorStage2_exact)
      (Q'.le_trans' _ _ _
        (by decide)
        (Q'.ge_of_eqv
          (Q'.mul_eqv_congr_left
            physicalRelativeErrorTolerance _ _
            computedFloorPrefixDemoFloorStage2_exact)))
  tail_cross := tail_cross

theorem computedFloorPrefixDemoAllStages_le
    (error floor : Nat -> Q')
    (computedFloorPrefixDemoErrorStage0_exact : error 0 ≈ Q'.mkPos 1 8192 (by decide))
    (computedFloorPrefixDemoFloorStage0_exact : floor 0 ≈ Q'.mkPos 1 2 (by decide))
    (computedFloorPrefixDemoErrorStage1_exact : error 1 ≈ Q'.mkPos 3 16384 (by decide))
    (computedFloorPrefixDemoFloorStage1_exact : floor 1 ≈ Q'.mkPos 3 4 (by decide))
    (computedFloorPrefixDemoErrorStage2_exact : error 2 ≈ Q'.mkPos 1 2048 (by decide))
    (computedFloorPrefixDemoFloorStage2_exact : floor 2 ≈ Q'.mkPos 1 1 (by decide))
    (floor_pos : forall stage, (0 : Q') < floor stage)
    (tail_cross : forall stage : Nat,
      2 <= stage ->
        error (stage + 1) * floor stage <=
          error stage * floor (stage + 1))
    : forall stage : Nat,
      error stage <= physicalRelativeErrorTolerance * floor stage := by
  intro stage
  exact (computedFloorPrefixDemoBudget error floor computedFloorPrefixDemoErrorStage0_exact computedFloorPrefixDemoFloorStage0_exact computedFloorPrefixDemoErrorStage1_exact computedFloorPrefixDemoFloorStage1_exact computedFloorPrefixDemoErrorStage2_exact computedFloorPrefixDemoFloorStage2_exact floor_pos tail_cross)
    |>.error_le_tolerance_mul_floor stage

end YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTailExample

#print axioms YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTailExample.computedFloorPrefixDemoBudget
#print axioms YMGap.Continuum.BF4BoundaryMessageComputedFloorCrossTailExample.computedFloorPrefixDemoAllStages_le
