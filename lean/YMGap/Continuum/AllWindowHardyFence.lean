/-
# Fence for the endpoint-weight Hardy/telescoping route

The exact Dirichlet identity in `AllWindowCorrDirichlet` suggests proving the
all-window retune inequality by a local ground-state transform.  At `w=1`, the
natural telescoping weights begin

    K_0 = 0,   K_1 = 1/4.

The corresponding first-edge certificate would be

    c_0 c_1 + K_0 c_0^2 <= r^3 c_0^2 + K_1 c_1^2.

This module machine-refutes that certificate at the exact rational base
`w=9/10`: its left-minus-right defect is `1081/15625 > 0`.  Crucially, the
GLOBAL cutoff-one retune residual remains positive.  Thus the target is not
refuted; what is refuted is the tempting cutoff-independent endpoint-weight
localization.  A successful Hardy transform must use genuinely `w`-dependent,
index-coupled weights (or a nonlocal theta/Abel mechanism).
-/

import YMGap.Continuum.AllWindowCorrDirichlet

namespace YMGap.Continuum.AllWindowHardyFence

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.ArbitraryTruncationRetuneCorr
open YMGap.Continuum.AllWindowCorrDirichlet

private def wNineTenths : Q' := Q'.mkPos 9 10 (by decide)
private def quarter : Q' := Q'.mkPos 1 4 (by decide)

/-- First-edge defect for the endpoint-derived local Hardy weights
`K_0=0`, `K_1=1/4`.  Positive means the desired local inequality fails. -/
def endpointLocalDefect : Q' :=
  coeffW wNineTenths 0 * coeffW wNineTenths 1 -
    (retuneCube wNineTenths *
        (coeffW wNineTenths 0 * coeffW wNineTenths 0) +
      quarter * (coeffW wNineTenths 1 * coeffW wNineTenths 1))

/-- The failed local step misses by the exact positive rational
`1081/15625`; no measured constant is used. -/
theorem endpointLocalDefect_exact :
    endpointLocalDefect.eqv (Q'.mkPos 1081 15625 (by decide)) := by
  decide

theorem endpointLocalDefect_pos : (0 : Q') < endpointLocalDefect := by
  exact CubeRatioBounds.pos_of_eqv_of_pos endpointLocalDefect_exact (by decide)

/-- **Machine-refuted endpoint-weight local certificate.** -/
theorem endpoint_weight_first_edge_fails :
    ¬ (coeffW wNineTenths 0 * coeffW wNineTenths 1 ≤
        retuneCube wNineTenths *
            (coeffW wNineTenths 0 * coeffW wNineTenths 0) +
          quarter * (coeffW wNineTenths 1 * coeffW wNineTenths 1)) := by
  decide

/-- The global cutoff-one residual has the exact positive value
`2443903819/2000000000`.  Hence the local failure above does not refute the
all-window correlation inequality; the boundary and neighboring energy must
be used jointly. -/
theorem cutoff_one_global_residual_exact :
    (corrResidual wNineTenths 1).eqv
      (Q'.mkPos 2443903819 2000000000 (by decide)) := by
  decide

theorem cutoff_one_global_retune_holds :
    adjCorr wNineTenths 1 ≤
      retuneCube wNineTenths * coordNormSq wNineTenths 1 := by
  decide

/-- At the same closed test point the sharp Dirichlet lower-bound slack is
exactly twice the spectral residual and is strictly positive. -/
theorem cutoff_one_poincare_slack_exact :
    ((coeffW wNineTenths 0 * coeffW wNineTenths 0 +
          coeffW wNineTenths 1 * coeffW wNineTenths 1 +
          dirichletEnergy wNineTenths 1) -
        (Q'.ofNat 2 * ((1 : Q') - retuneCube wNineTenths) *
          coordNormSq wNineTenths 1)).eqv
      (Q'.mkPos 2443903819 1000000000 (by decide)) := by
  decide

end YMGap.Continuum.AllWindowHardyFence

#print axioms YMGap.Continuum.AllWindowHardyFence.endpointLocalDefect_exact
#print axioms YMGap.Continuum.AllWindowHardyFence.endpointLocalDefect_pos
#print axioms YMGap.Continuum.AllWindowHardyFence.endpoint_weight_first_edge_fails
#print axioms YMGap.Continuum.AllWindowHardyFence.cutoff_one_global_residual_exact
#print axioms YMGap.Continuum.AllWindowHardyFence.cutoff_one_global_retune_holds
#print axioms YMGap.Continuum.AllWindowHardyFence.cutoff_one_poincare_slack_exact
