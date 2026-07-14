/-
# A fence against consuming one lifted row as an interval family

Shifted finite Jacobi uniqueness requires a recurrence certificate at every
absolute order in its interval.  A lifted `p = 1` row is only the centre row;
it does not logically provide the neighbouring `p = 2` certificate.  The
closed four-channel block below makes that missing datum machine-visible.
-/

import YMGap.Continuum.SU2OrderedRacahRightJacobiEndpointLift
import YMGap.Continuum.SU2OrderedRacahShiftedJacobiUniqueness

namespace YMGap.Continuum.SU2OrderedRacahRightJacobiIntervalFence

open YMGap.Constructive
open YMGap.Continuum.SU2OrderedRacahFiniteJacobiConsumer

/-- A sequence supported only at order three.  Thus its order-one Jacobi row
sees only zeros, while its order-two row sees the nonzero forward neighbour. -/
def endpointLiftFenceSequence (p : Nat) : Q' :=
  if p = 3 then 1 else 0

/-- **Machine refutation of the single-row consumer shortcut.**  In the
physical `(3,3,3,3)` four-channel block, the exact order-one equation holds
for `endpointLiftFenceSequence`, but the next equation fails.  Consequently
an exact `p=1` endpoint lift cannot by itself inhabit the interval hypothesis
required by shifted uniqueness. -/
theorem endpoint_lifted_row_does_not_supply_shifted_interval :
    JacobiSolutionAt 3 3 3 3 3 endpointLiftFenceSequence 1 ∧
    ¬ (∀ p, 1 ≤ p → p ≤ 3 →
      JacobiSolutionAt 3 3 3 3 3 endpointLiftFenceSequence p) := by
  constructor
  · unfold JacobiSolutionAt endpointLiftFenceSequence
    decide
  · intro h
    have h2 := h 2 (by omega) (by omega)
    have hn : ¬ JacobiSolutionAt 3 3 3 3 3 endpointLiftFenceSequence 2 := by
      unfold JacobiSolutionAt endpointLiftFenceSequence
      decide
    exact hn h2

/-- The missing datum is exactly the next absolute row, not an endpoint
normalization or lower-predecessor side condition. -/
theorem shifted_window_hypothesis_contains_next_row
    (x : Nat → Q')
    (hx : ∀ p, 1 ≤ p → p ≤ 3 → JacobiSolutionAt 3 3 3 3 3 x p) :
    JacobiSolutionAt 3 3 3 3 3 x 2 :=
  hx 2 (by omega) (by omega)

end YMGap.Continuum.SU2OrderedRacahRightJacobiIntervalFence

#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiIntervalFence.endpoint_lifted_row_does_not_supply_shifted_interval
#print axioms YMGap.Continuum.SU2OrderedRacahRightJacobiIntervalFence.shifted_window_hypothesis_contains_next_row
