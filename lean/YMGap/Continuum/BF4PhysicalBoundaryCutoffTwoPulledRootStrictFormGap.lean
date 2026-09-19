/-
# Strict finite-stage contraction for the explicit pulled root observable

The fixed cutoff-two pulled carrier has a kernel-checked uniform rate below
one.  Combined with the explicit root-indicator diagonal positivity, it gives
a strict finite-stage form inequality for the same observable at every later
representation cutoff covered by the carrier certificate.

This is still a fixed finite SU(2) carrier result.  It supplies no cofinal
physical capacity comparison, same-theory continuum bridge, or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledNontrivialGapObservable
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRootStrictFormGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledConstructedUniformCRealGap
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledNontrivialGapObservable
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.ClusteringImpliesGap

local infix:50 " ≈ " => Q'.eqv

/-- The explicit root indicator is strictly contracted by the fixed pulled
form at every later cutoff covered by the constructed uniform certificate. -/
theorem cutoffTwoPulledRootIndicator_strict_form_gap
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later) :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
          cutoffTwoPulledRootIndicator) <
      cutoffTwoPulledDiagonalAt later cutoffTwoPulledRootIndicator := by
  let rate := cutoffTwoConstructedUniformGapData.rate
  let diagonal := cutoffTwoPulledDiagonalAt later cutoffTwoPulledRootIndicator
  have hgap := cutoffTwoConstructedUniformGapData.moving_abs_gap
    later hlater cutoffTwoPulledRootIndicator
  have hdiag : (0 : Q') < diagonal := by
    exact cutoffTwoPulledRootIndicator_diagonal_pos later
  have hrate : rate < (1 : Q') :=
    cutoffTwoConstructedUniformGapData.rate_lt_one
  have hscaled : rate * diagonal < (1 : Q') * diagonal :=
    mul_lt_mul_of_pos_right hdiag hrate
  have hscaled' : rate * diagonal < diagonal := by
    exact Q'.lt_of_le_of_lt hscaled
      (Q'.lt_of_eqv (Q'.one_mul_eqv diagonal))
  exact Q'.lt_of_le_of_lt hgap hscaled'

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRootStrictFormGap

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRootStrictFormGap.cutoffTwoPulledRootIndicator_strict_form_gap
