/-
# Rational scalar action on the original full-action completion

The dense vectors and weighted pairing are definitionally those of
`BF4ExactSlabStarFullActionProbe.fullData`. Only the polynomial module law
needed to descend rational scalar multiplication is supplied here. This does
not construct a centered gap or a new completion.
-/

import YMGap.Continuum.BF4ExactSlabStarFullActionProbe
import YMGap.Continuum.HamiltonianScalar

namespace YMGap.Continuum.BF4ExactSlabFullActionScalar

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.GNSQuotient
open YMGap.Continuum.HamiltonianScalar
open YMGap.Continuum.BF4ExactSlabStarFullActionProbe
open YMGap.Continuum.BF4ExactSlabRetainedHeatHeadComparison
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential

/-- The rational scalar action on the SAME original weighted `fullData`. -/
def fullScalarData {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (K extent : Nat) (hK : headCutoff w ≤ K) : SmulGNSData where
  toGNSData := fullData hw0 hw1 K extent hK
  smul_sub := by
    intro c p q
    change RatPolyCoeffEqv (polySmul c (polyAdd p.val (polySmul (-1) q.val)))
      (polyAdd (polySmul c p.val) (polySmul (-1) (polySmul c q.val)))
    exact (RatPolyCoeffEqv.smul_add c p.val _).trans
      ((RatPolyCoeffEqv.refl _).add
        ((RatPolyCoeffEqv.smul_assoc c (-1) q.val).trans
          ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) q.val).trans
            (RatPolyCoeffEqv.smul_assoc (-1) c q.val).symm)))

/-- No transport or alternate carrier is needed at the completed level. -/
theorem fullScalarData_toGNSData {w : Q'} (hw0 : (0 : Q') < w)
    (hw1 : w < (1 : Q')) (K extent : Nat) (hK : headCutoff w ≤ K) :
    (fullScalarData hw0 hw1 K extent hK).toGNSData =
      fullData hw0 hw1 K extent hK := rfl

#print axioms fullScalarData
#print axioms fullScalarData_toGNSData

end YMGap.Continuum.BF4ExactSlabFullActionScalar
