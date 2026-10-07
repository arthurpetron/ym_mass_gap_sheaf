/-
# Actual completed alternating determinant squares

Finite coefficient identities and their explicit omitted-cell payments
meet on the literal E/H/A series completions. No value limit is
differentiated: the endpoint-frequency series is completed separately.
The nome remains named and fixed. These scalar identities do not establish
the Jacobi-product curvature ceiling, an original-action estimate, or a
physical mass gap.
-/

import YMGap.Continuum.ThetaEvenSeriesCompletion
import YMGap.Continuum.ThetaAlternatingEndpointJets
import YMGap.Constructive.CRealAbs
import YMGap.Constructive.CRealMul

namespace YMGap.Continuum.ThetaAlternatingCompletedPin

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.ThetaEvenSeriesCompletion
open YMGap.Continuum.ThetaOneSidedSeriesCompletion
open YMGap.Continuum.ThetaAlternatingMixedRectangle (evenPartial oddPartial)
open YMGap.Continuum.ThetaAlternatingKernel (alternatingPartial)
open YMGap.Continuum.ThetaAlternatingEndpointRectangle (oddEndpointJet evenEndpointJet)
open YMGap.Continuum.ThetaAlternatingMixedPin (alternatingPartial_factored_error_le_epsilon)
open YMGap.Continuum.ThetaAlternatingEndpointJets (endpoint_determinant_square_close)
open YMGap.Continuum.ThetaAngularShellTail (shellTailCutoff)

/-- SAME completed value determinant, with the original one-sided odd series. -/
def mixedDeterminantCReal {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) : CReal :=
  CReal.add
    (CReal.mul (evenCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
      (oddCReal hw0 hw1 hx0 hx1))
    (CReal.neg (CReal.mul (oddCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
      (evenCReal hw0 hw1 hx0 hx1)))

/-- Separately completed ACTUAL endpoint-frequency determinant. -/
def endpointDeterminantCReal {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) : CReal :=
  CReal.add
    (CReal.mul (evenCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
      (oddEndpointCReal hw0 hw1))
    (CReal.neg (CReal.mul (oddCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
      (evenEndpointCReal hw0 hw1)))

/-- Completed K(x)=(x-1)A(x)^2, on the constructed original series. -/
theorem completed_alternating_square_pin {w x : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (hx0 : (-1 : Q') ≤ x) (hx1 : x ≤ (1 : Q')) :
    CReal.Equiv (mixedDeterminantCReal hw0 hw1 hx0 hx1)
      (CReal.mul (CReal.ofQ' (x + -(1 : Q')))
        (CReal.mul (alternatingCReal hw0 hw1 hx0 hx1)
          (alternatingCReal hw0 hw1 hx0 hx1))) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  refine ⟨shellTailCutoff w epsilon, fun N hN => ?_⟩
  change Q'.abs ((evenPartial w 1 N*oddPartial w x N +
    -(oddPartial w 1 N*evenPartial w x N)) +
    -((x + -(1 : Q'))*(alternatingPartial w x N*alternatingPartial w x N))) ≤ epsilon
  exact alternatingPartial_factored_error_le_epsilon hw0 hw1 hx0 hx1 he N hN

/-- Completed endpoint determinant equals A(1)^2. The actual finite endpoint
tail was paid before this join; no derivative/limit interchange is invoked. -/
theorem completed_endpoint_square_pin {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) :
    CReal.Equiv (endpointDeterminantCReal hw0 hw1)
      (CReal.mul (alternatingCReal hw0 hw1 (by decide) (Q'.le_refl' 1))
        (alternatingCReal hw0 hw1 (by decide) (Q'.le_refl' 1))) := by
  apply CReal.Equiv_of_abs_sub_le_all_pos
  intro epsilon he
  apply CReal.leRat_of_eventually
  refine ⟨shellTailCutoff w epsilon, fun N hN => ?_⟩
  change Q'.abs ((evenPartial w 1 N*oddEndpointJet w N +
    -(oddPartial w 1 N*evenEndpointJet w N)) +
    -(alternatingPartial w 1 N*alternatingPartial w 1 N)) ≤ epsilon
  exact endpoint_determinant_square_close hw0 hw1 he N hN

end YMGap.Continuum.ThetaAlternatingCompletedPin

#print axioms YMGap.Continuum.ThetaAlternatingCompletedPin.mixedDeterminantCReal
#print axioms YMGap.Continuum.ThetaAlternatingCompletedPin.endpointDeterminantCReal
#print axioms YMGap.Continuum.ThetaAlternatingCompletedPin.completed_alternating_square_pin
#print axioms YMGap.Continuum.ThetaAlternatingCompletedPin.completed_endpoint_square_pin
