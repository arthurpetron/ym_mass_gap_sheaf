/-
# Chronological original-source pins for the SAME dyadic unit response

The existing completed centered Wilson moment equals the lower-first
chronological original joint limit minus its SAME stationary mean square.
The existing constructive normalizer then gives the literal unit response.
Multiplication by its original norm clears that normalizer; a lag difference
also cancels the mean square exactly.

All original actions, widths, loop sources and completions are retained.
These are scalar identity pins, not relative estimates, changing-family
moduli, carrier identifications or continuum-survival assertions. The
normalizer alpha below is not the coupling parameter.
-/

import YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
import YMGap.Continuum.BF4WilsonJointFunctionalLaws

namespace YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealAlg
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
  (originalJointLimit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonIntrinsicForm (unit)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonPhysicalTime (advance)
open YMGap.Continuum.BF4WilsonAllNomeReflectedForm
  (intrinsicForm intrinsicForm_symm)
open YMGap.Continuum.BF4WilsonAllNomeLoopTimePin (loopState pairing_lag)
open YMGap.Continuum.BF4WilsonAllNomeMomentConvexity
  (lagMoment lagExpression)
open YMGap.Continuum.BF4WilsonAllNomeCenteredMoments (centeredTimeMoment)
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr equiv_sub)
open YMGap.Continuum.BF4DyadicWilsonSquare (side paddedSquare)
open YMGap.Continuum.BF4WilsonAllNomeDyadicUnitExcitation
  (dyadicNormalizer dyadicOriginalNorm dyadicUnitResponse dyadicNormalizer_normalizes)

attribute [local irreducible] originalJointLimit intrinsicForm dyadicNormalizer
  dyadicOriginalNorm dyadicUnitResponse

section Loop

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

private theorem loop_chronological_pin (loop : SourceLoop width) (lag : Nat) :
    Equiv (intrinsicForm hw0 hw1 (loopState loop) (advance lag (loopState loop)))
      (originalJointLimit hw0 hw1 lag
        (.mul (.loop 0 loop 1) (.loop lag loop 1))
        ⟨Nat.zero_le lag, Nat.le_refl lag⟩) := by
  have horder := joint_congr hw0 hw1 lag
    (.mul (.loop lag loop 1) (.loop 0 loop 1))
    (.mul (.loop 0 loop 1) (.loop lag loop 1))
    ⟨Nat.le_refl lag, Nat.zero_le lag⟩ ⟨Nat.zero_le lag, Nat.le_refl lag⟩
    (RatPolyCoeffEqv.mul_comm _ _)
  exact (pairing_lag hw0 hw1 loop lag).trans
    (by simpa only [lagMoment, lagExpression] using horder)

/-- The SAME centered form uses a single stationary mean for both endpoints;
the raw original source is ordered lower slice first. -/
theorem centeredTimeMoment_chronological_pin (loop : SourceLoop width) (lag : Nat) :
    Equiv (centeredTimeMoment hw0 hw1 lag (loopState loop) (loopState loop))
      (sub (originalJointLimit hw0 hw1 lag
        (.mul (.loop 0 loop 1) (.loop lag loop 1))
        ⟨Nat.zero_le lag, Nat.le_refl lag⟩)
        (mul (intrinsicForm hw0 hw1 (loopState loop) (unit width))
          (intrinsicForm hw0 hw1 (loopState loop) (unit width)))) := by
  unfold centeredTimeMoment
  exact equiv_sub (loop_chronological_pin hw0 hw1 loop lag)
    (Pivot2.mul_congr_right (intrinsicForm_symm hw0 hw1 (unit width) (loopState loop)))

end Loop

section Dyadic

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
  (scale width : Nat) (hwidth : side scale < width)

local notation "square" => paddedSquare scale width hwidth
local notation "alpha" => dyadicNormalizer hw0 hw1 scale width hwidth
local notation "Norm" => dyadicOriginalNorm hw0 hw1 scale width hwidth
local notation "Mean" => intrinsicForm hw0 hw1 (loopState square) (unit width)
local notation:max "Joint" lag:arg => originalJointLimit hw0 hw1 lag
  (WindowExpression.mul (WindowExpression.loop 0 square 1)
    (WindowExpression.loop lag square 1))
  (And.intro (Nat.zero_le lag) (Nat.le_refl lag))
local notation:max "Response" lag:arg => dyadicUnitResponse hw0 hw1 scale width hwidth lag

/-- Literal existing normalizer and actual growing-square original source. -/
theorem dyadicUnitResponse_chronological_pin (lag : Nat) :
    Equiv (Response lag)
      (mul alpha (mul alpha (sub (Joint lag) (mul Mean Mean)))) := by
  unfold dyadicUnitResponse
  exact Pivot2.mul_congr_right
    (Pivot2.mul_congr_right (centeredTimeMoment_chronological_pin hw0 hw1 square lag))

private theorem normalizer_clears (moment : CReal) :
    Equiv (mul Norm (mul alpha (mul alpha moment))) moment :=
  (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.mul (.var 0) (.mul (.var 1) (.mul (.var 1) (.var 2))))
      (.mul (.mul (.var 1) (.mul (.var 1) (.var 0))) (.var 2))
      (by decide) (fun
        | 0 => (Norm).approx n
        | 1 => (alpha).approx n
        | _ => moment.approx n))).trans
    ((Pivot2.mul_congr_left (dyadicNormalizer_normalizes hw0 hw1 scale width hwidth)).trans
      (cone_mul moment))

/-- The actual positive norm clears the already constructed inverse-root
square without a supplied uniform norm floor. -/
theorem dyadicUnitResponse_cleared_pin (lag : Nat) :
    Equiv (mul Norm (Response lag)) (sub (Joint lag) (mul Mean Mean)) :=
  (Pivot2.mul_congr_right
    (dyadicUnitResponse_chronological_pin hw0 hw1 scale width hwidth lag)).trans
    (normalizer_clears hw0 hw1 scale width hwidth (sub (Joint lag) (mul Mean Mean)))

/-- BOTH lags use the SAME center and normalizer, so only the two literal
chronological raw joint limits remain in the cleared difference. -/
theorem dyadicUnitResponse_difference_cleared_pin (L J : Nat) :
    Equiv (mul Norm (sub (Response L) (Response J))) (sub (Joint L) (Joint J)) := by
  have hdistribute : Equiv (mul Norm (sub (Response L) (Response J)))
      (sub (mul Norm (Response L)) (mul Norm (Response J))) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
        (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
        (by decide) (fun
          | 0 => (Norm).approx n
          | 1 => (Response L).approx n
          | _ => (Response J).approx n))
  have hcenter : Equiv (sub (sub (Joint L) (mul Mean Mean))
      (sub (Joint J) (mul Mean Mean))) (sub (Joint L) (Joint J)) :=
    SumOfSquares.Equiv_of_approx_eqv (fun n =>
      poly_identity_of_normal_eq
        (.add (.add (.var 0) (.neg (.var 2)))
          (.neg (.add (.var 1) (.neg (.var 2)))))
        (.add (.var 0) (.neg (.var 1))) (by decide) (fun
          | 0 => (Joint L).approx n
          | 1 => (Joint J).approx n
          | _ => (mul Mean Mean).approx n))
  exact hdistribute.trans
    ((equiv_sub (dyadicUnitResponse_cleared_pin hw0 hw1 scale width hwidth L)
      (dyadicUnitResponse_cleared_pin hw0 hw1 scale width hwidth J)).trans hcenter)

end Dyadic

#print axioms centeredTimeMoment_chronological_pin
#print axioms dyadicUnitResponse_chronological_pin
#print axioms dyadicUnitResponse_cleared_pin
#print axioms dyadicUnitResponse_difference_cleared_pin

end YMGap.Continuum.BF4WilsonAllNomeDyadicChronologicalResponse
