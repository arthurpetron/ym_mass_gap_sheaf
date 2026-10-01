/-
# Source-computed continuity of ORIGINAL signed Cayley time

The exact signed displacement identity turns a time near zero into two
nearby positive-real parameters. Numerical real order translates those
differences into the hypotheses of the ORIGINAL source-computed parameter
estimate. Group composition and physical isometry translate this bound to
every signed-time center, using the SAME radius and supplied Rows.

The radius and its complete bound are returned as Type-level data. No
representative of a physical quotient is selected: the original Rows remain
the explicit source of the modulus. This is fixed nome and width, not a
spacing-uniform modulus, maximal-generator calibration or continuum QFT.
-/

import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
import YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity
import YMGap.Continuum.RingNormaliser

namespace YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.SignedRealTimeData
  (SignedTimeValue TimePair pairValue negPair realValue addTime negTime)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSCompletion
  (ComplexBondCompletion Rows ofRows distance)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime
  (signedAction signedAction_ofPair signedAction_addTime signedAction_neg_left
    signedAction_distance pairAction_displacement)
open YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleyPositiveTimeContinuity
  (parameterDelta parameterDelta_positive positiveRealAction_parameter_close_ofRows)

variable {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q')) {width : Nat}

local notation "H" => ComplexBondCompletion hw0 hw1 (width := width)
local notation "R" => Rows hw0 hw1 (width := width)
local notation "D" => distance hw0 hw1
local notation "G" => signedAction hw0 hw1
local notation "rat" q:arg => Quotient.mk crealSetoid (ofQ' q)

private theorem sub_add_cancel (a b : RC) : RCadd (RCsub a b) b = a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem add_comm (a b : RC) : RCadd a b = RCadd b a := by
  refine Quotient.inductionOn₂ a b ?_
  intro A B
  exact Quotient.sound (SumOfSquares.Equiv_of_approx_eqv (fun n =>
    poly_identity_of_normal_eq
      (.add (.var 0) (.var 1)) (.add (.var 1) (.var 0))
      (by decide) (fun | 0 => A.approx n | _ => B.approx n)))

private theorem sub_bound_to_add {a b c : RC} (h : RCle (RCsub a b) c) :
    RCle a (RCadd b c) := by
  have hh := RCadd_le_add h (RCle_refl b)
  rwa [sub_add_cancel,add_comm c b] at hh

/-- Actual distance at arbitrary signed times is the displacement at their
numerically pinned difference, by physical group isometry. -/
theorem signedAction_difference_distance (s t : SignedTimeValue) (x : H) :
    D (G s x) (G t x) = D (G (addTime s (negTime t)) x) x := by
  calc
    D (G s x) (G t x) = D (G (negTime t) (G s x)) (G (negTime t) (G t x)) :=
      (signedAction_distance hw0 hw1 (negTime t) _ _).symm
    _ = D (G (addTime (negTime t) s) x) x := by
      rw [← signedAction_addTime,signedAction_neg_left]
    _ = D (G (addTime s (negTime t)) x) x := by
      rw [SignedRealTimeData.addTime_comm]

/-- Two-sided smallness of the ACTUAL numerical time value controls original
physical displacement. The radius is independent of time presentations. -/
theorem signedAction_near_zero_ofRows (t : SignedTimeValue)
    (X : R) (e : Q') (he : (0 : Q') < e)
    (hpos : RCle (realValue t) (rat (parameterDelta hw0 hw1 X e he)))
    (hneg : RCle (realValue (negTime t)) (rat (parameterDelta hw0 hw1 X e he))) :
    RCle (D (G t (ofRows hw0 hw1 X)) (ofRows hw0 hw1 X)) (rat e) := by
  revert hpos hneg
  refine Quotient.inductionOn t ?_
  intro p hp hn
  change RCle (pairValue p) (rat (parameterDelta hw0 hw1 X e he)) at hp
  change RCle (pairValue (negPair p)) (rat (parameterDelta hw0 hw1 X e he)) at hn
  change RCle (D
    (BF4WilsonAllNomeComplexBondOSScaledCayleySignedTime.pairAction hw0 hw1 p
      (ofRows hw0 hw1 X)) (ofRows hw0 hw1 X)) (rat e)
  rw [pairAction_displacement]
  exact positiveRealAction_parameter_close_ofRows hw0 hw1 p.1 p.2 X e he
    (sub_bound_to_add hp) (sub_bound_to_add hn)

/-- The SAME source-computed zero-time radius works around EVERY signed-time
center. Closeness is measured by the genuine signed numerical difference. -/
theorem signedAction_parameter_close_ofRows (s t : SignedTimeValue)
    (X : R) (e : Q') (he : (0 : Q') < e)
    (hpos : RCle (realValue (addTime s (negTime t)))
      (rat (parameterDelta hw0 hw1 X e he)))
    (hneg : RCle (realValue (negTime (addTime s (negTime t))))
      (rat (parameterDelta hw0 hw1 X e he))) :
    RCle (D (G s (ofRows hw0 hw1 X)) (G t (ofRows hw0 hw1 X))) (rat e) := by
  rw [signedAction_difference_distance]
  exact signedAction_near_zero_ofRows hw0 hw1 (addTime s (negTime t)) X e he hpos hneg

/-- A constructive strong-continuity witness for supplied ORIGINAL Rows.
No physical quotient representative is chosen to manufacture this modulus. -/
def signedContinuityCertificate (X : R) (e : Q') (he : (0 : Q') < e) :
    Σ' delta : Q', ((0 : Q') < delta) ×'
      (∀ s t : SignedTimeValue,
        RCle (realValue (addTime s (negTime t))) (rat delta) →
        RCle (realValue (negTime (addTime s (negTime t)))) (rat delta) →
        RCle (D (G s (ofRows hw0 hw1 X)) (G t (ofRows hw0 hw1 X))) (rat e)) :=
  ⟨parameterDelta hw0 hw1 X e he,parameterDelta_positive hw0 hw1 X e he,
    fun s t hp hn => signedAction_parameter_close_ofRows hw0 hw1 s t X e he hp hn⟩

#print axioms signedAction_difference_distance
#print axioms signedAction_near_zero_ofRows
#print axioms signedAction_parameter_close_ofRows
#print axioms signedContinuityCertificate

end YMGap.Continuum.BF4WilsonAllNomeComplexBondOSScaledCayleySignedTimeContinuity
