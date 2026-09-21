/-
# Linear time control for one complete signed pair of Wilson loops

The generic time-zero convexity theorem applies to the whole signed
combination `c*a + d*b`.  An exact source-polynomial identity identifies its
squared time difference with the existing `combinedTimeIncrement`, retaining
the mixed term rather than estimating the two loops separately.

This is an all-strict-nome, fixed-width lattice-time statement.  It supplies
no spatial decay, scaling limit, variance comparison, or continuum claim.
-/

import YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity
import YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement

namespace YMGap.Continuum.BF4WilsonSignedPairTimeControl

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonProbe (SourceLoop)
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindow
open YMGap.Continuum.BF4ExactSlabFixedSpatialWilsonWindowJointCauchy
open YMGap.Continuum.BF4WilsonJointFunctionalLaws (joint_congr difference)
open YMGap.Continuum.BF4WilsonTimeZeroMomentConvexity
open YMGap.Continuum.BF4WilsonAllNomeMixedTimeIncrement
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics

/-- The complete signed pair, placed entirely at time zero. -/
def signedPair {width : Nat} (a b : SourceLoop width) (c d : Q') :
    WindowExpression width :=
  .add (.smul c (.loop 0 a 1)) (.smul d (.loop 0 b 1))

theorem signedPair_within {width : Nat} (a b : SourceLoop width) (c d : Q') :
    Within 0 (signedPair a b c d) :=
  ⟨Nat.le_refl 0, Nat.le_refl 0⟩

private theorem smul_neg_comm (c : Q') (p : RatPoly) :
    RatPolyCoeffEqv (polySmul c (polySmul (-1) p))
      (polySmul (-1) (polySmul c p)) :=
  (RatPolyCoeffEqv.smul_assoc c (-1) p).trans
    ((RatPolyCoeffEqv.smul_coefficient (Q'.mul_comm_eqv c (-1)) p).trans
      (RatPolyCoeffEqv.smul_assoc (-1) c p).symm)

private theorem signed_difference_source
    (p0 pn q0 qn : RatPoly) (c d : Q') :
    RatPolyCoeffEqv
      (polyAdd (polyAdd (polySmul c p0) (polySmul d q0))
        (polySmul (-1) (polyAdd (polySmul c pn) (polySmul d qn))))
      (polyAdd (polySmul c (polyAdd p0 (polySmul (-1) pn)))
        (polySmul d (polyAdd q0 (polySmul (-1) qn)))) := by
  let A := polySmul c p0
  let B := polySmul d q0
  let C := polySmul (-1) (polySmul c pn)
  let D := polySmul (-1) (polySmul d qn)
  have hleft : RatPolyCoeffEqv
      (polyAdd (polyAdd A B)
        (polySmul (-1) (polyAdd (polySmul c pn) (polySmul d qn))))
      (polyAdd (polyAdd A B) (polyAdd C D)) :=
    (RatPolyCoeffEqv.refl (polyAdd A B)).add
      (RatPolyCoeffEqv.smul_add (-1) (polySmul c pn) (polySmul d qn))
  have hc : RatPolyCoeffEqv
      (polySmul c (polyAdd p0 (polySmul (-1) pn))) (polyAdd A C) :=
    (RatPolyCoeffEqv.smul_add c p0 (polySmul (-1) pn)).trans
      ((RatPolyCoeffEqv.refl A).add (smul_neg_comm c pn))
  have hd : RatPolyCoeffEqv
      (polySmul d (polyAdd q0 (polySmul (-1) qn))) (polyAdd B D) :=
    (RatPolyCoeffEqv.smul_add d q0 (polySmul (-1) qn)).trans
      ((RatPolyCoeffEqv.refl B).add (smul_neg_comm d qn))
  have hreorder : RatPolyCoeffEqv
      (polyAdd (polyAdd A B) (polyAdd C D))
      (polyAdd (polyAdd A C) (polyAdd B D)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.var 1)) (.add (.var 2) (.var 3)))
      (.add (.add (.var 0) (.var 2)) (.add (.var 1) (.var 3)))
      (by decide) (fun | 0 => A | 1 => B | 2 => C | _ => D)
  exact hleft.trans (hreorder.trans (hc.add hd).symm)

/-- The generic increment of the complete signed time-zero expression is the
existing combined increment, with all cross terms preserved. -/
theorem timeIncrement_combined {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    Equiv
      (BF4WilsonTimeZeroMomentConvexity.timeIncrement hw0 hw1
        (signedPair a b c d) (signedPair_within a b c d) n)
      (combinedTimeIncrement hw0 hw1 a b c d n) := by
  have hsource : RatPolyCoeffEqv
      (sourcePolynomial
        (BF4WilsonTimeZeroMomentConvexity.timeDifference (signedPair a b c d) n))
      (sourcePolynomial (combinedDifference a b c d n)) := by
    simp only [signedPair, BF4WilsonTimeZeroMomentConvexity.timeDifference,
      combinedDifference, BF4WilsonAllNomeTimeIncrement.timeDifference,
      BF4ExactSlabFixedSpatialWilsonCenteredWindow.shift, mapOffsets,
      difference, sourcePolynomial, Nat.zero_add]
    exact signed_difference_source _ _ _ _ c d
  unfold BF4WilsonTimeZeroMomentConvexity.timeIncrement combinedTimeIncrement
  exact joint_congr hw0 hw1 n _ _ _ _ (hsource.mul hsource)

/-- Linear multi-step control retains the WHOLE signed pair as its one-step
reference energy. -/
theorem combinedTimeIncrement_linear {w : Q'}
    (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {width : Nat} (a b : SourceLoop width) (c d : Q') (n : Nat) :
    leEv (combinedTimeIncrement hw0 hw1 a b c d n)
      (mul (ofQ' (Q'.ofNat n)) (combinedTimeIncrement hw0 hw1 a b c d 1)) := by
  exact leEv_trans
    (leEv_of_equiv (timeIncrement_combined hw0 hw1 a b c d n).symm)
    (leEv_trans
      (BF4WilsonTimeZeroMomentConvexity.timeIncrement_linear hw0 hw1
        (signedPair a b c d) (signedPair_within a b c d) n)
      (leEv_smul_nonneg (Q'.ofNat_nonneg n)
        (leEv_of_equiv (timeIncrement_combined hw0 hw1 a b c d 1))))

end YMGap.Continuum.BF4WilsonSignedPairTimeControl

#print axioms YMGap.Continuum.BF4WilsonSignedPairTimeControl.signedPair_within
#print axioms YMGap.Continuum.BF4WilsonSignedPairTimeControl.timeIncrement_combined
#print axioms YMGap.Continuum.BF4WilsonSignedPairTimeControl.combinedTimeIncrement_linear
