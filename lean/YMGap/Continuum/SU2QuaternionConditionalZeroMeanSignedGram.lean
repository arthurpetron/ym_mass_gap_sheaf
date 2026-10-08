/-
# Exact zero-mean consumer of the signed conditional determinant

When the ACTUAL polynomial source moment is coefficientwise zero, the
signed moment determinant is V*(A*G-D^2)-A*E^2. Its existing integrated
order therefore yields the zero-mean bound without an additional marginal
factor or marginal inverse. Every certified surviving insertion remains.

The intended source is the original lastStepPairedResidual, whose exact
mean-zero pin is already produced for arbitrary incoming a,c. This leaf
does not identify c with a polynomial source quotient. The d/dd moments
remain precomputed signed jet moments, not automatically derivatives of
a marginal; original-action instantiation, OS and scaling remain separate.
-/

import YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

namespace YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarAngularCarrier (neg_smul)
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound (cap)
open YMGap.Continuum.QuaternionHaarClearedThreeGram (momentDeterminant centeredFisher)
open YMGap.Continuum.SU2QuaternionConditionalSignedGramReplica
open YMGap.Continuum.SU2QuaternionConditionalSignedGramOrder

/-- The zero-mean determinant is EXACTLY the Fisher product minus A*E^2.
No positivity, support or nonzero-marginal assumption is used in this pin. -/
theorem zero_mean_momentDeterminant_pin (A b D v e G : RatPoly)
    (hb : RatPolyCoeffEqv b polyZero) :
    RatPolyCoeffEqv (momentDeterminant A b D v e G)
      (polyAdd (polyMul v (centeredFisher A D G))
        (polyNeg (polyMul A (polyMul e e)))) := by
  have hbe : RatPolyCoeffEqv (polyMul (polyMul b D) e) polyZero :=
    ((hb.mul_right D).mul_right e).trans
      (((RatPolyCoeffEqv.mul_zero_left D).mul_right e).trans
        (RatPolyCoeffEqv.mul_zero_left e))
  have htwice : RatPolyCoeffEqv
      (polyMul (cap 2) (polyMul (polyMul b D) e)) polyZero :=
    (hbe.mul_left (cap 2)).trans (RatPolyCoeffEqv.mul_zero_right (cap 2))
  have hbb : RatPolyCoeffEqv (polyMul (polyMul b b) G) polyZero :=
    ((hb.mul hb).mul_right G).trans
      (((RatPolyCoeffEqv.mul_zero_left polyZero).mul_right G).trans
        (RatPolyCoeffEqv.mul_zero_left G))
  have hpositive : RatPolyCoeffEqv
      (polyAdd (polyMul (polyMul A v) G) (polyMul (cap 2) (polyMul (polyMul b D) e)))
      (polyMul (polyMul A v) G) :=
    ((RatPolyCoeffEqv.refl _).add htwice).trans (RatPolyCoeffEqv.add_zero _)
  have hnegative : RatPolyCoeffEqv
      (polyAdd (polyAdd (polyMul (polyMul b b) G) (polyMul A (polyMul e e)))
        (polyMul v (polyMul D D)))
      (polyAdd (polyMul A (polyMul e e)) (polyMul v (polyMul D D))) :=
    ((hbb.add (RatPolyCoeffEqv.refl _)).trans (RatPolyCoeffEqv.zero_add _)).add
      (RatPolyCoeffEqv.refl _)
  refine (hpositive.add (RatPolyCoeffEqv.neg hnegative)).trans ?_
  exact coeffEvalExpr_eqv_of_normalize_eq
    (.add (.mul (.mul (.var 0) (.var 2)) (.var 4))
      (.neg (.add (.mul (.var 0) (.mul (.var 3) (.var 3)))
        (.mul (.var 2) (.mul (.var 1) (.var 1))))))
    (.add (.mul (.var 2)
        (.add (.mul (.var 0) (.var 4)) (.neg (.mul (.var 1) (.var 1)))))
      (.neg (.mul (.var 0) (.mul (.var 3) (.var 3)))))
    (by decide) (fun
      | 0 => A | 1 => D | 2 => v | 3 => e | _ => G)

private theorem haar_difference (blocks : Nat) (R p q : RatPoly) :
    Q'.eqv (quaternionHaar blocks (polyMul R (polyAdd p (polyNeg q))))
      (quaternionHaar blocks (polyMul R p) + -quaternionHaar blocks (polyMul R q)) := by
  have hsplit : RatPolyCoeffEqv
      (polyMul R (polyAdd p (polyNeg q)))
      (polyAdd (polyMul R p) (polySmul (-1) (polyMul R q))) :=
    (coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.var 0) (.add (.var 1) (.neg (.var 2))))
      (.add (.mul (.var 0) (.var 1)) (.neg (.mul (.var 0) (.var 2))))
      (by decide) (fun | 0 => R | 1 => p | _ => q)).trans
        ((RatPolyCoeffEqv.refl _).add (neg_smul (polyMul R q)))
  refine Q'.eqv_trans _ _ _ (haar_of_coeff hsplit)
    (Q'.eqv_trans _ _ _ (quaternionHaar_append blocks _ _) ?_)
  exact Q'.add_eqv_congr' (Q'.eqv_refl _)
    (Q'.eqv_trans _ _ _ (quaternionHaar_polySmul blocks (-1) (polyMul R q))
      (poly_identity_of_normal_eq (.mul (.const (-1)) (.var 0)) (.neg (.var 0))
        (by decide) (fun _ => quaternionHaar blocks (polyMul R q))))

/-- The EXACT zero-mean signed Gram consumer, without the extra marginal
factor. The signed Fisher correction stays inside the original integral. -/
theorem conditional_zero_mean_signed_score_bound (tail heads : Nat) (q P d dd phi R : RatPoly)
    {ell upper : Q'}
    (hq : SupportedQuaternionBlocks (tail+heads) q)
    (hP : SupportedQuaternionBlocks (tail+heads) P)
    (hd : SupportedQuaternionBlocks (tail+heads) d)
    (hdd : SupportedQuaternionBlocks (tail+heads) dd)
    (hphi : SupportedQuaternionBlocks (tail+heads) phi)
    (Qcert : Certificate (tail+heads) q)
    (Ccert : Certificate (tail+heads) (polyAdd (polyMul P dd) (polyNeg (polyMul d d))))
    (Rcert : Certificate tail R)
    (hell : (0 : Q') < ell) (hupper : (0 : Q') < upper) (hle : ell ≤ upper)
    (L : Certificate (tail+heads) (polyAdd P (polyNeg (cap ell))))
    (U : Certificate (tail+heads) (polyAdd (cap upper) (polyNeg P)))
    (hzero : RatPolyCoeffEqv (momentB heads q P phi) polyZero) :
    quaternionHaar tail (polyMul R
      (polyMul (momentA heads q P) (polyMul (momentE heads q d phi) (momentE heads q d phi)))) ≤
    quaternionHaar tail (polyMul R
      (polyMul (momentV heads q P phi) (conditionalFisher heads q P d dd))) := by
  have h := conditional_determinant_nonnegative tail heads q P d dd phi R
    hq hP hd hdd hphi Qcert Ccert Rcert hell hupper hle L U
  have hpin := zero_mean_momentDeterminant_pin (momentA heads q P) (momentB heads q P phi)
    (momentD heads q d) (momentV heads q P phi) (momentE heads q d phi) (momentG heads q dd) hzero
  have hdiff : (0 : Q') ≤
      quaternionHaar tail (polyMul R
        (polyMul (momentV heads q P phi) (conditionalFisher heads q P d dd))) +
      -quaternionHaar tail (polyMul R
        (polyMul (momentA heads q P) (polyMul (momentE heads q d phi) (momentE heads q d phi)))) :=
    Q'.le_trans' _ _ _ h (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ (haar_of_coeff (hpin.mul_left R)) (haar_difference tail R _ _)))
  exact Q'.le_of_sub_nonneg hdiff

end YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram

#print axioms YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram.zero_mean_momentDeterminant_pin
#print axioms YMGap.Continuum.SU2QuaternionConditionalZeroMeanSignedGram.conditional_zero_mean_signed_score_bound
