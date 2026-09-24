/-
# The lower test product-heat score is a source derivative pairing

For a test depending only on the lower endpoint, upper angular integration by
parts differentiates only the upper copy of the endpoint source.  Thus this
score is a source response, rather than an upper bound for temporal energy.
The statement is an exact finite original-kernel identity.
-/

import YMGap.Continuum.SU2QuaternionProductHeatScoreCentering

namespace YMGap.Continuum.SU2QuaternionProductHeatScoreSource

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionAngularSupport
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionProductHeatDualForm
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

/-- Every finite signed angular direction kills the constant polynomial. -/
theorem signedAngularDirection_one {n : Nat} :
    ∀ terms : List (AngularTerm n),
      RatPolyCoeffEqv (signedAngularDirection terms polyOne) polyZero
  | [] => .refl _
  | term :: terms =>
      ((((angularDerivative_one _ _).smul term.coefficient).trans
        (RatPolyCoeffEqv.smul_zero term.coefficient)).add
          (signedAngularDirection_one terms)).trans (.zero_add _)

/-- With a lower-only test, the upper kernel score is exactly minus the
kinetic pairing of the differentiated source with the source-weighted test. -/
theorem productHeat_lower_score_eq_source_pair
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (_hids : ∀ i, i ∈ ids → i < n)
    (a f : RatPoly) (ha : SupportedQuaternionBlocks n a)
    (hf : SupportedQuaternionBlocks n f) :
    let R := polyMul a (liftBoundary n a)
    let d := signedAngularDirection (upperTerms terms) (productHeat n w K ids)
    quaternionHaar (n+n) (polyMul R (polyMul d f)) ≈
      -(kineticPair n w K ids (signedAngularDirection terms a)
        (polyMul a f)) := by
  let W := productHeat n w K ids
  let D := signedAngularDirection terms a
  let U := upperTerms terms
  let g := polyMul a f
  let p := polyMul g (liftBoundary n a)
  have hg : SupportedQuaternionBlocks n g := supported_polyMul ha hf
  have hstart : RatPolyCoeffEqv
      (polyMul (polyMul a (liftBoundary n a))
        (polyMul (signedAngularDirection U W) f))
      (polyMul p (signedAngularDirection U W)) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.mul (.mul (.var 0) (.var 1)) (.mul (.var 2) (.var 3)))
      (.mul (.mul (.mul (.var 0) (.var 3)) (.var 1)) (.var 2))
      (by decide) (fun
        | 0 => a
        | 1 => liftBoundary n a
        | 2 => signedAngularDirection U W
        | _ => f)
  have hibp := signedAngular_haar_pair U p W
  have hsource := upperDirection_source terms g a hg
  have hinterior : quaternionHaar (n+n)
      (polyMul (signedAngularDirection U p) W) ≈
      kineticPair n w K ids D g :=
    Q'.eqv_trans _ _ _ (haar_of_coeff (hsource.mul_right W))
      (Q'.eqv_trans _ _ _ (haar_of_coeff (RatPolyCoeffEqv.mul_comm _ _))
        (Q'.eqv_symm (productMap_pairing n w K ids g D)))
  exact Q'.eqv_trans _ _ _ (haar_of_coeff hstart)
    (Q'.eqv_trans _ _ _ hibp (Q'.neg_eqv_congr _ _ hinterior))

/-- For the flat endpoint source, every lower one-point score vanishes,
including nonconstant supported tests and arbitrary finite heat parameters. -/
theorem productHeat_flat_lower_score_zero
    (n : Nat) (terms : List (AngularTerm n)) (w : Q') (K : Nat)
    (ids : List Nat) (hids : ∀ i, i ∈ ids → i < n)
    (f : RatPoly) (hf : SupportedQuaternionBlocks n f) :
    let R := polyMul polyOne (liftBoundary n polyOne)
    let d := signedAngularDirection (upperTerms terms) (productHeat n w K ids)
    quaternionHaar (n+n) (polyMul R (polyMul d f)) ≈ 0 := by
  have hpair := productHeat_lower_score_eq_source_pair n terms w K ids hids
    polyOne f (supported_one n) hf
  have hD := signedAngularDirection_one terms
  have hz : kineticPair n w K ids (signedAngularDirection terms polyOne)
      (polyMul polyOne f) ≈ 0 :=
    Q'.eqv_trans _ _ _
      (haar_of_coeff ((hD.mul_right
        (productMap n w K ids (polyMul polyOne f))).trans
          (RatPolyCoeffEqv.mul_zero_left _)))
      (Q'.eqv_refl 0)
  exact Q'.eqv_trans _ _ _ hpair
    (Q'.eqv_trans _ _ _ (Q'.neg_eqv_congr _ _ hz)
      (by change -(0 : Q') ≈ 0; decide))

end YMGap.Continuum.SU2QuaternionProductHeatScoreSource

#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreSource.signedAngularDirection_one
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreSource.productHeat_lower_score_eq_source_pair
#print axioms YMGap.Continuum.SU2QuaternionProductHeatScoreSource.productHeat_flat_lower_score_zero
