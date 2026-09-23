/- # One actual relative-heat factor has nonpositive integrated angular Hessian -/

import YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
import YMGap.Continuum.QuaternionHaarPolynomialSquareBound

namespace YMGap.Continuum.SU2QuaternionSingleHeatHessian

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4GeometricHaarMehlerProjection
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.BF4ExactSlabAllExtentWeightedFactorization
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionAngularDerivative
open YMGap.Continuum.SU2QuaternionPartialFactorizedHaar
open YMGap.Continuum.SU2QuaternionRelativeHeatPairGeometry
open YMGap.Continuum.SU2QuaternionProductHeatMarginals
open YMGap.Continuum.SU2QuaternionSignedAngularHeatResponse
open YMGap.Continuum.SU2QuaternionProductHeatAngularHessian
open YMGap.Continuum.QuaternionHaarSquareCertificate

local infix:50 " ≈ " => Q'.eqv

private def singletonTerm {n : Nat} (block : Fin n) (first second : Fin 4) :
    AngularTerm n where
  block := block
  first := first
  second := second
  coefficient := 1

private theorem singletonDirection {n : Nat} (block : Fin n)
    (first second : Fin 4) (p : RatPoly) :
    RatPolyCoeffEqv
      (signedAngularDirection [singletonTerm block first second] p)
      (angularDerivative (4*block.val+first.val) (4*block.val+second.val) p) := by
  simp only [signedAngularDirection, applyAngularTerm, singletonTerm]
  exact ((RatPolyCoeffEqv.one_smul _).add (RatPolyCoeffEqv.refl polyZero)).trans
    (RatPolyCoeffEqv.add_zero _)

private theorem direction_congr {n : Nat} (terms : List (AngularTerm n))
    {p q : RatPoly} (h : RatPolyCoeffEqv p q) :
    RatPolyCoeffEqv (signedAngularDirection terms p)
      (signedAngularDirection terms q) := by
  induction terms with
  | nil => exact RatPolyCoeffEqv.refl _
  | cons term rest ih =>
      exact ((angularDerivative_congr _ _ h).smul term.coefficient).add ih

private theorem singletonProductHeat (n : Nat) (w : Q') (K : Nat) (i : Nat) :
    RatPolyCoeffEqv (productHeat n w K [i]) (heatAt i (n+i) w K) := by
  simp only [productHeat, polynomialProduct]
  exact RatPolyCoeffEqv.mul_one _

/-- For an arbitrary supported signed source, the upper-block angular Hessian
of the actual selected relative heat has nonpositive product-Haar integral.
Both copies of the same source remain explicit. -/
theorem heatAt_upperAngularHessian_nonpositive
    (n : Nat) (block : Fin n) (first second : Fin 4)
    (w : Q') (hw : (0 : Q') ≤ w) (K : Nat)
    (a : RatPoly) (ha : SupportedQuaternionBlocks n a) :
    quaternionHaar (n+n)
      (polyMul (polyMul a (liftBoundary n a))
        (angularDerivative (4*(n+block.val)+first.val)
          (4*(n+block.val)+second.val)
          (angularDerivative (4*(n+block.val)+first.val)
            (4*(n+block.val)+second.val)
            (heatAt block.val (n+block.val) w K)))) ≤ 0 := by
  let term := singletonTerm block first second
  let terms := [term]
  have H := productHeat_upperHessian_nonpositive n terms w hw K [block.val]
    (fun i hi => by
      simp only [List.mem_singleton] at hi
      subst i
      exact block.isLt) a ha
  have hp := singletonProductHeat n w K block.val
  have hu : RatPolyCoeffEqv
      (signedAngularDirection (upperTerms terms)
        (signedAngularDirection (upperTerms terms) (productHeat n w K [block.val])))
      (angularDerivative (4*(n+block.val)+first.val) (4*(n+block.val)+second.val)
        (angularDerivative (4*(n+block.val)+first.val) (4*(n+block.val)+second.val)
          (heatAt block.val (n+block.val) w K))) := by
    have houter := singletonDirection (upperTerm term).block
      (upperTerm term).first (upperTerm term).second
      (signedAngularDirection (upperTerms terms) (productHeat n w K [block.val]))
    have hinner := (direction_congr (upperTerms terms) hp).trans
      (singletonDirection (upperTerm term).block (upperTerm term).first
        (upperTerm term).second (heatAt block.val (n+block.val) w K))
    exact houter.trans (angularDerivative_congr _ _ hinner)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (haar_of_coeff (hu.mul_left (polyMul a (liftBoundary n a))).symm)) H

end YMGap.Continuum.SU2QuaternionSingleHeatHessian

#print axioms YMGap.Continuum.SU2QuaternionSingleHeatHessian.heatAt_upperAngularHessian_nonpositive
