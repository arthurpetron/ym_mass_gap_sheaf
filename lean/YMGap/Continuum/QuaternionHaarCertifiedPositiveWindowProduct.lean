/-
# Certified multiplication of positive polynomial windows

Exact one-sided lower and upper certificates multiply on the same original
quaternion Haar carrier. The lower certificate reuses the existing product
floor compiler; the upper certificate is built from the two positive upper
residuals. No product bound is assumed as an input.
-/

import YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor

namespace YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.RingNormaliser
open YMGap.Continuum.BF4CompactActionCPOrder
open YMGap.Continuum.BF4ExactCutoffOneSurfaceForestGaugeWordCarrierSemantics
open YMGap.Continuum.SU2QuaternionPolynomialHaarCarrier
open YMGap.Continuum.SU2QuaternionRatPolyDifferential
open YMGap.Continuum.SU2QuaternionArbitraryHaarRadialPositivity
open YMGap.Continuum.QuaternionHaarSquareCertificate
open YMGap.Continuum.QuaternionHaarPolynomialSquareBound
open YMGap.Continuum.SU2QuaternionProductHeatPositiveFloor

/-- Output data for multiplying two positive windows. The lower/upper fields
are actual sum-of-squares certificates on the shared carrier, not scalar
claims inferred from a different measure. -/
structure PositiveWindowProduct (blocks : Nat) (p q : RatPoly)
    (ellP upperP ellQ upperQ : Q') : Type where
  support : SupportedQuaternionBlocks blocks (polyMul p q)
  positiveP : Certificate blocks p
  positiveQ : Certificate blocks q
  lowerCertificate : Certificate blocks
    (polyAdd (polyMul p q) (polyNeg (cap (ellP * ellQ))))
  upperCertificate : Certificate blocks
    (polyAdd (cap (upperP * upperQ)) (polyNeg (polyMul p q)))
  lowerPositive : (0 : Q') < ellP * ellQ
  upperPositive : (0 : Q') < upperP * upperQ
  endpointsOrdered : ellP * ellQ ≤ upperP * upperQ

/-- The original lower residual constructs positivity of the SAME factor. -/
def positiveFromLowerWindow {blocks : Nat} {p : RatPoly} {ell : Q'}
    (hLower : Certificate blocks (polyAdd p (polyNeg (cap ell))))
    (hEll : (0 : Q') ≤ ell) : Certificate blocks p := by
  let S := hLower.add (Certificate.constant blocks ell hEll)
  have h : RatPolyCoeffEqv
      (polyAdd (polyAdd p (polyNeg (cap ell))) (cap ell)) p :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.add (.var 0) (.neg (.var 1))) (.var 1)) (.var 0)
      (by decide) (fun | 0 => p | _ => cap ell)
  exact Certificate.ofCoeff h.symm S

/-- Multiply two finite positive windows. Lower and upper endpoints, their
strict positivity, and their order are all produced from the supplied
factor windows. -/
def multiplyPositiveWindows {blocks : Nat} {p q : RatPoly}
    {ellP upperP ellQ upperQ : Q'}
    (hp : SupportedQuaternionBlocks blocks p)
    (hq : SupportedQuaternionBlocks blocks q)
    (hEllP : (0 : Q') < ellP) (hUpperP : (0 : Q') < upperP)
    (hEllQ : (0 : Q') < ellQ) (hUpperQ : (0 : Q') < upperQ)
    (hOrderP : ellP ≤ upperP) (hOrderQ : ellQ ≤ upperQ)
    (lowerP : Certificate blocks (polyAdd p (polyNeg (cap ellP))))
    (upperPcert : Certificate blocks (polyAdd (cap upperP) (polyNeg p)))
    (lowerQ : Certificate blocks (polyAdd q (polyNeg (cap ellQ))))
    (upperQcert : Certificate blocks (polyAdd (cap upperQ) (polyNeg q))) :
    PositiveWindowProduct blocks p q ellP upperP ellQ upperQ := by
  let pPositive := positiveFromLowerWindow lowerP (Q'.le_of_lt hEllP)
  let qPositive := positiveFromLowerWindow lowerQ (Q'.le_of_lt hEllQ)
  let lowerCertificate := Certificate.productFloor qPositive lowerP lowerQ
    (Q'.le_of_lt hEllP)
  let upperSource := upperPcert.mul qPositive
    |>.add ((Certificate.constant blocks upperP (Q'.le_of_lt hUpperP)).mul upperQcert)
  have hRaw : RatPolyCoeffEqv
      (polyAdd
        (polyMul (polyAdd (cap upperP) (polyNeg p)) q)
        (polyMul (cap upperP) (polyAdd (cap upperQ) (polyNeg q))))
      (polyAdd (polyMul (cap upperP) (cap upperQ))
        (polyNeg (polyMul p q))) :=
    coeffEvalExpr_eqv_of_normalize_eq
      (.add (.mul (.add (.var 2) (.neg (.var 0))) (.var 1))
        (.mul (.var 2) (.add (.var 3) (.neg (.var 1)))))
      (.add (.mul (.var 2) (.var 3)) (.neg (.mul (.var 0) (.var 1))))
      (by decide) (fun | 0 => p | 1 => q | 2 => cap upperP | _ => cap upperQ)
  have hCap : RatPolyCoeffEqv
      (polyAdd (polyMul (cap upperP) (cap upperQ)) (polyNeg (polyMul p q)))
      (polyAdd (cap (upperP * upperQ)) (polyNeg (polyMul p q))) :=
    (cap_mul upperP upperQ).add (RatPolyCoeffEqv.refl _)
  let upperCertificate := Certificate.ofCoeff (hRaw.trans hCap).symm upperSource
  have hMid : ellP * ellQ ≤ ellP * upperQ :=
    Q'.mul_le_mul_of_nonneg_left _ _ ellP hOrderQ (Q'.le_of_lt hEllP)
  have hEnd : ellP * upperQ ≤ upperP * upperQ :=
    Q'.mul_le_mul_of_nonneg_right _ _ upperQ hOrderP (Q'.le_of_lt hUpperQ)
  exact {
    support := supported_polyMul hp hq
    positiveP := pPositive
    positiveQ := qPositive
    lowerCertificate := lowerCertificate
    upperCertificate := upperCertificate
    lowerPositive := Q'.mul_pos hEllP hEllQ
    upperPositive := Q'.mul_pos hUpperP hUpperQ
    endpointsOrdered := Q'.le_trans' _ _ _ hMid hEnd
  }

end YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct

#print axioms YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct.multiplyPositiveWindows
#print axioms YMGap.Continuum.QuaternionHaarCertifiedPositiveWindowProduct.positiveFromLowerWindow
